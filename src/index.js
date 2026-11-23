// ■ 환경변수
//   PROXY_PASSWORD  (Secret) 비밀번호
//   API_이름        (Secret) 서비스 계정 JSON. API_namea, API_nameb 식으로 여러 개 등록 가능 (429 걸리면 전환됨)
//   USE_KEYS        (Text)   (선택) 사용할 키 이름 목록. 예: API_namea, API_nameb (쉼표/공백/줄바꿈 구분)
//                            비워두면 등록된 API_* 전부 순환. 값이 있으면 목록에 적힌 키만 순환에 사용됨
//   MODELS          (Text)   사용할 모델명 (alias=real 형태 지원)
//   UPSTREAM_MODE   (Text)   (선택) 기본 auto (Gemini 채팅은 네이티브, 도구 호출/비-Gemini는 openapi). 강제: native | openapi

const fakeChat = (msg) => JSON.stringify({
  id: "proxy-error", object: "chat.completion",
  choices: [{ index: 0, finish_reason: "stop",
    message: { role: "assistant", content: msg } }],
});

const enc = new TextEncoder();
const b64u = (buf) => {
  const u = new Uint8Array(buf);
  let s = "";
  for (let i = 0; i < u.length; i++) s += String.fromCharCode(u[i]);
  return btoa(s).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
};
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const once = (fn) => { let done = false, v; return () => (done ? v : ((done = true), (v = fn()))); };
const lexLess = (a, b) => {
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return a[i] < b[i];
  return false;
};

const ATTEMPT_TIMEOUT_MS = 300_000;   // 업스트림 첫 바이트(헤더 + 첫 청크)까지 3분. 초과 시 다른 키/홉으로 1회 재시도
const RETRY_WINDOW_MS = 45_000;       // 429/5xx 재시도(백오프 포함) 허용 시간
const TOKEN_TIMEOUT_MS = 15_000;
const STREAM_IDLE_MS = 300_000;       // 스트림 도중 업스트림 무응답 한도
const FAST_WINDOW_MS = 8_000;         // 이 시간 안에 결과가 나오면 정상 상태코드로 응답, 넘으면 200 + keepalive 로 전환
const PING_MS = 5_000;                // 클라이언트 keepalive 간격
const TOKEN_FAIL_COOLDOWN = 300_000;
const AUTH_FAIL_COOLDOWN = 300_000;
const NET_FAIL_COOLDOWN = 5_000;
const TRANSIENT_COOLDOWN = 5_000;
const KEY_429_BASE = 5_000;           // 키별 429 쿨다운: 5s → 10s → 20s → 40s → 60s (성공 시 리셋)
const KEY_429_MAX = 60_000;
const MAX_RETRY_AFTER_MS = 600_000;
const MAX_HONOR_RETRY_AFTER_MS = 15_000;
const BACKOFF_BASE_MS = 1_000;        // 모든 키가 쿨다운일 때 대기: 1s → 2s → 4s → 8s → 10s ...
const BACKOFF_MAX_MS = 10_000;
const MAX_TOTAL_ATTEMPTS = 6;        // 요청 1건당 업스트림 호출 상한
const MAX_SUBREQUESTS = 45;           // 무료 플랜 서브리퀘스트 50개 한도 보호 (토큰 발급 포함)
const MAX_TIMEOUT_RETRIES = 1;
const MAX_STOP = 5;
const HOP_COOLDOWN_STEPS = [20_000, 120_000, 600_000];
const HOP_429_COOLDOWN = 10_000;
const RETRYABLE = new Set([408, 429, 500, 502, 503, 504]);
const PING = enc.encode(": keepalive\n\n");

const CORS = {
  "Access-Control-Allow-Origin": "*",
  "Access-Control-Allow-Methods": "GET,POST,OPTIONS",
  "Access-Control-Allow-Headers": "*",
};

const SAFETY_OFF = [
  "HARM_CATEGORY_HARASSMENT",
  "HARM_CATEGORY_HATE_SPEECH",
  "HARM_CATEGORY_SEXUALLY_EXPLICIT",
  "HARM_CATEGORY_DANGEROUS_CONTENT",
].map((category) => ({ category, threshold: "OFF" }));

const tokenCache = new Map();
const cryptoKeyCache = new Map();
const cooldownUntil = new Map();
const keyFailStreak = new Map();
const hopCooldownUntil = new Map();
const hopFailStreak = new Map();
const noThoughtsModels = new Set();
let lastGoodHop = "direct";
let rrCursor = Math.floor(Math.random() * 1000);

const errMsg = (e) => (e && e.message) || String(e);
const jsonError = (status, message) =>
  new Response(JSON.stringify({ error: { message } }), {
    status,
    headers: { "Content-Type": "application/json", ...CORS },
  });
const sseError = (message, code) =>
  `\ndata: ${JSON.stringify({ error: { message, ...(code ? { code } : {}) } })}\n\ndata: [DONE]\n\n`;

function withTimeout(promise, ms, label, onTimeout) {
  let t;
  const timer = new Promise((_, rej) => {
    t = setTimeout(() => {
      try { onTimeout && onTimeout(); } catch {}
      const e = new Error(label || `timeout (${Math.round(ms / 1000)}s)`);
      e.timeout = true;
      rej(e);
    }, ms);
  });
  return Promise.race([promise, timer]).finally(() => clearTimeout(t));
}

async function raceWindow(promise, ms) {
  let t;
  const timer = new Promise((r) => { t = setTimeout(() => r(null), ms); });
  try { return await Promise.race([promise, timer]); } finally { clearTimeout(t); }
}

function parseRetryAfter(v) {
  if (!v) return 0;
  const n = Number(v);
  if (Number.isFinite(n) && n > 0) return Math.min(n * 1000, MAX_RETRY_AFTER_MS);
  const d = Date.parse(v);
  return Number.isFinite(d) ? Math.min(Math.max(0, d - Date.now()), MAX_RETRY_AFTER_MS) : 0;
}

const backoffMs = (n) =>
  Math.round(Math.min(BACKOFF_MAX_MS, BACKOFF_BASE_MS * 2 ** Math.max(0, n - 1)) * (0.75 + Math.random() * 0.5));

function unwrapVertexError(text) {
  try {
    const j = JSON.parse(text);
    if (Array.isArray(j) && j[0]?.error) return JSON.stringify({ error: j[0].error });
  } catch {}
  return text;
}

function upstreamMsg(status, text, tried) {
  let m = text;
  try {
    const j = JSON.parse(text);
    m = j?.error?.message || (Array.isArray(j) && j[0]?.error?.message) || text;
  } catch {}
  return `[upstream ${status}] ${String(m).slice(0, 800)}${tried.length ? ` (tried=${tried.join(",")})` : ""}`;
}

function withMeta(res, name, hopName, tried, mode, body = res.body, extraHeaders = null) {
  const h = new Headers(res.headers);
  for (const [k, v] of Object.entries(CORS)) h.set(k, v);
  h.set("x-proxy-key", name);
  if (hopName) h.set("x-proxy-hop", hopName);
  if (mode) h.set("x-proxy-mode", mode);
  if (tried.length) h.set("x-proxy-tried", tried.join(","));
  if (extraHeaders) {
    for (const [k, v] of Object.entries(extraHeaders)) h.set(k, v);
  }
  if (body !== res.body) {
    h.delete("content-length");
    h.delete("content-encoding");
  }
  return new Response(body, { status: res.status, statusText: res.statusText, headers: h });
}

function parseCred(raw) {
  try { return JSON.parse(raw); } catch {}
  const g = (key) => (raw.match(new RegExp(`"${key}"\\s*:\\s*"([\\s\\S]*?)"\\s*[,}]`)) || [])[1];
  const pk = g("private_key");
  return {
    client_email: g("client_email"),
    project_id: g("project_id"),
    private_key: pk && pk.replace(/\\n/g, "\n"),
    token_uri: g("token_uri"),
  };
}

let keysMemo = null;
function loadKeys(env) {
  if (keysMemo) return keysMemo;
  const keys = [], bad = [];
  const allow = String(env.USE_KEYS || "").split(/[\s,]+/).filter(Boolean);
  const allowSet = allow.length ? new Set(allow) : null;
  const missing = allow.filter((n) => typeof env[n] !== "string");
  for (const name of Object.keys(env).filter((k) => k.startsWith("API_") && (!allowSet || allowSet.has(k))).sort()) {
    const raw = env[name];
    if (typeof raw !== "string") continue;
    const cred = parseCred(raw);
    if (cred && cred.client_email && cred.private_key && cred.project_id) keys.push({ name, cred });
    else bad.push(name);
  }
  return (keysMemo = { keys, bad, missing, filtered: !!allowSet });
}

function loadHops(env) {
  const hops = [{ name: "direct", binding: null }];
  for (const name of Object.keys(env).filter((k) => k.startsWith("HOP_")).sort()) {
    if (env[name] && typeof env[name].fetch === "function") {
      hops.push({ name, binding: env[name] });
    }
  }
  return hops;
}

function parseModels(env) {
  const map = new Map();
  for (const item of String(env.MODELS || "").split(/[\s,]+/).filter(Boolean)) {
    const [alias, real] = item.includes("=") ? item.split("=") : [item, item];
    map.set(alias, real);
  }
  return map;
}

async function* idleRead(body, ms) {
  const reader = body.getReader();
  try {
    while (true) {
      const r = await withTimeout(reader.read(), ms, `upstream idle timeout (${ms / 1000}s)`);
      if (r.done) return;
      yield r.value;
    }
  } finally {
    reader.cancel().catch(() => {});
  }
}

async function primeBody(res, ms, label, onTimeout) {
  if (!res.body) return res;
  const reader = res.body.getReader();
  let first;
  try {
    first = await withTimeout(reader.read(), ms, label, onTimeout);
  } catch (e) {
    reader.cancel().catch(() => {});
    throw e;
  }
  const body = new ReadableStream({
    start(c) {
      if (first.done) c.close();
      else c.enqueue(first.value);
    },
    async pull(c) {
      const { done, value } = await reader.read();
      if (done) c.close();
      else c.enqueue(value);
    },
    cancel(reason) {
      return reader.cancel(reason);
    },
  });
  return new Response(body, { status: res.status, statusText: res.statusText, headers: res.headers });
}

function heartbeatStream(ctx, producer, initialPing) {
  const { readable, writable } = new TransformStream();
  const w = writable.getWriter();
  let last = Date.now();
  let atLineStart = true;
  let finished = false;
  const write = (bytes) => {
    last = Date.now();
    if (bytes.length) atLineStart = bytes[bytes.length - 1] === 10;
    return w.write(bytes);
  };
  const timer = setInterval(() => {
    if (finished || !atLineStart || Date.now() - last < PING_MS) return;
    write(PING).catch(() => {});
  }, 1_000);
  ctx.waitUntil((async () => {
    try {
      if (initialPing) await write(PING);
      await producer(write);
    } catch (e) {
      await write(enc.encode(sseError("[proxy] " + errMsg(e)))).catch(() => {});
    } finally {
      finished = true;
      clearInterval(timer);
      await w.close().catch(() => {});
    }
  })());
  return readable;
}

async function collectOpenAISSE(body, ms) {
  const choices = new Map();
  let meta = null, usage = null, err = null;

  const handle = (line) => {
    if (!line.startsWith("data:")) return;
    const p = line.slice(5).trim();
    if (!p || p === "[DONE]") return;
    let o;
    try { o = JSON.parse(p); } catch { return; }
    if (o.error) { err = o; return; }
    if (!meta) meta = { id: o.id, created: o.created, model: o.model };
    if (o.usage) usage = o.usage;
    for (const ch of o.choices || []) {
      const i = ch.index ?? 0;
      let c = choices.get(i);
      if (!c) choices.set(i, (c = { content: "", reasoning: "", tools: [], finish: null }));
      const d = ch.delta || {};
      if (typeof d.content === "string") c.content += d.content;
      if (typeof d.reasoning_content === "string") c.reasoning += d.reasoning_content;
      if (Array.isArray(d.tool_calls)) {
        for (const tc of d.tool_calls) {
          const ti = tc.index ?? c.tools.length;
          const t = c.tools[ti] ||
            (c.tools[ti] = { id: tc.id, type: tc.type || "function", function: { name: "", arguments: "" } });
          if (tc.id) t.id = tc.id;
          if (tc.function?.name) t.function.name = tc.function.name;
          if (tc.function?.arguments) t.function.arguments += tc.function.arguments;
        }
      }
      if (ch.finish_reason) c.finish = ch.finish_reason;
    }
  };

  const dec = new TextDecoder();
  let carry = "";
  for await (const chunk of idleRead(body, ms)) {
    carry += dec.decode(chunk, { stream: true });
    const lines = carry.split("\n");
    carry = lines.pop();
    lines.forEach(handle);
  }
  carry += dec.decode();
  if (carry) handle(carry);

  if (err) return { error: err };
  return {
    json: {
      id: meta?.id || "chatcmpl-proxy",
      object: "chat.completion",
      created: meta?.created || Math.floor(Date.now() / 1000),
      model: meta?.model,
      choices: [...choices.entries()].sort((a, b) => a[0] - b[0]).map(([index, c]) => {
        const tools = c.tools.filter(Boolean);
        const message = { role: "assistant", content: c.content || (tools.length ? null : "") };
        if (c.reasoning) { message.reasoning_content = c.reasoning; message.reasoning = c.reasoning; }
        if (tools.length) message.tool_calls = tools;
        return { index, message, finish_reason: c.finish || "stop" };
      }),
      ...(usage ? { usage } : {}),
    },
  };
}

const EFFORT_TO_LEVEL = {
  minimal: "low", minimum: "low", low: "low",
  medium: "medium",
  high: "high", xhigh: "high", max: "high", maximum: "high",
};
const EFFORT_TO_BUDGET = {
  minimal: 512, minimum: 512, low: 2048,
  medium: 8192,
  high: 24576, xhigh: 24576, max: 24576, maximum: 24576,
};

function canUseNative(body, bareModel, mode) {
  if (mode === "openapi") return false;
  if (!/^gemini-/i.test(bareModel)) return false;
  if (mode === "native") return true;
  if (body.tools || body.functions || body.tool_choice || body.audio || body.modalities) return false;
  if (body.n != null && Number(body.n) > 1) return false;
  if (body.response_format && body.response_format.type &&
      body.response_format.type !== "text" && body.response_format.type !== "json_object") {
    return false;
  }
  for (const m of Array.isArray(body.messages) ? body.messages : []) {
    if (!m || typeof m !== "object") continue;
    if (m.role === "tool" || m.role === "function" || m.tool_calls || m.function_call) return false;
    if (Array.isArray(m.content)) {
      for (const p of m.content) {
        if (!p || typeof p === "string") continue;
        if (p.type === "text") continue;
        if (p.type === "image_url") {
          const u = typeof p.image_url === "string" ? p.image_url : p.image_url?.url;
          if (!/^data:([^;,]+);base64,(.+)$/s.test(u || "")) return false;
          continue;
        }
        return false;
      }
    }
  }
  return true;
}

function partsOf(content) {
  if (typeof content === "string") return content ? [{ text: content }] : [];
  const out = [];
  for (const p of Array.isArray(content) ? content : []) {
    if (typeof p === "string") { if (p) out.push({ text: p }); continue; }
    if (p?.type === "text" && p.text) out.push({ text: String(p.text) });
    else if (p?.type === "image_url") {
      const u = typeof p.image_url === "string" ? p.image_url : p.image_url?.url;
      const m = /^data:([^;,]+);base64,(.+)$/s.exec(u || "");
      if (m) out.push({ inlineData: { mimeType: m[1], data: m[2] } });
    }
  }
  return out;
}

function buildNativePayload(body, bareModel, allowThoughts) {
  const system = [];
  const contents = [];
  let lead = true;

  for (const m of Array.isArray(body.messages) ? body.messages : []) {
    if (!m || typeof m !== "object") continue;
    const parts = partsOf(m.content);
    if (!parts.length) continue;
    if ((m.role === "system" || m.role === "developer") && lead) {
      system.push(...parts);
      continue;
    }
    lead = false;
    const role = m.role === "assistant" ? "model" : "user";
    const last = contents[contents.length - 1];
    if (last && last.role === role) last.parts.push(...parts);
    else contents.push({ role, parts });
  }
  if (!contents.length) contents.push({ role: "user", parts: [{ text: " " }] });

  const num = (v) => (typeof v === "number" && Number.isFinite(v) ? v : undefined);
  const g = {};
  const set = (k, v) => { if (v !== undefined && v !== null) g[k] = v; };
  set("temperature", num(body.temperature));
  set("topP", num(body.top_p));
  set("topK", num(body.top_k));
  set("maxOutputTokens", num(body.max_completion_tokens) ?? num(body.max_tokens));
  set("seed", num(body.seed));

  const ver = /gemini-(\d+)/i.exec(bareModel);
  if (!(ver && Number(ver[1]) >= 4)) {
    if (num(body.frequency_penalty)) g.frequencyPenalty = body.frequency_penalty;
    if (num(body.presence_penalty)) g.presencePenalty = body.presence_penalty;
  }

  const rawStop = Array.isArray(body.stop) ? body.stop : body.stop ? [body.stop] : [];
  const stop = [...new Set(rawStop.filter((x) => typeof x === "string" && x !== ""))].slice(0, MAX_STOP);
  if (stop.length) g.stopSequences = stop;

  if (body.response_format?.type === "json_object") {
    g.responseMimeType = "application/json";
  }

  const base = { contents, generationConfig: g, safetySettings: SAFETY_OFF };
  if (system.length) base.systemInstruction = { parts: system };

  const eff = body.reasoning_effort == null ? null : String(body.reasoning_effort).toLowerCase();
  if (!allowThoughts || eff === "none" || noThoughtsModels.has(bareModel)) {
    return { base, thought: null };
  }

  const tc = { includeThoughts: true };
  if (eff !== null) {
    if (/gemini-2\.5/i.test(bareModel)) {
      if (EFFORT_TO_BUDGET[eff]) tc.thinkingBudget = EFFORT_TO_BUDGET[eff];
    } else if (EFFORT_TO_LEVEL[eff]) {
      tc.thinkingLevel = EFFORT_TO_LEVEL[eff];
    }
  }
  return { base, thought: { ...base, generationConfig: { ...g, thinkingConfig: tc } } };
}

const mapFinishReason = (r) => {
  if (!r) return null;
  if (r === "STOP") return "stop";
  if (r === "MAX_TOKENS") return "length";
  if (["SAFETY", "RECITATION", "BLOCKLIST", "PROHIBITED_CONTENT", "SPII", "IMAGE_SAFETY"].includes(r)) {
    return "content_filter";
  }
  return "stop";
};

const mapUsage = (u) => u ? {
  prompt_tokens: u.promptTokenCount || 0,
  completion_tokens: (u.candidatesTokenCount || 0) + (u.thoughtsTokenCount || 0),
  total_tokens: u.totalTokenCount || 0,
} : undefined;

function extractNativeChunk(j) {
  const c = j?.candidates?.[0];
  let content = "", reasoning = "";
  for (const p of c?.content?.parts || []) {
    if (typeof p.text !== "string") continue;
    if (p.thought) reasoning += p.text;
    else content += p.text;
  }
  return {
    content,
    reasoning,
    finish: mapFinishReason(c?.finishReason),
    usage: mapUsage(j?.usageMetadata),
    blocked: j?.promptFeedback?.blockReason || "",
  };
}

async function* parseNativeSSE(body, ms) {
  const dec = new TextDecoder();
  let carry = "";
  for await (const chunk of idleRead(body, ms)) {
    carry += dec.decode(chunk, { stream: true });
    const lines = carry.split("\n");
    carry = lines.pop();
    for (const raw of lines) {
      const line = raw.trim();
      if (!line.startsWith("data:")) continue;
      const p = line.slice(5).trim();
      if (!p || p === "[DONE]") continue;
      try { yield JSON.parse(p); } catch {}
    }
  }
  carry += dec.decode();
  const tail = carry.trim();
  if (tail.startsWith("data:")) {
    const p = tail.slice(5).trim();
    if (p && p !== "[DONE]") {
      try { yield JSON.parse(p); } catch {}
    }
  }
}

async function pumpNative(body, write, model) {
  const id = "chatcmpl-" + crypto.randomUUID();
  const created = Math.floor(Date.now() / 1000);
  const send = (delta, finish = null, usage) =>
    write(enc.encode("data: " + JSON.stringify({
      id, object: "chat.completion.chunk", created, model,
      choices: [{ index: 0, delta, finish_reason: finish }],
      ...(usage ? { usage } : {}),
    }) + "\n\n"));

  await send({ role: "assistant", content: "" });
  let finish = null, usage;
  for await (const j of parseNativeSSE(body, STREAM_IDLE_MS)) {
    if (j?.error) {
      await write(enc.encode("data: " + JSON.stringify({ error: j.error }) + "\n\ndata: [DONE]\n\n"));
      return;
    }
    const p = extractNativeChunk(j);
    if (p.blocked) {
      await write(enc.encode("data: " + JSON.stringify({
        error: { message: "Blocked by Google: " + p.blocked, type: "content_filter" },
      }) + "\n\n"));
      finish = "content_filter";
      break;
    }
    if (p.reasoning) await send({ reasoning_content: p.reasoning, reasoning: p.reasoning });
    if (p.content) await send({ content: p.content });
    if (p.finish) finish = p.finish;
    if (p.usage) usage = p.usage;
  }
  await send({}, finish || "stop", usage);
  await write(enc.encode("data: [DONE]\n\n"));
}

async function pumpOpenAI(body, write, thoughts, marker) {
  if (!thoughts) {
    for await (const c of idleRead(body, STREAM_IDLE_MS)) await write(c);
    return;
  }
  const dec = new TextDecoder();
  const states = new Map();
  let carry = "";
  for await (const chunk of idleRead(body, STREAM_IDLE_MS)) {
    carry += dec.decode(chunk, { stream: true });
    const lines = carry.split("\n");
    carry = lines.pop();
    if (lines.length) {
      await write(enc.encode(lines.map((l) => rewriteLine(l, states, marker)).join("\n") + "\n"));
    }
  }
  carry += dec.decode();
  if (carry) await write(enc.encode(rewriteLine(carry, states, marker) + "\n"));
}

async function collectNativeSSE(body, ms, model) {
  let content = "", reasoning = "", finish = null, usage, err = null;
  for await (const j of parseNativeSSE(body, ms)) {
    if (j?.error) { err = { error: j.error }; break; }
    const p = extractNativeChunk(j);
    if (p.blocked) {
      err = { error: { message: "Blocked by Google: " + p.blocked, code: 400, type: "content_filter" } };
      break;
    }
    content += p.content;
    reasoning += p.reasoning;
    if (p.finish) finish = p.finish;
    if (p.usage) usage = p.usage;
  }
  if (err && !content) return { error: err };
  const message = { role: "assistant", content };
  if (reasoning) {
    message.reasoning_content = reasoning;
    message.reasoning = reasoning;
  }
  return {
    json: {
      id: "chatcmpl-" + crypto.randomUUID(),
      object: "chat.completion",
      created: Math.floor(Date.now() / 1000),
      model,
      choices: [{ index: 0, message, finish_reason: finish || "stop" }],
      ...(usage ? { usage } : {}),
    },
  };
}

function injectOpenAIThoughts(src, bareModel) {
  if (noThoughtsModels.has(bareModel)) return null;
  const eff = src.reasoning_effort == null ? null : String(src.reasoning_effort).toLowerCase();
  if (eff === "none") return null;

  const isObj = (v) => v && typeof v === "object" && !Array.isArray(v);
  const eb = isObj(src.extra_body) ? src.extra_body : {};
  const g0 = isObj(eb.google) ? eb.google : {};
  const tc = { ...(isObj(g0.thinking_config) ? g0.thinking_config : {}), include_thoughts: true };
  const g = { ...g0, thinking_config: tc };
  if (!g.thought_tag_marker) g.thought_tag_marker = "think";
  const b = { ...src, extra_body: { ...eb, google: g } };

  if (eff !== null) {
    delete b.reasoning_effort;
    if (tc.thinking_level == null && tc.thinking_budget == null) {
      if (/gemini-2\.5/i.test(bareModel)) {
        if (EFFORT_TO_BUDGET[eff]) tc.thinking_budget = EFFORT_TO_BUDGET[eff];
      } else if (EFFORT_TO_LEVEL[eff]) {
        tc.thinking_level = EFFORT_TO_LEVEL[eff];
      }
    }
  }
  return b;
}

const newState = (marker) => ({ buf: "", phase: "start", open: `<${marker}>`, close: `</${marker}>` });

function feed(st, text, final) {
  let buf = st.buf + text;
  st.buf = "";
  let content = "", reasoning = "";

  while (buf) {
    if (st.phase === "content") {
      content += buf;
      break;
    }
    if (st.phase === "start") {
      const trimmed = buf.replace(/^\s+/, "");
      if (trimmed.startsWith(st.open)) {
        st.phase = "think";
        buf = trimmed.slice(st.open.length);
        continue;
      }
      if (!final && st.open.startsWith(trimmed)) { st.buf = buf; break; }
      st.phase = "content";
      continue;
    }
    const i = buf.indexOf(st.close);
    if (i !== -1) {
      reasoning += buf.slice(0, i);
      buf = buf.slice(i + st.close.length);
      st.phase = "content";
      continue;
    }
    let hold = 0;
    if (!final) {
      for (let n = Math.min(st.close.length - 1, buf.length); n > 0; n--) {
        if (buf.endsWith(st.close.slice(0, n))) { hold = n; break; }
      }
    }
    reasoning += buf.slice(0, buf.length - hold);
    st.buf = buf.slice(buf.length - hold);
    break;
  }
  return { content, reasoning };
}

function rewriteLine(line, states, marker) {
  if (!line.startsWith("data:")) return line;
  const payload = line.slice(5).trim();
  if (!payload || payload === "[DONE]") return line;

  let obj;
  try { obj = JSON.parse(payload); } catch { return line; }

  for (const ch of obj.choices || []) {
    const d = ch.delta || (ch.finish_reason ? (ch.delta = {}) : null);
    if (!d) continue;
    const idx = ch.index ?? 0;
    if (!states.has(idx)) states.set(idx, newState(marker));
    const st = states.get(idx);

    let content = "", reasoning = "";
    if (typeof d.content === "string") {
      const r = feed(st, d.content, false);
      content = r.content; reasoning = r.reasoning;
    }
    if (ch.finish_reason) {
      const r = feed(st, "", true);
      content += r.content; reasoning += r.reasoning;
    }
    if (typeof d.content === "string" || content) d.content = content;
    if (reasoning) { d.reasoning_content = reasoning; d.reasoning = reasoning; }
  }
  return "data: " + JSON.stringify(obj);
}

function rewriteJson(text, marker) {
  try {
    const obj = JSON.parse(text);
    for (const ch of obj.choices || []) {
      const m = ch.message;
      if (!m || typeof m.content !== "string") continue;
      const { content, reasoning } = feed(newState(marker), m.content, true);
      if (reasoning) {
        m.content = content.replace(/^\s+/, "");
        m.reasoning_content = reasoning.trim();
        m.reasoning = m.reasoning_content;
      }
    }
    return JSON.stringify(obj);
  } catch {
    return text;
  }
}

async function getToken(k, ctl) {
  const now = Math.floor(Date.now() / 1000);
  const hit = tokenCache.get(k.name);
  if (hit && hit.exp - 300 > now) return hit.token;

  const sa = k.cred;
  const aud = sa.token_uri || "https://oauth2.googleapis.com/token";
  const header = b64u(enc.encode(JSON.stringify({ alg: "RS256", typ: "JWT" })));
  const claim = b64u(enc.encode(JSON.stringify({
    iss: sa.client_email,
    scope: "https://www.googleapis.com/auth/cloud-platform",
    aud,
    iat: now,
    exp: now + 3600,
  })));

  let sig;
  try {
    let key = cryptoKeyCache.get(k.name);
    if (!key) {
      const pem = sa.private_key.replace(/\\n/g, "").replace(/-----[^-]+-----/g, "").replace(/\s/g, "");
      const der = Uint8Array.from(atob(pem), (c) => c.charCodeAt(0));
      key = await crypto.subtle.importKey(
        "pkcs8", der, { name: "RSASSA-PKCS1-v1_5", hash: "SHA-256" }, false, ["sign"]);
      cryptoKeyCache.set(k.name, key);
    }
    sig = await crypto.subtle.sign("RSASSA-PKCS1-v1_5", key, enc.encode(`${header}.${claim}`));
  } catch (e) {
    const err = new Error("invalid private_key: " + errMsg(e));
    err.fatal = true;
    throw err;
  }

  if (ctl) ctl.subreq++;
  const ac = new AbortController();
  let r;
  try {
    r = await withTimeout(fetch(aud, {
      method: "POST",
      headers: { "Content-Type": "application/x-www-form-urlencoded" },
      body: new URLSearchParams({
        grant_type: "urn:ietf:params:oauth:grant-type:jwt-bearer",
        assertion: `${header}.${claim}.${b64u(sig)}`,
      }),
      signal: ac.signal,
    }), TOKEN_TIMEOUT_MS, `token timeout (${TOKEN_TIMEOUT_MS / 1000}s)`, () => ac.abort());
  } catch (e) {
    throw new Error("token fetch failed: " + errMsg(e));
  }
  const j = await r.json().catch(() => ({}));
  if (!r.ok || !j.access_token) {
    const err = new Error(`token error ${r.status}: ${JSON.stringify(j).slice(0, 300)}`);
    err.fatal = r.status >= 400 && r.status < 500 && r.status !== 408 && r.status !== 429;
    throw err;
  }
  tokenCache.set(k.name, { token: j.access_token, exp: now + (j.expires_in || 3600) });
  return j.access_token;
}

function pickKey(keys, used) {
  const now = Date.now();
  const n = keys.length;
  const off = rrCursor++ % n;
  let best = null, bs = null;
  for (let i = 0; i < n; i++) {
    const k = keys[(off + i) % n];
    const until = cooldownUntil.get(k.name) || 0;
    const cooling = until > now;
    const s = [cooling ? 1 : 0, used.get(k.name) || 0, cooling ? until : 0];
    if (!bs || lexLess(s, bs)) { best = k; bs = s; }
  }
  return best;
}

function pickHop(hops, hopUsed) {
  if (hops.length === 1) return hops[0];
  const now = Date.now();
  let best = null, bs = null;
  for (const h of hops) {
    const until = hopCooldownUntil.get(h.name) || 0;
    const cooling = until > now;
    const s = [cooling ? 1 : 0, hopUsed.get(h.name) || 0, h.name === lastGoodHop ? 0 : 1, cooling ? until : 0, Math.random()];
    if (!bs || lexLess(s, bs)) { best = h; bs = s; }
  }
  return best;
}

function fetchViaHop(hop, targetUrl, init) {
  if (!hop.binding) return fetch(targetUrl, init);
  const headers = new Headers(init.headers);
  headers.set("x-hop-target", targetUrl);
  return hop.binding.fetch("https://hop.internal/proxy", {
    method: init.method,
    headers,
    body: init.body,
    signal: init.signal,
  });
}

function coolHop(hopName, status) {
  if (status === 429) {
    hopCooldownUntil.set(hopName, Date.now() + HOP_429_COOLDOWN);
    return;
  }
  const streak = (hopFailStreak.get(hopName) || 0) + 1;
  hopFailStreak.set(hopName, streak);
  const wait = HOP_COOLDOWN_STEPS[Math.min(streak - 1, HOP_COOLDOWN_STEPS.length - 1)];
  hopCooldownUntil.set(hopName, Date.now() + wait);
}

async function callVertex(keys, hops, buildUrl, method, bodyText, ctl) {
  const tried = [];
  const multiHop = hops.length > 1;
  const tag = (hop, k, label) => (multiHop ? `${hop.name}/${k.name}:${label}` : `${k.name}:${label}`);
  const used = new Map();
  const hopUsed = new Map();
  const dead = new Set();      
  const refreshed = new Set(); 
  const bump = (m, n) => m.set(n, (m.get(n) || 0) + 1);
  const alive = () => keys.filter((k) => !dead.has(k.name));
  const timeoutLabel = `upstream timeout (${Math.round(ctl.attemptTimeoutMs / 1000)}s)`;
  let fails = 0;
  let timeouts = 0;
  let lastErr = null;

  const planNext = ({ retryAfterMs = 0, immediate = false, hopIssue = false } = {}) => {
    if (ctl.attempts >= MAX_TOTAL_ATTEMPTS || ctl.subreq >= MAX_SUBREQUESTS) return null;
    const live = alive();
    if (!live.length) return null;
    if (immediate) return 0;
    const now = Date.now();
    const keyReady = live.some((k) => (cooldownUntil.get(k.name) || 0) <= now);
    const hopReady = multiHop && hops.some((h) => (hopCooldownUntil.get(h.name) || 0) <= now);
    let delay;
    if (hopIssue ? hopReady : keyReady) delay = 0;
    else delay = Math.max(Math.min(retryAfterMs, MAX_HONOR_RETRY_AFTER_MS), backoffMs(fails));
    if (now - ctl.start + delay > ctl.retryWindowMs) return null;
    return delay;
  };
  const pause = async (d) => {
    if (!d) return;
    tried.push(`wait:${d}ms`);
    await sleep(d);
  };

  for (let guard = 0; guard < MAX_TOTAL_ATTEMPTS * 3; guard++) {
    const live = alive();
    if (!live.length) break;
    const k = pickKey(live, used);
    const hop = pickHop(hops, hopUsed);
    bump(used, k.name);

    let token;
    try {
      token = await getToken(k, ctl);
    } catch (e) {
      lastErr = e;
      tried.push(tag(hop, k, "token"));
      if (e.fatal) {
        dead.add(k.name);
        cooldownUntil.set(k.name, Date.now() + TOKEN_FAIL_COOLDOWN);
      } else {
        cooldownUntil.set(k.name, Date.now() + NET_FAIL_COOLDOWN);
        fails++;
      }
      const d = planNext();
      if (d === null) break;
      await pause(d);
      continue;
    }

    ctl.attempts++;
    ctl.subreq++;
    bump(hopUsed, hop.name);
    const ac = new AbortController();
    const endAt = Date.now() + ctl.attemptTimeoutMs;
    let r;
    try {
      r = await withTimeout(fetchViaHop(hop, buildUrl(k), {
        method,
        headers: { Authorization: `Bearer ${token}`, "Content-Type": "application/json" },
        body: bodyText,
        signal: ac.signal,
      }), ctl.attemptTimeoutMs, timeoutLabel, () => ac.abort());
      if (r.ok) r = await primeBody(r, Math.max(1, endAt - Date.now()), timeoutLabel, () => ac.abort());
    } catch (e) {
      const timedOut = !!(e && e.timeout);
      lastErr = e;
      tried.push(tag(hop, k, timedOut ? "timeout" : "net"));
      if (multiHop) coolHop(hop.name, 0);
      else cooldownUntil.set(k.name, Date.now() + NET_FAIL_COOLDOWN);
      let d;
      if (timedOut) {
        d = ++timeouts <= MAX_TIMEOUT_RETRIES ? planNext({ immediate: true }) : null;
      } else {
        fails++;
        d = planNext({ hopIssue: multiHop });
      }
      if (d === null) break;
      await pause(d);
      continue;
    }

    const status = r.status;
    if (r.ok) {
      cooldownUntil.delete(k.name);
      keyFailStreak.delete(k.name);
      lastGoodHop = hop.name;
      hopFailStreak.delete(hop.name);
      hopCooldownUntil.delete(hop.name);
      return { res: r, name: k.name, hop: hop.name, tried };
    }
    if (status !== 401 && status !== 403 && !RETRYABLE.has(status)) {
      return { res: r, name: k.name, hop: hop.name, tried };
    }

    tried.push(tag(hop, k, status));
    let d;
    if (status === 401) {
      tokenCache.delete(k.name);
      if (!refreshed.has(k.name)) {
        refreshed.add(k.name);
      } else {
        dead.add(k.name);
        cooldownUntil.set(k.name, Date.now() + AUTH_FAIL_COOLDOWN);
      }
      d = planNext({ immediate: true });
    } else if (status === 403) {
      dead.add(k.name);
      cooldownUntil.set(k.name, Date.now() + AUTH_FAIL_COOLDOWN);
      d = planNext({ immediate: true });
    } else {
      fails++;
      const retryAfterMs = parseRetryAfter(r.headers.get("retry-after"));
      if (status === 429) {
        const streak = (keyFailStreak.get(k.name) || 0) + 1;
        keyFailStreak.set(k.name, streak);
        const cd = Math.max(retryAfterMs, Math.min(KEY_429_MAX, KEY_429_BASE * 2 ** (streak - 1)));
        cooldownUntil.set(k.name, Date.now() + Math.min(cd, MAX_RETRY_AFTER_MS));
        if (multiHop) coolHop(hop.name, 429);
        d = planNext({ retryAfterMs });
      } else {
        cooldownUntil.set(k.name, Date.now() + Math.max(TRANSIENT_COOLDOWN, retryAfterMs));
        if (multiHop) coolHop(hop.name, status);
        d = planNext({ retryAfterMs, hopIssue: multiHop });
      }
    }

    if (d === null) return { res: r, name: k.name, hop: hop.name, tried };
    await r.body?.cancel().catch(() => {});
    await pause(d);
  }

  throw new Error(`${lastErr ? errMsg(lastErr) : "all keys failed"} tried=${tried.join(",")}`);
}

export default {
  async fetch(req, env, ctx) {
    if (req.method === "OPTIONS") return new Response(null, { status: 204, headers: CORS });

    const url = new URL(req.url);
    const p = url.pathname;
    if (p === "/") return Response.json({ ok: true }, { headers: CORS });

    const secret = env.PROXY_PASSWORD;
    const given =
      (req.headers.get("authorization") || "").replace(/^Bearer\s+/i, "") ||
      req.headers.get("x-api-key") || "";
    if (!secret || given !== secret) return jsonError(401, "unauthorized");

    const hops = loadHops(env);
    const retryWindowMs = RETRY_WINDOW_MS;
    const attemptTimeoutMs = ATTEMPT_TIMEOUT_MS;

    if (p === "/__egress") {
      const rows = await Promise.all(hops.map(async (h) => {
        try {
          const r = h.binding
            ? await h.binding.fetch("https://hop.internal/__egress")
            : await fetch("https://www.cloudflare.com/cdn-cgi/trace");
          const txt = await r.text();
          const colo = (txt.match(/^colo=(.+)$/m) || [])[1] || "-";
          const loc = (txt.match(/^loc=(.+)$/m) || [])[1] || "-";
          const ip = (txt.match(/^ip=(.+)$/m) || [])[1] || "-";
          return `${h.name}: colo=${colo} loc=${loc} ip=${ip}`;
        } catch (e) {
          return `${h.name}: error=${errMsg(e)}`;
        }
      }));
      const now = Date.now();
      const cooling = [...cooldownUntil.entries()]
        .filter(([, u]) => u > now)
        .map(([n, u]) => `${n}:${Math.ceil((u - now) / 1000)}s`);
      const out = [
        `worker_colo=${req.cf?.colo || "-"}`,
        `cf_placement=${req.headers.get("cf-placement") || "-"}`,
        `upstream_mode=${(env.UPSTREAM_MODE || "auto").trim().toLowerCase()}`,
        `retry_seconds=${retryWindowMs / 1000} timeout_seconds=${attemptTimeoutMs / 1000}`,
        `last_good_hop=${lastGoodHop}`,
        `cooling_keys=${cooling.join(",") || "-"}`,
        "---",
        ...rows,
      ].join("\n") + "\n";
      return new Response(out, { headers: { "Content-Type": "text/plain", ...CORS } });
    }

    const models = parseModels(env);
    if (req.method === "GET" && (p === "/v1/models" || p === "/models")) {
      return Response.json({
        object: "list",
        data: [...models.keys()].map((id) => ({ id, object: "model", owned_by: "google" })),
      }, { headers: CORS });
    }

    const { keys, bad, missing, filtered } = loadKeys(env);
    if (!keys.length) {
      return jsonError(500, "no valid service account key (API_*)" +
        (filtered ? " matching USE_KEYS" : "") +
        (missing.length ? ` / not found: ${missing.join(", ")}` : "") +
        (bad.length ? ` / invalid: ${bad.join(", ")}` : ""));
    }

    const path = p.replace(/^\/v1/, "") + url.search;
    const rawBody = req.method === "GET" || req.method === "HEAD" ? undefined : await req.text();

    let body = null;
    if (rawBody) { try { body = JSON.parse(rawBody); } catch {} }
    if (body !== null && typeof body !== "object") body = null;

    const isChat = p.endsWith("/chat/completions");
    const wantsStream = !!(body && body.stream);
    const allowThoughts = String(env.THOUGHTS || "on").toLowerCase() !== "off";
    const upstreamMode = String(env.UPSTREAM_MODE || "auto").trim().toLowerCase();
    const location = (env.VERTEX_LOCATION || "global").trim() || "global";
    const base = location === "global"
      ? "https://aiplatform.googleapis.com"
      : `https://${location}-aiplatform.googleapis.com`;

    let askedModel = "";
    let bareModel = "";
    let useNative = false;
    let forceStream = false;
    let getPlain = () => rawBody;
    let thoughtText = null;
    let marker = "think";

    if (body) {
      if (body.model) {
        askedModel = String(body.model);
        let real = models.get(askedModel) || models.get(askedModel.replace(/^google\//, ""));
        if (!real) {
          if (models.size) {
            return jsonError(404, `model '${askedModel}' is not registered. available: ${[...models.keys()].join(", ")}`);
          }
          real = askedModel;
        }
        bareModel = real.replace(/^(models\/|google\/)/, "");
        body.model = real.includes("/") ? real : `google/${real}`;
      }

      if (isChat && req.method === "POST" && bareModel && canUseNative(body, bareModel, upstreamMode)) {
        useNative = true;
        forceStream = !wantsStream;
        const built = buildNativePayload(body, bareModel, allowThoughts);
        getPlain = once(() => JSON.stringify(built.base));
        if (built.thought) thoughtText = JSON.stringify(built.thought);
      } else {
        delete body.logprobs;
        delete body.top_logprobs;

        if (Array.isArray(body.stop)) {
          const s = [...new Set(body.stop.filter((x) => typeof x === "string" && x !== ""))].slice(0, MAX_STOP);
          if (s.length) body.stop = s; else delete body.stop;
        }

        const ver = /gemini-(\d+)/i.exec(bareModel);
        if (ver && Number(ver[1]) >= 4) {
          delete body.frequency_penalty;
          delete body.presence_penalty;
        }

        if (isChat && !wantsStream) {
          body.stream = true;
          forceStream = true;
        }

        getPlain = once(() => JSON.stringify(body));
        if (isChat && allowThoughts) {
          const tb = injectOpenAIThoughts(body, bareModel);
          if (tb) {
            thoughtText = JSON.stringify(tb);
            marker = String(tb.extra_body.google.thought_tag_marker);
          }
        }
      }
    }

    const modeLabel = useNative ? "native" : "openapi";
    const buildUrl = useNative
      ? (k) => `${base}/v1/projects/${k.cred.project_id}/locations/${location}/publishers/google/models/${encodeURIComponent(bareModel)}:streamGenerateContent?alt=sse`
      : (k) => `${base}/v1/projects/${k.cred.project_id}/locations/${location}/endpoints/openapi${path}`;

    const ctl = { start: Date.now(), attempts: 0, subreq: 0, retryWindowMs, attemptTimeoutMs };

    const report = async (out) => {
      console.log(`mode=${modeLabel} hop=${out.hop} key=${out.name} project=${keys.find((k) => k.name === out.name)?.cred.project_id} status=${out.res.status} attempts=${ctl.attempts} ms=${Date.now() - ctl.start} tried=${out.tried.join(",") || "-"}`);
      if (out.res.ok) return "";
      const errText = await out.res.clone().text().catch(() => "");
      console.log(`upstream error ${out.res.status}: ${errText.slice(0, 300)}`);
      return errText;
    };

    const call = async () => {
      const out = await callVertex(keys, hops, buildUrl, req.method, thoughtText ?? getPlain(), ctl);
      out.thoughts = !!thoughtText;
      const errText = await report(out);
      if (thoughtText && out.res.status === 400 && /think|thought|reasoning/i.test(errText)) {
        if (bareModel) noThoughtsModels.add(bareModel);
        await out.res.body?.cancel().catch(() => {});
        const retry = await callVertex(keys, hops, buildUrl, req.method, getPlain(), ctl);
        retry.thoughts = false;
        retry.tried = [...out.tried, "thoughts-off", ...retry.tried];
        await report(retry);
        return retry;
      }
      return out;
    };

    if (req.method === "GET") {
      try {
        const out = await call();
        return withMeta(out.res, out.name, out.hop, out.tried, modeLabel);
      } catch (e) {
        return jsonError(502, errMsg(e));
      }
    }

    if (wantsStream) {
      const settled = call().then((r) => ({ r }), (e) => ({ e }));
      const fast = await raceWindow(settled, FAST_WINDOW_MS);
      if (fast?.e) return jsonError(502, errMsg(fast.e));
      if (fast && !fast.r.res.ok) {
        const { res, name, hop, tried } = fast.r;
        const text = unwrapVertexError(await res.text().catch(() => ""));
        return withMeta(res, name, hop, tried, modeLabel, text, { "Content-Type": "application/json" });
      }

      const stream = heartbeatStream(ctx, async (write) => {
        const s = fast || (await settled);
        if (s.e) throw s.e;
        const out = s.r;
        if (!out.res.ok) {
          const text = unwrapVertexError(await out.res.text().catch(() => ""));
          await write(enc.encode(sseError(upstreamMsg(out.res.status, text, out.tried), out.res.status)));
          return;
        }
        if (!out.res.body) {
          await write(enc.encode("data: [DONE]\n\n"));
          return;
        }
        if (useNative) await pumpNative(out.res.body, write, askedModel || bareModel);
        else await pumpOpenAI(out.res.body, write, out.thoughts, marker);
      }, !fast);

      const headers = new Headers({
        "Content-Type": "text/event-stream; charset=utf-8",
        "Cache-Control": "no-cache, no-transform",
        "X-Accel-Buffering": "no",
        "x-proxy-mode": modeLabel,
        ...CORS,
      });
      if (fast) {
        headers.set("x-proxy-key", fast.r.name);
        headers.set("x-proxy-hop", fast.r.hop);
        if (fast.r.tried.length) headers.set("x-proxy-tried", fast.r.tried.join(","));
      }
      return new Response(stream, { status: 200, headers });
    }

    const run = async () => {
      const out = await call();
      const { res } = out;
      let status = res.status;
      let text;
      if (forceStream && res.ok) {
        const agg = useNative
          ? await collectNativeSSE(res.body, STREAM_IDLE_MS, askedModel || bareModel)
          : await collectOpenAISSE(res.body, STREAM_IDLE_MS);
        if (agg.error) {
          const code = Number(agg.error.error?.code);
          status = code >= 400 && code < 600 ? code : 502;
          text = JSON.stringify(agg.error);
        } else {
          text = JSON.stringify(agg.json);
        }
      } else {
        text = await res.text();
        if (useNative && !res.ok) text = unwrapVertexError(text);
      }
      if (!useNative && out.thoughts && status >= 200 && status < 300) {
        text = rewriteJson(text, marker);
      }
      return { ...out, status, text };
    };

    const settled = run().then((r) => ({ r }), (e) => ({ e }));
    const fast = await raceWindow(settled, FAST_WINDOW_MS);
    if (fast) {
      if (fast.e) return jsonError(502, errMsg(fast.e));
      const h = new Headers({
        "Content-Type": "application/json",
        ...CORS,
        "x-proxy-key": fast.r.name,
        "x-proxy-hop": fast.r.hop,
        "x-proxy-mode": modeLabel,
      });
      if (fast.r.tried.length) h.set("x-proxy-tried", fast.r.tried.join(","));
      return new Response(fast.r.text, { status: fast.r.status, headers: h });
    }

    const { readable, writable } = new TransformStream();
    const w = writable.getWriter();

    ctx.waitUntil((async () => {
      await w.write(enc.encode("\n")).catch(() => {});
      const ping = setInterval(() => w.write(enc.encode("\n")).catch(() => {}), PING_MS);
      let out;
      try {
        const s = await settled;
        if (s.e) {
          out = fakeChat("[proxy error] " + errMsg(s.e));
        } else {
          out = s.r.text;
          const ok = s.r.status >= 200 && s.r.status < 300;
          if (!ok || !/"choices"\s*:\s*\[\s*\{/.test(out)) {
            out = fakeChat(`[upstream ${s.r.status}] tried=${s.r.tried.join(",")}\n${s.r.text.slice(0, 800)}`);
          }
        }
      } catch (e) {
        out = fakeChat("[proxy error] " + errMsg(e));
      }
      clearInterval(ping);
      await w.write(enc.encode(out)).catch(() => {});
      await w.close().catch(() => {});
    })());

    return new Response(readable, {
      status: 200,
      headers: {
        "Content-Type": "application/json",
        "Cache-Control": "no-transform",
        "Content-Encoding": "identity",
        "X-Accel-Buffering": "no",
        ...CORS,
      },
    });
  },
};

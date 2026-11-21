// Prints what undici sees from an llhttp.wasm for one input, in the format
// of compat/llhttp/test/trace.c: the callbacks undici's client-h1.js
// registers (wasm_on_*), with spans joined across calls as undici joins
// them, plus the error name where parsing stops.
//
//   node trace.mjs WASM (req|res) (whole|bytes|SEED) FILE
//
// `bytes` feeds one byte per llhttp_execute call; a number feeds random
// pieces from that seed (the same generator as trace.c). With PAUSE=k in
// the environment, the k-th callback pauses the parser, which then resumes
// where it stopped: the trace must not change.
import { readFileSync, writeSync } from 'node:fs'

const [wasmPath, kind, split, file] = process.argv.slice(2)
const input = readFileSync(file)
const HPE_OK = 0
const HPE_PAUSED = 21
const pauseAt = process.env.PAUSE ? Number(process.env.PAUSE) : -1
let ncb = 0
const ret = () => (++ncb === pauseAt ? HPE_PAUSED : 0)

let out = ''
let url = []; let status = []; let field = []; let value = []
let inValue = false; let havePair = false
let bodyLen = 0n; let bodyHash = 1469598103934665603n
const M64 = (1n << 64n) - 1n
let ll, mem
const bytes = (at, len) => Buffer.from(new Uint8Array(ll.memory.buffer, at, len))
const flushPair = () => {
  if (!havePair) return
  out += `h ${Buffer.concat(field).toString('latin1')}: [${Buffer.concat(value).toString('latin1')}]\n`
  field = []; value = []; havePair = false; inValue = false
}

const env = {
  wasm_on_message_begin: (p) => {
    out += 'begin\n'
    url = []; status = []; field = []; value = []
    havePair = inValue = false
    bodyLen = 0n; bodyHash = 1469598103934665603n
    return ret()
  },
  wasm_on_url: (p, at, len) => { url.push(bytes(at, len)); return ret() },
  wasm_on_status: (p, at, len) => { status.push(bytes(at, len)); return ret() },
  wasm_on_header_field: (p, at, len) => {
    if (inValue) flushPair()
    havePair = true
    field.push(bytes(at, len))
    return ret()
  },
  wasm_on_header_value: (p, at, len) => { inValue = true; value.push(bytes(at, len)); return ret() },
  wasm_on_headers_complete: (p, statusCode, upgrade, keepAlive) => {
    flushPair()
    const req = ll.llhttp_get_type(p) === 1
    if (req) out += `url ${Buffer.concat(url).toString('latin1')}\n`
    else out += `status ${statusCode} ${Buffer.concat(status).toString('latin1')}\n`
    out += `hc method=${req ? ll.llhttp_get_method(p) : -1} v=${ll.llhttp_get_http_major(p)}.${ll.llhttp_get_http_minor(p)} upgrade=${upgrade} keepalive=${keepAlive}\n`
    return 0
  },
  wasm_on_body: (p, at, len) => {
    const b = new Uint8Array(ll.memory.buffer, at, len)
    for (let i = 0; i < len; i++) {
      bodyHash ^= BigInt(b[i])
      bodyHash = (bodyHash * 1099511628211n) & M64
    }
    bodyLen += BigInt(len)
    return ret()
  },
  wasm_on_message_complete: (p) => {
    flushPair()
    out += `body ${bodyLen} ${bodyHash.toString(16).padStart(16, '0')}\nmc\n`
    return ret()
  }
}

ll = new WebAssembly.Instance(new WebAssembly.Module(readFileSync(wasmPath)), { env }).exports
const p = ll.llhttp_alloc(kind === 'req' ? 1 : 2)
const buf = ll.malloc(Math.max(1, input.length))
new Uint8Array(ll.memory.buffer, buf, input.length).set(input)
const cstr = (ptr) => {
  const m = new Uint8Array(ll.memory.buffer)
  let e = ptr
  while (m[e]) e++
  return Buffer.from(m.subarray(ptr, e)).toString('latin1')
}

let mode = 0; let seed = 0
if (split === 'bytes') mode = 1
else if (split !== 'whole') { mode = 2; seed = Number(split) >>> 0 }
const n = input.length
let off = 0; let err = HPE_OK; let resumed = false
while (off < n || resumed) {
  resumed = false
  let len = n - off
  if (mode === 1 && off < n) len = 1
  if (mode === 2) {
    seed = (Math.imul(seed, 1103515245) + 12345) >>> 0
    len = 1 + ((seed >>> 8) % 64)
    if (len > n - off) len = n - off
  }
  err = ll.llhttp_execute(p, buf + off, len)
  if (err === HPE_PAUSED) {
    const at = ll.llhttp_get_error_pos(p) - buf
    ll.llhttp_resume(p)
    off = at
    resumed = true
    err = HPE_OK
    continue
  }
  if (err !== HPE_OK) {
    const at = ll.llhttp_get_error_pos(p) - buf
    out += `stop ${cstr(ll.llhttp_errno_name(err))} @${at}\n`
    break
  }
  off += len
}
if (err === HPE_OK) {
  err = ll.llhttp_finish(p)
  if (err !== HPE_OK && err !== HPE_PAUSED) out += `finish ${cstr(ll.llhttp_errno_name(err))}\n`
  else out += 'eof\n'
}
ll.free(buf)
ll.llhttp_free(p)
writeSync(1, Buffer.from(out, "latin1"))

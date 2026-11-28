# verilith-serverless

A serverless host whose sandbox is proven with
[Verus](https://github.com/verus-lang/verus): untrusted WebAssembly
request handlers, run by [verilith-wasm](../wasm) behind
[verilith-server](../server). A function is a `.wasm` module that exports
`handle` and imports five host functions. It can read the request and
build a response, and that is all it can do. Each request runs on a fresh
copy of the instance, with a fuel budget, a memory cap and limits on the
response.

**Status: pre-release.** HTTP/1.1, h2c, TLS and HTTP/3 come from
verilith-server (anything `serve` accepts). There is no WASI, no outbound
network and no storage: a function is a pure request-to-response
transformer for now.

```sh
cargo build --release -p verilith-serverless
(cd crates/serverless/examples/hello && cargo build --release)   # a Rust guest, wasm32
./target/release/verilith-serverless --http 8080 \
  --fn hello=crates/serverless/examples/hello/target/wasm32-unknown-unknown/release/hello.wasm
curl 'http://localhost:8080/fn/hello?name=you'    # Hello, you!
curl -d 'shout' http://localhost:8080/fn/hello     # SHOUT
```

As a library, `Functions` is a `verilith_server::Handler`:

```rust,no_run
use std::sync::Arc;
use verilith_serverless::{Functions, Options};

let mut fns = Functions::new();
fns.add("hello", &std::fs::read("hello.wasm").unwrap(), Options::default()).unwrap();
verilith_server::serve(verilith_server::Config { port: 8080, ..Default::default() }, Arc::new(fns)).unwrap();
```

`Options` sets the fuel per request (default 100M branches, calls and
returns), the memory cap (64 MiB), the largest response body (8 MiB), and
the most response fields (64) and field bytes (16 KiB). Other flags:
`--threads N`, `--fuel N`, `--max-memory MIB`.

## The guest ABI

A function module imports from module `vl` (all parameters and results
`i32`; pointers and lengths are unsigned) and exports `handle: () -> ()`.
It may import nothing else: no other functions, memories, tables or
globals.

| import | does |
|---|---|
| `req_size(part) -> len` | length of request part `part`: 0 the method, 1 the target (`/fn/name/...?query`), 2 the header lines (`name: value\r\n` each), 3 the body. -1 for another part |
| `req_read(part, off, dst, len) -> n` | copies `n = min(len, size - off)` bytes of the part, from `off`, to linear memory at `dst`. -1 if `off` is past the end or `dst..dst+len` is not inside memory |
| `resp_status(code) -> 0` | sets the status, 200 to 599 (default 200). -1 otherwise |
| `resp_header(name, name_len, value, value_len) -> 0` | adds a response field. -1 if either range is outside memory, the name is not a token, the value has a CR, LF, NUL, DEL or surrounding whitespace, the name is Content-Length, Transfer-Encoding or a hop-by-hop field (Connection, Keep-Alive, Proxy-Connection, Upgrade, TE, Trailer), or the field limits are reached |
| `resp_write(ptr, len) -> 0` | appends `ptr..ptr+len` of memory to the body. -1 if outside memory or past the body limit |

When `handle` returns, the reply is sent. If it traps, the reply is
dropped and the client gets 500 (503 when it ran out of fuel or stack).
The start function, if any, runs once at load and may not call the ABI.

[`examples/hello`](examples/hello) is a `no_std` Rust guest with the
bindings in 40 lines. Build guests for WebAssembly 2.0 without reference
types (`-C target-cpu=mvp` plus the 2.0 features; see its
`.cargo/config.toml`), and give them a small shadow stack: every request
starts from a copy of linear memory, so its size is the per-request cost
(see Performance).

## What is proven

`scripts/verify.sh` (Verus): 33 verified, 0 errors, on top of the
proofs of verilith-wasm, verilith-server and verilith-http, whose
specifications these theorems are stated with.

- **The host does exactly what the ABI says** (`abi::Abi::dispatch`,
  against `abi::step`). For every import index, arguments, result buffer
  and guest memory: a call that is not well-formed (an unknown import,
  the wrong number of arguments) traps and changes nothing; a well-formed
  one returns `step`'s result and leaves `step`'s reply and memory. So
  the host writes guest memory only at `dst..dst+n` of a `req_read` that
  fits, and only with that part's bytes `off..off+n`; every other call
  leaves memory exactly as it was. Every range the guest names is checked
  as 32-bit unsigned numbers with no wraparound (`lo`). Guest memory is
  read only inside its bounds (Verus checks every access).
- **Every reply is well-formed** (`abi::reply_ok`, the type invariant of
  `abi::Reply`, so it holds for every reply there is, whatever the guest
  did): status 200 to 599; at most the configured number of fields and
  field bytes and body bytes; and every field passes
  `field_ok`, which is verilith-server's own `respond::name_ok` and
  `respond::value_ok` (the predicates of its theorem that a response head
  parses back exactly, under verilith-http's specification) plus no
  hop-by-hop name. A guest cannot split a response, inject a field, set
  the framing or take over the connection, and the server's check of the
  fields cannot fail on a guest's reply.
- **Requests are isolated** (`host::Func::serve`). Before each call the
  instance's store (linear memory, its size, globals, tables, which data
  segments were dropped) is put back to the snapshot taken after
  instantiation (`verilith_wasm::instance::Checked::restore`, verified),
  and the guest gets a new, empty reply. The contract returns the store
  the call started from and proves it equal to the snapshot: nothing a
  request leaves behind (a global, a byte of memory, a grown memory, a
  partial reply) reaches the next request. If the store could not be put
  back, the guest is not run.
- **Memory is capped and every call ends.** Every request starts with a
  `memory.grow` limit no higher than the cap (`host::Func`'s type
  invariant), and verilith-wasm's refinement theorem (`run::execute`) has
  `memory.grow` fail past it. Every call is metered with the configured
  fuel (`execute_metered`), so it ends.
- **Routing** (`host::route`): a function runs only for a path
  `/fn/<name>` or `/fn/<name>/...` with a name of 1 to 64 bytes from
  `[a-z0-9_-]`, and the name it looks up is exactly that segment.

Together with verilith-wasm's theorems (the guest can only reach its own
memory, globals, tables and stack, and every step the interpreter takes
is the semantics' step) and verilith-server's (the handler sees exactly
the request the HTTP specification sees; the response on the wire parses
back as exactly what the handler sent), the request path from bytes on
the socket, through the guest, to bytes on the socket is proven, except
for the glue listed below.

### What is trusted

Beyond what every Verilith crate trusts (Verus, Z3, rustc) and what
verilith-wasm and verilith-server trust ([wasm's trusted
base](../wasm#trusted-base), [server's TRUST.md](../server/TRUST.md)),
this crate has no `external_body`, axiom or `assume`. Its unverified code
is the glue in `src/lib.rs` and the binary, listed in
[TRUST.md](TRUST.md): loading a module (checking its imports and building
the import table), writing the request's header lines into one buffer,
handing the reply to `Response::send`, and keeping one instance per
function per worker thread. A bug there can give a guest the wrong
request bytes or the wrong ABI function for an import, but every call
still goes through `dispatch` and every run through `serve`, so it cannot
break the theorems above.

### What is not proven

- That a guest's reply is what ends up on the wire is the composition of
  this crate's theorem with the server's, joined by the glue in `respond`
  (TRUST.md); it is not one stated theorem.
- Isolation is about state. Timing is not covered: a guest can measure
  how long things take (with fuel, roughly) and nothing here hides that.
- Fuel bounds work in branches, calls and returns, not wall-clock time;
  a `memory.fill` or `memory.copy` of the whole memory costs one unit.
- Each worker thread holds, per function, the instance (memory up to the
  cap, plus verilith-wasm's 8 MiB value stack) and the snapshot.

## Performance

`wrk -t2 -c64 -d8s` against the server with two worker threads, on a
4-core cloud x86-64 VM (noisy; one run each, same sitting):

| route | requests/s |
|---|---:|
| verilith-server `/plaintext` (native Rust handler) | 203,000 |
| `/fn/hello?name=x` (examples/hello, 64 KiB shadow stack, 2 pages of memory) | 141,000 |
| the same guest with Rust's default 1 MiB shadow stack (17 pages) | 18,300 |

Most of the per-request cost is copying the snapshot's memory back
(`Checked::restore`), so it grows with the guest's memory: keep the
shadow stack small. Restoring only the pages a request wrote would remove
most of it; that needs a dirty-page record in the interpreter, which is
not built yet.

## Prior work

Production serverless platforms run WebAssembly on unverified engines:
Cloudflare Workers on V8 isolates, Fastly Compute and Fermyon Spin on
Wasmtime. VeriWasm (Johnson et al., NDSS 2021) was built for Lucet,
Fastly's earlier compiler, to check that compiled native code keeps its
software-fault-isolation bounds, and Wasmtime has verified some of
Cranelift's lowering rules (Crocus, ASPLOS 2024); neither covers the
host functions, the HTTP front end, or what one request can leave for the
next. Sledge (Gadepalli et al., 2020) is a serverless-first WebAssembly
runtime, not verified.

The verified work is about pieces:

- **vWasm and rWasm** (Bosamiya, Lim and Parno, USENIX Security 2022): a
  sandboxing compiler verified in F*, and a translation to safe Rust.
- **WaVe** (Johnson et al., IEEE S&P 2023): the closest. A WASI runtime
  layer verified (in Rust, with Prusti) to keep a guest's system calls
  within its memory and its share of the file system and network. It is
  the layer around an engine, for command-line WASI programs.
- **WasmCert** (Isabelle, Coq): mechanized semantics and verified
  reference interpreters.

As far as we could find, no serverless host has been built where the
engine (refinement of a WebAssembly semantics), the host interface (each
host call against a specification), per-request isolation, and the HTTP
parser and serializer around them are all proven, in one proof
development. That combination is what is new here. WaVe's guarantees for
WASI are complementary, and adding WASI-style capabilities (a key-value
store, outbound HTTP through verilith-http) is the natural next step.

## Testing

`cargo test --release -p verilith-serverless`: guests written in WAT that
use the ABI as intended and guests that try to break out of it
(out-of-bounds and wrapping pointers, CR/LF and NUL in fields,
Content-Length, Transfer-Encoding and Connection fields, state left in
globals, memory and grown pages, memory exhaustion, an endless loop,
traps, refused imports, a start function calling the ABI), unit-level
through `Func::serve` and end to end through verilith-server over TCP,
pipelined requests included.

## License

MIT OR Apache-2.0.

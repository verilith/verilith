# verilith-http

An HTTP/1.1 (RFC 9112) message parser in Rust, formally verified with
[Verus](https://github.com/verus-lang/verus). It parses request and response
heads, decides how the body is framed, and decodes the chunked transfer
coding. It ships four APIs over one verified core:

- a Rust API (`verilith_http::parse_request`, `parse_response`, `ChunkedDecoder`),
- the API of the [httparse](https://crates.io/crates/httparse) crate
  (`verilith_http::httparse`), so hyper and other httparse users can switch with a
  `[patch.crates-io]` line,
- the C API of [picohttpparser](https://github.com/h2o/picohttpparser)
  (`phr_parse_request` and friends),
- the parser behind [llhttp](https://github.com/nodejs/llhttp)'s C API, so
  Node.js can be built with verilith-http in place of llhttp's generated parser.
  Node.js 24 built this way passes 763 of its 771 HTTP tests; each of the
  8 others expects a leniency verilith-http refuses on purpose.

What is proven, in one paragraph: the parser never panics, reads out of
bounds or overflows; it computes exactly a written specification of the
RFC 9112 grammar and framing rules; it runs in linear time; its answer
never depends on how input is split across reads; and **every message it
accepts is read the same way by every recipient in a model of RFC 9112
that includes the deviations behind published smuggling bugs** (same end
of head, same framing, and for chunked bodies the same end and the same
decoded bytes). That last theorem is the precise form of "no request
smuggling", and its limits are listed below.

Speed: parsing a head, it is faster than picohttpparser, httparse and
llhttp on every message benchmarked, requests and responses (1.3x to 1.8x
faster than httparse, 3.7x to 4.2x faster than llhttp). Behind llhttp's
API, as Node.js uses it, it is 1.15x to 1.9x faster than llhttp itself (see
[Performance](#performance)).

## Two speeds: drop-in and native

Swap verilith-http in behind llhttp's or picohttpparser's API today and get the
proofs at no cost in speed; call `verilith_http::parse_request` and
`parse_response` directly where parsing is hot.

| against | task | **drop-in** (relink) | **native** (port the calling code) |
| --- | --- | --- | --- |
| llhttp 9.4.3 | parse a whole message: target or reason, every header name and value, the body | 1.18x (0.66x to 1.47x) | 2.09x (1.10x to 2.96x) |
| picohttpparser | parse a head into a reused header array | 1.39x (0.80x to 2.02x) | 1.48x (1.02x to 2.18x) |

Measured with [vbench](https://github.com/verilith/verilith/tree/main/bench) on an
Apple M3 Pro (2026-11-20, 31 alternating pairs per case; speedup is the original's
time over ours, geometric mean and range over the cases). Both columns run
the same task against the same driver of the original. The native number is what you
get after porting the calling code; relinking alone gets the drop-in
number.

Six messages: four requests and two responses.

- Against llhttp the gap is the API's shape: llhttp reports every piece
  through a callback as it goes, and the native API parses a complete head
  in one call and returns spans. The low end of both ranges is the chunked
  response. Behind llhttp's API verilith-http is slower than llhttp there (0.66x);
  through its own API it is level (1.10x), and that figure includes a copy
  of the body, because `ChunkedDecoder` decodes in place and the benchmark
  has to keep its input.
- Against picohttpparser the two columns are close, as they should be: its
  API is already flat and copies nothing. verilith-http's own call also works out
  the body framing, which picohttpparser leaves to the caller.

## Using it

### From hyper (or anything else that uses httparse)

`compat/httparse` is a crate named `httparse`, version 1.10.1, that
re-exports `verilith_http::httparse`. In your application's `Cargo.toml`:

```toml
[patch.crates-io]
httparse = { git = "https://github.com/verilith/verilith/tree/main/crates/http" }
```

Every crate in the build that depends on httparse 1.x, hyper included, now
parses with verilith-http. The API is httparse 1.10's: `Request`, `Response`,
`Header`, `EMPTY_HEADER`, `Status`, `Error`, `ParserConfig`,
`parse_headers`, `parse_chunk_size`, `parse_with_uninit_headers`. Where
they differ:

- verilith-http is stricter (the rules are below). A message httparse accepts and
  verilith-http rejects returns an `Err`, so hyper answers 400 as it would for any
  malformed request. The leniency switches on `ParserConfig`
  (`allow_spaces_after_header_name_in_responses`,
  `allow_obsolete_multiline_headers_in_responses` and the rest) are
  accepted and ignored.
- Ambiguous framing (Content-Length lines that disagree, Content-Length with
  Transfer-Encoding, and so on) is rejected at parse time with
  `Error::HeaderValue`, rather than left to the caller.
- A missing or repeated `Host` is not checked here, because httparse does
  not and hyper handles it.

hyper 1.7.0's own test suite passes with this patch except for five
tests, each of which asserts that hyper accepts a message verilith-http rejects
on purpose: two Transfer-Encoding lines, Transfer-Encoding with
Content-Length, a Content-Length list (`3,3`), obsolete line folding,
and whitespace before a colon (the last two behind opt-in `ParserConfig`
switches). Two more client tests fail with stock httparse too.

`tests/parse.rs` runs 300,000 generated messages through both httparse and
`verilith_http::httparse` and checks that they agree whenever verilith-http accepts.

### From Rust

```rust
use verilith_http::{parse_request, Body, ChunkedDecoder, Chunked, Status};

let mut headers = Vec::new(); // reuse across requests: no allocation once warm
match parse_request(&buf, &mut headers)? {
    Status::Partial => { /* read more, call again */ }
    Status::Complete(req) => {
        println!("{:?} {:?} HTTP/1.{}", req.method(), req.target(), req.minor_version());
        for (name, value) in req.headers(&headers) { /* ... */ }
        match req.body {
            Body::Empty => {}
            Body::Length(n) => { /* the next n bytes after req.head_len */ }
            Body::Chunked => {
                let mut dec = ChunkedDecoder::new();
                // Decodes in place, across as many reads as it takes.
                match dec.decode(&mut body_bytes)? {
                    Chunked::More { out } => { /* body_bytes[..out] is body */ }
                    Chunked::Done { out, rest } => { /* then `rest` bytes of the next message */ }
                }
            }
            Body::Close => unreachable!(), // only for responses
        }
    }
}
```

Errors say why a message was rejected: `Method`, `Target`, `Version`,
`Status`, `NewLine`, `HeaderName`, `HeaderValue`, `TooManyHeaders`,
`ContentLength`, `TransferEncoding`, `ContentLengthAndTransferEncoding`,
`TransferEncodingHttp10`, `Host` and `Chunked`; `Error::is_framing()` tells
a smuggling-shaped rejection from a malformed one. The reason is computed
after the verified parser has rejected, by unverified code that cannot
change the verdict. `parse_response(buf, head_request, connect_request,
&mut headers)` does the same for responses, and `parse_request_with` takes
a header limit and picohttpparser's `last_len`.

### From C (native API)

`cargo build --profile release-abort --features capi`, include `include/vhttp.h`, and
link `target/release-abort/libverilith_http.a` (`-lpthread -ldl -lm`). This is the Rust
API above with C types. Use it when you can change the calling code; use
the picohttpparser or llhttp shapes below when you cannot.

```c
vhttp_header h[64];
size_t n = 64;
vhttp_request r;
int rc = vhttp_parse_request(buf, len, 0, h, &n, &r);
if (rc == VHTTP_OK) {
    /* r.method, r.target and h[i].name/value are offsets into buf;
       r.head_len is where the body starts; r.body says how it is framed
       (VHTTP_BODY_EMPTY, _LENGTH with r.content_length, or _CHUNKED). */
} else if (rc == VHTTP_PARTIAL) {
    /* read more and call again */
} else {
    /* rejected: vhttp_error_message(rc); vhttp_error_is_framing(rc) is
       true for the request smuggling shapes */
}
```

Unlike picohttpparser's shape, it returns the framing decision (the one
the smuggling proofs are about) and the reason for a rejection, and
`vhttp_parse_response` takes whether the request was HEAD or CONNECT.
`vhttp_chunked_decode` is the in-place chunked decoder. Nothing is
allocated per call, and field lines are written into the caller's array.

### From C (picohttpparser's API)

`cargo build --profile release-abort --features phr-abi`, include
`include/picohttpparser.h`, and link `target/release-abort/libverilith_http.a`
(`-lpthread -ldl -lm`). `phr_parse_request`, `phr_parse_response`,
`phr_parse_headers`, `phr_decode_chunked` and
`phr_decode_chunked_is_in_data` behave as picohttpparser's, with the
differences listed [below](#differences-from-picohttpparser).

### From Node.js (or anything else that uses llhttp)

llhttp is three C files: `api.c` and `http.c` (the public API and the
keep-alive rules) and `llhttp.c` (the generated parser). With
`--features llhttp-abi`, `libverilith_http.a` exports the two functions `llhttp.c`
defines, `llhttp__internal_init` and `llhttp__internal_execute`, so
llhttp's own `api.c` and `http.c` (copied in `compat/llhttp`, from llhttp
9.4.4) link against it unchanged. Callers keep llhttp's header, struct
layout, callbacks, pausing and error codes.

For Node.js, `compat/llhttp/node.sh NODE_DIR` points a Node checkout's
llhttp build at `libverilith_http.a` (built with `--features llhttp-lenient`);
then build Node as usual. Node.js v26.13.1 built this way (with verilith-hpack in
nghttp2 and verilith-http in undici too, via verilith-hpack's `compat/node/node.sh`)
passes 7,245 of the 7,248 tests in its default suite (`tools/test.py
default`); the three failures (`test-fs-rmSync-special-char-additional-error`,
which fails on any build run as root, and two TLS tests that need system
certificates) fail the same way on the official binary. Node 26 links a
Rust library of its own, so both scripts build ours without LTO for it.
v24.22.1 passed 5557 of 5558. Several llhttp behaviours go
beyond the HTTP/1.x grammar the machines verify, and the drop-in maps them
onto it:

| llhttp behaviour | In the drop-in |
| --- | --- |
| Lenient flags (`--insecure-http-parser`, `httpValidation`) accept malformed messages | A parser with any lenient flag set runs on llhttp's own generated parser, linked under other names (`compat/llhttp/src/lenient.c`). The strict default stays on the verified machines. |
| `HTTP/0.9` and `HTTP/2.0` heads, and a request line with no version (taken as HTTP/0.9) | Checked by the machine as HTTP/1.0 heads; `http_major` and `http_minor` give the real version. `HTTP/1.2` and up are rejected, as llhttp does. Proven: no recipient in the model accepts such a head at all, so none can frame it differently (`llproof::theorem_ll_request_other`, `theorem_ll_response_other`). |
| A request whose Transfer-Encoding does not end in `chunked` reaches `on_headers_complete`, then fails | The same, so Node answers 400 after the application sees the request; no body byte is parsed. Proven: such a head never gets a body framing; it is rejected unless llhttp's own rules make it an upgrade or the callback skips the body (`llcore::after_head`). |

Differences that remain, all of them messages verilith-http rejects and llhttp
takes, except the first: two equal Content-Length fields (verilith-http takes them
as one, as RFC 9110 allows; llhttp rejects), DEL or other control
characters in a reason phrase, a Transfer-Encoding with a coding that is
not a token in a response, a bare LF before a request line, an HTTP/1.0
request with Transfer-Encoding, and RTSP and ICE messages.

How it works: `src/stream.rs` is the head grammar and framing rules as a
byte-at-a-time state machine, for a caller like Node that gets a head in
pieces and cannot keep the earlier ones. It is proven to accept exactly the
heads the spec accepts, with the same end and framing (below), so the
smuggling theorems hold for what Node is told. When the whole head is in
one buffer (the usual case) the drop-in uses the one-shot parser and its
SIMD scanners instead, and both report the same callbacks. Bodies use the
verified chunked decoder.

The adapter itself is in two parts. `src/llcore.rs` is verified: it is
every decision the drop-in makes about a head. That is the step on each
byte of the wire, including the version bytes the machine reads in place
of `0.9` and `2.0`; the one-shot path; the bulk steps; what follows a
complete head (a body with the verified framing, an upgrade, or a
rejection); and how the machine state is packed into `llhttp_t` between
calls. `src/llproof.rs` proves what those decisions amount to (see
[What is proven](#what-is-proven)). `src/llhttp.rs` is not verified: it
calls the callbacks, keeps spans and pauses, and applies llhttp's own
method, URL, `Connection` and `Upgrade` rules, which only reject more.
It calls `llcore` once per wire byte (or once per bulk run) in order;
that it does so, and that it reports to the callbacks what `llcore`
decided, is what remains trusted in it, and what the differential tests
against llhttp check.

Two things llhttp does that the adapter also does are outside the
theorems, and both are the caller's or llhttp's decision, not a reading
of the bytes: blank lines before a status line are skipped (llhttp skips
them for responses as RFC 9112 asks for requests), and when llhttp's
`http.c` says a message is an upgrade, or `on_headers_complete` asks for
the body to be skipped, the rest of the stream is not read as a body.

`compat/llhttp/test` checks the drop-in against llhttp itself: random
streams of pipelined, chunked, upgraded and corrupted messages, each fed
whole, one byte per call, in random pieces, and with a callback pausing
the parser. Whenever verilith-http accepts a stream, llhttp reports the same
callbacks in the same order with the same data. The CI workflow runs it (manual runs only; automatic runs are off).

### From `fetch()` (undici)

Node's `fetch()` does not use Node's llhttp: undici carries its own copy,
compiled to WebAssembly and embedded in `lib/llhttp/llhttp-wasm.js` and
`llhttp_simd-wasm.js`. `compat/undici/build.sh` builds the same module from
verilith-http: the drop-in above, llhttp's `api.c` and `http.c`, and `malloc`,
`free` and `abort` from Rust, for `wasm32-unknown-unknown` with only clang
and `wasm-ld` (no wasi-sdk). It has exactly the imports (`wasm_on_*`) and
exports undici's `lib/dispatcher/client-h1.js` uses, so undici loads it
unchanged:

```sh
compat/undici/build.sh                 # target/undici/llhttp.wasm
compat/undici/build.sh UNDICI_DIR      # also replaces undici's two embedded copies (keeping *.orig)
```

`compat/node/node.sh` in verilith-hpack does both this and the llhttp change above
for a Node checkout (its `deps/undici/undici.js` embeds the same module).

On a 32-bit target such as wasm32, `llhttp_t`'s pointer-sized spare fields
cannot hold verilith-http's parser state, so the drop-in keeps it in a side table
keyed by the parser's address; `free` drops the entry.

`compat/undici/test/run.sh REF [N] [SEEDS...]` runs the generator of
`compat/llhttp/test` through the callbacks undici registers
(`test/trace.mjs`, under Node), against REF: undici's own `llhttp.wasm`
(stock llhttp), or a native trace binary. Against undici 7.30.1's module,
3,000 random streams (seeds 1 and 2, each split whole, byte by byte and at
random, with pausing) give the same callbacks whenever verilith-http accepts.

## What is proven

Everything here is checked by Verus: `./scripts/verify.sh` reports 367
verified items and 0 errors.

| Property | Where |
| --- | --- |
| **No panics, no out-of-bounds reads, no integer overflow** in the head parser, the framing decision and the chunked decoder. Verus checks every index and every arithmetic operation. | `src/parse.rs`, `src/scan.rs`, `src/framing.rs`, `src/chunked.rs` |
| **Head parsing is exactly the spec.** `request_at`, `response_at` and `headers_at` compute `spec::parse_request`, `parse_response` and `parse_headers`, including telling an incomplete head (`Partial`) from an invalid one. | `src/parse.rs` |
| **SIMD scanning is exact.** The SSE2 (x86-64) and NEON (AArch64) scanners for targets, field values and reason phrases return exactly `spec::run_end`. | `src/scan.rs`, `src/scan_neon.rs` |
| **Linear time.** The parser counts its loop iterations in ghost state and proves the count is at most `3n + 16` for an `n`-byte input, whatever the outcome. | `request_at`, `response_at` |
| **Framing is exactly the spec.** `request_body_exec` and `response_body_exec` compute `spec::request_body` and `spec::response_body`, the RFC 9112 §6.3 decision with the strict rules below. | `src/framing.rs` |
| **Chunked decoding is exactly the spec.** `decode` computes `chunked::run`, the chunked grammar as a byte-level state machine, writing the body in place, at most one loop iteration per input byte. | `src/chunked.rs` |
| **Split invariance.** Decoding `a + c` in one call equals decoding `a`, then `c` from the state `a` left. How a peer splits a chunked body across TCP segments cannot change how it decodes. | `chunked::theorem_split` |
| **Extension stability.** Once a prefix decides a head (complete or invalid), more bytes never change the answer, so a parse never depends on the body or on the next pipelined request. | `lemmas::theorem_request_ext`, `theorem_response_ext`, `theorem_request_agree` |
| **Incremental parsing is sound.** `request_resume` (picohttpparser's `last_len`) may answer `Partial` without reparsing, and never hides a complete request. Fed one byte at a time, a head costs linear total time. | `lemmas::theorem_request_crlfcrlf`, `theorem_request_resume` |
| **Head and framing uniqueness.** If verilith-http accepts a request head ending at `end` with framing `F`, every recipient in the model reads a head ending at `end` with framing `F`, or rejects it outright. Only two kinds of recipient may reject: one that skips fewer leading empty lines than verilith-http, and one that rejects repeated Content-Length lines even when they agree. Both choices are allowed by the RFC, and rejecting a message cannot desynchronise a connection. The same holds for responses. | `unique::theorem_request_unique`, `theorem_response_unique` |
| **The streaming parser is the spec.** Whenever the byte-at-a-time machine behind the llhttp API accepts a head, `spec::parse_request` (or `parse_response`) accepts the same bytes, ending at the same byte, with the same version, status and framing; and it accepts every head the spec accepts. Its bulk steps (runs of URL, value and name bytes at once) are proven equal to stepping each byte. | `stream_proof::theorem_stream_request`, `theorem_stream_request_complete`, the response versions, `stream::hbulk_exec` |
| **The llhttp drop-in's decisions are the machine's.** A head the adapter accepts as HTTP/1.0 or 1.1 is, byte for byte on the wire, a head the spec accepts, with the head end and framing the adapter uses; so every recipient in the model reads the same head end and framing, or rejects. The one-shot path ends in the same state as the byte-at-a-time run. A head accepted as HTTP/0.9 or 2.0 (llhttp takes these) is accepted by no recipient in the model. The machine state survives being packed into `llhttp_t` and unpacked. | `llproof::theorem_ll_request`, `theorem_ll_response`, `theorem_ll_request_other`, `theorem_ll_response_other`, `llcore::fast_head_exec`, `lbulk_exec`, `after_head_exec`, `ph_pack` |
| **Chunked-body uniqueness.** If verilith-http's decoder accepts a chunked body ending at `k` that decodes to `out`, every chunk reader in the model reads a body ending at `k` that decodes to `out`. | `unique_chunked::theorem_chunked_unique` |

### The recipient model

`src/rfc.rs` is a model of HTTP/1.1 recipients, written separately from
the spec and in a different style: it splits the head into lines first, as
the RFC's prose does, and only then looks inside lines. It is trusted, so
it is written to be read next to RFC 9112. Each choice the RFC leaves
open is a parameter, and so is each deviation from the RFC that has led to
a published smuggling bug. The theorems hold for every combination of
parameters, so two recipients that differ in any of these ways still agree
on every message verilith-http accepts.

| Parameter | Kind | Seen in |
| --- | --- | --- |
| A bare LF ends a line | RFC choice (§2.2) | most parsers |
| A bare CR is replaced by SP | RFC choice (§2.2) | |
| Empty lines before the request line are skipped (how many) | RFC choice (§2.2) | |
| Start line split on any whitespace | RFC choice (§3) | |
| Whitespace-led lines after the start line ignored | RFC choice (§2.2) | |
| Obsolete line folding unfolded | RFC choice (§5.2) | |
| NUL in a value replaced by SP | RFC choice (RFC 9110 §5.5) | |
| Identical Content-Length list accepted | RFC choice (§6.3) | |
| Transfer-Encoding overrides Content-Length | RFC choice (§6.1) | |
| Any reading of Transfer-Encoding in HTTP/1.0 | unspecified by the RFC | |
| Any reading of transfer codings with parameters | not modelled, so free | |
| A bare CR ends a line | deviation | llhttp, CVE-2023-30589 |
| Whitespace before the colon dropped from the name | deviation | several proxies |
| A folded line read as a field line of its own | deviation | CVE-2022-32215 shape |
| A value ends at the first NUL | deviation | C string handling |
| `_` in a name matches `-` | deviation | CGI-style servers |
| Content-Length read as one number, not a list | deviation | |
| Content-Length read like `strtol` (leading `+`, trailing junk) | deviation | |
| First or last of several Content-Length values wins | deviation | |
| Content-Length wins over Transfer-Encoding | deviation | the CL.TE shape |
| First or last of several Transfer-Encoding lines wins | deviation | |
| Transfer-Encoding ignored unless it ends in `chunked` | deviation | |
| Chunk lines: bare LF or bare CR ends them | deviation | 2025 "funky chunks" |
| Chunk size line ends only at CR LF (LF is extension) | deviation | 2025 "funky chunks" |
| Anything after the chunk size ignored | deviation | many decoders |
| Whitespace before the chunk size skipped | deviation | |
| The two bytes after chunk data skipped unchecked | deviation | h11, CVE-2025-43859 |

**Not covered.** Recipients that match field names case-sensitively, or
that recognise `chunked` only as the whole Transfer-Encoding value: these
disagree with the RFC on ordinary well-formed messages, so no parser that
accepts such messages can agree with them. Chunk decoders that truncate
the size (to 32 bits, say) are not modelled; verilith-http rejects sizes that do
not fit 64 bits. The model asks nothing of methods, targets or the bytes
allowed in values, since those do not change framing; a real recipient is
the model plus extra rejections, and rejecting more cannot make two
readings disagree.

### Trusted computing base

- The specs: `src/spec.rs` (the head grammar and framing rules), the
  state machine `step` in `src/chunked.rs`, and the recipient model
  `src/rfc.rs`.
- Verus, Z3 and the Rust compiler.
- `src/lanes.rs`: one-instruction wrappers for six SSE2 intrinsics, each
  with a spec restating Intel's definition (checked exhaustively by
  `tests/lanes.rs`), and `verilith_core::prims::copy_within` (one `memmove`, in
  [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core)'s trusted
  primitives).
- The NEON intrinsic specs in
  [verilith-simd](https://github.com/verilith/verilith/tree/main/crates/simd) (`verilith_simd::neon`),
  checked against the real instructions by verilith-simd's `tests/neon.rs` on
  AArch64, and `has_neon`, which is true exactly on AArch64.
- Unverified adapters that only ever pass bytes to the verified code and
  slice by spans it proved in bounds: `src/api.rs`, `src/httparse.rs`,
  `src/capi.rs` (pointer handling, return codes, packing the decoder
  state) and `src/diagnose.rs` (error reasons after a rejection). These
  are fuzzed, below.
- `src/native.rs` (feature `capi`, 238 lines of code for 6 functions), the
  native C API, is the same kind of adapter over `src/api.rs`: pointer
  checks, result codes, copying spans into the caller's structs, and the
  decoder state packed as `src/capi.rs` packs it. It makes no parsing
  decision. `tests/capi.rs` checks every result against the Rust API over
  prefixes and single-byte changes of a set of messages, and
  `tests/c/native.c` runs under ASan and UBSan.
- `src/llhttp.rs`, the llhttp adapter's shell, does more: it drives
  callbacks and pausing, and applies llhttp's own method, URL,
  `Connection` and `Upgrade` rules. Every decision about a head is the
  verified `src/llcore.rs`'s. What is trusted is that the shell hands
  `llcore` each wire byte once and in order, counts Content-Length and
  chunk-data bytes as the verified states say, and tells the callbacks
  what was decided. It is tested against llhttp, below.

## The strict rules

verilith-http takes the strict option wherever RFC 9112 gives a choice, and the
uniqueness theorems are why: each rule below removes a message that two
recipients in the model would frame differently. A message verilith-http rejects
for these reasons gets a 400.

| Rule | RFC 9112 | verilith-http | Why |
| --- | --- | --- | --- |
| Transfer-Encoding and Content-Length together | §6.1: MAY reject, else TE wins | rejected | CL.TE and TE.CL smuggling |
| `chunked` not the final coding of a request | §6.3: 400 | rejected | |
| Transfer-Encoding in HTTP/1.0 | §6.1: framing faulty | rejected | the RFC gives no reading |
| More than one Transfer-Encoding line | allowed (a list) | rejected | first-wins and last-wins parsers |
| Content-Length lines with different numbers | §6.3: reject | rejected | first-wins and last-wins parsers |
| Repeated Content-Length lines with the same number | §6.3: MAY accept | accepted, as hyper does | every recipient reads the same number, or rejects |
| A Content-Length list (`5, 5`) | §6.3: MAY accept identical values | rejected | kept strict for now; rare in practice |
| Content-Length not 1*DIGIT (`+5`, `0x5`, overflow) | §6.3 | rejected; at most 19 digits | `strtol` parsers |
| `Content_Length`, `Transfer_Encoding` | allowed (other names) | rejected | `_`-as-`-` servers |
| Whitespace between field name and colon | §5.1: MUST reject | rejected | |
| Obsolete line folding | §5.2: reject or unfold | rejected | |
| Bare LF line endings | §2.2: MAY accept | rejected | bare-CR and bare-LF parsers |
| Bare CR | §2.2: reject or replace | rejected | CVE-2023-30589 |
| NUL and other controls in names, values, targets | RFC 9110 §5.5 | rejected | NUL-terminating parsers |
| Extra whitespace in the request line | §3: MAY accept | rejected | |
| Missing or repeated Host in HTTP/1.1 | §3.2: 400 | rejected (Rust and C APIs) | |
| Chunk size, extensions and trailers | §7.1 | strict grammar: CRLF only, BWS only where the grammar has it, size fits 64 bits, data followed by CRLF | funky chunks, CVE-2025-43859 |

What strictness costs: these are all shapes that well-behaved clients do
not send, and several (bare CR, whitespace before the colon) the RFC
already requires rejecting. The ones a lenient deployment may meet are
bare LF from hand-written clients and obsolete line folding from very old
servers. A proxy that must accept those can normalise them first and hand
verilith-http the result.

`tests/smuggling.rs` exercises each rule with the shapes of published
attacks:

| CVE | Parser | Shape | verilith-http |
| --- | --- | --- | --- |
| CVE-2022-32213 | llhttp | Transfer-Encoding not validated | rejected: TE is a strict token list, `chunked` last |
| CVE-2022-32214 | llhttp | requests not strictly delimited by CRLF | rejected: CRLF only |
| CVE-2022-32215 | llhttp | multi-line Transfer-Encoding | rejected: no line folding |
| CVE-2023-30589 | llhttp | CR alone accepted as a header delimiter | rejected |
| CVE-2025-43859 | h11 | bytes after chunk data accepted in place of CRLF | rejected: chunk data must be followed by CRLF |

## Testing beyond the proofs

The proofs cover the verified core. The adapters around it are tested:

- `cargo test --profile release-abort`: the smuggling corpus, every prefix and every
  split of every test message, a 300,000-message differential test against
  httparse, and httparse-API tests that drive `verilith_http::httparse` the way
  hyper does.
- `./scripts/test-c.sh`: picohttpparser's own `test.c` against verilith-http's C
  API under ASan and UBSan. 246 of its 295 checks pass; each of the 49
  others is a deliberate difference listed below.
- `compat/llhttp/test`: the differential test against llhttp 9.4.4
  described [above](#from-nodejs-or-anything-else-that-uses-llhttp), and
  Node.js's own HTTP tests.
- `./scripts/fuzz.sh [seconds]`: cargo-fuzz under ASan on four targets,
  the Rust API, the C API, the chunked decoder (checked against
  byte-at-a-time decoding) and the httparse API (checked against
  httparse). The CI workflow runs each for 60 seconds (manual runs only).

## Differences from picohttpparser

All deliberate.

- Obsolete line folding, a bare LF line ending, and more than one space in
  the start line are rejected (picohttpparser accepts them). In chunked
  trailers, too, lines must end in CRLF.
- Messages with ambiguous framing are rejected with -1. For responses the
  C API applies the checks as for a response to a GET; the Rust API takes
  the request method into account.
- On -2 (incomplete), the out-parameters are not written; picohttpparser
  fills in whatever it parsed so far.
- Leading empty lines before a request line are skipped (RFC 9112 §2.2), as
  in picohttpparser.

## Performance

ns per message. Each parser runs alone in its own process, pinned to one
core, for 15 batches of 50,000 parses; the table is the best of 5 such
runs. All parsers record the method, target, and every header name and
value. Lower is better.

| Message | verilith-http (head only) | verilith-http (head + framing) | verilith_http::httparse | httparse 1.10 | picohttpparser | llhttp 9.4 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small request (37 B, 1 header) | **32** | 35 | 50 | 41 | 38 | 118 |
| picohttpparser's bench request (703 B, 9 headers) | **151** | 159 | 188 | 246 | 193 | 617 |
| browser request (1245 B, 16 headers) | **262** | 273 | 331 | 466 | 335 | 1097 |
| response (440 B, 12 headers) | **163** | 191 | 219 | 233 | 196 | 638 |

- "Head only" does what picohttpparser and httparse do. "Head + framing"
  adds the verified framing decision (Content-Length, Transfer-Encoding,
  Host), which llhttp also does. `verilith_http::httparse` adds the framing
  checks and copying into httparse's header type.
- Where the speed comes from, all inside the verified code: field names
  are scanned 16 bytes at a time with a proven SSE2 token classifier;
  the end of a field value is searched for from the start of the line, in
  parallel with the name scan, instead of after it; scans near the end of
  the buffer reuse a final overlapping 16-byte block instead of a byte
  loop; and the framing decision (Content-Length, Transfer-Encoding, Host)
  is folded into the header loop, so headers are not walked twice.
- The `verilith_http::httparse` drop-in pays for the framing checks and for
  copying into httparse's header type, so on the smallest request it is
  about 9 ns slower than httparse itself; on larger messages it is faster.
- The SIMD scanners are SSE2 (the x86_64 baseline) and NEON on AArch64.
  The NEON ones are tested under qemu but not yet benchmarked on ARM
  hardware. Other targets (including the WebAssembly build) use the
  verified scalar scanners.
- **One machine.** These numbers are from a single 4-vCPU cloud VM
  (Intel Xeon @ 2.80GHz), each parser pinned to the same core. Cloud VMs are noisy, so
  differences under about 10% are within noise. To reproduce on your own
  hardware, run `bench/run.sh`: it fetches picohttpparser and llhttp at
  the pinned revisions, builds everything with `-O3 -march=native` (C) and
  `-C target-cpu=native` (Rust), and prints the best of five runs per parser.

### Through llhttp's API

What Node.js pays: a fresh parser state per message, and the URL, status
and every header name and value delivered to callbacks. ns per message;
each parser runs alone in its own process, best of 5 runs of 15 batches of
50,000. Both are built with `-march=native` / `-C target-cpu=native`.

| Message | llhttp 9.4.3 | verilith-http's llhttp drop-in |
| --- | ---: | ---: |
| small request (37 B, 1 header) | 110 | **96** |
| picohttpparser's bench request (703 B, 9 headers) | 537 | **344** |
| browser request (1245 B, 16 headers) | 1034 | **547** |
| response (440 B, 12 headers) | 544 | **404** |

The drop-in is faster than llhttp on every message, by 13% on the
smallest and 1.9x on the browser request. A whole message in one call
takes a lean path: the verified one-shot parser, then the callbacks. A
head split across calls is parsed by the streaming machine, which steps
over runs of URL, value and name bytes at once but is slower than the
one-shot path. `compat/llhttp/test/bench.sh` reproduces this table.

On an Apple M3 Pro (NEON scanners), at `d259b7f`: medians of five
alternating runs, ns per message.

| Message | llhttp 9.4.3 | verilith-http's llhttp drop-in | llhttp ÷ verilith-http |
| --- | ---: | ---: | ---: |
| small request | 44 | **33** | 1.33x |
| picohttpparser's bench request | 191 | **139** | 1.37x |
| browser request | 327 | **231** | 1.42x |
| response | 215 | **158** | 1.36x |

## Building and checking

```sh
cargo build --profile release-abort            # Rust library and static C library
cargo test --profile release-abort             # tests above
cargo test --profile release-abort --features capi --test capi   # the native C API against the Rust API
./scripts/test-c.sh              # the native C API's tests, and picohttpparser's test suite
LLHTTP=path/to/llhttp OUT=dir compat/llhttp/test/build.sh  # llhttp trace harness
python3 compat/llhttp/test/diff.py dir 3000                 # differential test vs llhttp
compat/llhttp/node.sh path/to/node                          # build Node.js with verilith-http
./scripts/fuzz.sh 60             # fuzzing (nightly, cargo-fuzz)
./scripts/verify.sh              # Verus (needs `cargo-verus` on PATH)
bench/run.sh                     # benchmarks
```

The crate builds with stable Rust and depends only on `vstd` from
crates.io (pinned to an exact version), whose proof code is erased in a
normal build. Verification needs the Verus build pinned in
`.github/workflows/ci.yml`; CI builds it from source, verifies, runs the
tests, builds the httparse crate, runs `cargo package`, and fuzzes.

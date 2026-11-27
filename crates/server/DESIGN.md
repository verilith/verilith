# verilith-server: design

A formally verified HTTP server, built by composing the Verilith crates
that already exist (http, hpack, url, text, x509, sync, zlib, brotli,
zstd) with the few new verified pieces a server needs. It has two goals of
equal weight:

1. **Everything that decides what a byte from the network means is
   proven**, to the standard the other crates set: exactly a written
   specification, no panics, no out-of-bounds access, no overflow, bounded
   work and memory. What is trusted is listed, small, and kept apart.
2. **World-class speed.** Parity with or better than nginx, h2o and hyper
   on every benchmark in `bench/server`, measured on the same machine in the
   same sitting. A verified server nobody deploys because it is slower
   proves nothing that matters.

Status: design. This document is the plan; the code follows it in the
milestones at the end. Where the plan and the code later disagree, the code
and its README are right and this file is updated.

## Contents

- [What a server adds to the parsers](#what-a-server-adds-to-the-parsers)
- [Architecture](#architecture)
- [I/O model](#io-model)
- [HTTP/1.1](#http11)
- [HTTP/2](#http2)
- [HTTP/3](#http3)
- [TLS](#tls)
- [Static files, compression and the rest of the request path](#static-files-compression-and-the-rest-of-the-request-path)
- [What is verified and what is trusted](#what-is-verified-and-what-is-trusted)
- [Performance plan](#performance-plan)
- [Benchmarks](#benchmarks)
- [Milestones](#milestones)
- [Open questions](#open-questions)

## What a server adds to the parsers

The crates prove things about one message at a time: verilith-http that a
request head and its framing are read exactly as RFC 9112 says, and the
same way by every recipient in a model that includes the smuggling
deviations; verilith-hpack that a header block decodes exactly as RFC 7541
says however it is split. A server is where those single-message facts
have to compose into facts about a connection, and where most real
vulnerabilities in servers live:

| Class | Real examples | What the server proves |
|---|---|---|
| Request smuggling across a keep-alive connection | CL.TE, TE.TE, "funky chunks" (2025) | The next request starts exactly where verilith-http's framing theorem says the previous one ended, so the uniqueness theorem extends from one message to the whole connection. |
| Response splitting, header injection | CRLF in a handler's header value | Every response the serializer writes parses back, under `spec::parse_response`, to exactly the status, fields and body the handler gave; a value with CR or LF cannot be written. |
| Response framing errors | Content-Length that does not match the body, a body on a 304 or HEAD | Same theorem: the framing of the bytes on the wire is the framing of the body that was produced. |
| HTTP/2 resource exhaustion | Rapid Reset (CVE-2023-44487), CONTINUATION flood (2024), HPACK bomb, SETTINGS and PING floods, zero-window stalls | Memory per connection is bounded by configured limits, and work is linear in bytes received, with a stated constant, whatever the peer sends. Control-frame replies are budgeted, so the server cannot be made to send more than it receives. |
| HTTP/2 protocol state errors | Frames on closed streams, stream ID reuse, flow-control window overflow | The connection follows RFC 9113's stream state machine (§5.1) and flow-control rules (§6.9): windows never exceed 2^31-1 or go below the RFC's bound, and DATA is never sent beyond a window. |
| Path traversal in static files | `/..%2f..%2fetc/passwd`, `%00`, `\` on Windows | The file path opened is the document root followed by components, none of which is `.`, `..`, empty, or contains `/` or NUL. |
| Content negotiation mistakes | Serving gzip to a client that sent `gzip;q=0` | The coding chosen is one RFC 9110 §12.5.3 says the request accepts. |

Composition is also where bugs in the single-crate proofs show up, because
a server uses each crate through every path at once. Each such finding gets
fixed in the crate it belongs to.

## Architecture

Four layers, from the wire up. Only the bottom one is trusted beyond the
usual base (Verus, Z3, rustc, the specs).

```
          ┌───────────────────────────────────────────────────────────┐
  L3      │ application: Handler trait, router, static files, proxy  │  plain Rust over L2's API
          ├───────────────────────────────────────────────────────────┤
  L2      │ verified protocol engines, sans I/O                      │
          │   h1::Conn  (verilith-http)                               │  verified
          │   h2::Conn  (verilith-h2: frames, streams, flow control;  │
          │              verilith-hpack: decoder + new encoder)       │
          │   negotiate, path, range, conditional (text, url)         │
          ├───────────────────────────────────────────────────────────┤
  L1      │ verified per-worker resources                             │  verified
          │   buffer pool, connection slab, timer wheel, write queue  │
          ├───────────────────────────────────────────────────────────┤
  L0      │ trusted OS shim: sockets, epoll/kqueue (io_uring later),  │  trusted, small
          │   writev, sendfile, accept4, clock; TLS crypto (aws-lc)   │
          └───────────────────────────────────────────────────────────┘
```

**Sans I/O is the central decision.** The protocol engines never call the
operating system. A connection engine is a value with three operations:

```rust
impl Conn {
    /// Bytes arrived. Returns how many were consumed and what happened:
    /// requests ready for a handler, body bytes, errors.
    fn recv(&mut self, input: &[u8], ev: &mut Events) -> usize;
    /// A handler's response, or a piece of a streamed body.
    fn send(&mut self, id: StreamId, part: ResponsePart) -> Result<(), SendError>;
    /// Bytes to write now, as a list of slices for one writev.
    fn poll_write<'a>(&'a mut self, out: &mut IoSlices<'a>) -> WriteHint;
    /// That many bytes from the last poll_write reached the socket.
    fn wrote(&mut self, n: usize);
}
```

This is what lets the engines be verified: their specification is a
function from the sequence of bytes received and handler responses to the
sequence of bytes written and events produced, with no I/O in it. It is the
shape rustls, quinn and h2's state machine already use, and it costs
nothing at run time, because the event loop calls these directly with no
dynamic dispatch, no futures and no allocation per call.

The same engines then run under any I/O backend (epoll, kqueue, io_uring,
a test harness that replays a byte stream split every possible way), and
the proofs hold under all of them.

## I/O model

**Thread per core, shared nothing.** N worker threads, one per core the
server is given, each pinned, each with its own event loop, listening
socket, buffer pool, connection slab and timers. A connection lives on one
worker for its whole life. There is no work stealing and no lock on the
request path. This is the model nginx and h2o use and the one that wins
the plaintext and pipelining benchmarks; it is also the easiest to verify,
because a worker's state is never shared.

- **Accept.** Linux: one `SO_REUSEPORT` listening socket per worker, so the
  kernel spreads connections; `accept4(SOCK_NONBLOCK | SOCK_CLOEXEC)` in a
  loop until `EAGAIN`. macOS, where `SO_REUSEPORT` does not balance: one
  shared listening socket registered in every worker's kqueue, each worker
  accepting until `EAGAIN` (some herd, measured; if it matters, a single
  acceptor hands sockets to workers over `verilith-sync`'s SPSC queues).
- **Readiness.** Edge-triggered epoll (Linux) and kqueue with `EV_CLEAR`
  (macOS): read until `EAGAIN`, then parse everything read, then write
  everything produced, in one turn per wakeup. `epoll_wait` returns up to
  1024 events per call.
- **One read, one write per batch.** Pipelined requests in one read produce
  their responses into one buffer, written with one `writev`. Small
  responses never cost a syscall each. Under HTTP/2 the same holds for all
  the streams of a connection.
- **Large bodies.** Static files go out with `sendfile` on plaintext
  connections and, with `--ktls`, under TLS, after the head; under TLS
  without kTLS they are read in 16 KiB pieces into the record layer.
- **Blocking work.** Handlers that block (a file read on a slow disk, a
  database call) run on a pool fed by a `verilith-sync` MPMC channel;
  completions come back over a per-worker channel and an `eventfd` (Linux)
  or `EVFILT_USER` (macOS) wakeup. Fast handlers run inline on the worker.
- **Time.** One coarse clock per worker per loop turn (`CLOCK_MONOTONIC_COARSE`
  on Linux), a hashed timer wheel for idle, header and body timeouts, and the
  `Date` header formatted once a second per worker.

**Why not tokio.** hyper's numbers in `bench/server` show the cost: work
stealing moves connections between cores, wakers are reference counted,
and every connection is a heap-allocated future. Those buy fairness for
arbitrary async code, which a server whose engines are sans-I/O state
machines does not need. An async handler API on top of the worker loop
(a minimal executor per worker, no stealing) is planned for applications
that want one; it sits in L3 and changes nothing below.

**io_uring** is the second backend for Linux (`Config::io_uring`,
`--io-uring`; `src/worker_uring.rs` over `src/sys/uring.rs`), driving the
same engines: multishot accept, multishot receive from a provided-buffer
ring, sends as ring entries, single-issuer rings with deferred task work,
one `io_uring_enter` per loop turn. Measured on the 4-vCPU cloud VM
(`bench/server/results/2026-11-26-cloud-uring`), it makes 12x fewer system
calls than epoll on `h1-plaintext` for the same CPU: system calls are cheap
there and loopback TCP is most of the profile, so the results are +4 to
+10% on large files, h2c and h2 over TLS and -3 to -7% on small HTTP/1.1
requests and new connections. Epoll stays the default until a machine
where system calls cost more (KPTI, older CPUs) or a real NIC
(`send_zc`, zero-copy receive) shows io_uring ahead; registered files and
`send_zc` are the next things to try there.

## HTTP/1.1

`h1::Conn` is built on verilith-http's verified parser and framing, and
adds the connection-level layer, verified.

**Reading.** Each connection has a read buffer from the worker's pool
(16 KiB to start, grown up to the configured head limit, 64 KiB by
default). `recv` calls `parse_request_with` with the previous length, so an
incomplete head is not rescanned (`theorem_request_resume`). On a complete
head it records the framing (`Body::Empty`, `Length(n)` or `Chunked`) and
hands the request to the handler; body bytes then go through the framing:
exactly `n` bytes, or the verified `ChunkedDecoder` in place. The next
request starts at the byte the framing says, never before.

Proven for `h1::Conn`, against a specification that is the list of
messages `spec::parse_request` and the chunked spec read off the whole
byte stream:

- **Connection-level framing.** For any byte stream and any way it is split
  into reads, the requests the engine delivers are exactly the spec's
  sequence of messages: same heads, same bodies, same boundaries. With
  `theorem_request_unique` and `theorem_chunked_unique`, every recipient in
  the model splits the stream into the same messages, so a proxy in front of
  verilith-server cannot be desynchronised from it.
- **Persistence (RFC 9112 §9.3).** The engine closes exactly when the RFC
  says it must: after `Connection: close`, after an HTTP/1.0 request without
  `keep-alive`, after a response that is delimited by closing, and after any
  framing error (whose length is unknown, so nothing after it can be read).
- **Pipelining.** Responses are written in the order the requests arrived,
  each completely before the next, whatever order handlers finish in.
- **Responses parse back.** `serialize` is proven against
  `spec::parse_response(head_request, connect_request)`: the bytes written
  parse back to the handler's status, fields and body, with framing chosen
  by the rules (Content-Length when the length is known, chunked when it is
  not and the request is 1.1, close-delimited otherwise; no body at all for
  HEAD, 1xx, 204 and 304). A field name that is not a token or a value with
  CR, LF or NUL is refused at `send`, so no handler can split a response.
- **Bounded resources.** Memory per connection is at most the head limit
  plus the write buffer limit; work is linear in bytes received, from the
  parser's `3n + 16` bound and the decoder's one step per byte.
- **`Expect: 100-continue`**: the interim response is sent at most once,
  before any body byte is read, and only if the handler asks for the body.

Not proven here: what the handler does with the request.

## HTTP/2

A new crate, `verilith-h2`, holds the HTTP/2 (RFC 9113) frame layer and
connection state machine, sans I/O like `h1::Conn`. HTTP/2 is reached by
ALPN `h2` under TLS and by prior knowledge (the connection preface) on
plaintext; the `Upgrade: h2c` dance from HTTP/1.1 was removed by RFC 9113
and is not supported.

**Frames.** A verified parser and serializer for the frame header and the
ten frame types, with the RFC's per-type length and flag rules, proven to
round-trip (`parse(serialize(f)) == f`) and to reject exactly what the spec
rejects, with the right error code (`FRAME_SIZE_ERROR`, `PROTOCOL_ERROR`).

**Header blocks.** HEADERS and CONTINUATION fragments go to
verilith-hpack's `Decoder::feed`, whose split-invariance theorem is exactly
what CONTINUATION needs: the fields decoded are those of the concatenated
block however it is fragmented. The decoded list is then checked against
§8.3 (pseudo-headers first, exactly the required ones, no connection-specific
fields, lowercase names), proven against a spec of those rules, and turned
into the same `Request` type HTTP/1.1 handlers receive.

**HPACK encoder.** verilith-hpack has the decoder only; the server needs an
encoder. It goes in verilith-hpack, proven against the decoder's own spec:
`spec::decode_block(table, encode(table, fields)) == (fields, table')`
where `table'` is the encoder's own next table, so the peer's decoder and
the encoder never disagree about the dynamic table. Strategy: static table
matches, a small dynamic table for repeated response fields (`server`,
`content-type`, `cache-control`), Huffman only when shorter. Response heads
that repeat (a static file server sends almost the same head every time)
are cached per connection as already-encoded bytes.

**Streams and flow control.** Proven against a spec written from §5.1,
§5.1.1, §5.1.2, §6.9 and §6.5:

- Every stream follows the state diagram; a frame not allowed in a state is
  the error the RFC names (stream or connection).
- Client stream IDs are odd and increase; a smaller or reused one is a
  connection error.
- At most `SETTINGS_MAX_CONCURRENT_STREAMS` open streams.
- Connection and stream windows stay in `[-(2^31-1), 2^31-1]`; a
  WINDOW_UPDATE that would overflow is the RFC's error; the engine never
  sends DATA beyond either window; a SETTINGS_INITIAL_WINDOW_SIZE change
  adjusts every open stream as §6.9.2 says.
- SETTINGS are acknowledged in order; the peer's new values apply from the
  frame that carries them.

**Resource bounds, the headline theorem.** For any sequence of bytes from
the peer:

```text
memory(conn)      <= M(settings)                       always
work(recv(input)) <= c * input.len() + d                each call
bytes_queued_for_control_replies <= budget               always
```

`M` is the sum of the configured limits (header block size, open streams,
buffered DATA per stream), not a function of what the peer sends. The work
bound is a potential argument in the style of verilith-hpack's
`feed_metered`, which the h2 bound reuses for the header blocks. The
control budget is how Rapid Reset, PING and SETTINGS floods become
theorems rather than heuristics: a RST_STREAM costs the peer a frame and
the server a bounded, prepaid amount of work; replies to PING and SETTINGS
are counted against bytes received and the connection is closed with
`ENHANCE_YOUR_CALM` when a peer exceeds the configured ratio. CONTINUATION
without END_HEADERS is bounded by the header block limit, and a header
block is decoded as it arrives rather than buffered.

**Scheduling.** RFC 9218 extensible priorities (urgency 0 to 7,
incremental), not the RFC 7540 dependency tree, which RFC 9113 deprecates.
Within an urgency, round robin by DATA frame. Proven fair in the simple
sense: a stream with data and window is served within one round.

## HTTP/3

HTTP/3 (RFC 9114) runs on QUIC (RFC 9000), a transport of its own over
UDP: packet protection, loss recovery, congestion control and TLS 1.3 built
in. HTTP/3's own layer is small (frames on QUIC streams, and QPACK, RFC
9204, for fields). It comes after HTTP/2, in three steps:

1. **Verified HTTP/3 framing and QPACK** (a sibling of verilith-hpack, with
   the same split-invariance and linear-work theorems, plus QPACK's
   blocked-stream rules), on **quinn-proto** as the QUIC transport.
   quinn-proto is sans I/O, so it slots in as rustls does: trusted, not
   verified. *(done: `src/h3.rs`, one quinn-proto endpoint per worker on
   its own SO_REUSEPORT UDP socket, sending with GSO; QPACK without a
   dynamic table, so no stream ever blocks)*
2. **Verified QUIC parsing and state**: packet headers, varints, the
   frame types, transport parameters, stream and connection flow control,
   and the stream state machines (RFC 9000 §3), with the same resource
   bounds as HTTP/2 (amplification limits before address validation, §8,
   are a theorem rather than a check). Congestion control and the
   cryptography stay trusted. This is [verilith-quic](../quic): the wire
   format and these state machines, proven. *(done:
   [verilith-quic-conn](../quic-conn) is a QUIC server connection on
   verilith-quic and verilith-tls's verified QUIC handshake and packet
   protection, and `src/h3.rs` runs on it. quinn-proto is no longer a
   dependency of the server; it stays only as the client in tests.)*

   The HTTP/3 connection layer above QUIC is verified too:
   `src/h3core.rs` holds what each stream's bytes mean, on verilith-h3's
   `Reader` and its specification. A request reaches the handler at most
   once per stream, only after its stream ended well formed, with its body
   exactly the stream's DATA content (or over `max_body` and answered
   413), and with any Content-Length equal to that length (§4.1.2). Every
   response's bytes read back, under the same specification at the
   client, as one HEADERS frame with the encoded section and then the
   body (`lemma_response_rt`). Our control stream is its type and our
   SETTINGS. The peer gets one control stream and one of each QPACK
   stream, none of which may end, and QPACK is fed exactly the bytes after
   a QPACK stream's type. Requests the peer abandons or has refused are
   bounded by `2 * max_streams` plus `abandoned_per_request` per completed
   request (`Budget`, the HTTP/3 form of the Rapid Reset defence).
   `src/h3.rs` is the glue between QUIC, QPACK and the core (TRUST.md).
3. **UDP speed**: GSO and GRO, `sendmmsg`/`recvmmsg`, and one socket per
   worker with connection IDs routed to the worker that owns them (a BPF
   steering program on Linux). Without these every HTTP/3 server loses to
   HTTP/2 on throughput.

## TLS

**The TLS stack is verilith-tls: TLS 1.3's handshake state machine, key
schedule, message parsing and record protection, verified, with aws-lc's
primitives (AEAD, key exchange, signatures, random numbers) trusted
through the small verilith-tls-aws-lc crate.** It is sans I/O
(`read_tls`, `process`, `plaintext`, `write`, `pending`), so it sits
between L0 and L2 with no adaptation: ciphertext from the socket goes into
it, plaintext goes into `h1::Conn` or `h2::Conn`, and back. aws-lc's
AES-GCM and ChaCha20-Poly1305 are the same assembly OpenSSL uses (nginx and
h2o in the benchmarks), and several of its primitives have proofs of their
own (AWS's SAW and HOL Light work on aws-lc). ALPN chooses `h2` or
`http/1.1`. rustls stays as a second backend (`--features tls-rustls`,
`--tls-backend rustls`), to compare against; TLS 1.2 clients are refused.

What Verilith adds at the boundary:

- **Certificates through verilith-x509.** The server's own chain is parsed
  by the verified DER and X.509 parser at load time, before it is handed to
  the TLS stack, so a malformed certificate in a deployment is rejected with a
  reason rather than half-used. Client certificates for mutual TLS are
  parsed the same way to give handlers their fields (subject, SANs,
  validity) from a verified parse. verilith-x509 parses, it does not
  verify signatures.
- **Record sizes.** The engines' small output pieces are gathered into
  16 KiB writes so each produces full records, and the first records
  of a response are kept small (one MSS) while the connection is new, as
  h2o does, for time to first byte.
- **kTLS** on Linux (`--ktls`), after the handshake, for `sendfile` of
  static files under TLS: the kernel seals what the server sends,
  verilith-tls exports the sending key, IV and sequence number
  (`ServerConn::tx_keys`) and keeps opening what the client sends. Done
  for the epoll loop; TX only, so the verified record layer still checks
  every byte that comes in.

## Static files, compression and the rest of the request path

**Targets and paths.** Origin-form targets (`/a/b?q`) are split at `?`,
percent-decoded with verilith-text's verified decoder, and resolved by a
verified dot-segment removal (RFC 3986 §5.2.4). The theorem is the one in
the table at the top: the path opened is the root followed by components
that are never `.`, `..`, empty, or contain `/`, `\` or NUL; a target that
would escape is a 404, not a clamp. Opening is `openat2` with
`RESOLVE_BENEATH | RESOLVE_NO_MAGICLINKS` on Linux, which also stops
symlinks out of the root (the kernel's guarantee, trusted), and
component-by-component `openat(O_NOFOLLOW)` on macOS. Absolute-form
targets (proxies) and `Host` go through verilith-url's verified WHATWG
host parser.

**Conditional and range requests** (RFC 9110 §13, §14): `If-None-Match`,
`If-Modified-Since`, `Range` with one or several ranges, parsed by verified
parsers against specs of those grammars, with the proven property that the
bytes served are exactly the requested ranges of the file, within its
length. Multipart byteranges are supported; a range set whose total exceeds
the file (the 2011 Apache "range of death" shape) is served as the whole
file.

**Compression.** `Accept-Encoding` is parsed (with q-values) by a verified
parser, and the coding chosen is proven acceptable. Static files prefer a
precompressed sibling (`.br`, `.zst`, `.gz`) when it exists and is
acceptable: no compression work on the request path, which is what the
fastest deployments do. Dynamic responses above a size threshold and of a
compressible type are gzip-compressed with verilith-zlib's verified
compressor. Brotli and zstd compressors do not exist in Verilith yet (the
crates are decoders); they would slot in the same way.

**Shared state across workers** (configuration reload, graceful shutdown,
statistics) uses verilith-sync: an `RwLock` for the configuration snapshot,
read once per loop turn, never per request; channels for control messages.

## What is verified and what is trusted

| Part | Status | Notes |
|---|---|---|
| HTTP/1.1 head parsing, framing, chunked decoding | verified | verilith-http, as today |
| `h1::Conn`: message boundaries, persistence, pipelining order, response serialization | verified | new |
| HTTP/2 frames, streams, flow control, resource bounds | verified | new crate verilith-h2 |
| HPACK decoding | verified | verilith-hpack, as today |
| HPACK encoding | verified | new, in verilith-hpack |
| Pseudo-header and field validation (RFC 9113 §8) | verified | new |
| Path normalization, Range, conditional, Accept-Encoding | verified | new, on verilith-text and verilith-url |
| gzip of dynamic responses | verified | verilith-zlib |
| Certificate parsing | verified | verilith-x509 |
| Buffer pool, connection slab, timer wheel | verified | new; proven no use after free of a slot, no double use of a buffer, bounded |
| Cross-worker control | verified | verilith-sync |
| Event loop and syscalls (epoll, kqueue, io_uring, sockets, writev, sendfile, openat2) | **trusted** | `src/sys/`, each call an `external_body` with a contract (a read of `n` writes `buf[..n]`, `n <= len`); kept as small as possible and listed in TRUST.md |
| TLS 1.3: handshake, key schedule, records | verified | verilith-tls |
| TLS cryptography: aws-lc (verilith-tls-aws-lc) | **trusted** | C and assembly behind the contracts on verilith-tls's `Provider` trait |
| The kernel's TCP, `sendfile`, `openat2` semantics | **trusted** | |
| Handlers and the router | not verified | application code; it only reaches the wire through the verified `send` |
| Configuration file parsing | not verified at first | small; a verified parser later if the format grows |

As in every Verilith crate: no `assume` or `admit` in the source, every
`external_body` counted by `scripts/trust-ledger.py`, and the specs are the
files to review.

## Performance plan

The proofs constrain how code is written, not how fast it can be: the
other crates are faster than the C they replace. The server applies the
same approach, and these choices in particular:

- **No allocation per request** once a connection is warm: buffers from the
  worker's pool, field spans into the read buffer (verilith-http already
  returns spans), handler responses written straight into the write
  buffer.
- **One syscall per batch**, both ways, as above; `TCP_NODELAY`; writes
  only at the end of a loop turn.
- **Precomputed response heads**: the status line and fixed fields of a
  route's response are serialized once; per response only `Date`,
  `Content-Length` and the variable fields are written. `Date` once a
  second per worker.
- **SIMD where it pays**, through verilith-simd's specified intrinsics, as
  verilith-http's scanners already do: header value validation at `send`,
  HPACK Huffman encoding.
- **Proof-friendly fast paths.** Where a proof wants a simple loop and the
  hardware wants something else, the fast version is the one verified,
  with the simple one as its specification, as the CRC-32C kernel was.
- **Profiles before guesses.** Each milestone ends with a profile of the
  plaintext and static cases against nginx and h2o, and the largest
  difference is the next thing fixed.

## Benchmarks

`bench/server` (see its README) runs verilith-server, hyper, nginx and h2o
side by side, the same routes, the same CPUs and threads, cases taking
turns and the order reversed each round. It reports requests per second,
latency percentiles, and **requests per server CPU-second**, which is the
figure least disturbed by a shared machine and the one to compare when the
load generator might be the bottleneck.

Cases (each with a reason):

| Case | Why |
|---|---|
| `h1-plaintext` | the TechEmpower plaintext route without pipelining: per-request overhead |
| `h1-plaintext-pipe` | 16 pipelined requests: batching, one write per batch |
| `h1-static-1k`, `-64k`, `-1m` | file serving, `sendfile`, write paths |
| `h1-close` | a new connection per request: accept and setup cost |
| `h1-tls-plaintext` | TLS 1.3 record overhead on HTTP/1.1 |
| `h2c-plaintext` | HTTP/2 framing, HPACK, stream scheduling, without TLS |
| `h2-tls-plaintext` | the common deployment: HTTP/2 over TLS |
| `h2-tls-static-64k` | flow control and DATA scheduling under TLS |

Planned additions: TLS handshakes per second (new connection per request
under TLS), latency at a fixed rate below saturation (an open-loop load
generator, as wrk2 or oha), many idle connections (memory per connection,
which the resource theorems bound), and adversarial cases (Rapid Reset,
CONTINUATION flood, slowloris) whose metric is the legitimate traffic's
throughput while under attack.

Baseline, on the 4-vCPU cloud VM this design was written on (server on 2
CPUs, wrk and h2load on the other 2, one round of 3 s per case, so
indicative only; the Mac runs are the ones to quote):

| Case | hyper 1.13 | nginx 1.24 | h2o 2.2.5 |
|---|---:|---:|---:|
| h1-plaintext, req/s | 220k | 322k | 193k |
| h1-plaintext-pipe, req/s | 397k | 308k | 203k |
| h1-static-64k, req/s | 110k | 131k | 99k |
| h2c-plaintext, req/s | 255k | 330k | 516k |
| h2-tls-plaintext, req/s | 237k | 384k | 478k |

The targets follow from this: nginx's HTTP/1.1 numbers and h2o's HTTP/2
numbers, on every case, on both the Mac and Linux.

## Milestones

Each one ends with the proofs passing, the tests passing, a benchmark run
in `bench/server/results`, and a merge.

1. **Design and harness.** This document and `bench/server`. *(done with
   this file)*
2. **HTTP/1.1 server.** `crates/server`: the L0 shim for epoll and kqueue,
   the worker loop, `h1::Conn` with its connection-level theorems,
   verified serialization, `/plaintext` and in-memory routes. Benchmark
   against all three on `h1-*` cases.
3. **Static files.** Path theorem, `openat2`, `sendfile`, Range,
   conditional requests, precompressed variants and Accept-Encoding.
   *(done: path theorem, `openat2`, single ranges, ETag and
   Last-Modified, per-worker cache; left: precompressed variants,
   multipart ranges, streaming files larger than the cache)*
4. **TLS.** ALPN, certificates through verilith-x509. *(done on
   verilith-tls, with rustls kept to compare, session tickets, and 0-RTT
   behind `--early-data` (425 Too Early for unsafe methods), and
   Encrypted Client Hello behind `--ech`, kTLS sending behind `--ktls`;
   left: verilith-x509 at load)*
5. **HPACK encoder** in verilith-hpack, and **verilith-h2 frames**. These
   two do not depend on milestones 2 to 4 and can run in parallel threads.
   *(encoder done: `crates/hpack/src/encoder.rs`, the per-connection cache
   of encoded response heads left to verilith-h2; frames done:
   `crates/h2`, with the round trip and its benchmark against h2 and
   nghttp2 in its README)*
6. **HTTP/2 connection**: streams, flow control, scheduling, the resource
   bounds; h2c and h2 benchmarks against h2o. *(done: `h2core.rs`, every
   frame decision verified, with the stream table, SETTINGS, GOAWAY and
   the flood budget, at the old engine's speed; left: the work bound per
   input byte as a theorem (the budget bounds frames, not cycles), RFC
   9218 priorities)*
7. **io_uring and kTLS** backends, if the benchmarks show they are needed
   for parity.
8. **HTTP/3**: QPACK and HTTP/3 framing on quinn-proto, then verified
   QUIC parsing and state, then GSO/GRO (see [HTTP/3](#http3)). *(first
   step done; GSO and GRO done, `recvmmsg` and connection-ID steering left.
   First results, `bench/server/results/2026-11-26-cloud-h3`, in requests
   per server CPU-second: h3-plaintext 292k against nginx-quic's 262k,
   h2o's 114k and quinn's 132k; but h3-static-64k 17k against nginx-quic's
   26k, and h3-static-1m 1.1k against 1.7k. Large bodies are about 45%
   AES-GCM and most of the rest is quinn-proto's packet building and ACK
   processing: the next step, a verified QUIC transport of our own, is
   also where those numbers move)*
9. **Reverse proxy.** Upstream HTTP/1.1 with verilith-http's response
   parser: here the smuggling theorem is about two hops of the same
   connection, which is the case it was written for.

## Open questions

- **Async handlers.** A per-worker executor with no stealing is the plan;
  whether to make it compatible with the `http` crate's types and tower's
  `Service`, so existing Rust handlers run unchanged, is open. The cost is
  an allocation per request for boxed futures, which the plaintext case
  would show.
- **One crate or several.** The engines might be more reusable as their own
  crate (`verilith-h1` next to `verilith-h2`), so that hyper or another
  server could use them. Start with them inside `verilith-server` and split
  if anyone wants them.
- **h2o's HTTP/2 lead.** h2o is 1.5x nginx on `h2c-plaintext` here. Its
  techniques (per-connection encoded-header caches, writing frames
  directly into the TLS record buffer, and its scheduler) are the first
  things to study for milestone 6.
- **Benchmark machine.** A shared 4-vCPU VM puts the load generator on the
  same host as the server; the Apple M3 Pro the other benchmarks use is
  quieter but still one machine. Two machines on a fast link would be the
  honest setup for publishing numbers.

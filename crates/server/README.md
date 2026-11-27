# verilith-server

A formally verified HTTP server, built from the Verilith parsers, aiming
for nginx- and h2o-class speed. The plan, with the theorems still to come,
is in [DESIGN.md](DESIGN.md). This README describes what exists today.

**Status: HTTP/1.1, HTTP/2 over cleartext with prior knowledge (h2c,
`--h2c PORT`), and TLS with h2 or http/1.1 by ALPN (`--features tls`,
`--tls PORT --cert PEM --key PEM`; TLS 1.3 on the verified verilith-tls),
and static files from disk with a proven path check (`files::Files`;
`--root DIR`, served under `/static/`), and HTTP/3 (`--features h3`,
`--h3 PORT --cert PEM --key PEM`, UDP): the verified verilith-h3 framing
and verilith-qpack on verilith-quic-conn's QUIC (verified wire format,
recovery, handshake and packet protection).** The API will change.

```rust,no_run
use std::sync::Arc;
use verilith_server::{serve, Config, Field, Request, Response};

fn main() {
    let hello = |req: &Request, res: &mut Response| {
        if req.path() == b"/" {
            let _ = res.send(200, &[Field { name: b"Content-Type", value: b"text/plain" }], b"Hello, World!");
        } else {
            res.error(404);
        }
    };
    serve(Config { port: 8080, ..Config::default() }, Arc::new(hello)).unwrap();
}
```

`cargo run --release --features tls --bin verilith-server -- --http 8080
--h2c 8081 --tls 8443 --cert C --key K --root DIR` runs the server
`bench/server` measures.

## Quickstart

Rust 1.89 or later; macOS or Linux. From the repository root:

```sh
# Build: HTTP/1.1 and h2c always; `tls` adds HTTPS (h2 + http/1.1 by ALPN);
# `h3` adds HTTP/3 over UDP (and implies `tls`).
cargo build --release -p verilith-server --features h3

# A certificate for localhost (or use mkcert, or your real cert and key in PEM;
# the key must be PKCS#8: ECDSA, Ed25519 or RSA).
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:prime256v1 -nodes \
  -keyout key.pem -out cert.pem -days 365 -subj /CN=localhost \
  -addext subjectAltName=DNS:localhost,IP:127.0.0.1

# Serve ./site under /static/ over HTTP/1.1 (8080), HTTPS (TCP 8443) and
# HTTP/3 (UDP 8443; HTTPS responses advertise it with Alt-Svc).
./target/release/verilith-server --http 8080 \
  --tls 8443 --h3 8443 --cert cert.pem --key key.pem --root ./site
```

Then `curl http://localhost:8080/static/`, `curl -k
https://localhost:8443/static/index.html` (h2), or a browser at
`https://localhost:8443/static/` (it moves to HTTP/3 after the first
response). `GET /plaintext` answers "Hello, World!". Other flags:
`--threads N` (default: one per CPU), `--h2c PORT` (cleartext HTTP/2 with
prior knowledge), `--io-uring` (Linux), and `--tls-backend rustls` (the trusted library, to
compare).

The binary is the benchmark server; for your own routes, use the library
(the example above): `serve(Config, handler)`, where the handler gets a
`Request` and writes through `Response::send`, and `files::Files::serve`
serves a directory from inside it.

## How the crates fit together

The request path, from socket to response, with the crate that does each
step (each a separate crate with its own proofs):

| Step | HTTP/1.1 | HTTP/2 | HTTP/3 |
|---|---|---|---|
| Event loop, sockets | `worker.rs` / `worker_uring.rs`, `sys/` (trusted) | same | same, UDP with GSO/GRO |
| Encryption | verilith-tls (TLS 1.3 handshake, record layer), crypto from verilith-tls-aws-lc (trusted) | same | verilith-quic-conn (QUIC transport) on verilith-quic (packets, frames, loss recovery) and verilith-tls's QUIC mode |
| Framing | verilith-http (request parser, body framing: the smuggling theorems) | verilith-h2 (frames) | verilith-h3 (frames, stream rules) |
| Field compression | — | verilith-hpack | verilith-qpack |
| Connection logic | `conn.rs` + `persist.rs` (verified: requests exactly the spec's, in order) | `h2core.rs` with `flow.rs`, `streams.rs` (verified: every frame decision, the stream table, SETTINGS, GOAWAY, the flood budget), driven by `h2.rs` | `h3.rs` |
| Handler | your code: `Request` in, `Response` out | same | same |
| Response | `respond.rs` (verified: the head parses back exactly) | HPACK-encoded fields | QPACK-encoded fields |
| Static files | `path.rs` (verified: never leaves the root), `range.rs` (verified), verilith-text (percent-decoding), `files.rs` | same | same |

Where the proofs meet: each crate proves its piece against an RFC
specification written in that crate's `spec.rs`, and the server's
verified modules use those specifications directly. For example, `conn.rs`'s
invariant is stated with verilith-http's `spec::parse_request`, and
`respond.rs`'s theorem with its `spec::parse_response`, so "the server
hands the handler exactly the request the parser's spec sees" and "the
response the client parses is exactly what the handler sent" are one
chain. The plain-Rust glue (event loops, the buffer and handler side of
`h2.rs`, `h3.rs`, the trusted
OS and crypto calls) is listed in [TRUST.md](TRUST.md) with what each
piece is assumed to do.

## How it works

One worker thread per CPU, each pinned, each with its own epoll (Linux)
or kqueue (macOS) loop, listening socket (SO_REUSEPORT on Linux) and
connections; nothing is shared between workers on the request path. Per
readiness event a worker reads until the socket is empty, has the
HTTP/1.1 engine handle every complete request in what it read, and writes
all the responses with one system call. Handlers run inline on the
worker and get a zero-copy view of the request. On Linux, `--io-uring`
(`Config::io_uring`) runs each worker on io_uring instead: the same
engines, one `io_uring_enter` per loop turn (see DESIGN.md, "I/O model",
for when it is faster and when not).

## What is proven

`scripts/verify.sh` (Verus): 288 verified, 0 errors.

- **Requests are exactly the specification's, in order** (`conn.rs`,
  the invariant of `Core`). `first` is the request at the front of a byte
  stream by verilith-http's specification: `spec::parse_request` for the
  head, `spec::request_body` for the framing, `chunked::run` for a chunked
  body. At every moment, the requests the server has handed to handlers
  are the stream's first requests back to back (`prefix_ok` of every byte
  received), whatever the bytes are and however they were split into
  reads: the server never acts on a request the specification does not
  see at that place, never skips one, and never disagrees with it about
  where a body ends, including chunked bodies decoded in place across
  reads and buffer moves. Request smuggling and desynchronization within a
  connection are ruled out by the theorem.
- **Responses go out once each, in request order** (`out.rs`, the
  invariant of `Engine`). The bytes queued on a connection are its
  responses back to back: exactly one per request the core has handed to a
  handler, in that order, plus at most one error response at the end for a
  request the core rejected. Only `Wire::answer` adds a response, only for
  the open request, and only once (a second send is `AlreadySent`; a
  handler that sends nothing gets a 500 in its place). Every response is
  final (a 1xx from a handler is refused: a client would read it as interim
  and pair every later response with the wrong request), its head is one
  `theorem_head_parses` covers, and it is framed by its true body length,
  with no body for HEAD, 1xx, 204 and 304. A response that lists the
  connection option `close` anywhere in its fields, the server's own or the
  handler's, in any case and in any list, is the last one (RFC 9112 §9.6:
  the server must close after it), and every close the server decides
  itself is announced: the response before it says `Connection: close`
  (unless the handler called `close_after` after sending, which still
  closes). `100 Continue` is sent at most once per request, before its
  final response, only when it asked with `Expect: 100-continue`.
- **The output queue hands the event loop exactly the queued bytes, in
  order** (`out.rs`, `Out`): `slices` and `slices_io` return the start of
  the unwritten bytes (all of them if the slices fit), a `sendfile` range
  is the sealed file's copy of exactly the next bytes, and `advance` moves
  past exactly what was written, across owned bytes and shared bodies.
- **Persistence is RFC 9112 §9.3's** (`persist.rs`, `Core::done`). A
  request persists unless a `Connection` field lists `close`; an
  HTTP/1.0 request only if one lists `keep-alive`; options are the list's
  elements, OWS trimmed, in any case, on any number of Connection lines.
  `persists_exec` computes that exactly, and `Core::done` calls it
  itself: the core reads a next request only if the one answered
  persists, whatever the plain Rust around it asks.
- **HTTP/2 flow control** (`flow.rs`). A send window is always what the
  peer granted minus what was sent, within ±(2^31 − 1); credit past that
  is refused (FLOW_CONTROL_ERROR, RFC 9113 §6.9.1), and `take_data`, the
  only way to spend it, sizes each DATA frame to at most what both the
  stream's and the connection's windows allow. A receive window catches a
  peer sending past what we advertised (`unacked <= window` always) and
  says when a WINDOW_UPDATE is due.
- **HTTP/2 stream states** (`streams.rs`). Every frame that names a
  stream goes through `classify`, which computes `verdict`, a table of
  RFC 9113 §5.1 over the server's view of the stream (idle, open,
  half-closed (remote), closed). Only HEADERS opens a stream, only on an
  odd ID above every ID opened before (§5.1.1), and DATA is taken only on
  an open stream.
- **The HTTP/2 connection** (`h2core.rs`, the invariant of `Core` and
  `Core::on_frame`'s postconditions). Every frame goes through the
  verified core, which keeps the stream table, the peer's SETTINGS, both
  connection windows, the header block in progress and the flood budget,
  and writes the control frames the RFC asks for. Proven: streams are
  kept in ID order, every ID odd and at most the highest opened, which
  never goes down; a frame opens at most one stream, only HEADERS on a
  new ID, never after the peer's GOAWAY, and never more than
  `max_streams` at once (§5.1.2: past that, RST_STREAM(REFUSED_STREAM)
  once the block, CONTINUATION included, is decoded); inside a header
  block any frame but its CONTINUATION is a connection error (§6.10), and
  a block is decoded even for a refused or reset stream so the HPACK
  tables stay in step; every SETTINGS is acknowledged once applied
  (§6.5.3) and every PING answered with its own payload (the exact bytes,
  by verilith-h2's serializer spec); SETTINGS_INITIAL_WINDOW_SIZE shifts
  every open stream's send window (§6.9.2); RST_STREAM is sent only for a
  stream that is not idle (§5.1); GOAWAY names the highest stream opened
  and is sent at most once; a peer's GOAWAY(NO_ERROR) drains (open
  streams finish, then GOAWAY and close). **Flood budget:** while the
  connection is open, budget units spent never exceed 1000 plus
  `control_per_request` per response sent in full, and every frame that
  costs nothing carries at least one byte of a header block or body or
  completes a request. PING, SETTINGS (per parameter), WINDOW_UPDATE,
  PRIORITY, RST_STREAM, GOAWAY, unknown and empty frames, refused
  streams and frames on closed streams all cost a unit, so Rapid Reset
  (CVE-2023-44487), PING and SETTINGS floods and the empty-CONTINUATION
  flood end in GOAWAY(ENHANCE_YOUR_CALM) after a bounded number of
  frames.
- **Responses parse back exactly** (`respond::theorem_head_parses`). For
  any status, reason phrase, field lines and framing that pass the checks
  in `respond.rs`, the head `write_head` writes, followed by any bytes at
  all, is parsed by verilith-http's specification of a response head
  (`spec::parse_response`, the definition its smuggling theorems use) to
  exactly that status and reason, exactly those field lines in that order,
  ending exactly where the head ends; and its framing fields (`fields_of`)
  say exactly the Content-Length or `Transfer-Encoding: chunked` the server
  chose and nothing else. So no handler input can add a field line, end a
  head early, or change how the body is framed: response splitting and
  header injection are ruled out by the theorem, not by a filter someone
  might forget to call.
- **The checks are exact** (`check_name`, `check_value`, `check_reason`,
  `check_fields`, `write_head_checked`): each computes its specification,
  and `write_head_checked` writes nothing unless every precondition of the
  theorem holds. A name that a recipient could read as Content-Length or
  Transfer-Encoding (including `Content_Length`) is refused, because the
  server writes the framing itself.
- **Content-Length is written correctly** (`push_dec`, `lemma_dec_digits`):
  the digits read back, under the spec's `decimal`, as the body length.
- **Static files never leave the root** (`path.rs`,
  `lemma_resolve_safe`). A request path becomes a file path only through
  `resolve_exec`, which computes `resolve` exactly: segments split at `/`,
  each percent-decoded by verilith-text's verified decoder, then applied
  to a stack (empty and `.` do nothing, `..` pops and is an error at the
  root, never a clamp). A decoded segment holding `/`, `\\` or NUL is an
  error, so `%2f`, `%5c` and `%00` cannot make a separator or end a C
  string. The theorem: every component of a resolved path is non-empty,
  not `.` or `..`, and has none of those bytes, and `join_to` writes
  exactly those components joined by `/`. The file is then opened with
  `openat2(RESOLVE_BENEATH | RESOLVE_NO_MAGICLINKS)` (trusted: the
  kernel's guarantee that no symlink leads out), or one component at a
  time with `O_NOFOLLOW` where there is no openat2. Hidden files (a
  component starting with `.`, except `.well-known`) are not served.
- **Ranges lie inside the file** (`range.rs`, `lemma_part_ok`):
  `parse_range` computes `range_of` exactly for `Range: bytes=…`, and a
  range it serves is non-empty and ends within the file's length.
- No panics, overflow or out-of-bounds access in the above.

Everything about reading a request is verilith-http's, verified there:
the head parser, the framing decision (with its uniqueness theorems: every
recipient in a model of RFC 9112 that includes the published smuggling
deviations reads the same head end and framing), and the chunked decoder.

## What is not proven yet

- **The plain-Rust half of the HTTP/2 engine** (`h2.rs`): the read
  buffer, feeding each fragment the core hands back to verilith-hpack's
  verified decoder and collecting the fields (the decoded-size limit is
  checked here), buffering bodies, running handlers, and framing
  responses (`schedule`), which encodes heads with verilith-hpack's
  verified encoder (dynamic table included) when their HEADERS frame is
  written, so blocks reach the peer in the order they were encoded, and
  sizes DATA with the core's `take` (verified `take_data`). Tested in
  `tests/h2.rs`: every split of a request stream gives the same
  responses, read back with the verified parser and decoder; DATA stops
  at the peer's window; protocol errors, a PING flood, Rapid Reset and
  an empty-CONTINUATION flood end in GOAWAY; a refused stream's
  CONTINUATION is decoded and the stream reset; a peer's GOAWAY drains.
- **The event loop and the OS shim** (`worker.rs`, `sys/`): trusted, as
  in every server. See [TRUST.md](TRUST.md).
- The `Date` formatter and the reason-phrase table are plain Rust (both
  pass the verified checks before they reach the wire, so a bug there
  cannot split a response). PEM decoding of the TLS certificate and key
  uses verilith-text's verified base64 decoder; finding the PEM blocks is
  plain Rust.
- The static file server around the two proofs (`files.rs`: the
  per-worker cache, Content-Type, ETag and Last-Modified, 304, If-Range,
  301 to a directory's `/`) is plain Rust, tested in `tests/files.rs`
  (escapes by `..`, encoded `..`, `%2f`, `%5c`, `%00`, symlinks and hidden
  files are all 404s).

## Performance

`bench/server` against hyper 1.13, nginx 1.24 and h2o 2.2.5, on a 4-vCPU
cloud VM (server on 2 CPUs, wrk on the other 2). These are noisy numbers;
the full report is in `bench/server/results/`.

Requests per second, median of 3 rounds of 10 s, after the HTTP/2,
connection-setup and sendfile work
(`bench/server/results/2026-11-26-cloud-all`, which also has Bun, the TLS
cases and latencies), and in brackets requests per server CPU-second, the
figure least disturbed by a shared machine:

| case | verilith | hyper | may-minihttp | nginx | h2o |
|---|---:|---:|---:|---:|---:|
| `h1-plaintext` | 297k (**184k**) | 231k (120k) | **305k** (167k) | 303k (160k) | 192k (98k) |
| `h1-plaintext-pipe` (16 deep) | 3.00M (**2.07M**) | 1.29M (654k) | **3.05M** (1.81M) | 352k (179k) | 199k (100k) |
| `h1-static-1k` | 303k (**172k**) | 199k (103k) | **310k** (162k) | 184k (94k) | 305k (162k) |
| `h1-static-64k` | **119k** (**74k**) | 90k (46k) | 84k (43k) | 118k (63k) | 99k (51k) |
| `h1-static-1m` | **9.7k** (**5.0k**) | 6.4k (3.3k) | 5.4k (2.7k) | 5.2k (2.7k) | 5.0k (2.6k) |

Static files there were held in memory by the benchmark binary. Served
from disk by `files::Files` (verified path resolution, openat2, checked
against the disk once a second per worker), a quick run gives the same:
`h1-static-1k` 272k (166k) against h2o 270k (146k) and nginx 173k (89k);
`h1-static-64k` 121k (81k) against nginx 109k (58k); `h1-static-1m` 9.5k
(4.9k) against h2o 5.1k (2.6k); `h2-tls-static-64k` 69k (36k) against h2o
64k (34k).
| `h1-close` (new connection per request) | 76k (**76k**) | **78k** (44k) | n/a* | 62k (59k) | 75k (50k) |
| `h2c-plaintext` (h2load, 64 conns × 32 streams) | **1.54M** (**1.15M**) | 248k (134k) | no h2 | 321k (163k) | 502k (254k) |

\* may-minihttp ignores `Connection: close`, so its 311k there is a
keep-alive figure. Where it is close in raw req/s, verilith-server does the same work on less CPU.

Where the numbers come from: bodies of 8 KiB and more are written from a
shared buffer by `writev`, not copied. HTTP/2 heads go through the
verified HPACK encoder with its dynamic table (header bytes on the wire
90% smaller than uncompressed, as with h2o), and streams are pooled; in
`h2c-plaintext`, h2load is the bottleneck.

TLS 1.3 on verilith-tls (verified handshake and record layer, aws-lc
cryptography; `bench/server/results/2026-11-26-cloud-tls`), quick run, req/s
with requests per server CPU-second in brackets: `h1-tls-plaintext` 221k
(**156k**) against nginx 194k (106k), hyper 180k (99k), h2o 151k (81k);
`h2-tls-plaintext` **1.16M** (1.11M) against h2o 535k (270k), nginx 372k,
hyper 226k; `h2-tls-static-64k` **71k** (38k) against h2o 65k (34k), hyper
57k, nginx 41k. The same server on rustls (`--tls-backend rustls`) is within
the run-to-run noise of it (209k, 1.35M, 64k). `h1-tls-close`, a new
connection per request, with session tickets (shared by all workers, so
a ticket from one resumes on any; `results/2026-11-26-cloud-tls-tickets`):
5.6k req/s and **8.2k** per server CPU-second, against hyper 6.4k (4.9k),
nginx 6.0k (3.4k) and h2o 4.0k (2.5k); there wrk's own CPU is the limit.
A TLS 1.3 server answers a client's Finished with nothing when it sends no
ticket, so a client with Nagle on would hold its request for the kernel's
40 ms delayed ACK: the server sets `TCP_QUICKACK` while handshaking.

TLS 1.3 0-RTT (`--early-data N`, off by default): a client resuming a
session sends its request with the ClientHello and gets the response with
the server's flight, one round trip sooner. Through a proxy adding 20 ms
of round trip, the first response byte of a resumed connection came after
42.5 ms without 0-RTT and **21.7 ms** with it (50 ms: 102.8 against
51.6 ms; `bench/server/zero-rtt`, `results/2026-11-26-cloud-0rtt`).
Early data can be replayed by an attacker, so the server takes it only as
verilith-tls proves (a resumption, the ticket's suite and ALPN, within
the size it advertised) and only once: a single-use register of
ClientHellos and a 10 s freshness window on the ticket's age (RFC 8446
§8), proven to take no ClientHello twice (verilith-tls's
`antireplay.rs`). A request read from early data has
`Request::early()` set, and any method but GET, HEAD and OPTIONS is
answered 425 Too Early (RFC 8470) without calling the handler (the
decision is `early::too_early`, verified); the
client sends it again after the handshake. The register is per process,
so servers on several machines sharing ticket keys should leave 0-RTT
off.

Encrypted Client Hello (`--ech PUBLIC_NAME [--ech-key FILE]`, off by
default; RFC 9849): the client encrypts its real ClientHello (server name,
ALPN) to a key the server publishes, so an on-path observer sees only
PUBLIC_NAME. The server prints the ECHConfigList to put in the name's DNS
HTTPS record (`ech=`); FILE holds the 32-byte X25519 key
(`head -c 32 /dev/urandom > ech.key`) so the record outlives restarts, and
the certificate must also be valid for PUBLIC_NAME, which a client with
stale keys authenticates to fetch the new ones. verilith-tls proves how
ClientHelloInner is rebuilt from the decrypted bytes and the outer one
and the acceptance signal in ServerHello; HPKE is aws-lc's, trusted. An
ECH handshake costs the server about 30 µs more (one X25519 and the
decryption: 77 against 107 µs of server CPU per full handshake, in
memory, `tls-aws-lc/tests/ech.rs` `ech_server_cost`); GREASE ECH from
clients with no keys costs nothing measurable.

Client certificates (mutual TLS; `--client-ca PEM
[--client-cert-required]`, or `TlsOptions::client_auth` with
`tls::ClientAuth`): the server sends a CertificateRequest and checks the
chain the client sends against PEM's CAs, and that the client signed the
handshake with the leaf's key. verilith-tls proves the check: each
certificate parses, is valid now and fit for client authentication, each
is issued (names and signature) by the next, the last by a configured CA,
within 8 certificates (verilith-tls README, "client authentication");
signature verification and the clock are aws-lc's and the system's,
trusted. A handler sees the leaf in `Request::client_certificate()` (DER;
`None` for a client that sent none, when certificates are optional). With
client certificates on, connections are never resumed and take no 0-RTT
data, so every request's identity is from its own connection's
handshake. HTTP/3 does not ask for client certificates.

Connection setup (`h1-close`): accepting with `TCP_DEFER_ACCEPT` (the
request arrives with the connection, one wakeup instead of two),
TCP_NODELAY inherited from the listener, and no epoll removal before
`close` took it from 63k to **88k** req/s (84k per CPU-second) in a quick
run, against hyper 73k (42k), h2o 74k (54k) and nginx 68k (62k).
`Config::spin` (`--spin N`) polls N times before sleeping, for more
throughput at more CPU; it is off by default and in the benchmarks.

Static files (`StaticBody`): bodies of 16 to 112 KiB are sent with
`sendfile` from a sealed memory file (`memfd` with write, grow and shrink
seals), so the bytes sent are always the ones the Content-Length counted,
even if the file on disk changes; head and body go out in one packet
(MSG_MORE). Larger bodies are faster by `writev` from memory on loopback
(measured: `sendfile` is 10-37% slower from 128 KiB up), so they stay
there. Quick run, requests per server CPU-second: `h1-static-64k` 76k
against nginx's 73k, `h1-static-1m` 4.8k against 2.5k. nginx's low pipelined number is how it works:
it writes each pipelined response with its own system call.

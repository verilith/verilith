# verilith-server

A formally verified HTTP server, built from the Verilith parsers, aiming
for nginx- and h2o-class speed. The plan, with the theorems still to come,
is in [DESIGN.md](DESIGN.md). This README describes what exists today.

**Status: milestones 2 and 3 of the design: HTTP/1.1, and HTTP/2 over
cleartext with prior knowledge (h2c, `--h2c PORT`).** TLS (so h2 by ALPN)
and static files from disk are next. The API will change.

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

`cargo run --release --bin verilith-server -- --http 8080 --root DIR`
runs the server `bench/server` measures.

## How it works

One worker thread per CPU, each pinned, each with its own epoll (Linux)
or kqueue (macOS) loop, listening socket (SO_REUSEPORT on Linux) and
connections; nothing is shared between workers on the request path. Per
readiness event a worker reads until the socket is empty, has the
HTTP/1.1 engine handle every complete request in what it read, and writes
all the responses with one system call. Handlers run inline on the
worker and get a zero-copy view of the request.

## What is proven

`scripts/verify.sh` (Verus): 48 verified, 0 errors.

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
- No panics, overflow or out-of-bounds access in the above.

Everything about reading a request is verilith-http's, verified there:
the head parser, the framing decision (with its uniqueness theorems: every
recipient in a model of RFC 9112 that includes the published smuggling
deviations reads the same head end and framing), and the chunked decoder.

## What is not proven yet

- **The connection engine** (`h1.rs`): where each next request starts
  (head length plus the framing's body), when to close (RFC 9112 §9.3),
  and that responses go out in request order. It is a few hundred lines of
  glue that only calls the verified parser, decoder and writer, and is
  tested in `tests/h1.rs`: every split of a pipelined stream (each single
  and double cut, and one byte at a time) gives the same output, every
  response parses back with verilith-http, and the smuggling shapes
  (CL+TE, differing Content-Lengths, bare LF in chunks, obsolete folding)
  get one 400 and a closed connection. Verifying it is the next proof
  milestone in DESIGN.md.
- **The HTTP/2 engine** (`h2.rs`): stream states, flow control, SETTINGS,
  PING/GOAWAY and the control-frame flood limit. It only reads frames
  through verilith-h2's verified parser and header blocks through
  verilith-hpack's verified decoder, and it writes frames with verilith-h2's
  serializer, and encodes response heads with verilith-hpack's verified
  encoder (dynamic table included), whose theorem is that each block
  decodes to exactly the fields given. That needs blocks to reach the peer
  in the order they were encoded, so a head is encoded only when its
  HEADERS frame is written. Tested in `tests/h2.rs`: every split of a
  request stream gives the same responses, read back with the verified
  parser and decoder; DATA stops at the peer's window; protocol errors and
  a PING flood end in GOAWAY.
- **The event loop and the OS shim** (`worker.rs`, `sys/`): trusted, as
  in every server. See [TRUST.md](TRUST.md).
- `Connection` and `Expect` handling, the `Date` formatter, and the
  reason-phrase table are plain Rust.

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
| `h1-close` (new connection per request) | 76k (**76k**) | **78k** (44k) | n/a* | 62k (59k) | 75k (50k) |
| `h2c-plaintext` (h2load, 64 conns × 32 streams) | **1.54M** (**1.15M**) | 248k (134k) | no h2 | 321k (163k) | 502k (254k) |

\* may-minihttp ignores `Connection: close`, so its 311k there is a
keep-alive figure. Where it is close in raw req/s, verilith-server does the same work on less CPU.

Where the numbers come from: bodies of 8 KiB and more are written from a
shared buffer by `writev`, not copied. HTTP/2 heads go through the
verified HPACK encoder with its dynamic table (header bytes on the wire
90% smaller than uncompressed, as with h2o), and streams are pooled; in
`h2c-plaintext`, h2load is the bottleneck.

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

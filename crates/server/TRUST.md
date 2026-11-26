# What verilith-server trusts

Beyond what every Verilith crate trusts (Verus, Z3, rustc, the specs: here
verilith-http's `spec.rs`, whose response grammar and framing rules the
serializer is proven against):

| File | What it is | What the rest assumes of it |
|---|---|---|
| `src/sys/mod.rs`, `linux.rs`, `macos.rs` | One-call wrappers over `socket`, `bind`, `listen`, `accept4`/`accept`, `read`, `writev`, `close`, `epoll_*`/`kqueue`, `sched_setaffinity`, `time` | `read_into` returning `Done(n)` wrote exactly `buf[..n]`, `n <= buf.len()`; `write_slices` returning `Done(n)` wrote the first `n` bytes in order; events name the token a socket was registered with |
| `src/worker.rs` | The event loop | Hands each connection's bytes to its engine once and in order, and writes the engine's output in order; one connection per slot |
| `src/h1.rs` | The HTTP/1.1 connection engine | Not yet verified (DESIGN.md milestone 2): sequences the verified parser, chunked decoder and response writer; tested in `tests/h1.rs` |
| `src/date.rs` | `Date` formatting | Writes 29 bytes of IMF-fixdate; the value is checked by the verified `check_value` before it is sent, so a bug here cannot split a response |
| `src/lib.rs` | The handler API | Passes handler fields to `write_head_checked` and nothing else to the wire |
| `src/bin/verilith-server.rs` | The benchmark server's routes | Application code |

`scripts/trust-ledger.py` counts these files in the root
[TRUST-LEDGER.md](../../TRUST-LEDGER.md).

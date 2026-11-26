# What verilith-server trusts

Beyond what every Verilith crate trusts (Verus, Z3, rustc, the specs: here
verilith-http's `spec.rs`, whose response grammar and framing rules the
serializer is proven against):

| File | What it is | What the rest assumes of it |
|---|---|---|
| `src/sys/mod.rs`, `linux.rs`, `macos.rs` | One-call wrappers over `socket`, `bind`, `listen`, `accept4`/`accept`, `read`, `writev`, `close`, `epoll_*`/`kqueue`, `sched_setaffinity`, `time` | `read_into` returning `Done(n)` wrote exactly `buf[..n]`, `n <= buf.len()`; `write_slices` returning `Done(n)` wrote the first `n` bytes in order; `sendfile_nb` returning `Done(n)` sent the next `n` bytes of the file range; a sealed memfd's contents cannot change; events name the token a socket was registered with; closing a socket's only descriptor also removes it from the poller |
| `src/worker.rs` | The event loop | Hands each connection's bytes to its engine once and in order, and writes the engine's output in order; one connection per slot |
| `src/h1.rs` | Runs handlers between the verified request core (`conn.rs`) and the verified response writer | Writes only into `rbuf[end..]` (the slice `read_buf` returns) between core calls; persistence (§9.3) and response order are plain Rust, tested in `tests/h1.rs` |
| `src/conn.rs` trusted wrappers | `shift_down` (`copy_within`), `grow_zeros` (`resize`), `truncate_to`, `decode_in` (`chunked::decode` on `&mut v[from..end]`) | Each is the one std call it names; the rest of `conn.rs` is verified |
| `src/h2.rs` | The HTTP/2 connection engine | Not yet verified (DESIGN.md milestone 3): sequences the verified frame parser and serializer and the HPACK decoder; tested in `tests/h2.rs` |
| `src/tls.rs` (`--features tls`) | moving bytes between the socket, verilith-tls and the engines; PEM decoding of the certificate and key | the handshake, key schedule and record layer are verilith-tls's, verified; `tls.rs` only buffers and moves bytes and is tested in `tests/tls.rs` (every ciphertext split, both ALPN protocols, both backends) |
| verilith-tls-aws-lc (aws-lc) | TLS cryptography: AEAD, key exchange, signatures, random numbers | each function meets the contract on verilith-tls's `Provider` trait; aws-lc is the cryptography OpenSSL-class servers trust, with proofs of its own for several primitives |
| rustls (`--features tls-rustls`, `--tls-backend rustls`) | a second TLS backend, for comparison | off unless chosen; trusted as any TLS library |
| `src/date.rs` | `Date` formatting | Writes 29 bytes of IMF-fixdate; the value is checked by the verified `check_value` before it is sent, so a bug here cannot split a response |
| `src/lib.rs` | The handler API | Passes handler fields to `write_head_checked` and nothing else to the wire |
| `src/bin/verilith-server.rs` | The benchmark server's routes | Application code |

`scripts/trust-ledger.py` counts these files in the root
[TRUST-LEDGER.md](../../TRUST-LEDGER.md).

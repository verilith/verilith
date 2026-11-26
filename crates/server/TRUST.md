# What verilith-server trusts

Beyond what every Verilith crate trusts (Verus, Z3, rustc, the specs: here
verilith-http's `spec.rs`, whose response grammar and framing rules the
serializer is proven against):

| File | What it is | What the rest assumes of it |
|---|---|---|
| `src/sys/mod.rs`, `linux.rs`, `macos.rs` | One-call wrappers over `socket`, `bind`, `listen`, `accept4`/`accept`, `read`, `writev`, `close`, `epoll_*`/`kqueue`, `sched_setaffinity`, `time` | `read_into` returning `Done(n)` wrote exactly `buf[..n]`, `n <= buf.len()`; `write_slices` returning `Done(n)` wrote the first `n` bytes in order; `sendfile_nb` returning `Done(n)` sent the next `n` bytes of the file range; a sealed memfd's contents cannot change; events name the token a socket was registered with; closing a socket's only descriptor also removes it from the poller |
| `src/worker.rs` | The event loop | Hands each connection's bytes to its engine once and in order, and writes the engine's output in order; one connection per slot |
| `src/h1.rs` | Runs handlers between the verified request core (`conn.rs`) and the verified response writer | Writes only into `rbuf[end..]` (the slice `read_buf` returns) between core calls; persistence is decided by the verified core (`persist.rs`); response order is plain Rust, tested in `tests/h1.rs` |
| `src/conn.rs` trusted wrappers | `shift_down` (`copy_within`), `grow_zeros` (`resize`), `truncate_to`, `decode_in` (`chunked::decode` on `&mut v[from..end]`) | Each is the one std call it names; the rest of `conn.rs` is verified |
| `src/h2.rs` | The HTTP/2 connection engine | Not yet verified (DESIGN.md milestone 3): sequences the verified frame parser and serializer and the HPACK decoder; tested in `tests/h2.rs` |
| `src/tls.rs` (`--features tls`) | moving bytes between the socket, verilith-tls and the engines; PEM decoding of the certificate and key | the handshake, key schedule and record layer are verilith-tls's, verified; `tls.rs` only buffers and moves bytes and is tested in `tests/tls.rs` (every ciphertext split, both ALPN protocols, both backends) |
| verilith-tls-aws-lc (aws-lc) | TLS cryptography: AEAD, key exchange, signatures, random numbers | each function meets the contract on verilith-tls's `Provider` trait; aws-lc is the cryptography OpenSSL-class servers trust, with proofs of its own for several primitives |
| rustls (`--features tls-rustls`, `--tls-backend rustls`) | a second TLS backend, for comparison | off unless chosen; trusted as any TLS library |
| `src/h3.rs` (`--features h3`) | The HTTP/3 engine: accepts QUIC streams, sequences the verified HTTP/3 stream reader (verilith-h3) and QPACK decoder and encoder (verilith-qpack), dispatches handlers, writes responses | Feeds each stream's bytes to its `Reader` once and in order; frame syntax, frame order, critical-stream rules and their error codes are the verified crates'; tested in `tests/h3.rs` |
| quinn-proto with rustls (`--features h3`) | QUIC: packet protection, TLS 1.3 for QUIC, loss recovery, congestion control, stream reassembly and flow control | Delivers each stream's bytes in order and once, and sends what it was given in order; the same trust as any QUIC library (DESIGN.md, "HTTP/3": verilith-quic's verified parsers replace parts of it later) |
| `sys::bind_udp`, `recv_from`, `recv_gro`, `send_to` | `socket`/`bind`, `recvfrom`, `recvmsg` with UDP_GRO, `sendmsg` with UDP_SEGMENT (Linux GSO) | `recv_from` and `recv_gro` returning `n` wrote `buf[..n]` (for `recv_gro`, datagrams of the `seg` bytes the kernel reported, back to back); `send_to` sends `buf` as datagrams of `segment` bytes, or drops them (QUIC recovers) |
| `sys::open_beneath` | `openat2(RESOLVE_BENEATH \| RESOLVE_NO_MAGICLINKS)` on Linux; `openat(O_NOFOLLOW)` per component elsewhere | The kernel resolves no `..` or symlink outside the root (Linux), or follows no symlink at all (the fallback); the path given is `path.rs`'s, proven to have no `.`, `..`, empty or NUL component |
| `src/files.rs` | The static file server around the verified path and range functions | Opens only paths `resolve_exec` returned, joined by `join_to`; serves only ranges `parse_range` returned; the cache, validators and media types are plain Rust, tested in `tests/files.rs` |
| `src/date.rs` | `Date` formatting | Writes 29 bytes of IMF-fixdate; the value is checked by the verified `check_value` before it is sent, so a bug here cannot split a response |
| `src/lib.rs` | The handler API | Passes handler fields to `write_head_checked` and nothing else to the wire |
| `src/bin/verilith-server.rs` | The benchmark server's routes | Application code |

`scripts/trust-ledger.py` counts these files in the root
[TRUST-LEDGER.md](../../TRUST-LEDGER.md).

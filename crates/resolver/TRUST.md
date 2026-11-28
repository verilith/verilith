# What verilith-resolver trusts

Beyond what every Verilith crate trusts (Verus, Z3, rustc, and the
specifications: here this crate's `src/spec.rs` and `src/dspec.rs`, verilith-sha2's SHA-256 specification, and verilith-dns's
`spec.rs` and `spec_rdata.rs`, whose message format the resolver's
theorems are stated over):

| File | What it is | What the rest assumes of it |
|---|---|---|
| `src/resolve.rs`: `Net` (`exchange`, `now`, `random`, `wall`) | The verified resolver's only way to the network and the clocks: four `external_body` methods over the `Transport` trait | Nothing about what `exchange` returns: the verified code treats a response as arbitrary bytes and parses, checks (`accept.rs`) and classifies (`classify.rs`) it itself. `now` is assumed only to be a number of seconds (a wrong clock makes entries live too long or too short, never makes the cache hand out data for another question). `random` is assumed unpredictable to an off-path attacker; nothing is proven about it. `wall` is the Unix time in seconds (mod 2^32, RFC 4034 §3.1.5), compared with RRSIG validity windows |
| `src/crypto.rs`: `verify_sig` | The signature arithmetic: aws-lc-rs's RSA/SHA-256, RSA/SHA-512, ECDSA P-256/SHA-256, P-384/SHA-384 and Ed25519 verification, with the DNSSEC encodings of keys and signatures (RFC 3110, 5702, 6605, 8080) turned into aws-lc's | That it returns true only for a signature made with the private key of `key` over exactly `data`. The proofs treat it as an uninterpreted function (`dspec::sig_valid`): what is proven is that the bytes handed to it are exactly what RFC 4034 §3.1.8.1 says is signed, and the key is one the chain of trust says to use. Algorithms 5 and 7 (SHA-1) are refused |
| `src/trust.rs`: `anchors_x`, `set_anchors` | The trust anchors (DS records for the root, by default IANA's KSK-2017 and KSK-2024), kept in a `OnceLock` | That `anchors_x` returns the same anchors for the life of the process (`set_anchors` takes effect only before the first read, and the resolver checks it did), since the proofs state everything about validation relative to one `dspec::anchors()`. An empty set turns validation off |
| `src/net.rs` | `Transport` for real servers: a UDP socket bound to an OS-chosen port and `connect`ed to the server for each query, a read deadline, TCP on TC, the clock (`Instant`), and query IDs and 0x20 bits (SipHash-1-3 of a counter, keyed by std's `RandomState` from the OS's randomness) | Datagrams from any address or port other than the server's are dropped by the kernel (`connect`), so the response checked is one the queried server sent or an off-path attacker forged with the right ID, port and 0x20 case; the OS picks the source port at random (Linux and macOS do); a response with another ID is skipped while waiting, and the rest of the checking is the verified `response_ok` |
| `src/service.rs` | The listeners: UDP (cache-only answers on one thread per CPU, the rest handed to a pool), TCP and DoT (a thread per connection, two-byte length framing, an idle timeout and a connection cap), DoH (a handler for verilith-server: `/dns-query`, GET with base64url `dns=` decoded by verilith-text's verified forgiving base64, or POST with `application/dns-message`) | Every message from a client goes to the verified `frontend::serve` whole and every byte sent back is its reply, unchanged, framed for the transport; a reply for a UDP client is sent to the address it came from. `answer_cached` reads only the RCODE of a verified reply to decide whether to hand the question to the pool. The DoT handshake and records are verilith-tls's, verified; the HTTP/1.1 and HTTP/2 framing is verilith-server's (its TRUST.md) |
| `src/bin/verilith-resolver.rs` | Command line | Application code |
| verilith-tls-aws-lc (aws-lc), with `--features tls` | TLS cryptography for DoT and DoH | As in [verilith-server's TRUST.md](../server/TRUST.md) |

`scripts/trust-ledger.py` counts these in the root
[TRUST-LEDGER.md](../../TRUST-LEDGER.md).

The cache shared by the threads (`resolve.rs`'s `Shared`) is verified:
shards of the verified `Cache`, each behind vstd's verified `RwLock`,
whose invariant is the cache's own type invariant.

What is not claimed at all: anything about timing, that the wall clock
used for RRSIG validity windows is right (a wrong clock can make a valid
signature look expired or an expired one valid), and anything about
DNSSEC data the resolver does not check (RRSIGs are not passed on to
clients).

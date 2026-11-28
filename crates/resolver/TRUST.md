# What verilith-resolver trusts

Beyond what every Verilith crate trusts (Verus, Z3, rustc, and the
specifications: here this crate's `src/spec.rs`, and verilith-dns's
`spec.rs` and `spec_rdata.rs`, whose message format the resolver's
theorems are stated over):

| File | What it is | What the rest assumes of it |
|---|---|---|
| `src/resolve.rs`: `Net` (`exchange`, `now`, `random`) | The verified resolver's only way to the network and the clock: three `external_body` methods over the `Transport` trait | Nothing about what `exchange` returns: the verified code treats a response as arbitrary bytes and parses, checks (`accept.rs`) and classifies (`classify.rs`) it itself. `now` is assumed only to be a number of seconds (a wrong clock makes entries live too long or too short, never makes the cache hand out data for another question). `random` is assumed unpredictable to an off-path attacker; nothing is proven about it |
| `src/resolve.rs`: `Shared` (`lookup`, `insert`) | The cache shared by all threads: shards of the verified `Cache`, each behind a `Mutex` | The contracts are the verified `Cache::lookup` and `Cache::insert`'s, and the bodies only pick a shard (`lib.rs`'s `shared_shard`, any function of the lowercased name) and lock it. A shard's lock is held for one call, so the type invariant of each `Cache` (every entry holds a chain for its own question) is what every thread sees |
| `src/net.rs` | `Transport` for real servers: a UDP socket bound to an OS-chosen port and `connect`ed to the server for each query, a read deadline, TCP on TC, the clock (`Instant`), and query IDs and 0x20 bits (SipHash-1-3 of a counter, keyed by std's `RandomState` from the OS's randomness) | Datagrams from any address or port other than the server's are dropped by the kernel (`connect`), so the response checked is one the queried server sent or an off-path attacker forged with the right ID, port and 0x20 case; the OS picks the source port at random (Linux and macOS do); a response with another ID is skipped while waiting, and the rest of the checking is the verified `response_ok` |
| `src/service.rs` | The listeners: UDP (cache-only answers on one thread per CPU, the rest handed to a pool), TCP and DoT (a thread per connection, two-byte length framing, an idle timeout and a connection cap), DoH (a handler for verilith-server: `/dns-query`, GET with base64url `dns=` decoded by verilith-text's verified forgiving base64, or POST with `application/dns-message`) | Every message from a client goes to the verified `frontend::serve` whole and every byte sent back is its reply, unchanged, framed for the transport; a reply for a UDP client is sent to the address it came from. `answer_cached` reads only the RCODE of a verified reply to decide whether to hand the question to the pool. The DoT handshake and records are verilith-tls's, verified; the HTTP/1.1 and HTTP/2 framing is verilith-server's (its TRUST.md) |
| `src/bin/verilith-resolver.rs` | Command line | Application code |
| verilith-tls-aws-lc (aws-lc), with `--features tls` | TLS cryptography for DoT and DoH | As in [verilith-server's TRUST.md](../server/TRUST.md) |

`scripts/trust-ledger.py` counts these in the root
[TRUST-LEDGER.md](../../TRUST-LEDGER.md).

What is not claimed at all: anything about DNSSEC (the resolver does not
validate), and anything about timing.

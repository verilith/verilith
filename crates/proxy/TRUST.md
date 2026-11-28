# What verilith-proxy trusts

Beyond what every Verilith crate trusts (Verus, Z3, rustc, the specs:
here verilith-http's `spec.rs`, whose request and response grammar and
framing rules the proxy's proofs are stated against), and what
verilith-server trusts ([its TRUST.md](../server/TRUST.md)):

| File | What it is | What the rest assumes of it |
|---|---|---|
| `src/proxy.rs` | The handler: routes a request, builds the proxy's own fields for the verified `fields::request_fields`, writes the request with the verified `upreq::write_request`, defers the response, and drives one upstream connection per request (connect, write, read, timeouts, retry) on the worker's poller | Hands the upstream's bytes to `upresp::read_head` from the connection's first unread byte, skips exactly an interim response's length, reads the body as the verified framing says (Content-Length: that many bytes; chunked: verilith-http's verified decoder; close: until EOF), and returns a connection to the pool only when `upresp::reuse_ok` says so, counting every byte received; fields go to the upstream and to the client only through `hop::forward`; the route is `route::choose`'s and the coding `coding::choose`'s; a response is stored only when `rules::decide` says so and served from the cache only while `rules::fresh_exec` holds and `rules::bypass_exec` does not; tested in `tests/proxy.rs` and `tests/h3.rs` |
| `src/proxy.rs` field values | The values of the fields the proxy sets (X-Forwarded-For, X-Forwarded-Proto, Via, one joined Cookie, Accept-Encoding when compression is off); recognizes Pragma no-cache, Vary and compressible media types | Application policy: which fields are dropped is `fields.rs`'s, proved, and none of it can change how a message is framed, since `write_request` and verilith-server's engines check every field they write |
| `src/cache.rs` | The shared cache's storage: sharded maps, byte budget, oldest-first eviction | Returns an entry only for the key it was stored under |
| `src/bin/verilith-proxy.rs` | Command-line parsing and start | Application code |
| verilith-server `src/defer.rs`, the reactor in `worker.rs` | Deferred responses and handler-registered sockets | Listed in [verilith-server's TRUST.md](../server/TRUST.md) |

`scripts/trust-ledger.py` counts these files in the root
[TRUST-LEDGER.md](../../TRUST-LEDGER.md).

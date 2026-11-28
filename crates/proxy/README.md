# verilith-proxy

A reverse proxy on [verilith-server](../server): HTTP/1.1, h2c, HTTPS
(h2 and http/1.1 by ALPN, TLS 1.3 on verilith-tls) and HTTP/3 in front,
pooled HTTP/1.1 connections to the upstreams behind, with a shared cache
and Brotli, Zstandard and gzip compression by Verilith's verified
compressors. Every decision about bytes that cross the proxy is made by
verified code; the plain-Rust glue moves bytes between sockets and
buffers, keeps timers and picks upstream servers ([TRUST.md](TRUST.md)).

**Status: new.** One request at a time per upstream connection, IPv4
upstreams resolved at start, no request or response streaming (bodies
are buffered, up to `max_response`), no revalidation of stale cache
entries, no WebSocket. The API will change.

```sh
cargo build --release -p verilith-proxy --features h3

# Everything to two backends in turn, /api on example.com to a third;
# HTTP/1.1 on 8080, h2c on 8081, HTTPS and HTTP/3 on 8443.
target/release/verilith-proxy --http 8080 --h2c 8081 --listen 0.0.0.0 \
    --tls 8443 --h3 8443 --cert cert.pem --key key.pem \
    --upstream web=127.0.0.1:9001,127.0.0.1:9002 --upstream api=10.0.0.5:8000 \
    --route /=web --route example.com/api=api
```

`--help` lists the options. As a library, `proxy::Proxy` is a
`verilith_server::Handler`: `serve(cfg, Arc::new(Proxy::new(pc)))`.

## What is proven

Each theorem is checked by Verus (`scripts/verify.sh`; 86 functions and
lemmas).

**The upstream reads exactly the request the proxy means** (`upreq.rs`).
`write_request` appends a request head only if the method is a token, the
target has no byte that ends it early, the Host value and every forwarded
field are valid and none is Host, Content-Length or Transfer-Encoding, and
the body length is in range; otherwise it writes nothing.
`theorem_request_parses`: verilith-http's verified request parser
(`spec::parse_request`, RFC 9112) reads that head, followed by anything,
as one complete request with this method and target, HTTP/1.1, exactly
these fields in this order (Host first, Content-Length last if given), and
a body of exactly the length given (or none). A client cannot make the
proxy send the upstream a second, smuggled request: the head is closed
where the proof says, and the framing is the proxy's own.

**Hop-by-hop fields stop at the proxy** (`hop.rs`). `forward` keeps,
in order, exactly the fields `forwarded` names: none named Connection,
Keep-Alive, Proxy-Connection, TE, Transfer-Encoding, Upgrade, Trailer,
Proxy-Authorization, Proxy-Authenticate, Host or Content-Length (ASCII
case-insensitive), and none named in a Connection field's list (RFC 9110
§7.6.1), with the list read as verilith-server's `persist.rs` reads it.
`theorem_forwarded`: the result is an ordered subsequence of the input
and no field of it is hop-by-hop. Used both ways: client to upstream, and
upstream to client.

**The upstream's response is read as the RFC says** (`upresp.rs`).
`read_head` computes `up` exactly: verilith-http's verified
`parse_response` and `response_body` (RFC 9112 §4, §6.3: the body's
framing, with Transfer-Encoding over Content-Length, conflicting lengths
refused), interim responses (1xx) skipped and 101 refused, and the
connection's persistence read as verilith-server's `persist.rs` reads a
request's.

**A pooled connection is never desynchronized** (`upresp.rs`).
`reuse_ok` is exactly `reusable`: the response persists, its length is
known from its framing (not read until close), and it ended exactly where
the bytes received end. A connection with any byte left over, such as a
second response the upstream sent unasked, is closed, so one client never
gets a response meant for another ("response queue poisoning"). Bytes
arriving on an idle connection close it too (tested).

**Routing sees the path the upstream will resolve** (`route.rs`). The
path is first resolved by verilith-server's verified
`path::resolve_exec` (segments percent-decoded, `.` and `..` applied,
`%2f`, `%5c`, `%00` and escapes above the root refused), so `/api/../admin`,
`/%61dmin` and `/admin` are one path to the router. `choose` computes
`best` exactly: among matching routes, one naming the host
(case-insensitively) over one that does not, then the longest prefix in
whole path components (`/api` does not match `/apix`), then the first
listed.

**Accept-Encoding** (`coding.rs`). `choose` returns a coding the client
accepts with a nonzero weight (RFC 9110 §12.5.3: its own element's
q-value, else `*`'s, else 0; q-values parsed exactly, to thousandths) that
no allowed coding beats, preferring Brotli, then Zstandard, then gzip
among equals, or none. The compressors are each proven to decode back to
their input (verilith-brotli, -zstd, -zlib).

**What is cached, and for how long** (`rules.rs`, RFC 9111). `decide`
computes `storable` and `lifetime` exactly: a GET; a status cacheable by
default (§3, RFC 9110 §15.1); no `no-store` in the request or response
and no `private` or `no-cache` in the response (Cache-Control parsed as a
list with quoted strings, directive names case-insensitive, delta-seconds
capped at 2^31, §1.2.2); for a request with Authorization, `public`,
`must-revalidate` or `s-maxage` (§3.5); no Set-Cookie; no Vary but
Accept-Encoding; and a positive `s-maxage`, else `max-age`. `fresh_exec`
is §4.2's `current_age < freshness_lifetime`, and `bypass_exec` says a
request's `no-cache`, `no-store`, `max-age=0` or `Pragma: no-cache` is
not answered from the cache.

**What the client is sent** is verilith-server's: its verified engines
write every response (status line, fields, Content-Length, framing), so a
bad field from an upstream cannot split a response (`SendError::Invalid`
becomes 502).

## What is not proven

The glue in `proxy.rs`, `cache.rs` and the binary is plain Rust:
assembling the forwarded fields (dropping X-Forwarded-*, Forwarded, Via,
Expect, Cookie and Accept-Encoding to set them itself), the upstream
connection state machine (connect, write, read, timeouts, retries),
buffering the body with verilith-http's verified chunked decoder, the
cache's storage and eviction, which media types are compressed, and
upstream selection. verilith-server's deferral (`defer.rs`) and reactor
hook (`Handler::on_io`, `register`) are plain Rust too. [TRUST.md](TRUST.md)
lists each piece and what the rest assumes of it; `tests/proxy.rs` and
`tests/h3.rs` test them end to end.

## Behavior

- **Requests**: Host (or `:authority`) and the resolved path pick the
  route; the target goes upstream as sent. HEAD is forwarded as GET, so
  the client gets the length the body would have and the response can be
  cached. The body is sent with Content-Length. `X-Forwarded-For` (the
  client's address), `X-Forwarded-Proto` and `Via` are set by the proxy;
  a client's own are dropped. Cookies from h2 and h3 are joined into one
  field (RFC 9113 §8.2.3).
- **Upstreams**: servers of an upstream are used in turn; one that
  refuses a connection, or does not accept one within `connect_timeout`,
  is skipped for `fail_timeout` and the request tried on another. An
  idempotent request whose reused connection closes before any byte of
  the response is sent once more. `response_timeout` gives 504, a bad or
  oversized response 502.
- **Cache**: shared by all workers, keyed by host and target, byte
  budgeted (`--cache-mb`), oldest out first. Answers carry `Age`. A body
  the upstream compressed itself is not stored.
- **Compression**: status 200, at least 256 bytes, a text-like media type,
  no Content-Encoding, Content-Range or `no-transform`. With compression
  on, the upstream is asked for identity bodies. A cached body is
  compressed once per coding (Brotli at quality 6); one compressed for a
  single client gets Zstandard or gzip if the client takes either, since
  verilith-brotli spends about half a millisecond setting up its match
  finder whatever the input's length. `Vary: Accept-Encoding` is added,
  and a strong ETag weakened.

## Performance

`bench/proxy/run.sh`: one upstream (verilith-server, one CPU), each proxy
with one worker on one CPU, wrk or h2load with 64 connections on two
more; nginx 1.24 with `proxy_pass`, an upstream keepalive pool and gzip
level 6. Requests per second on a 4-vCPU Xeon @ 2.30 GHz VM:

| | verilith-proxy | nginx |
|---|---:|---:|
| HTTP/1.1, 13-byte body | 78,000 | 62,200 |
| HTTP/1.1, 16 KiB HTML | 57,100 | 47,600 |
| HTTP/1.1, 16 KiB HTML, gzip | 12,600 | 13,900 |
| HTTP/1.1, 16 KiB HTML, Zstandard | 16,800 | (no module) |
| HTTP/1.1, 16 KiB HTML, Brotli only, uncached | 390 | (no module) |
| h2c, 10 streams per connection | 50,100 | 32,500 |

verilith-zlib's gzip is about 10% behind zlib's here. Brotli per request
is slow for the reason above; cached responses are compressed once.

## License

MIT OR Apache-2.0.

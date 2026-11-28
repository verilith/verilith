# verilith-resolver

A recursive, caching DNS resolver, formally verified with
[Verus](https://github.com/verus-lang/verus), that answers over UDP, TCP,
DNS over TLS (RFC 7858) and DNS over HTTPS (RFC 8484). It is built from the
Verilith crates: [verilith-dns](../dns) reads and writes every message,
[verilith-tls](../tls) (with [verilith-x509](../x509) for the
certificate chain) runs DoT, and [verilith-server](../server) serves DoH
over HTTP/1.1 and HTTP/2.

**Status: a working resolver.** It iterates from the root servers,
follows referrals and CNAMEs, caches answers, negative answers and
delegations, and passes its tests against a local hierarchy of servers
that lie in the ways resolvers have been attacked. It does not validate
DNSSEC yet, and it has not run in production. The API will change.

## Quickstart

```sh
# UDP and TCP on 127.0.0.1:53 (root, or set --port).
cargo run --release -p verilith-resolver -- --listen 127.0.0.1 --port 53
dig @127.0.0.1 example.com

# With DNS over TLS (853) and DNS over HTTPS (443) as well:
cargo run --release -p verilith-resolver --features tls -- --listen 127.0.0.1 \
  --dot 853 --doh 443 --http 8053 --cert cert.pem --key key.pem
kdig @127.0.0.1 +tls example.com
dig @127.0.0.1 +https example.com      # https://127.0.0.1/dns-query
```

Other flags: `--threads N` (the pool that waits on servers; default 8 per
CPU, at least 32), `--root IP` (repeatable; default: the 13 IPv4 root
server addresses), `--upstream-port P` and `--timeout-ms MS`.

From Rust, `service::Resolver::new(&Options)` and `Resolver::answer(query,
udp)` (a message in, the reply out); `service::udp`, `service::tcp`,
`service::tls::dot` and `service::tls::doh` run the listeners.

## How it fits together

| Step | Where | Verified |
|---|---|---|
| A client's message: parse, check, decide the reply's size limit | `frontend.rs`, verilith-dns's parser | yes |
| The cache: answers, negative answers, delegations | `cache.rs` | yes |
| Walking down the zones from the closest known one; following CNAMEs; the query budget | `resolve.rs` (`resolve`, `iterate`, `ns_addrs`) | yes |
| Writing a query to a server | `reply.rs` (`build_query`), verilith-dns's serializer | yes |
| Taking a response: ID, question, 0x20 case | `accept.rs` | yes |
| What a response means, and which of its records to believe | `classify.rs` | yes |
| Writing the client's reply, truncating it for UDP | `reply.rs` (`build_reply`), verilith-dns's compressing serializer | yes |
| Sockets to servers, the clock, random bits | `net.rs` | no ([TRUST.md](TRUST.md)) |
| Listeners: UDP, TCP, DoT, DoH | `service.rs`, verilith-tls, verilith-server | the TLS and HTTP engines are; the glue is not |

## What is proven

`scripts/verify.sh` (Verus): 121 verified, 0 errors. The specification is
`src/spec.rs`; every theorem below holds for every input, whatever any
server or client sends.

- **Only responses to the query sent are taken** (`accept.rs`,
  `response_matches` computes `spec::response_ok`): QR set, Opcode 0, the
  query's ID, exactly one question, and that question is the one sent byte
  for byte, so with the query's random letter case (0x20), type and class
  IN (RFC 5452 §9.1).
- **Only records in the bailiwick are believed** (`classify.rs`,
  `classify` ensures `outcome_ok`). Every record taken from a response
  from a server for zone Z is owned by a name at or below Z: answers,
  CNAME links, the SOA of a negative answer, and the addresses of name
  servers (glue). A server for `example.com` cannot plant an address for
  `host.other.com` or for the `.com` servers, in any section. This is the
  rule that defeats the classic out-of-zone cache poisoning (Kaminsky,
  2008).
- **Referrals only go down** (`outcome_ok`, the `Referral` case): a
  referral is followed only to a zone strictly below the current one and
  at or above the name asked, and only from NS records of that zone in the
  authority section. Upward, sideways and self referrals are refused, so
  referral loops cannot happen.
- **Every answer is a chain for the question** (`resolve` ensures
  `answer_ok`; `frontend::serve` ensures `served_ok`): the answer section
  is CNAME links starting at the name asked, each owned by the previous
  link's target (RFC 1034 §3.6.2), at most `MAX_CNAME` (8) of them, then
  records of the type asked at the chain's end; NXDOMAIN and NODATA
  replies carry the links only. CNAME loops and over-long chains end in
  SERVFAIL. Every TTL is at most a day (`MAX_TTL`).
- **The cache never answers a different question, or after its TTL**
  (`cache.rs`: the type invariant of `Cache`, and `lookup` ensures
  `hit_ok`). Every entry holds a chain for its own question (name compared
  ignoring ASCII case, RFC 4343), a negative answer's RCODE is NOERROR or
  NXDOMAIN, and a delegation holds 4- or 16-byte addresses; a hit is
  returned only before the entry expires, with every TTL lowered to the
  seconds left. Its memory is fixed: `capacity()` entries, set when it is
  made.
- **Bounded work for every question** (`resolve`, `iterate`, `ns_addrs`):
  resolution terminates, and sends at most `QUERY_BUDGET` (32) queries to
  servers in all, the lookups of name server addresses it starts
  included; those nest at most `NS_DEPTH` (3) deep and are started for at
  most `MAX_NS_LOOKUPS` (2) names per referral. A referral naming 50
  servers without glue costs a handful of queries, not hundreds
  (NXNSAttack, CVE-2020-12662).
- **Replies parse back to exactly what was decided** (`reply.rs`,
  `build_reply` ensures `reply_ok`, with verilith-dns's theorem that
  `to_bytes_compressed` parses back to the message): the client's ID, its
  question unchanged (its letter case included), RD copied, QR and RA set,
  and the answer and authority sections exactly the records decided, or a
  truncated reply (TC, no records) when it would not fit the UDP limit
  (512 bytes without EDNS, else what the client offered, at most 1232).
- **No panics, no out-of-bounds access, no overflow** in all of the above.

Where these theorems sit in the code: `classify.rs` is where a response
becomes beliefs; `cache.rs` and `resolve.rs` only ever hold what
`classify` returned (with TTLs lowered) and what the cache's invariant
allows; `frontend.rs` is the whole path from a client's bytes to the reply's
bytes.

## What is trusted

The specification (`src/spec.rs`, and verilith-dns's), Verus and the
toolchain, and the network glue, listed with what is assumed of each in
[TRUST.md](TRUST.md): the transport (`net.rs`), whose responses the
verified code treats as arbitrary bytes, and the listeners
(`service.rs`), which pass messages whole to the verified `frontend::serve`
and send back exactly its reply. Two small wrappers have `external_body`
contracts: `Net`, which promises nothing, and `Shared`, the locked shards
of the verified cache, whose contract is the cache's own.

## What it does not do (yet)

- **DNSSEC validation.** Nothing is validated; the AD bit is never set.
  This is the largest gap, and the next piece: verilith-dns already parses
  RRSIG, DNSKEY, DS and NSEC/NSEC3.
- **QNAME minimisation** (RFC 9156): servers see the full name.
- **IPv6 root hints**: the default roots are IPv4 (`--root` takes IPv6).
- **Serve-stale, prefetch, EDNS Client Subnet, DNS cookies, local zones.**
- **ANY** (QTYPE 255) is answered with whatever the authoritative server
  gives for it, not RFC 8482's minimal answer.
- A DoH request whose answer is not cached holds its verilith-server
  worker until it is resolved (the handler API is synchronous), which is
  why the DoH listener runs as many workers as the resolver pool.

## Speed against Unbound

`bench/run.sh` runs both resolvers on the same two CPUs, iterating from
the test hierarchy (tests/hier: a root, `.com`, `.net` and zones under
them on 127.0.0.2-9), with Unbound 1.19.2 configured to match
(`bench/unbound.conf`: no validator, no QNAME minimisation). Load from
dnsperf 2.14 (UDP, DoT) and h2load (DoH, HTTP/2, 10 streams per
connection) on two other CPUs.

Medians of 5 alternating rounds on a cloud x86-64 container (4 vCPUs,
2026-11-28; every round in
[bench/results-cloud-x86-2026-11-28.md](bench/results-cloud-x86-2026-11-28.md)):

| | verilith-resolver | Unbound | ratio |
|---|---|---|---|
| UDP, cached answers (q/s) | 430,716 | 343,397 | 1.25x |
| CPU per cached answer (µs) | 4.46 | 4.87 | 1.09x less |
| UDP, uncached answers, 200 in flight (q/s) | 64,339 | 42,259 | 1.52x |
| One uncached lookup at a time (µs latency) | 111 | 86 | 0.77x (slower) |
| DNS over TLS, cached (q/s) | 181,319 | 110,114 | 1.65x |
| DNS over HTTPS, cached (req/s) | 622,691 | 174,992 | 3.56x |

The one row where Unbound is ahead is the latency of a single cold
lookup, by about 25 µs: the receiving thread answers only from the cache
and hands a miss to the pool, which costs a thread wake-up, and each query
to a server opens a fresh socket. Over loopback that is a quarter of the
total; against real servers 10 to 100 ms away it is noise. The container
is noisy (rounds vary by up to 30%), so the ratios matter more than the
absolute numbers. dnsperf's DoH mode stalls against verilith-server when
two HTTP/2 responses arrive in one TLS record (curl, nghttp and h2load do
not), so DoH is measured with h2load.

## Tests

`tests/resolve.rs` runs the resolver against `tests/hier`, a hierarchy of
authoritative servers on 127.0.0.2-9 that includes a server injecting
out-of-bailiwick answers and glue into every response, one that refers
every query up and sideways, one that refers its zone to itself, CNAME
loops and chains of 13 links, and a 50-server delegation with no glue.
`tests/encrypted.rs` runs DoT (pipelined) and DoH (GET and POST) against
rustls clients. `./ci.sh` runs both.

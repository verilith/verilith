# bench/server

verilith-server against hyper, nginx and h2o (and, for HTTP/3, h3 on quinn,
nginx with QUIC and h2o's quicly): the same routes, the same
CPUs, the same worker thread count, the same load generators, in one sitting.
The design and the reasons for each case are in
[crates/server/DESIGN.md](../../crates/server/DESIGN.md#benchmarks).

```sh
# Linux (Debian/Ubuntu): the servers and load generators
sudo apt-get install nginx-light h2o wrk nghttp2-client
(cd baselines/hyper && cargo build --release)    # the hyper baseline
cargo build --release -p verilith-server --features tls   # from the repo root

./run.py --list                                   # what was found
./run.py --quick                                  # smoke test: 1 round, 3 s per case
./run.py                                          # 3 rounds, 10 s per case
./run.py --servers nginx,verilith --cases h1-plaintext,h2c-plaintext --rounds 5
```

HTTP/3 needs tools no distribution ships yet. `h3/build.sh` builds them from
pinned sources into `target/h3-tools` (about 10 minutes on 4 CPUs; the
packages it needs are listed at its top):

```sh
h3/build.sh                                       # h2load (HTTP/3), nginx-quic, h2o-quic
(cd baselines/h3-quinn && cargo build --release)  # the h3 + quinn baseline
./run.py --cases h3-plaintext,h3-static-64k,h3-static-1m
```

The report is `results/<date>-<host>/report.md`, with `raw.json` (every
load generator's full output) beside it.

## What every server serves

| Route | Response |
|---|---|
| `GET /plaintext` | 200, `Hello, World!` (13 bytes), `text/plain`, with `Server` and `Date` |
| `GET /static/1k.bin`, `64k.bin`, `1m.bin` | 200, the file, from a directory `run.py` writes |

Each server listens on three ports: HTTP/1.1 on 18080, HTTP/2 by prior
knowledge (h2c) on 18081, and TLS 1.3 with ALPN `h2` and `http/1.1` on 18443,
with an ECDSA P-256 certificate `run.py` makes. HTTP/3 servers listen on UDP
18443 with the same certificate; verilith-server does when its
`--protocols` lists `h3`, and is started with `--h3 18443`. nginx and h2o are configured
from `conf/*.conf.in`; hyper is `baselines/hyper`, hyper 1.x with
hyper-util's auto connection builder on a multi-threaded tokio runtime and
tokio-rustls with aws-lc-rs.

The HTTP/3 servers:

| Server | What it is |
|---|---|
| `verilith-vq` | verilith-server with `--h3-backend verilith`: the same HTTP/3 code on verilith-quic-conn instead of quinn-proto (`verilith` rows are quinn-proto). h3 cases only |
| `h3-quinn` | `baselines/h3-quinn`: the h3 crate on quinn 0.11 (quinn-udp with GSO), rustls on aws-lc-rs. One current-thread runtime and one endpoint per worker thread on `SO_REUSEPORT` sockets, since a quinn endpoint is driven by a single task |
| `nginx-quic` | nginx mainline with `--with-http_v3_module` on BoringSSL, `quic_gso on`, `reuseport`, one worker per thread (`conf/nginx-quic.conf.in`) |
| `h2o-quic` | h2o master with quicly and picotls on OpenSSL, `num-threads` workers (`conf/h2o-quic.conf.in`) |

The load generator is nghttp2's h2load built with ngtcp2 and nghttp3 on
aws-lc, run with `--alpn-list=h3`: the same tool, options and output as the
HTTP/2 cases, so h2 and h3 rows compare directly. None of the servers sends
a Retry, and all use 1-RTT handshakes; h2load opens its connections once and
keeps them for the run, so the cases measure request handling, not
handshakes. On a 4-CPU VM h2o-quic leaves CPU idle under these loads (neither it nor
h2load saturates; it is bound by how quicly schedules sends and ACKs on a
sub-millisecond path), so compare it by requests per server CPU-second.

h2o 2.2's plaintext route is an mruby handler, the way h2o answers without
a file; nginx's is `return 200`. Both are those servers' fastest way to send
a fixed body.

## How it measures

- The server runs under `taskset` on `--server-cpus` (default the first half
  of the CPUs) with that many worker threads; wrk and h2load run on
  `--client-cpus` (the second half) with one thread per CPU.
- Each case starts the server fresh, warms up for 2 s, then measures for
  10 s. Servers take turns within a case, and the order reverses each
  round.
- **Requests per server CPU-second** is requests completed over the user
  and system time of the server's whole process group during the measured
  run (from `/proc`). When the load generator is the bottleneck, which on a
  4-CPU machine it often is, raw requests per second understates the
  fastest server and this figure does not.
- wrk reports latency percentiles; h2load reports a mean, shown in the p50
  column for h2 cases.

## Caveats

On one machine, the load generator competes with the server for memory
bandwidth and caches even when pinned apart, and on a cloud VM other tenants
add noise. Numbers to publish come from a quiet machine (`bench/README.md`
describes quieting one) or, better, from two machines. Linux only for now;
macOS support (kqueue-based servers are fine, the harness needs `ps` in
place of `/proc` and no `taskset`) is planned.

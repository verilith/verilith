# bench/server

verilith-server against hyper, nginx and h2o: the same routes, the same
CPUs, the same worker thread count, the same load generators, in one sitting.
The design and the reasons for each case are in
[crates/server/DESIGN.md](../../crates/server/DESIGN.md#benchmarks).

```sh
# Linux (Debian/Ubuntu): the servers and load generators
sudo apt-get install nginx-light h2o wrk nghttp2-client
(cd baselines/hyper && cargo build --release)    # the hyper baseline
cargo build --release -p verilith-server          # once it exists (from the repo root)

./run.py --list                                   # what was found
./run.py --quick                                  # smoke test: 1 round, 3 s per case
./run.py                                          # 3 rounds, 10 s per case
./run.py --servers nginx,verilith --cases h1-plaintext,h2c-plaintext --rounds 5
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
with an ECDSA P-256 certificate `run.py` makes. nginx and h2o are configured
from `conf/*.conf.in`; hyper is `baselines/hyper`, hyper 1.x with
hyper-util's auto connection builder on a multi-threaded tokio runtime and
tokio-rustls with aws-lc-rs.

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

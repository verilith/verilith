# bench/server report

2026-11-26T08:58, Intel(R) Xeon(R) Processor @ 2.10GHz, 4 CPUs (server on 0-1, load generator on 2-3), 1 rounds of 3s per case.

Versions: verilith 843851b, verilith-rustls 843851b, nginx 1.24.0 (Ubuntu), hyper 1.13.0, h2o 2.2.5

Requests per second: median over the rounds, with the range. Server CPU efficiency is requests per server CPU-second (higher is better), the figure least disturbed by a shared machine.

## h1-tls-close

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 5557 | 5557 to 5557 | 8228 | 2.84 ms | 6.02 ms | 0 |
| verilith-rustls | 5221 | 5221 to 5221 | 5283 | 2.85 ms | 6.02 ms | 0 |
| nginx | 5977 | 5977 to 5977 | 3371 | 2.97 ms | 11.61 ms | 0 |
| hyper | 6391 | 6391 to 6391 | 4900 | 2.23 ms | 5.24 ms | 0 |
| h2o | 4032 | 4032 to 4032 | 2485 | 5.61 ms | 15.60 ms | 0 |

## h1-tls-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 216k | 216k to 216k | 155k | 554 µs | 3.16 ms | 0 |
| verilith-rustls | 215k | 215k to 215k | 149k | 540 µs | 2.04 ms | 0 |
| nginx | 192k | 192k to 192k | 102k | 1.13 ms | 6.96 ms | 0 |
| hyper | 187k | 187k to 187k | 102k | 1.11 ms | 2.65 ms | 0 |
| h2o | 151k | 151k to 151k | 79k | 1.50 ms | 6.49 ms | 0 |

h2load reports a mean request time, not percentiles; for h2 cases p50 shows that mean.

Notes: verilith-tls with session tickets (two per connection, keys shared
by all workers); `verilith-rustls` the same server on rustls with tickets.
In `h1-tls-close` wrk's two CPUs are the limit; compare requests per
server CPU-second.

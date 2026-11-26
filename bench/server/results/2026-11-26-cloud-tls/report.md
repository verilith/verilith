# bench/server report

2026-11-26T08:30, Intel(R) Xeon(R) Processor @ 2.10GHz, 4 CPUs (server on 0-1, load generator on 2-3), 1 rounds of 3s per case.

Versions: verilith 2fbe4b9, verilith-rustls 2fbe4b9, nginx 1.24.0 (Ubuntu), h2o 2.2.5, hyper 1.13.0

Requests per second: median over the rounds, with the range. Server CPU efficiency is requests per server CPU-second (higher is better), the figure least disturbed by a shared machine.

## h1-tls-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 221k | 221k to 221k | 156k | 536 µs | 2.59 ms | 0 |
| verilith-rustls | 209k | 209k to 209k | 147k | 553 µs | 4.60 ms | 0 |
| nginx | 194k | 194k to 194k | 106k | 970 µs | 3.31 ms | 0 |
| h2o | 151k | 151k to 151k | 81k | 1.41 ms | 4.76 ms | 0 |
| hyper | 180k | 180k to 180k | 99k | 1.12 ms | 2.74 ms | 0 |

## h1-tls-close

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 3168 | 3168 to 3168 | 6997 | 4.43 ms | 16.69 ms | 0 |
| verilith-rustls | 3190 | 3190 to 3190 | 4980 | 4.33 ms | 14.38 ms | 0 |
| nginx | 5451 | 5451 to 5451 | 3207 | 2.52 ms | 16.57 ms | 0 |
| h2o | 4231 | 4231 to 4231 | 2528 | 5.46 ms | 15.33 ms | 0 |
| hyper | 6513 | 6513 to 6513 | 5351 | 2.27 ms | 5.68 ms | 0 |

## h2-tls-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 1155k | 1155k to 1155k | 1107k | 898 µs | n/a | 0 |
| verilith-rustls | 1351k | 1351k to 1351k | 1158k | 731 µs | n/a | 0 |
| nginx | 372k | 372k to 372k | 192k | 4.81 ms | n/a | 0 |
| h2o | 535k | 535k to 535k | 270k | 3.89 ms | n/a | 0 |
| hyper | 226k | 226k to 226k | 124k | 8.86 ms | n/a | 0 |

## h2-tls-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 71k | 71k to 71k | 38k | 2.49 ms | n/a | 0 |
| verilith-rustls | 64k | 64k to 64k | 34k | 3.05 ms | n/a | 0 |
| nginx | 41k | 41k to 41k | 21k | 5.40 ms | n/a | 0 |
| h2o | 65k | 65k to 65k | 34k | 3.75 ms | n/a | 0 |
| hyper | 57k | 57k to 57k | 31k | 3.51 ms | n/a | 0 |

h2load reports a mean request time, not percentiles; for h2 cases p50 shows that mean.

Notes: `verilith` is TLS 1.3 on verilith-tls (verified) with aws-lc;
`verilith-rustls` the same server with `--tls-backend rustls`. In
`h1-tls-close` wrk is the bottleneck (its two CPUs are busy): verilith-tls
sends no session tickets, so wrk does a full handshake every time, while
nginx and hyper let it resume; compare requests per server CPU-second there.

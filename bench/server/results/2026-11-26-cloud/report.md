# bench/server report

2026-11-26T05:40, Intel(R) Xeon(R) Processor @ 2.10GHz, 4 CPUs (server on 0-1, load generator on 2-3), 1 rounds of 3s per case.

Versions: hyper 1.13.0, nginx 1.24.0 (Ubuntu), h2o 2.2.5

Requests per second: median over the rounds, with the range. Server CPU efficiency is requests per server CPU-second (higher is better), the figure least disturbed by a shared machine.

## h1-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| hyper | 220k | 220k to 220k | 117k | 1.09 ms | 3.39 ms | 0 |
| nginx | 322k | 322k to 322k | 170k | 631 µs | 1.66 ms | 0 |
| h2o | 193k | 193k to 193k | 102k | 1.17 ms | 18.63 ms | 0 |

## h1-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| hyper | 110k | 110k to 110k | 59k | 490 µs | 1.50 ms | 0 |
| nginx | 131k | 131k to 131k | 73k | 343 µs | 1.91 ms | 0 |
| h2o | 99k | 99k to 99k | 52k | 548 µs | 2.43 ms | 0 |

## h2c-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| hyper | 255k | 255k to 255k | 137k | 7.96 ms | n/a | 0 |
| nginx | 330k | 330k to 330k | 167k | 6.08 ms | n/a | 0 |
| h2o | 516k | 516k to 516k | 263k | 4.00 ms | n/a | 0 |

## h2-tls-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| hyper | 237k | 237k to 237k | 130k | 8.41 ms | n/a | 0 |
| nginx | 384k | 384k to 384k | 197k | 4.93 ms | n/a | 0 |
| h2o | 478k | 478k to 478k | 246k | 4.30 ms | n/a | 0 |

## h1-plaintext-pipe

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| hyper | 397k | 397k to 397k | 203k | 5.75 ms | 17.51 ms | 0 |
| nginx | 308k | 308k to 308k | 158k | 7.22 ms | 25.59 ms | 0 |
| h2o | 203k | 203k to 203k | 105k | 10.89 ms | 28.61 ms | 0 |

h2load reports a mean request time, not percentiles; for h2 cases p50 shows that mean.

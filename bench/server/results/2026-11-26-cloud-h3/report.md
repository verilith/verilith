# bench/server report

2026-11-26T10:51, Intel(R) Xeon(R) Processor @ 2.10GHz, 4 CPUs (server on 0-1, load generator on 2-3), 3 rounds of 10s per case.

Versions: verilith 7623130, h3-quinn h3 0.0.8 quinn 0.11.12, nginx-quic 1.31.10, h2o-quic 2.3.0-DEV@d3e43fc, h2load (h3) nghttp2/1.71.0

Requests per second: median over the rounds, with the range. Server CPU efficiency is requests per server CPU-second (higher is better), the figure least disturbed by a shared machine.

## h3-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 535k | 532k to 571k | 292k | n/a | n/a | 0 |
| h3-quinn | 260k | 242k to 275k | 132k | n/a | n/a | 0 |
| nginx-quic | 458k | 443k to 498k | 262k | n/a | n/a | 0 |
| h2o-quic | 122k | 114k to 131k | 114k | n/a | n/a | 0 |

## h3-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 33k | 32k to 35k | 17k | n/a | n/a | 0 |
| h3-quinn | 20k | 19k to 20k | 9988 | n/a | n/a | 0 |
| nginx-quic | 51k | 49k to 52k | 26k | n/a | n/a | 0 |
| h2o-quic | 30k | 28k to 31k | 16k | n/a | n/a | 0 |

## h3-static-1m

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 2184 | 1956 to 2381 | 1122 | n/a | n/a | 0 |
| h3-quinn | 1470 | 1358 to 1482 | 745 | n/a | n/a | 0 |
| nginx-quic | 3162 | 2899 to 3185 | 1701 | n/a | n/a | 0 |
| h2o-quic | 1934 | 1808 to 1985 | 1008 | n/a | n/a | 0 |

h2load reports a mean request time, not percentiles; for h2 and h3 cases p50 shows that mean.

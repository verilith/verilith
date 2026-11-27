# bench/server report

2026-11-27T03:36, Intel(R) Xeon(R) Processor @ 2.10GHz, 4 CPUs (server on 0-1, load generator on 2-3), 5 rounds of 5s per case.

Versions: verilith d73951b, nginx-quic 1.31.10, h2load (h3) nghttp2/1.71.0

Requests per second: median over the rounds, with the range. Server CPU efficiency is requests per server CPU-second (higher is better), the figure least disturbed by a shared machine.

## h3-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 93k | 86k to 96k | 49k | n/a | n/a | 0 |
| nginx-quic | 51k | 45k to 52k | 26k | n/a | n/a | 0 |

## h3-static-1m

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 5382 | 4397 to 5822 | 3195 | n/a | n/a | 0 |
| nginx-quic | 3383 | 3155 to 3616 | 1817 | n/a | n/a | 0 |

## h3-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 613k | 537k to 643k | 411k | n/a | n/a | 0 |
| nginx-quic | 444k | 430k to 518k | 262k | n/a | n/a | 0 |

h2load reports a mean request time, not percentiles; for h2 and h3 cases p50 shows that mean.

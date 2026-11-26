# bench/server report

HTTP/3 on its two QUIC backends: `verilith` is verilith-server on quinn-proto, `verilith-vq` the same server with `--h3-backend verilith` (verilith-quic-conn). "736a143" is main with this change applied, before it was committed.

2026-11-26T12:32, Intel(R) Xeon(R) Processor @ 2.30GHz, 4 CPUs (server on 0-1, load generator on 2-3), 3 rounds of 10s per case.

Versions: verilith 736a143, verilith-vq 736a143, h3-quinn h3 0.0.8 quinn 0.11.12, h2load (h3) nghttp2/1.71.0

Requests per second: median over the rounds, with the range. Server CPU efficiency is requests per server CPU-second (higher is better), the figure least disturbed by a shared machine.

## h3-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 714k | 699k to 715k | 375k | n/a | n/a | 0 |
| verilith-vq | 769k | 735k to 772k | 605k | n/a | n/a | 0 |
| h3-quinn | 286k | 286k to 293k | 145k | n/a | n/a | 0 |

## h3-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 40k | 37k to 41k | 21k | n/a | n/a | 0 |
| verilith-vq | 43k | 41k to 45k | 23k | n/a | n/a | 0 |
| h3-quinn | 23k | 23k to 23k | 12k | n/a | n/a | 0 |

## h3-static-1m

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 2439 | 2422 to 2604 | 1255 | n/a | n/a | 0 |
| verilith-vq | 2726 | 2399 to 2892 | 1481 | n/a | n/a | 0 |
| h3-quinn | 1585 | 1472 to 1635 | 798 | n/a | n/a | 0 |

h2load reports a mean request time, not percentiles; for h2 and h3 cases p50 shows that mean.

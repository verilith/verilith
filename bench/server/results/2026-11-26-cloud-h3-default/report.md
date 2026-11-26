# bench/server report

HTTP/3 with verilith-quic-conn as verilith-server's default QUIC (`verilith`), against the same server on quinn-proto (`verilith-quinn`, `--h3-backend quinn`), h3 on quinn, and nginx-quic. "f512398" is main with the change that makes verilith-quic-conn the default applied, before it was committed.

2026-11-26T12:41, Intel(R) Xeon(R) Processor @ 2.30GHz, 4 CPUs (server on 0-1, load generator on 2-3), 3 rounds of 10s per case.

Versions: verilith f512398, verilith-quinn f512398, h3-quinn h3 0.0.8 quinn 0.11.12, nginx-quic 1.31.10, h2load (h3) nghttp2/1.71.0

Requests per second: median over the rounds, with the range. Server CPU efficiency is requests per server CPU-second (higher is better), the figure least disturbed by a shared machine.

## h3-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 770k | 706k to 799k | 546k | n/a | n/a | 0 |
| verilith-quinn | 684k | 592k to 737k | 359k | n/a | n/a | 0 |
| h3-quinn | 289k | 278k to 294k | 146k | n/a | n/a | 0 |
| nginx-quic | 512k | 473k to 635k | 296k | n/a | n/a | 0 |

## h3-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 39k | 38k to 45k | 22k | n/a | n/a | 0 |
| verilith-quinn | 40k | 34k to 41k | 20k | n/a | n/a | 0 |
| h3-quinn | 22k | 20k to 23k | 11k | n/a | n/a | 0 |
| nginx-quic | 53k | 51k to 55k | 27k | n/a | n/a | 0 |

## h3-static-1m

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 2926 | 2745 to 2967 | 1517 | n/a | n/a | 0 |
| verilith-quinn | 2466 | 2294 to 2552 | 1251 | n/a | n/a | 0 |
| h3-quinn | 1478 | 1417 to 1528 | 747 | n/a | n/a | 0 |
| nginx-quic | 3736 | 3231 to 3920 | 1947 | n/a | n/a | 0 |

h2load reports a mean request time, not percentiles; for h2 and h3 cases p50 shows that mean.

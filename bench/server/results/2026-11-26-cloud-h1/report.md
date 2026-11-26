# bench/server report

2026-11-26T06:00, Intel(R) Xeon(R) Processor @ 2.10GHz, 4 CPUs (server on 0-1, load generator on 2-3), 3 rounds of 10s per case.

Versions: verilith 3bf8e86, hyper 1.13.0, nginx 1.24.0 (Ubuntu), h2o 2.2.5

Requests per second: median over the rounds, with the range. Server CPU efficiency is requests per server CPU-second (higher is better), the figure least disturbed by a shared machine.

## h1-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 315k | 297k to 323k | 192k | 402 µs | 1.37 ms | 0 |
| hyper | 223k | 216k to 231k | 116k | 1.10 ms | 2.73 ms | 0 |
| nginx | 299k | 286k to 308k | 156k | 686 µs | 2.17 ms | 0 |
| h2o | 202k | 196k to 205k | 103k | 1.17 ms | 3.01 ms | 0 |

## h1-plaintext-pipe

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 3037k | 2972k to 3170k | 1882k | 535 µs | 0 µs | 0 |
| hyper | 1340k | 1309k to 1374k | 681k | 1.71 ms | 5.16 ms | 0 |
| nginx | 333k | 330k to 336k | 170k | 6.73 ms | 24.73 ms | 0 |
| h2o | 198k | 196k to 205k | 100k | 11.24 ms | 30.51 ms | 0 |

## h1-static-1k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 316k | 311k to 319k | 185k | 426 µs | 2.23 ms | 0 |
| hyper | 203k | 197k to 205k | 106k | 1.21 ms | 3.37 ms | 0 |
| nginx | 168k | 160k to 174k | 85k | 1.46 ms | 3.80 ms | 0 |
| h2o | 306k | 294k to 312k | 161k | 603 µs | 2.15 ms | 0 |

## h1-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 105k | 103k to 107k | 55k | 546 µs | 2.15 ms | 0 |
| hyper | 88k | 85k to 90k | 45k | 704 µs | 1.71 ms | 0 |
| nginx | 131k | 123k to 136k | 70k | 396 µs | 1.66 ms | 0 |
| h2o | 103k | 95k to 104k | 53k | 597 µs | 2.84 ms | 0 |

## h1-static-1m

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 6577 | 6515 to 6590 | 3360 | 2.35 ms | 5.19 ms | 0 |
| hyper | 6410 | 6385 to 6438 | 3268 | 2.46 ms | 4.77 ms | 0 |
| nginx | 5271 | 5259 to 5424 | 2702 | 2.93 ms | 5.24 ms | 0 |
| h2o | 5010 | 4612 to 5150 | 2630 | 4.35 ms | 9.17 ms | 0 |

## h1-close

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 63k | 61k to 64k | 59k | 287 µs | 1.68 ms | 0 |
| hyper | 78k | 76k to 80k | 44k | 459 µs | 1.52 ms | 0 |
| nginx | 65k | 64k to 65k | 59k | 304 µs | 1.57 ms | 0 |
| h2o | 78k | 76k to 79k | 53k | 366 µs | 1.54 ms | 0 |

h2load reports a mean request time, not percentiles; for h2 cases p50 shows that mean.

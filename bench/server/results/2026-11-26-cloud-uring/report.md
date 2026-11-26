# bench/server report

2026-11-26T11:10, Intel(R) Xeon(R) Processor @ 2.10GHz, 4 CPUs (server on 0-1, load generator on 2-3), 3 rounds of 5s per case.

Versions: verilith 649aa8c, verilith-uring 649aa8c, nginx 1.24.0 (Ubuntu), h2o 2.2.5, hyper 1.13.0

Requests per second: median over the rounds, with the range. Server CPU efficiency is requests per server CPU-second (higher is better), the figure least disturbed by a shared machine.

## h1-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 277k | 275k to 289k | 180k | 435 µs | 1.48 ms | 0 |
| verilith-uring | 298k | 283k to 306k | 174k | 539 µs | 2.32 ms | 0 |
| nginx | 246k | 238k to 281k | 133k | 799 µs | 2.38 ms | 0 |
| h2o | 179k | 171k to 188k | 92k | 1.35 ms | 3.42 ms | 0 |
| hyper | 200k | 194k to 219k | 105k | 1.22 ms | 2.74 ms | 0 |

## h1-plaintext-pipe

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 2805k | 2758k to 2840k | 1954k | 548 µs | 0 µs | 0 |
| verilith-uring | 2866k | 2813k to 2921k | 1943k | 568 µs | 0 µs | 0 |
| nginx | 318k | 278k to 325k | 163k | 6.99 ms | 26.22 ms | 0 |
| h2o | 177k | 177k to 183k | 91k | 12.51 ms | 34.75 ms | 0 |
| hyper | 1237k | 1091k to 1331k | 635k | 1.83 ms | 5.14 ms | 0 |

## h1-static-1k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 279k | 242k to 279k | 163k | 509 µs | 1.81 ms | 0 |
| verilith-uring | 294k | 248k to 296k | 164k | 558 µs | 2.33 ms | 0 |
| nginx | 149k | 138k to 156k | 76k | 1.62 ms | 3.38 ms | 0 |
| h2o | 263k | 250k to 284k | 148k | 729 µs | 2.64 ms | 0 |
| hyper | 199k | 182k to 207k | 104k | 1.19 ms | 3.02 ms | 0 |

## h1-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 111k | 111k to 115k | 81k | 280 µs | 821 µs | 0 |
| verilith-uring | 114k | 111k to 115k | 83k | 284 µs | 714 µs | 0 |
| nginx | 116k | 111k to 117k | 63k | 413 µs | 1.40 ms | 0 |
| h2o | 96k | 92k to 97k | 50k | 587 µs | 2.05 ms | 0 |
| hyper | 81k | 79k to 84k | 42k | 751 µs | 1.45 ms | 0 |

## h1-static-1m

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 8754 | 8359 to 9476 | 4482 | 1.68 ms | 3.77 ms | 0 |
| verilith-uring | 9139 | 8831 to 9458 | 4927 | 1.56 ms | 3.66 ms | 0 |
| nginx | 4786 | 4776 to 4861 | 2438 | 3.27 ms | 6.03 ms | 0 |
| h2o | 4679 | 4633 to 5020 | 2382 | 3.30 ms | 5.56 ms | 0 |
| hyper | 6009 | 5766 to 6075 | 3097 | 2.60 ms | 5.42 ms | 0 |

## h1-close

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 69k | 66k to 73k | 70k | 267 µs | 2.24 ms | 0 |
| verilith-uring | 68k | 60k to 68k | 65k | 301 µs | 2.35 ms | 0 |
| nginx | 57k | 56k to 58k | 52k | 342 µs | 1.58 ms | 0 |
| h2o | 69k | 68k to 69k | 46k | 444 µs | 2.49 ms | 0 |
| hyper | 70k | 70k to 72k | 39k | 501 µs | 1.56 ms | 0 |

## h1-tls-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 202k | 199k to 207k | 140k | 600 µs | 2.90 ms | 0 |
| verilith-uring | 203k | 191k to 208k | 143k | 616 µs | 3.22 ms | 0 |
| nginx | 177k | 175k to 191k | 94k | 1.09 ms | 3.18 ms | 0 |
| h2o | 134k | 131k to 138k | 69k | 1.68 ms | 4.78 ms | 0 |
| hyper | 194k | 194k to 202k | 104k | 1.11 ms | 4.80 ms | 0 |

## h1-tls-close

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 5958 | 5948 to 6217 | 8469 | 2.66 ms | 6.10 ms | 0 |
| verilith-uring | 5916 | 5902 to 6244 | 8418 | 2.69 ms | 5.92 ms | 0 |
| nginx | 6038 | 6000 to 6048 | 3419 | 2.27 ms | 13.00 ms | 0 |
| h2o | 4245 | 3455 to 4251 | 2632 | 5.41 ms | 14.27 ms | 0 |
| hyper | 5656 | 5609 to 5757 | 4631 | 2.64 ms | 5.77 ms | 0 |

## h2c-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 1418k | 1416k to 1465k | 1134k | 708 µs | n/a | 0 |
| verilith-uring | 1476k | 1470k to 1531k | 1176k | 712 µs | n/a | 0 |
| nginx | 299k | 294k to 309k | 152k | 6.75 ms | n/a | 0 |
| h2o | 462k | 460k to 482k | 234k | 4.26 ms | n/a | 0 |
| hyper | 226k | 223k to 229k | 122k | 8.99 ms | n/a | 0 |

## h2-tls-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 1217k | 1208k to 1279k | 1033k | 812 µs | n/a | 0 |
| verilith-uring | 1290k | 1268k to 1302k | 1046k | 811 µs | n/a | 0 |
| nginx | 356k | 353k to 368k | 184k | 5.13 ms | n/a | 0 |
| h2o | 441k | 430k to 447k | 221k | 4.54 ms | n/a | 0 |
| hyper | 221k | 215k to 234k | 119k | 9.04 ms | n/a | 0 |

## h2-tls-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 64k | 64k to 67k | 34k | 2.91 ms | n/a | 0 |
| verilith-uring | 61k | 61k to 63k | 34k | 2.92 ms | n/a | 0 |
| nginx | 40k | 38k to 41k | 20k | 5.60 ms | n/a | 0 |
| h2o | 63k | 61k to 65k | 32k | 3.93 ms | n/a | 0 |
| hyper | 56k | 50k to 56k | 29k | 3.35 ms | n/a | 0 |

h2load reports a mean request time, not percentiles; for h2 and h3 cases p50 shows that mean.

Notes: `verilith-uring` is the same build with `--io-uring` (the io_uring
event loop: multishot accept and receive from a provided-buffer ring,
sends on the ring, one `io_uring_enter` per loop turn). On `h1-plaintext`
it makes 12x fewer system calls than epoll (29k/s against 368k/s, `perf
stat`) for the same server CPU: on this VM a system call is cheap
(eIBRS, no KPTI) and loopback TCP is 90% of the profile, so the
difference is small either way: +4 to +10% on `h1-static-1m`, `h2c` and
`h2-tls-plaintext`, -3 to -7% CPU efficiency on `h1-plaintext` and
`h1-close`. Epoll stays the default.

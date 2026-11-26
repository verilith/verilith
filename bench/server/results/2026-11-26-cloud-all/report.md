# bench/server report

2026-11-26T07:18, Intel(R) Xeon(R) Processor @ 2.10GHz, 4 CPUs (server on 0-1, load generator on 2-3), 3 rounds of 10s per case.

Versions: verilith c71e452, hyper 1.13.0, bun ?, may-minihttp 0.1.11, nginx 1.24.0 (Ubuntu), h2o 2.2.5

Requests per second: median over the rounds, with the range. Server CPU efficiency is requests per server CPU-second (higher is better), the figure least disturbed by a shared machine.

## h1-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 297k | 270k to 313k | 184k | 457 µs | 1.87 ms | 0 |
| hyper | 231k | 219k to 233k | 120k | 1.05 ms | 2.22 ms | 0 |
| bun | 234k | 229k to 236k | 118k | 980 µs | 2.47 ms | 0 |
| may-minihttp | 305k | 304k to 322k | 167k | 600 µs | 2.05 ms | 0 |
| nginx | 303k | 272k to 306k | 160k | 660 µs | 2.47 ms | 0 |
| h2o | 192k | 183k to 197k | 98k | 1.24 ms | 3.07 ms | 0 |

## h1-plaintext-pipe

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 2996k | 2632k to 3077k | 2072k | 522 µs | 0 µs | 0 |
| hyper | 1289k | 1186k to 1339k | 654k | 1.78 ms | 5.41 ms | 0 |
| bun | 257k | 245k to 272k | 131k | 8.65 ms | 26.40 ms | 0 |
| may-minihttp | 3048k | 2932k to 3150k | 1811k | 539 µs | 0 µs | 0 |
| nginx | 352k | 330k to 363k | 179k | 6.38 ms | 24.40 ms | 0 |
| h2o | 199k | 188k to 223k | 100k | 11.21 ms | 33.61 ms | 0 |

## h1-static-1k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 303k | 288k to 306k | 172k | 492 µs | 1.84 ms | 0 |
| hyper | 199k | 190k to 203k | 103k | 1.23 ms | 2.86 ms | 0 |
| bun | 79k | 78k to 80k | 40k | 3.03 ms | 8.53 ms | 0 |
| may-minihttp | 310k | 302k to 316k | 162k | 641 µs | 1.80 ms | 0 |
| nginx | 184k | 174k to 186k | 94k | 1.33 ms | 2.70 ms | 0 |
| h2o | 305k | 300k to 311k | 162k | 519 µs | 2.04 ms | 0 |

## h1-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 119k | 119k to 126k | 74k | 319 µs | 1.26 ms | 0 |
| hyper | 90k | 89k to 91k | 46k | 683 µs | 1.33 ms | 0 |
| bun | 46k | 45k to 47k | 23k | 1.31 ms | 4.26 ms | 0 |
| may-minihttp | 84k | 84k to 85k | 43k | 703 µs | 2.10 ms | 0 |
| nginx | 118k | 113k to 123k | 63k | 440 µs | 1.55 ms | 0 |
| h2o | 99k | 95k to 100k | 51k | 579 µs | 1.37 ms | 0 |

## h1-static-1m

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 9716 | 9138 to 9766 | 4999 | 1.54 ms | 3.86 ms | 0 |
| hyper | 6408 | 6234 to 6462 | 3251 | 2.47 ms | 4.60 ms | 0 |
| bun | 5888 | 5867 to 6433 | 3934 | 1.94 ms | 6.36 ms | 0 |
| may-minihttp | 5408 | 5261 to 5427 | 2746 | 2.71 ms | 10.14 ms | 0 |
| nginx | 5233 | 5101 to 5267 | 2661 | 3.06 ms | 5.60 ms | 0 |
| h2o | 4974 | 4758 to 5654 | 2628 | 3.09 ms | 6.66 ms | 0 |

## h1-close

**may-minihttp ignores `Connection: close`** (it answers a second request on the same connection), so its h1-close figure is a keep-alive measurement and not comparable. Bun's errors here are wrk's read errors on connections Bun resets.

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 76k | 75k to 78k | 76k | 234 µs | 1.81 ms | 0 |
| hyper | 78k | 70k to 80k | 44k | 442 µs | 1.34 ms | 0 |
| bun | 72k | 67k to 74k | 58k | 268 µs | 1.91 ms | 2150442 |
| may-minihttp | 311k | 290k to 330k | 166k | 164 µs | 626 µs | 0 |
| nginx | 62k | 61k to 67k | 59k | 303 µs | 1.94 ms | 0 |
| h2o | 75k | 69k to 79k | 50k | 400 µs | 2.10 ms | 0 |

## h1-tls-plaintext

verilith-server has no TLS yet (next milestone), so it is absent from the TLS cases.

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| hyper | 205k | 201k to 209k | 109k | 1.08 ms | 3.78 ms | 0 |
| bun | 207k | 197k to 211k | 110k | 940 µs | 3.62 ms | 0 |
| nginx | 201k | 181k to 209k | 106k | 1.00 ms | 2.99 ms | 0 |
| h2o | 147k | 130k to 150k | 76k | 1.53 ms | 3.91 ms | 0 |

## h2c-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 1536k | 1481k to 1622k | 1146k | 686 µs | n/a | 0 |
| hyper | 248k | 244k to 249k | 134k | 8.27 ms | n/a | 0 |
| nginx | 321k | 320k to 322k | 163k | 6.16 ms | n/a | 0 |
| h2o | 502k | 446k to 516k | 254k | 4.66 ms | n/a | 0 |

## h2-tls-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| hyper | 237k | 227k to 237k | 129k | 8.71 ms | n/a | 0 |
| bun | 331k | 330k to 331k | 168k | 6.21 ms | n/a | 0 |
| nginx | 378k | 347k to 386k | 193k | 4.88 ms | n/a | 0 |
| h2o | 478k | 443k to 497k | 243k | 4.23 ms | n/a | 0 |

## h2-tls-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| hyper | 59k | 56k to 59k | 31k | 3.26 ms | n/a | 0 |
| bun | 47k | 35k to 50k | 24k | 5.50 ms | n/a | 0 |
| nginx | 45k | 44k to 46k | 23k | 4.87 ms | n/a | 0 |
| h2o | 65k | 64k to 66k | 33k | 3.79 ms | n/a | 0 |

h2load reports a mean request time, not percentiles; for h2 cases p50 shows that mean.

# bench/server report

2026-11-26T19:37, Intel(R) Xeon(R) Processor @ 2.10GHz, 4 CPUs (server on 0-1, load generator on 2-3), 3 rounds of 5s per case.

Versions: verilith 48d8257, hyper 1.13.0, nginx 1.24.0 (Ubuntu), h2o 2.2.5, h3-quinn h3 0.0.8 quinn 0.11.12, nginx-quic 1.31.10, h2o-quic 2.3.0-DEV@d3e43fc, h2load (h3) nghttp2/1.71.0

Requests per second: median over the rounds, with the range. Server CPU efficiency is requests per server CPU-second (higher is better), the figure least disturbed by a shared machine.

## h1-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 285k | 272k to 322k | 184k | 427 µs | 1.22 ms | 0 |
| hyper | 214k | 200k to 227k | 112k | 1.12 ms | 2.73 ms | 0 |
| nginx | 275k | 270k to 302k | 148k | 731 µs | 1.87 ms | 0 |
| h2o | 188k | 154k to 194k | 99k | 1.20 ms | 3.03 ms | 0 |

## h1-tls-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 197k | 184k to 198k | 144k | 593 µs | 3.04 ms | 0 |
| hyper | 190k | 183k to 196k | 103k | 1.08 ms | 4.37 ms | 0 |
| nginx | 187k | 179k to 195k | 102k | 1.02 ms | 3.37 ms | 0 |
| h2o | 140k | 128k to 146k | 72k | 1.61 ms | 4.69 ms | 0 |

## h2c-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 1362k | 1332k to 1445k | 1338k | 774 µs | n/a | 0 |
| hyper | 237k | 236k to 241k | 128k | 8.64 ms | n/a | 0 |
| nginx | 316k | 284k to 316k | 160k | 6.25 ms | n/a | 0 |
| h2o | 466k | 442k to 477k | 234k | 4.35 ms | n/a | 0 |

## h2-tls-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 1173k | 957k to 1212k | 1137k | 868 µs | n/a | 0 |
| hyper | 224k | 221k to 238k | 122k | 9.06 ms | n/a | 0 |
| nginx | 344k | 304k to 364k | 177k | 5.22 ms | n/a | 0 |
| h2o | 464k | 396k to 480k | 234k | 4.39 ms | n/a | 0 |

## h2-tls-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 63k | 59k to 71k | 35k | 2.64 ms | n/a | 0 |
| hyper | 51k | 51k to 57k | 28k | 3.51 ms | n/a | 0 |
| nginx | 42k | 37k to 46k | 22k | 4.81 ms | n/a | 0 |
| h2o | 64k | 56k to 68k | 32k | 3.83 ms | n/a | 0 |

## h3-plaintext

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 606k | 604k to 649k | 449k | n/a | n/a | 0 |
| h3-quinn | 251k | 217k to 253k | 126k | n/a | n/a | 0 |
| nginx-quic | 425k | 413k to 473k | 242k | n/a | n/a | 0 |
| h2o-quic | 94k | 86k to 102k | 92k | n/a | n/a | 0 |

## h3-static-64k

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 36k | 35k to 41k | 22k | n/a | n/a | 0 |
| h3-quinn | 20k | 17k to 20k | 9998 | n/a | n/a | 0 |
| nginx-quic | 46k | 45k to 49k | 24k | n/a | n/a | 0 |
| h2o-quic | 28k | 28k to 29k | 15k | n/a | n/a | 0 |

## h3-static-1m

| server | req/s | range | req per server CPU-s | p50 | p99 | errors |
|---|---:|---:|---:|---:|---:|---:|
| verilith | 2517 | 2499 to 2699 | 1416 | n/a | n/a | 0 |
| h3-quinn | 1261 | 1222 to 1428 | 635 | n/a | n/a | 0 |
| nginx-quic | 2904 | 2865 to 3360 | 1535 | n/a | n/a | 0 |
| h2o-quic | 1829 | 1779 to 2045 | 931 | n/a | n/a | 0 |

h2load reports a mean request time, not percentiles; for h2 and h3 cases p50 shows that mean.

Notes: this run is PR #136 (commit 48d8257) after profiling the hot paths
with `prof.py`: HTTP/2 request checks and HPACK compares word at a time,
no allocation per HTTP/2 response, TLS records moved out of verilith-tls
once instead of copied, HTTP/3 bodies kept as shared buffers in
verilith-quic-conn, and IdHash for the HTTP/3 stream maps. A/B against
the build before it (`ab.py`, alternating runs, the same VM) measured
requests per server CPU-second: h2c-plaintext +22%, h2-tls-plaintext
+23%, h2-tls-static-64k +7% (TLS copy) and +3% (HTTP/2), h3-static-64k
+25%, h3-static-1m +15%, h3-plaintext +6%; HTTP/1.1 is unchanged, as its
profile is 93% kernel (loopback TCP). One run here against the others is
noisier than those A/B pairs: on h3-static-64k and -1m nginx-quic is
still ahead, by about 10% per CPU-second.

# vbench

One benchmark setup for every [Verilith](https://github.com/verilith/verilith)
library, measured one way: each of our libraries against the library it
replaces, on the same machine, in the same sitting, built with the same
compiler and flags, reported as a median speedup with a 95% confidence
interval, plus instructions per call. Two speeds are reported and kept
apart: **drop-in** (ours behind the original's API, caller unchanged) and
**native** (the same task through our own API). And Node.js's own benchmark suite on an
official build against one with our libraries swapped in.

```sh
./run.sh               # everything: about 1.5 to 2.5 hours on a MacBook
./run.sh --skip-node   # library benchmarks only: about 30 minutes
./run.sh --quick       # smoke test, a few minutes
```

The report is `results/<date>-<host>/report.md`.

## On a Mac (Apple Silicon)

1. Install the tools once:
   ```sh
   xcode-select --install                          # clang, git, make
   brew install cmake ninja
   curl https://sh.rustup.rs -sSf | sh              # Rust (stable)
   ```
2. Get the machine quiet: plug in the charger, turn off Low Power Mode,
   quit everything else (browser, Slack, Docker, Dropbox), and leave it
   alone with the lid open. `run.sh` checks the power state, warns about
   battery and Low Power Mode, and keeps the Mac awake with `caffeinate`.
3. `./run.sh`

Apple Silicon can't pin a core or switch off frequency boost the way a Linux
server can. vbench copes in three ways: every runner asks for the
user-interactive QoS class, which keeps it on a performance core; ours and
the original alternate sample by sample (A B, B A, ...), so drift hits both
equally; and the statistics are over the paired ratios, not over raw times.

### Instruction counts on macOS

Linux reads instructions with `perf_event_open` (what `perf stat` uses).
macOS has no `perf`; vbench reads the per-process counters the kernel keeps
for `proc_pid_rusage(RUSAGE_INFO_V4)` (`ri_instructions`, `ri_cycles`, the
same numbers `/usr/bin/time -l` prints). That needs no root and no
Instruments, and it is read around every timed sample, so each sample has its
own instruction count. `machine.json` records whether the counters worked
(`"counters": "yes (proc_pid_rusage)"`); if they don't, the instruction
columns say n/a and everything else still runs. On Linux, counters need a
PMU (most cloud VMs have none) and `kernel.perf_event_paranoid` <= 2.

### Sharing the machine

Timed runs take a lock, `~/vf-bench.lock` (a directory; override with
`VF_BENCH_LOCK`), so that two benchmark jobs on one machine never time at the
same time. Builds and downloads do not take it. `run.sh` holds it only while
the library samples are taken, and `scripts/node.sh` only during compare.js.
If it is held, the script waits and prints who holds it (`~/vf-bench.lock/who`).
A lock whose `pid` file names a dead process is removed, and so is one with
no `pid` file that has not changed for `VF_BENCH_LOCK_STALE` seconds (default
3 hours). Other tools on the
same machine can use the same convention: `mkdir ~/vf-bench.lock` (then write
your pid to `~/vf-bench.lock/pid`) before
timing, `rmdir` (or `rm -rf`) after.

## What it compares

Every comparison is one of two kinds, and the report labels each number
with its kind. They answer different questions, so neither replaces the
other.

- **drop-in**: our library behind the original's API. Both sides are **the
  same driver source** linked against a different library, so the library is
  the only difference. This is the speed a user gets by relinking and
  changing nothing, and it is exactly how they would adopt it.
- **native**: the same task done through our library's own API, against the
  original doing that task through its own best API. This is the speed after
  porting the calling code. A drop-in user does not get it, and it is never
  reported as the drop-in number.

The rule for a native comparison is same task, best API on each side: both
sides read the same values out of the same input and return the same check
value, the original runs the same driver as in the drop-in comparison, and
where one side's API makes it do work the other side skips, the report says
so under the table (`note` in `harness/suites.py`).

| comparison | API | ours | original | what one call does | inputs |
| --- | --- | --- | --- | --- | --- |
| zlib-inflate | drop-in | verilith-zlib (zlib ABI) | zlib 1.4 | `inflate` a whole stream | 5 Silesia files + 4 KiB and 64 KiB pieces |
| zlib-deflate | drop-in | verilith-zlib (zlib ABI) | zlib 1.4 | `deflate` at levels 1, 6, 9 | same |
| brotli-decode | drop-in | verilith-brotli (brotli decoder ABI) | brotli 1.2.1 | `BrotliDecoderDecompress`, and `BrotliDecoderDecompressStream` fed 1 KiB at a time | the same files, compressed by brotli at quality 5 and 11 |
| lz4-decompress, lz4-compress | drop-in | verilith-lz4 (lz4 ABI) | lz4 1.11.1 | `LZ4_decompress_safe`, `LZ4_compress_default` of a whole file as one block | 5 Silesia files + 4 KiB and 64 KiB pieces |
| lz4-frame-decompress, lz4-frame-compress | drop-in | verilith-lz4 (lz4 ABI) | lz4 1.11.1 | `LZ4F_decompress`, `LZ4F_compressFrame` of a whole file as one frame | same |
| snappy-uncompress, snappy-validate, snappy-compress | drop-in | verilith-snappy (snappy-c ABI) | snappy 1.3.1 | `snappy_uncompress`, `snappy_validate_compressed_buffer`, `snappy_compress` | same |
| archive-read | drop-in | verilith-archive (libarchive read ABI) | libarchive 3.8.11 (with zlib 1.4) | open from memory, then `read/`: every header and all data (`archive_read_data_block`); `list/`: every header, data skipped | tar, zip (deflate and stored) and tar.gz of the 5 Silesia files and of 2000 files of 4 KiB, made by libarchive's bsdtar |
| dns-parse | drop-in | c-ares + verilith-dns patch | c-ares | `ares_dns_parse` + destroy | 4 responses (data/dns) |
| dns-write | drop-in | c-ares + verilith-dns patch | c-ares | `ares_dns_write` | same |
| dns-read | drop-in | c-ares + verilith-dns patch | c-ares | `ares_dns_parse`, read every question and record down to each RDATA field, destroy | same |
| dns-native | native | verilith-dns (`Message::parse_into`, `records`, `data`) | c-ares | the dns-read task | same |
| http-llhttp | drop-in | verilith-http under llhttp's api.c | llhttp 9.4.4 | parse a message with Node's callbacks | 6 messages (data/http) |
| http-llhttp-native | native | verilith-http (`parse_request`/`parse_response`, `ChunkedDecoder`) | llhttp 9.4.4 | the http-llhttp task: target or reason, every header, the body | same |
| http-pico | drop-in | verilith-http (phr ABI) | picohttpparser | `phr_parse_request`/`_response` | same |
| http-pico-native | native | verilith-http (`parse_request`/`parse_response`) | picohttpparser | the http-pico task: a head into a reused header array | same |
| url-ada | drop-in | verilith-url (ada C ABI) | ada 4.1.1 | parse every URL, read href | ada's URL dataset (100k URLs) and its first 1k |
| json-cjson-parse | drop-in | verilith-json (cJSON ABI) | cJSON 1.7.19 | parse, visit every value, delete | simdjson's examples |
| json-cjson-native | native | verilith-json (`Parser`) | cJSON 1.7.19 | the json-cjson-parse task | same |
| json-cjson-print | drop-in | verilith-json (cJSON ABI) | cJSON 1.7.19 | `cJSON_PrintUnformatted` | same |
| json-simdjson | native | verilith-json (`Parser`) | simdjson 5.2.0 (DOM) | parse, read every value | same |
| x509-mbedtls | drop-in | mbedTLS + verilith-x509 patch | mbedTLS 4.3.0 | `mbedtls_x509_crt_parse_der` + free | verilith-x509's 3 certificates, Mozilla's roots |
| x509-mbedtls-read | drop-in | mbedTLS + verilith-x509 patch | mbedTLS 4.3.0 | `mbedtls_x509_crt_parse_der_nocopy`, read serial, names, validity, key usage, CA flag, DNS names and EKUs, free | same |
| x509-mbedtls-native | native | verilith-x509 (`verilith_x509::parse` and its accessors) | mbedTLS 4.3.0 | the x509-mbedtls-read task | same |
| x509-verdict | native | verilith-x509 (`verilith_x509::parse`) | Verdict ([secure-foundations/verdict](https://github.com/secure-foundations/verdict), 2025-11-18) | parse the whole certificate from memory, Rust to Rust, both verified in Verus | same |
| png-libpng | native | verilith-png (Rust API) | libpng 1.6.59 | decode to RGBA8 | the 24 Kodak photos |
| webp-lossless | drop-in | verilith-webp (libwebp ABI) | libwebp 1.6.0 | `WebPDecodeRGBAInto` | the Kodak photos, lossless WebP |
| webp-lossy | drop-in | verilith-webp (libwebp ABI) | libwebp 1.6.0 | `WebPDecodeRGBAInto` | the Kodak photos, lossy WebP at quality 75 |
| jpeg-baseline | drop-in | verilith-jpeg (TurboJPEG ABI) | libjpeg-turbo 3.2.1 | `tj3Decompress8` to RGB | the Kodak photos, baseline JPEG, 4:2:0 at quality 75 |
| jpeg-progressive | drop-in | verilith-jpeg (TurboJPEG ABI) | libjpeg-turbo 3.2.1 | `tj3Decompress8` to RGB | the same as progressive JPEG |
| jpeg-444 | drop-in | verilith-jpeg (TurboJPEG ABI) | libjpeg-turbo 3.2.1 | `tj3Decompress8` to RGB | the Kodak photos, baseline JPEG, 4:4:4 at quality 90 |
| font-sanitize | drop-in | verilith-font (OTS's C++ API) | OTS ([khaledhosny/ots](https://github.com/khaledhosny/ots), 2026-11) | `ots::OTSContext::Process` into a memory stream | Source Serif 4 Regular as OTF, TTF, WOFF and WOFF2 |
| regex-re2 | drop-in | verilith-regex (cre2 C ABI) | RE2 2025-11-05 under cre2 | find every match of a pattern, with its groups (`cre2_match` in a loop) | 12 patterns over 64 KiB and 1 MiB of dickens and 1k URLs |
| xml-expat-read | native | verilith-xml (`parse`, `Element::attrs`, `children`) | expat 2.7.3 (SAX) | parse, visit every element, attribute (normalized value) and run of character data | 6 of Silesia's XML files and the 7 files of roxmltree's benchmarks |
| xml-expat-check | native | verilith-xml (`check`) | expat 2.7.3 (no handlers) | decide whether the document is well-formed | same |
| xml-libxml2-read | native | verilith-xml (`parse`, `Element::attrs`, `children`) | libxml2 2.15.4 (SAX2) | the xml-expat-read task | same |
| xml-libxml2-check | native | verilith-xml (`check`) | libxml2 2.15.4 (SAX2, no content handlers) | the xml-expat-check task | same |

In archive-read the two libraries do not do quite the same work: verilith-archive
parses and checks the whole archive when it is opened and checks a member's
length and CRC-32 before it returns any of its data, where libarchive streams.

Five tasks are measured both ways (against c-ares, llhttp, picohttpparser,
cJSON and mbedTLS), and the report prints those side by side, case by case,
under "Drop-in and native, side by side". Three things to know when reading
the native column:

- **mbedTLS.** `mbedtls_x509_crt_parse_der_nocopy` also decodes the public
  key and allocates the name and extension lists, which its API does not let
  a caller skip and which `verilith_x509::parse` does not do. The native number
  there is an upper bound.
- **cJSON and c-ares** allocate a tree per parse and free it; that is the
  only way their APIs parse, and it is most of the gap. verilith-json and verilith-dns parse
  into buffers the caller reuses.
- **picohttpparser** already has a flat API that copies nothing, so its two
  columns are close, as they should be.

verilith-png has no libpng C ABI yet, nor verilith-xml an expat or libxml2 one, and
simdjson and Verdict are compared core against core, so those five have a native number only. zlib, brotli, lz4, snappy, archives, WebP, JPEG, fonts, regex
and URL have a drop-in number only: their own APIs do the same work as the
originals' (verilith-url's Rust API against ada's C++ API is not measured yet).
Native comparisons use Rust runners (`runners/`) against C/C++ runners, with
the same timer and counters. They will move to C drivers as our libraries
gain C entry points for their own APIs.

Every input is pinned: originals by tag or commit and data sets by commit
(`pins.sh`), and every input file by SHA-256 (`data/SHA256SUMS`, checked on
each run). The WebP inputs are made from the PNGs by libwebp's encoder during
the build, and the JPEG inputs by libjpeg-turbo's. libjpeg-turbo is built with
its SIMD code, as it ships: NEON on Apple Silicon, and on x86-64 that needs
NASM or Yasm (the build stops without one). Our libraries are taken at `main`; `machine.json` records the
exact commit of everything used.

### Node.js

`scripts/node.sh` builds Node.js 22.23.5 twice from the same source with
the same flags: *official* (as shipped) and *hardened*, with verilith-http in place
of llhttp, verilith-url and verilith-json (via verilith-bind) in place of ada and simdjson, verilith-zlib in
place of zlib, and c-ares with verilith-dns. Both builds use the same c-ares commit,
so its version is not a difference. It checks that our code is in the
hardened binary (`node/build-check.txt`) and smoke-tests both, then runs
Node's `benchmark/compare.js` on the URL, HTTP-parser and zlib benchmarks
(`NODE_BENCHES` in the script) with 30 runs each. `NODE_SWAPS` picks the
swaps, e.g. `NODE_SWAPS="llhttp ada" ./run.sh`.

verilith-bind is fetched at `main` like our other libraries. If its checkout is
missing, the hardened build keeps ada and simdjson and says so. Node's DNS benchmark measures `dns.lookup`, which
uses the OS resolver rather than c-ares, so c-ares has no Node benchmark.

## The method

For each case, `harness/vbench.py` starts both runners (ours and the
original) as long-lived processes, then:

1. warms both up and picks one iteration count so a sample takes about
   25 ms (at least one call);
2. takes 31 samples of each, alternating A B, B A, A B, ...;
3. records every sample's time, instructions, cycles and a check value
   (`raw.csv`). The check value (output size, a checksum of decoded pixels,
   records parsed, ...) must match between the two sides unless the outputs
   legitimately differ (compressed or printed sizes, shown in the report).

`harness/report.py` then computes, per case, the speedup of each pair
(original time / our time, so above 1 means ours is faster), its median, and
a distribution-free 95% confidence interval for the median (order statistics
of the binomial distribution: for 31 pairs, the 10th and 22nd smallest
ratios). If the interval contains 1.00x, the report says "no measurable
difference" instead of a winner. Instructions per call are the median over
the samples of each side.

A results line then reads like: *zlib-inflate, dickens: 1.92x (95% CI
1.89–1.95), 31% fewer instructions.*

For Node, compare.js does not pair its runs, so `harness/node_report.py`
reports the ratio of median rates with a bootstrap 95% interval. Node's own
`benchmark/compare.R` works on the same `node/compare.csv`.

## Results directory

| file | what |
| --- | --- |
| `report.md` | the readable summary: overview, drop-in and native side by side, every case, Node |
| `summary.csv` | one row per case: API kind, times, MB/s, speedup and CI, instructions, cycles |
| `raw.csv` | every sample |
| `machine.json` | CPU, OS, power state, compilers, flags, counters, every commit |
| `node/` | compare.csv, its summary, the build check |
| `run.log`, `run.sh.log` | logs |

## Layout

```
run.sh               the one command
pins.sh              versions of everything
scripts/             fetch.sh, build.sh, node.sh, lib.sh
harness/             vbench.py (runs), report.py and node_report.py (stats),
                     suites.py (the comparisons), counters.c and runner.c
                     (timer, counters and protocol for C runners), machine.py
runners/             Rust runners (vbrun: the protocol for Rust)
suites/<name>/       the drivers
data/                inputs kept here (DNS and HTTP messages) and SHA256SUMS
work/                everything fetched and built (not in git)
```

Useful while working on one library:

```sh
./run.sh --only json --skip-node
python3 harness/vbench.py --list
python3 harness/vbench.py --out /tmp/r --only zlib-inflate --case dickens --pairs 11
python3 harness/report.py /tmp/r
```

Our libraries are built from this checkout's `crates/`, as they are on
disk, so a local change is measured without committing it.

## Adding a library

1. Write a driver against the original library's API in `suites/<name>/`:
   register cases with `vb_case(name, bytes, fn, ctx)` and call `vb_main()`
   (see `harness/runner.h`). For a Rust API, add a runner under `runners/`
   using `vbrun::Runner`.
2. Add `build_<name>` to `scripts/build.sh`, building the original with
   `$CFLAGS_BENCH` and ours with `rust_lib REPO FEATURES`.
3. Pin the original and any data in `pins.sh`, and add the inputs' hashes to
   `data/SHA256SUMS`.
4. Add the comparison to `harness/suites.py`, with `api="drop-in"`. If the
   library has its own faster API, add a second comparison with
   `api="native"` and the same `pair`: a Rust runner doing the same task
   with the same check value against the same original driver, and a `note`
   on anything one side does that the other does not.

No CI or GitHub Actions: runs are manual, on purpose.

# Verilith

Formally verified drop-in replacements for foundational open source
libraries, written in Rust and proven with [Verus](https://github.com/verus-lang/verus).

Each library is its own crate, verified and versioned on its own, and most
also build a static library behind the C API of the library they replace
(zlib, cJSON, llhttp, c-ares, libpng, OpenSSL's SHA-2 and so on), so existing C and C++
callers can relink without changing code.

**Status: pre-release.** The crates are at 0.1 and are not on crates.io
yet. APIs can change. Read [what is proven and what is
trusted](#what-is-proven-and-what-is-trusted) before relying on any of it.

## What is proven and what is trusted

"Formally verified" means something specific here, and it has limits.

**Proven**, by Verus, for every input, each time the proofs are checked:

- **Conformance to a written specification.** Each crate states its format
  or protocol as mathematical functions (`src/spec.rs` in most crates),
  written from the standard: RFC 8259 for JSON, RFC 1951 for DEFLATE, the
  WHATWG URL Standard, and so on. The code that runs is proven to return
  exactly what the specification returns: the same accept or reject
  decision and the same output.
- **No memory errors and no crashes in the verified code.** No
  out-of-bounds read or write, no integer overflow, no panic, and every
  loop terminates.
- **More, crate by crate.** Many crates prove further properties: bounds on
  work or on output size (zlib, http, regex, dns), that compression
  round-trips (zlib, lz4, snappy), that a stream split into pieces anywhere
  decodes the same (zlib, zstd, brotli, hpack, http), linearizability of
  the queues (sync). Each crate's README has a "What is proven" section
  that names the theorem and the function it is stated on.

No crate's source contains `assume(...)` or `admit()`. Everything a proof
takes for granted is declared where it can be found: as an axiom or as the
contract of an `external_body` function, in the trusted files listed below.

**Trusted**, which means assumed and not proven:

- **The specifications.** If a `spec.rs` misreads its standard, the proofs
  still hold, about the wrong thing. The specifications are the files to
  review, and each README says where its specification narrows or departs
  from the standard or from the library it replaces.
- **The tools.** Verus, its standard library `vstd`, the Z3 solver, and the
  Rust compiler and LLVM.
- **A small set of unsafe primitives.** Raw copies, unchecked loads and
  allocations are written as `external_body` functions: Verus assumes the
  contract of each and does not check its body. Most are one line, and most
  live in [`verilith-core`](crates/core#trusted-base).
- **CPU instructions.** [`verilith-simd`](crates/simd#trusted-base) states
  what each x86 and NEON SIMD intrinsic computes, as assumed
  specifications. They are tested against the CPU, not proven.
- **C API glue and language bindings.** The layer that turns a C call into
  a call of the verified Rust function is, in most crates, ordinary
  unverified `unsafe` Rust, and so are the patches that fit a crate into
  c-ares, mbedTLS, nghttp2 and llhttp. All of
  [`verilith-bind`](crates/bind#what-is-not-verified) is unverified.
- **A few unverified fast paths**, each tested against a verified one, such
  as the carry-less-multiply CRC-32 in `verilith-core`.
- **A memory model, for concurrency.** The queue proofs in `verilith-sync`
  hold under a release/acquire model of atomics that the crate states and
  does not derive from the hardware.

The exact list differs per crate, and each crate gives its own, in a
`TRUST.md` or in a "Trusted base" section of its README (linked in the
table below).

**Not claimed at all:** constant-time behaviour or any other resistance to
side channels, and bug-for-bug agreement with the library a crate
replaces. Where a crate is stricter than the original, or differs from it,
its README lists how. The tests, fuzzers and differential tests against
the original libraries are evidence about the unverified parts. They are
not proofs.

## The crates

| Crate | What it is | Proof notes |
|---|---|---|
| [`verilith-archive`](crates/archive) | Formally verified (Verus) zip and tar readers with proven extraction safety, behind libarchive's read API | [proven](crates/archive#what-is-proven), [trusted](crates/archive/TRUST.md) |
| [`verilith-bind`](crates/bind) | One native library and C ABI for the Verilith parsers, with C++, Python and Node.js bindings on top | [not verified](crates/bind#what-is-not-verified) |
| [`verilith-brotli`](crates/brotli) | A formally verified (Verus) Brotli (RFC 7932) decompressor with google/brotli's decoder C API | [proven](crates/brotli#what-is-proven), [trusted](crates/brotli#trusted) |
| [`verilith-core`](crates/core) | Formally verified (Verus) building blocks shared by the Verilith libraries: trusted memory primitives, byte and bit readers, canonical Huffman tables, UTF-8 validation, CRC-32, CRC-32C and Adler-32 | [trusted](crates/core#trusted-base) |
| [`verilith-dns`](crates/dns) | A formally verified (Verus) DNS message parser and serializer, and a drop-in parser for c-ares | [proven](crates/dns#what-is-proven), [trusted](crates/dns#trusted-computing-base) |
| [`verilith-font`](crates/font) | A formally verified (Verus) OpenType font sanitizer | [proven](crates/font#what-is-proven), [trusted](crates/font/TRUST.md) |
| [`verilith-gif`](crates/gif) | A formally verified (Verus) GIF decoder: LZW, interlacing and graphic control, checked against giflib | [proven](crates/gif#what-is-proven), [trusted](crates/gif#trusted-base) |
| [`verilith-hpack`](crates/hpack) | An HPACK (RFC 7541) header decoder formally verified with Verus, with nghttp2's inflater API | [proven](crates/hpack#what-is-proven), [trusted](crates/hpack#trusted-computing-base) |
| [`verilith-http`](crates/http) | A fast HTTP/1.1 parser formally verified with Verus | [proven](crates/http#what-is-proven), [trusted](crates/http#trusted-computing-base) |
| [`verilith-jpeg`](crates/jpeg) | A formally verified (Verus) JPEG decoder: baseline and progressive Huffman | [proven](crates/jpeg#what-is-proven), [trusted](crates/jpeg/TRUST.md) |
| [`verilith-json`](crates/json) | A fast JSON parser, proven correct with Verus: exactly RFC 8259, no panics, bounded recursion. Includes serde support and a cJSON-compatible C ABI. | [proven](crates/json#what-is-proven), [trusted](crates/json#what-is-not-proven) |
| [`verilith-lz4`](crates/lz4) | A formally verified (Verus) LZ4 compressor and decompressor (block and frame formats) with liblz4's C API | [proven](crates/lz4#what-is-proven), [trusted](crates/lz4/TRUST.md) |
| [`verilith-png`](crates/png) | A formally verified (Verus) PNG decoder | [proven](crates/png#what-is-proven), [trusted](crates/png#trusted-base) |
| [`verilith-regex`](crates/regex) | A linear-time regular expression engine (RE2 syntax and semantics) formally verified with Verus | [proven](crates/regex#what-is-proven), [trusted](crates/regex/TRUST.md) |
| [`verilith-sha2`](crates/sha2) | Formally verified (Verus) SHA-2 (FIPS 180-4): SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256, with SHA-NI and ARMv8 kernels, behind OpenSSL's `SHA*` C API | [proven](crates/sha2#what-is-proven), [trusted](crates/sha2#trusted-base) |
| [`verilith-simd`](crates/simd) | Verus specifications for x86 SIMD intrinsics (SSE2..AVX2, some AVX-512), differentially tested against the CPU | [trusted](crates/simd#trusted-base) |
| [`verilith-snappy`](crates/snappy) | A formally verified (Verus) Snappy compressor and decompressor with the snappy-c API | [proven](crates/snappy#what-is-proven), [trusted](crates/snappy/TRUST.md) |
| [`verilith-sync`](crates/sync) | Formally verified (Verus) concurrency primitives: SPSC and MPMC queues, channels, and locks, as drop-ins for rtrb, crossbeam and parking_lot | [proven](crates/sync#what-is-proven), [trusted](crates/sync/TRUST.md) |
| [`verilith-text`](crates/text) | Formally verified (Verus) text encodings and Unicode: base64, hex, percent-encoding, Unicode normalization and IDNA (UTS #46) | [proven](crates/text#what-is-proven), [trusted](crates/text#the-trusted-base) |
| [`verilith-url`](crates/url) | A formally verified (Verus) WHATWG URL parser | [proven](crates/url#what-is-proven), [trusted](crates/url#trusted-computing-base) |
| [`verilith`](crates/verilith) | Formally verified (Verus) drop-in replacements for foundational libraries: one crate that re-exports each verilith-* library behind a feature | no code of its own |
| [`verilith-wasm`](crates/wasm) | A formally verified (Verus) WebAssembly validator and sandboxed interpreter | [proven](crates/wasm#what-is-proven), [trusted](crates/wasm#trusted-base) |
| [`verilith-webp`](crates/webp) | A formally verified (Verus) WebP lossless (VP8L) decoder | [proven](crates/webp#what-is-proven), [trusted](crates/webp#trusted-base) |
| [`verilith-x509`](crates/x509) | A formally verified (Verus) DER and X.509 certificate parser | [proven](crates/x509#what-is-proven) |
| [`verilith-xml`](crates/xml) | A fast XML 1.0 parser formally verified with Verus: exactly the well-formedness rules, no panics, no recursion | [proven](crates/xml#what-is-proven), [trusted](crates/xml#what-is-not-proven) |
| [`verilith-xxhash`](crates/xxhash) | Formally verified (Verus) XXH32 and XXH64, the checksums of the LZ4 and Zstandard frame formats | [proven](crates/xxhash#what-is-proven), [trusted](crates/xxhash#trusted-base) |
| [`verilith-zlib`](crates/zlib) | A formally verified (Verus) DEFLATE, zlib and gzip decompressor | [proven](crates/zlib#what-is-proven), [trusted](crates/zlib#trusted-base) |
| [`verilith-zstd`](crates/zstd) | A formally verified (Verus) Zstandard (RFC 8878) decompressor with libzstd's C API | [proven](crates/zstd#what-is-proven), [trusted](crates/zstd#trusted-base) |

`verilith` is a front door only: it re-exports the others behind features,
none on by default, and has no code of its own.

```toml
# Until the crates are on crates.io, depend on the repository:
verilith = { git = "https://github.com/verilith/verilith", features = ["json", "zlib"] }   # verilith::json, verilith::zlib
verilith-json = { git = "https://github.com/verilith/verilith" }                           # or one library directly
```

## Benchmarks

Each library is measured against the one it replaces by the harness in
[`bench/`](bench), and each number is one of two kinds, never mixed:

- **drop-in**: our library behind the original's API. Both sides are the
  same driver source linked against a different library. This is what a
  caller gets by relinking and changing nothing.
- **native**: the same task through our library's own API, against the
  original through its own best API. This is the speed after porting the
  calling code.

The table is one run of `bench/run.sh` at commit `bcfd98c` (2026-11-22) on
an Apple M3 Pro laptop (macOS, Apple clang, both sides built from source
with the same compiler and flags). Speedup is the original's time divided
by ours, as the geometric mean over the comparison's cases, so above 1.00x
ours is faster and below it the original is.

| Comparison | Kind | Original | Speedup |
|---|---|---|---:|
| zlib-inflate | drop-in | zlib 1.4 | 2.00x |
| zlib-deflate (levels 1, 6, 9) | drop-in | zlib 1.4 | 1.53x |
| brotli-decode | drop-in | brotli 1.2.1 | 0.95x |
| lz4-decompress | drop-in | lz4 1.11.1 | 1.10x |
| lz4-compress | drop-in | lz4 1.11.1 | 0.97x |
| lz4-frame-decompress | drop-in | lz4 1.11.1 | 1.09x |
| lz4-frame-compress | drop-in | lz4 1.11.1 | 0.94x |
| snappy-uncompress | drop-in | snappy 1.3.1 | 0.93x |
| snappy-validate | drop-in | snappy 1.3.1 | 0.97x |
| snappy-compress | drop-in | snappy 1.3.1 | 0.91x |
| archive-read | drop-in | libarchive 3.8.11 | 4.06x |
| dns-parse | drop-in | c-ares | 1.25x |
| dns-write | drop-in | c-ares | 1.17x |
| dns-read | drop-in | c-ares | 1.23x |
| dns-native | native | c-ares | 14.33x |
| http-llhttp | drop-in | llhttp 9.4.4 | 1.17x |
| http-llhttp-native | native | llhttp 9.4.4 | 2.05x |
| http-pico | drop-in | picohttpparser | 1.33x |
| http-pico-native | native | picohttpparser | 1.48x |
| url-ada | drop-in | ada 4.1.1 | 0.82x |
| json-cjson-parse | drop-in | cJSON 1.7.19 | 1.31x |
| json-cjson-print | drop-in | cJSON 1.7.19 | 1.56x |
| json-cjson-native | native | cJSON 1.7.19 | 6.66x |
| json-simdjson | native | simdjson 5.2.0 (DOM) | 1.07x |
| xml-expat-read | native | expat 2.10.0 | 1.35x |
| xml-expat-check | native | expat 2.10.0 | 2.23x |
| xml-libxml2-read | native | libxml2 2.15.4 | 1.14x |
| xml-libxml2-check | native | libxml2 2.15.4 | 1.72x |
| x509-mbedtls | drop-in | mbedTLS 4.3.0 | 1.02x |
| x509-mbedtls-read | drop-in | mbedTLS 4.3.0 | 1.01x |
| x509-mbedtls-native | native | mbedTLS 4.3.0 | 4.43x |
| x509-verdict | native | Verdict | 32.15x |
| png-libpng | native | libpng 1.6.59 | 1.41x |
| webp-lossless | drop-in | libwebp 1.6.0 | 1.08x |
| webp-lossy | drop-in | libwebp 1.6.0 | 0.98x |
| jpeg-baseline | drop-in | libjpeg-turbo 3.2.1 | 0.91x |
| jpeg-progressive | drop-in | libjpeg-turbo 3.2.1 | 0.95x |
| jpeg-444 | drop-in | libjpeg-turbo 3.2.1 | 0.97x |
| font-sanitize | drop-in | OTS | 1.19x |
| regex-re2 | drop-in | RE2 2025-11-05 | 5.70x |

How to read it:

- **One machine, one run.** These are laptop numbers from a single sitting.
  On another CPU the order can change, and a difference of a few percent is
  within what a rerun moves.
- **The native numbers against cJSON, c-ares and mbedTLS are mostly about
  allocation.** Those libraries build a tree, or decode more than was asked
  for, on every parse, and their APIs give no way to skip it. Ours parse
  into buffers the caller reuses. The mbedTLS native number is an upper
  bound for that reason.
- **archive-read** does not compare equal work: verilith-archive checks the
  whole archive when it is opened, where libarchive streams.
- **url-ada is now below 1.00x.** The previous run measured 1.55x against
  ada 3.4.4; against ada 4.1.1 vurl is slower: it runs 28 to 32% more
  instructions per URL, with the same results on both sides. The
  [crate's own measurement](crates/url#speed) against ada 4.0.0 on x86
  shows the same direction (0.92x).
- **x509 rows come from a second run** of `bench/run.sh --only x509` on
  the same machine, after a fix to the bench script's mbedTLS 4 build (a
  missing Python module); the library code is the same.
- **Inside Node.js.** Node 26.13.1 built with verilith-http, -url, -json,
  -dns and -zlib in place of llhttp, ada, simdjson, c-ares and zlib runs
  Node's own URL, HTTP-parser and zlib benchmarks at 0.50x to 1.64x of the
  official build. The HTTP parser is 1.02x to 1.03x and inflate 1.01x;
  `URL.canParse` on long, `ws:` and dotted URLs (0.50x to 0.60x) and
  `deflate` (0.83x) are the slowest cases. Every row is in the run's
  `report.md` ([Node.js](bench#nodejs)).

**How it is measured.** For each case both libraries run as long-lived
processes. After a warm-up, the harness takes 31 timed samples of each,
alternating which goes first (A B, B A, ...), so drift on the machine hits
both sides equally. The speedup of a case is the median of the 31 paired
ratios, with a distribution-free 95% confidence interval; a case whose
interval contains 1.00x is reported as "no measurable difference".
Instructions and cycles per call are recorded next to every sample. A
check value (output size, a checksum of the decoded pixels, the number of
records parsed) must match between the two sides. Every original library
is pinned by tag or commit in [`bench/pins.sh`](bench/pins.sh) and every
input file by SHA-256. [`bench/README.md`](bench/README.md) has the full
method, what one call does in each comparison, the inputs, and how to run
it yourself.

## Layout

```
crates/<name>/     one library: src/, tests/, its own README, scripts/, ci.sh
crates/verilith/   the umbrella crate
bench/             the benchmark harness: each library against the one it replaces
scripts/           verify.sh, prove.sh, profile, and what CI runs
verus/             the Buck2 rules that run Verus (see BUILDING.md)
third-party/       what the proofs need from crates.io, for Buck2 (generated)
IMPORT.md          the repositories and commits this one was assembled from
THIRD-PARTY.md     what comes from other projects, and under which licence
SECURITY.md        how to report a vulnerability
```

Some crates also hold separate Cargo projects (`bench/`, `fuzz/`,
`compat/`). Those are not workspace members: they have their own
dependencies and are built from their own directory.

## Building and testing

Work on one crate at a time, from its directory or with `-p`:

```sh
cd crates/zlib
cargo test --release
./ci.sh                     # everything CI runs for this crate
```

Avoid `cargo build --workspace` with features: several crates have a feature
that exports the original library's symbol names (`zlib-abi`, `llhttp-abi`),
and Cargo would turn those on for every crate built in the same command.

**Profiles.** Cargo takes profiles from the workspace, not from each crate.
The workspace defines three release profiles, and each crate's scripts use
the one `scripts/profile <name>` prints:

| Profile | Settings | Crates |
|---|---|---|
| `release` | 1 codegen unit, thin LTO | every crate not listed below |
| `release-fat` | 1 codegen unit, fat LTO | text, url, x509 |
| `release-abort` | 1 codegen unit, fat LTO, `panic = "abort"` | json, http, hpack, regex, bind, xml |

So the drop-in JSON library is built with
`cargo build --profile release-abort --features cjson` and lands in
`target/release-abort/libverilith_json.a`.

## Verifying

Every crate is verified with one Verus version: the commit in
`scripts/verus-version`, whose `vstd` release is pinned in the workspace
`Cargo.toml`. Build Verus from that commit and put its directory on `PATH`.
There are two ways to run it, and they check the same proofs:

```sh
scripts/verify.sh            # with cargo verus: every crate, dependencies first
scripts/verify.sh json png   # some

scripts/prove.sh             # with Buck2: every crate
scripts/prove.sh json png    # some
```

Both fail unless each crate reports 0 errors. `cargo verus` is the way the
Verus project supports. Buck2 knows exactly which files each proof is built
from, so it skips what has not changed and can check a large crate in
parts; CI uses it. [BUILDING.md](BUILDING.md) explains the Buck2 setup and
what keeps it from passing a proof it did not check.

## CI

One workflow, `.github/workflows/ci.yml`.

**Proofs** run through Buck2, one job per crate, or per part for the crates
verified in parts (brotli). A proof that has already passed with
exactly the same inputs is not checked again (`scripts/proof-plan.py`), so
a change to one crate checks that crate and the crates that depend on it,
and a second push to a pull request checks only what the push changed.
Pushes to main also verify on Apple Silicon, with `cargo verus`.

**Tests** run for the crates a change touches: a crate whose files changed,
plus every crate that depends on it (`scripts/affected.py`). A change to
the workspace files runs everything. What runs for a crate is its `ci.sh`.

**Once a week**, and on request (run the workflow with "fresh"), every proof
is checked again from nothing and each crate's count of verified proofs
under Buck2 is compared with the count from `cargo verus`
(`scripts/crosscheck.sh`).

## Security

To report a vulnerability, see [SECURITY.md](SECURITY.md). Please do not
open a public issue for one.

## License

MIT, in [LICENSE](LICENSE). Some crates include test data, tables or
headers from other projects under those projects' licences: MIT,
BSD-3-Clause, Apache-2.0 and Unicode-3.0. [THIRD-PARTY.md](THIRD-PARTY.md)
lists each one, and the licence text is in a `LICENSE-*` file in the crate
that holds it.

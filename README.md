# Verilith

Formally verified drop-in replacements for foundational open source
libraries, written in Rust and proven with [Verus](https://github.com/verus-lang/verus).

Each library is its own crate, verified and versioned on its own, and most
also build a static library behind the C API of the library they replace
(zlib, cJSON, llhttp, c-ares, libpng and so on), so existing C and C++
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
| [`verilith-core`](crates/core) | Formally verified (Verus) building blocks shared by the Verilith libraries: trusted memory primitives, byte and bit readers, canonical Huffman tables, UTF-8 validation, CRC-32 and Adler-32 | [trusted](crates/core#trusted-base) |
| [`verilith-dns`](crates/dns) | A formally verified (Verus) DNS message parser and serializer, and a drop-in parser for c-ares | [proven](crates/dns#what-is-proven), [trusted](crates/dns#trusted-computing-base) |
| [`verilith-font`](crates/font) | A formally verified (Verus) OpenType font sanitizer | [proven](crates/font#what-is-proven), [trusted](crates/font/TRUST.md) |
| [`verilith-hpack`](crates/hpack) | An HPACK (RFC 7541) header decoder formally verified with Verus, with nghttp2's inflater API | [proven](crates/hpack#what-is-proven), [trusted](crates/hpack#trusted-computing-base) |
| [`verilith-http`](crates/http) | A fast HTTP/1.1 parser formally verified with Verus | [proven](crates/http#what-is-proven), [trusted](crates/http#trusted-computing-base) |
| [`verilith-jpeg`](crates/jpeg) | A formally verified (Verus) JPEG decoder: baseline and progressive Huffman | [proven](crates/jpeg#what-is-proven), [trusted](crates/jpeg/TRUST.md) |
| [`verilith-json`](crates/json) | A fast JSON parser, proven correct with Verus: exactly RFC 8259, no panics, bounded recursion. Includes serde support and a cJSON-compatible C ABI. | [proven](crates/json#what-is-proven), [trusted](crates/json#what-is-not-proven) |
| [`verilith-lz4`](crates/lz4) | A formally verified (Verus) LZ4 compressor and decompressor (block and frame formats) with liblz4's C API | [proven](crates/lz4#what-is-proven), [trusted](crates/lz4/TRUST.md) |
| [`verilith-png`](crates/png) | A formally verified (Verus) PNG decoder | [proven](crates/png#what-is-proven), [trusted](crates/png#trusted-base) |
| [`verilith-regex`](crates/regex) | A linear-time regular expression engine (RE2 syntax and semantics) formally verified with Verus | [proven](crates/regex#what-is-proven), [trusted](crates/regex/TRUST.md) |
| [`verilith-simd`](crates/simd) | Verus specifications for x86 SIMD intrinsics (SSE2..AVX2, some AVX-512), differentially tested against the CPU | [trusted](crates/simd#trusted-base) |
| [`verilith-snappy`](crates/snappy) | A formally verified (Verus) Snappy compressor and decompressor with the snappy-c API | [proven](crates/snappy#what-is-proven), [trusted](crates/snappy/TRUST.md) |
| [`verilith-sync`](crates/sync) | Formally verified (Verus) concurrency primitives: SPSC and MPMC queues, channels, and locks, as drop-ins for rtrb, crossbeam and parking_lot | [proven](crates/sync#what-is-proven), [trusted](crates/sync/TRUST.md) |
| [`verilith-text`](crates/text) | Formally verified (Verus) text encodings and Unicode: base64, hex, percent-encoding, Unicode normalization and IDNA (UTS #46) | [proven](crates/text#what-is-proven), [trusted](crates/text#the-trusted-base) |
| [`verilith-url`](crates/url) | A formally verified (Verus) WHATWG URL parser | [proven](crates/url#what-is-proven), [trusted](crates/url#trusted-computing-base) |
| [`verilith`](crates/verilith) | Formally verified (Verus) drop-in replacements for foundational libraries: one crate that re-exports each verilith-* library behind a feature | no code of its own |
| [`verilith-wasm`](crates/wasm) | A formally verified (Verus) WebAssembly validator and sandboxed interpreter | [proven](crates/wasm#what-is-proven), [trusted](crates/wasm#trusted-base) |
| [`verilith-webp`](crates/webp) | A formally verified (Verus) WebP lossless (VP8L) decoder | [proven](crates/webp#what-is-proven), [trusted](crates/webp#trusted-base) |
| [`verilith-x509`](crates/x509) | A formally verified (Verus) DER and X.509 certificate parser | [proven](crates/x509#what-is-proven) |
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

The table is one run of `bench/run.sh --skip-node` at commit `b0c1452` on
an Apple M3 Pro laptop (macOS, Apple clang, both sides built from source
with the same compiler and flags). Speedup is the original's time divided
by ours, as the geometric mean over the comparison's cases, so above 1.00x
ours is faster and below it the original is.

| Comparison | Kind | Original | Speedup |
|---|---|---|---:|
| zlib-inflate | drop-in | zlib 1.3.2 | 2.089x |
| zlib-deflate (levels 1, 6, 9) | drop-in | zlib 1.3.2 | 1.548x |
| brotli-decode | drop-in | brotli 1.2.0 | 0.952x |
| lz4-decompress | drop-in | lz4 1.10.0 | 0.907x |
| lz4-compress | drop-in | lz4 1.10.0 | 0.961x |
| lz4-frame-decompress | drop-in | lz4 1.10.0 | 0.936x |
| lz4-frame-compress | drop-in | lz4 1.10.0 | 0.941x |
| snappy-uncompress | drop-in | snappy 1.2.2 | 0.928x |
| snappy-validate | drop-in | snappy 1.2.2 | 0.974x |
| snappy-compress | drop-in | snappy 1.2.2 | 0.914x |
| archive-read | drop-in | libarchive 3.8.9 | 4.366x |
| dns-parse | drop-in | c-ares | 1.231x |
| dns-write | drop-in | c-ares | 1.158x |
| dns-read | drop-in | c-ares | 1.22x |
| dns-native | native | c-ares | 14.44x |
| http-llhttp | drop-in | llhttp 9.4.3 | 1.170x |
| http-llhttp-native | native | llhttp 9.4.3 | 2.07x |
| http-pico | drop-in | picohttpparser | 1.353x |
| http-pico-native | native | picohttpparser | 1.49x |
| url-ada | drop-in | ada 3.4.4 | 1.545x |
| json-cjson-parse | drop-in | cJSON 1.7.19 | 1.316x |
| json-cjson-print | drop-in | cJSON 1.7.19 | 1.547x |
| json-cjson-native | native | cJSON 1.7.19 | 6.47x |
| json-simdjson | native | simdjson 5.1.1 (DOM) | 1.066x |
| x509-mbedtls | drop-in | mbedTLS 3.6.4 | 1.001x |
| x509-mbedtls-read | drop-in | mbedTLS 3.6.4 | 0.98x |
| x509-mbedtls-native | native | mbedTLS 3.6.4 | 3.16x |
| x509-verdict | native | Verdict | 32.679x |
| png-libpng | native | libpng 1.6.59 | 1.407x |
| webp-lossless | drop-in | libwebp 1.6.0 | 1.104x |
| webp-lossy | drop-in | libwebp 1.6.0 | 0.970x |
| jpeg-baseline | drop-in | libjpeg-turbo 3.1.2 | 0.956x |
| jpeg-progressive | drop-in | libjpeg-turbo 3.1.2 | 0.953x |
| jpeg-444 | drop-in | libjpeg-turbo 3.1.2 | 0.946x |
| font-sanitize | drop-in | OTS | 1.183x |
| regex-re2 | drop-in | RE2 2025-11-05 | 5.308x |

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
- **The code has moved since.** `main` is past `b0c1452`; the regex matcher
  in particular has changed.

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
scripts/           verify.sh, profile, affected.py (what CI runs)
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
| `release-abort` | 1 codegen unit, fat LTO, `panic = "abort"` | json, http, hpack, regex, bind |

So the drop-in JSON library is built with
`cargo build --profile release-abort --features cjson` and lands in
`target/release-abort/libverilith_json.a`.

## Verifying

Every crate is verified with one Verus version: the commit in
`scripts/verus-version`, whose `vstd` release is pinned in the workspace
`Cargo.toml`. Build Verus from that commit, put `cargo-verus` on `PATH`,
then:

```sh
scripts/verify.sh            # every crate, dependencies first
scripts/verify.sh json png   # some
```

It fails unless each crate reports 0 errors.

## CI

One workflow verifies and tests only the crates a change touches: a crate
whose files changed, plus every crate that depends on it
(`scripts/affected.py`). A change to the workspace files runs everything.
What runs for a crate is that crate's `scripts/verify.sh` and `ci.sh`.

## Security

To report a vulnerability, see [SECURITY.md](SECURITY.md). Please do not
open a public issue for one.

## License

MIT, in [LICENSE](LICENSE). Some crates include test data, tables or
headers from other projects under those projects' licences: MIT,
BSD-3-Clause, Apache-2.0 and Unicode-3.0. [THIRD-PARTY.md](THIRD-PARTY.md)
lists each one, and the licence text is in a `LICENSE-*` file in the crate
that holds it.

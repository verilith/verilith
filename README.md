# Verilith

Formally verified drop-in replacements for foundational open source
libraries, written in Rust and proven with [Verus](https://github.com/verus-lang/verus).

Each library is its own crate, verified and versioned on its own, and most
also build a static library behind the C API of the library they replace
(zlib, cJSON, llhttp, c-ares, libpng and so on), so existing C and C++
callers can relink without changing code.

| Crate | What it is |
|---|---|
| [`verilith-archive`](crates/archive) | Formally verified (Verus) zip and tar readers with proven extraction safety, behind libarchive's read API |
| [`verilith-bind`](crates/bind) | One native library and C ABI for the Verilith parsers, with C++, Python and Node.js bindings on top |
| [`verilith-brotli`](crates/brotli) | A formally verified (Verus) Brotli (RFC 7932) decompressor with google/brotli's decoder C API |
| [`verilith-core`](crates/core) | Formally verified (Verus) building blocks shared by the verified-foundations libraries: trusted memory primitives, byte and bit readers, canonical Huffman tables, UTF-8 validation, CRC-32 and Adler-32 |
| [`verilith-dns`](crates/dns) | A formally verified (Verus) DNS message parser and serializer, and a drop-in parser for c-ares |
| [`verilith-font`](crates/font) | A formally verified (Verus) OpenType font sanitizer |
| [`verilith-hpack`](crates/hpack) | An HPACK (RFC 7541) header decoder formally verified with Verus, with nghttp2's inflater API |
| [`verilith-http`](crates/http) | A fast HTTP/1.1 parser formally verified with Verus |
| [`verilith-jpeg`](crates/jpeg) | A formally verified (Verus) JPEG decoder: baseline and progressive Huffman |
| [`verilith-json`](crates/json) | A fast JSON parser, proven correct with Verus: exactly RFC 8259, no panics, bounded recursion. Includes serde support and a cJSON-compatible C ABI. |
| [`verilith-lz4`](crates/lz4) | A formally verified (Verus) LZ4 compressor and decompressor (block and frame formats) with liblz4's C API |
| [`verilith-png`](crates/png) | A formally verified (Verus) PNG decoder |
| [`verilith-regex`](crates/regex) | A linear-time regular expression engine (RE2 syntax and semantics) formally verified with Verus |
| [`verilith-simd`](crates/simd) | Verus specifications for x86 SIMD intrinsics (SSE2..AVX2, some AVX-512), differentially tested against the CPU |
| [`verilith-snappy`](crates/snappy) | A formally verified (Verus) Snappy compressor and decompressor with the snappy-c API |
| [`verilith-sync`](crates/sync) | Formally verified (Verus) concurrency primitives: SPSC and MPMC queues, channels, and locks, as drop-ins for rtrb, crossbeam and parking_lot |
| [`verilith-text`](crates/text) | Formally verified (Verus) text encodings and Unicode: base64, hex, percent-encoding, Unicode normalization and IDNA (UTS #46) |
| [`verilith-url`](crates/url) | A formally verified (Verus) WHATWG URL parser |
| [`verilith`](crates/verilith) | Formally verified (Verus) drop-in replacements for foundational libraries: one crate that re-exports each verilith-* library behind a feature |
| [`verilith-wasm`](crates/wasm) | A formally verified (Verus) WebAssembly validator and sandboxed interpreter |
| [`verilith-webp`](crates/webp) | A formally verified (Verus) WebP lossless (VP8L) decoder |
| [`verilith-x509`](crates/x509) | A formally verified (Verus) DER and X.509 certificate parser |
| [`verilith-xml`](crates/xml) | A fast XML 1.0 parser formally verified with Verus: exactly the well-formedness rules, no panics, no recursion |
| [`verilith-zlib`](crates/zlib) | A formally verified (Verus) DEFLATE, zlib and gzip decompressor |
| [`verilith-zstd`](crates/zstd) | A formally verified (Verus) Zstandard (RFC 8878) decompressor with libzstd's C API |

`verilith` is a front door only: it re-exports the others behind features,
none on by default, and has no code of its own.

```toml
verilith = { version = "0.1", features = ["json", "zlib"] }   # verilith::json, verilith::zlib
verilith-json = "0.1"                                          # or one library directly
```

## Layout

```
crates/<name>/     one library: src/, tests/, its own README, scripts/, ci.sh
crates/verilith/   the umbrella crate
bench/             the benchmark harness: each library against the one it replaces
scripts/           verify.sh, prove.sh, profile, and what CI runs
verus/             the Buck2 rules that run Verus (see BUILDING.md)
third-party/       what the proofs need from crates.io, for Buck2 (generated)
IMPORT.md          the repositories and commits this one was assembled from
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

## License

MIT. Some crates include data or test files under other licenses, noted in
a `LICENSE-*` file in that crate.

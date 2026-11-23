# verilith-xxhash

XXH32 and XXH64, in Rust, proven with
[Verus](https://github.com/verus-lang/verus) to compute exactly the
functions of the xxHash specification (`doc/xxhash_spec.md` in the
[xxHash](https://github.com/Cyan4973/xxHash) repository). These are the
checksums of the LZ4 frame format (XXH32) and of Zstandard frames
(XXH64). [verilith-lz4](https://github.com/verilith/verilith/tree/main/crates/lz4) and [verilith-zstd](https://github.com/verilith/verilith/tree/main/crates/zstd) take both the
code and the specification from here. They are fast checksums, not
cryptographic hashes.

`cargo verus verify` (or `scripts/verify.sh`) checks 70 functions and
lemmas with no errors, no `assume` and no `external_body` in this crate.

The proofs are checked once per pointer width: CI also runs Verus
compiling for `wasm32-unknown-unknown`, where `usize` is 32 bits
(`scripts/verify-narrow.sh`), so the crate builds for wasm32 (browsers,
Cloudflare Workers) and is proven as built there. Its tests also pass on
`wasm32-wasip1` under wasmtime (`scripts/wasm32.sh` at the root).

```rust
use std::hash::Hasher;
use verilith_xxhash::{xxh32, xxh64, XxHash64};

assert_eq!(xxh32(b"abc", 0), 0x32D153FF);
assert_eq!(xxh64(b"abc", 0), 0x44BC2CF5AD770999);
assert_eq!(xxh64(b"abc", 1), xxhash_rust::xxh64::xxh64(b"abc", 1));

// XXH64 of input that comes in pieces, and a std::hash::Hasher.
let mut h = XxHash64::with_seed(0);
h.write(b"ab");
h.write(b"c");
assert_eq!(h.finish(), 0x44BC2CF5AD770999);
```

`Xxh64` is the same streaming hash with the proof's ghost arguments
showing, for callers that are verified with Verus themselves
(verilith-zstd is one).

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds read, no overflow, no panic | every function (Verus checks all indexing and arithmetic) |
| Termination of every loop | every function (`decreases`) |
| XXH32 of a slice, with any seed | `xxh32::xxh32_with_seed` against `spec::xxh32_seed`, and seed 0 against `spec::xxh32` |
| XXH64 of a slice, with any seed | `xxh64::xxh64_with_seed` against `spec::xxh64_seed`, and seed 0 against `spec::xxh64` |
| XXH64 fed in pieces of any sizes, in order, is XXH64 of all of them. Whole stripes are hashed straight from the caller's slice, and only the last partial stripe (under 32 bytes) is kept | `xxh64::Xxh64::update` and `digest` against `spec::xxh64_seed`, with the invariant `Xxh64::is_seeded`; `XxHash64` keeps the ghost state itself |

## Layout

- `src/spec.rs`: XXH32 and XXH64 as spec functions, named after the
  specification's constants and steps: the four accumulators, the
  stripes, the merge (XXH64), the remaining bytes and the avalanche.
- `src/xxh32.rs`: XXH32 of a slice.
- `src/xxh64.rs`: XXH64 of a slice, and the streaming `Xxh64`.
- `src/bytes.rs`: the spec's little-endian numbers are verilith-core's.

## Trusted base

- `src/spec.rs`: the specification. `tests/vectors.rs` checks the code,
  and so the specification, against published values and against an
  independent implementation (xxhash-rust) on every length up to 600
  bytes and on streamed input split every way.
- From [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core#trusted-base): `load_u64_le`, an unaligned
  8-byte load (`external_body`). `load32` and `get` are verified in
  verilith-core.
- Verus, vstd, Z3, and the Rust compiler.

## Not here yet

- Streaming XXH32 (verilith-lz4 hashes whole blocks and whole frames).
- XXH3 and XXH128.
- libxxhash's C API.

## Tests

```sh
cargo test --release
./ci.sh
```

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/xxhash/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/xxhash/LICENSE-MIT), at your option.

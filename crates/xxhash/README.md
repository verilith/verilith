# verilith-xxhash

XXH32 and XXH64 with seed 0, in Rust, proven with
[Verus](https://github.com/verus-lang/verus) to compute exactly the
functions of the xxHash specification (`doc/xxhash_spec.md` in the
[xxHash](https://github.com/Cyan4973/xxHash) repository). These are the
checksums of the LZ4 frame format (XXH32) and of Zstandard frames
(XXH64). [verilith-lz4](../lz4) and [verilith-zstd](../zstd) take both the
code and the specification from here. They are fast checksums, not
cryptographic hashes.

`cargo verus verify` (or `scripts/verify.sh`) checks 60 functions and
lemmas with no errors, no `assume` and no `external_body` in this crate.

```rust
use verilith_xxhash::{xxh32_exec, xxh64_exec, Xxh64};
use vstd::prelude::Ghost;

assert_eq!(xxh32_exec(b"abc"), 0x32D153FF);
assert_eq!(xxh64_exec(b"abc"), 0x44BC2CF5AD770999);

// XXH64 of input that comes in pieces. The ghost argument (what was
// hashed before) exists only for the proof; outside Verus it is erased.
let mut h = Xxh64::new();
h.update(b"ab", Ghost::assume_new());
h.update(b"c", Ghost::assume_new());
assert_eq!(h.digest(Ghost::assume_new()), 0x44BC2CF5AD770999);
```

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds read, no overflow, no panic | every function (Verus checks all indexing and arithmetic) |
| Termination of every loop | every function (`decreases`) |
| XXH32 of a slice | `xxh32::xxh32_exec` against `spec::xxh32` |
| XXH64 of a slice | `xxh64::xxh64_exec` against `spec::xxh64` |
| XXH64 fed in pieces of any sizes, in order, is XXH64 of all of them. Whole stripes are hashed straight from the caller's slice, and only the last partial stripe (under 32 bytes) is kept | `xxh64::Xxh64::update` and `digest` against `spec::xxh64`, with the invariant `Xxh64::is` |

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
  bytes and on streamed input split every way. `spec-tests/` checks the
  specification on its own, with no code and no proof in between: Verus
  evaluates `spec::xxh32` and `spec::xxh64` on xxHash's sanity test
  vectors (`tests/sanity_test_vectors.h`, seed 0, every length up to 256
  bytes: 514 cases), and every one agrees
  (`scripts/spec-tests.sh xxhash`, run in CI).
- From [verilith-core](../core#trusted-base): `load_u64_le`, an unaligned
  8-byte load (`external_body`). `load32` and `get` are verified in
  verilith-core.
- Verus, vstd, Z3, and the Rust compiler.

## Not here yet

- Seeds other than 0, which libxxhash's `XXH32` and `XXH64` take.
  verilith-lz4 and verilith-zstd only need seed 0.
- Streaming XXH32 (verilith-lz4 hashes whole blocks and whole frames).
- XXH3 and XXH128.
- libxxhash's C API.

## Tests

```sh
cargo test --release
./ci.sh
../../scripts/spec-tests.sh xxhash   # the spec itself on xxHash's sanity vectors
```

## License

Licensed under either of the [Apache License, Version 2.0](LICENSE-APACHE)
or the [MIT license](LICENSE-MIT), at your option.

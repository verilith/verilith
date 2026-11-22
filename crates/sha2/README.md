# verilith-sha2

SHA-224 and SHA-256 (FIPS 180-4) in Rust, proven with
[Verus](https://github.com/verus-lang/verus): the hash functions behind
TLS, X.509 signatures, Git's SHA-256 object format and most content
addressing. It uses the CPU's SHA instructions where there are any, and
it builds a static library behind OpenSSL's `SHA256_*` C API.

`cargo verus verify` (or `scripts/verify.sh`) checks 59 functions and
lemmas with no errors and no `assume`. The one `external_body` function
in this crate is the CPU dispatch for the compression function.

```rust
let d: [u8; 32] = verilith_sha2::sha256(b"abc");

let mut h = verilith_sha2::Sha256::new();
h.update(b"ab");
h.update(b"c");
assert_eq!(h.finalize(), d);
```

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds read or write, no overflow, no panic | every function in `compress` and `hash` (Verus checks all indexing and arithmetic) |
| Termination of every loop | every function (`decreases`) |
| The compression function computes FIPS 180-4 §6.2.2 steps 1 to 4 on a block | `compress::compress_block` against `spec::compress` |
| Over many blocks, it computes H(n) from H(0) | `compress::compress_blocks` against `spec::hash_blocks` |
| Ch and Maj in their one-operation-shorter forms are Ch and Maj | `compress::ch`, `compress::maj` (bit-vector proofs) |
| Whatever the sizes of the pieces given to `update`, `finalize` returns the hash of all of them in order: padding (§5.1.1), the bit length modulo 2^64, one or two final blocks | `Sha256::finalize` against `spec::sha256`, `Sha224::finalize` against `spec::sha224` |
| The one-shot functions | `sha256` and `sha224` against the same |

## Layout

- `src/spec.rs`: FIPS 180-4 as spec functions, each naming the section it
  transcribes: the operations of §3.2 and functions of §4.1.2, the
  constants of §4.2.2 and §5.3, padding and parsing (§5.1.1, §5.2.1), the
  schedule, rounds and compression of §6.2.2, and the digests.
- `src/compress.rs`: the compression function. The eight working
  variables are eight locals that never move: round t updates d and h in
  place and the next round is called with the names rotated by one
  (`tools/gen_rounds.py` writes those calls, and `ci.sh` checks they are up
  to date). The schedule is a 16-word window. Each group of eight rounds
  is its own proof, so no single proof covers more than eight.
- `src/hash.rs`: the streaming hashers. Whole blocks of an `update` are
  compressed straight from the caller's slice, and only the last partial
  block is buffered.
- `src/cpu.rs`: the kernel dispatch and the SHA-NI and ARMv8 kernels
  (trusted, below).
- `src/capi.rs`: the C API (an unverified adapter).

## Trusted base

What the proofs here assume rather than prove:

- `src/spec.rs`: the specification. Its constants (K, and both H(0)) are
  also derived again from their definitions, the fractional parts of cube
  and square roots of primes, by `tests/vectors.rs` with exact integer
  roots.
- `src/cpu.rs`, the one `external_body` function `compress_blocks`: that
  the SHA-NI kernel (x86-64) and the ARMv8 SHA2 kernel (AArch64) compute
  what the verified portable kernel computes. They are tested against it
  (`tests/kernels.rs`: every length up to 40 blocks, from random states)
  and against RustCrypto's `sha2` and OpenSSL. CI runs the ARMv8 kernel
  on an Arm runner and under qemu. Without those instructions the verified
  kernel runs, with nothing assumed.
- From [verilith-core](../core): `prims::copy_in` (trusted, one
  `copy_nonoverlapping`). `prims::get` is verified there.
- vstd's specifications of `slice_subrange`, `wrapping_add` and
  `wrapping_mul`.
- `src/capi.rs`: the C API is not verified. It converts pointers to slices
  and stores the hasher in the caller's context.
- Verus, Z3 and the Rust compiler.

## C API

`SHA256_Init`, `SHA256_Update`, `SHA256_Final`, `SHA256`, and the same
four for SHA-224, with OpenSSL's signatures and return values. They are
exported as `vsha2_SHA256_Init` and so on. With the `openssl-abi`
feature they take OpenSSL's own names, so the static library can be
linked ahead of libcrypto for these functions.

Departures from OpenSSL:

- `SHA256_CTX` has OpenSSL's size (112 bytes) and alignment, so callers'
  stack allocations are unchanged, but not its fields. Code that reads
  `h`, `Nl`, `Nh` or `num` directly gets other values.
- `SHA256_Transform` (one block, no padding) is not provided.
- `_Update` and `_Final` return 0, and do nothing, for a context whose
  buffered-byte count is out of range: one that `_Init` did not set up.
  OpenSSL's behaviour there is undefined.
- As in OpenSSL, `_Final` wipes the context, and the one-shot functions
  write to a static buffer when `md` is NULL (not thread safe).

## Tests

`cargo test --release`:

- `tests/vectors.rs`: the examples of FIPS 180-2 (Appendix B, and Change
  Notice 1 for SHA-224), including the million a's whole and in pieces,
  and the constants from their definitions.
- `tests/kernels.rs`: the CPU kernel against the verified one, and every
  length up to 4200, every split point of every length up to 300, and
  2000 random messages in random pieces against RustCrypto's `sha2`.
- `tests/openssl.rs`: the C API against the system libcrypto
  (`libcrypto.so.3`, or `VSHA2_LIBCRYPTO`) loaded with `dlopen`. That
  covers one-shot and streamed, every length up to 600 and some longer,
  in six patterns of pieces, plus the C API's edge cases.

## Performance

`cargo run --release --example speed` compares against RustCrypto's
`sha2` 0.10 and the system OpenSSL (3.0, through `SHA256()`). On an x86-64
cloud VM with SHA-NI, in MB/s, best of 15:

| bytes | verilith-sha2 | portable kernel alone | RustCrypto sha2 | OpenSSL |
| ---: | ---: | ---: | ---: | ---: |
| 64 | 483 | 242 | 592 | 139 |
| 1024 | 1299 | 242 | 1287 | 889 |
| 8192 | 1396 | 248 | 1385 | 1305 |
| 1 MiB | 1397 | 245 | 1407 | 1408 |

From 1 KiB up, the three run at the speed of the SHA instructions. Below
that, verilith-sha2 spends more per call than RustCrypto (about 25 ns at
64 bytes), which is not yet tuned. The verified portable kernel is what
runs on CPUs without SHA instructions.

## Not yet

- SHA-384 and SHA-512 (the 64-bit family), and HMAC.
- `no_std`: the crate needs `std` for run-time CPU detection.
- RustCrypto's `digest` traits, for a drop-in `sha2` replacement.
- A [vbench](../../bench) suite against OpenSSL through the drop-in C API.
- Verifying the SHA-NI and ARMv8 kernels, against specifications of the
  instructions in [verilith-simd](../simd), as verilith-core does for
  AArch64's `crc32x`.
- A proof that the portable kernel's time does not depend on the data. It
  has no branch or memory index that depends on the message, but this
  is by inspection, not proven.

## Verifying

```sh
./scripts/verify.sh
```

needs `cargo-verus` from Verus commit
8bf68ee741df833ea5d0fe6a2255126fdea87e47 on `PATH` and z3 (via
`VERUS_Z3_PATH` or next to the verus binary). From the repository root,
`scripts/prove.sh sha2` verifies it through Buck2.

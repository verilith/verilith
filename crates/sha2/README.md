# verilith-sha2

SHA-2 (FIPS 180-4) in Rust, proven with
[Verus](https://github.com/verus-lang/verus): SHA-224 and SHA-256, and
the 64-bit family SHA-384, SHA-512, SHA-512/224 and SHA-512/256. These
are the hash functions behind TLS, X.509 signatures, Ed25519 (SHA-512),
Git's SHA-256 object format and most content addressing. It uses the
CPU's SHA instructions where there are any, and it builds a static
library behind OpenSSL's `SHA224_*`, `SHA256_*`, `SHA384_*` and
`SHA512_*` C API.

`cargo verus verify` (or `scripts/verify.sh`) checks 154 functions and
lemmas with no errors and no `assume`. What is assumed instead is listed
under [Trusted base](#trusted-base): the CPU dispatch, the SHA instruction
kernels, the AVX2 message schedules, and two byte stores.

```rust
let d: [u8; 32] = verilith_sha2::sha256(b"abc");

let mut h = verilith_sha2::Sha256::new();
h.update(b"ab");
h.update(b"c");
assert_eq!(h.finalize(), d);

let d: [u8; 64] = verilith_sha2::sha512(b"abc");
let d: [u8; 48] = verilith_sha2::sha384(b"abc");
```

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds read or write, no overflow, no panic | every function in `compress` and `hash` (Verus checks all indexing and arithmetic) |
| Termination of every loop | every function (`decreases`) |
| The compression functions compute FIPS 180-4 §6.2.2 (SHA-256) and §6.4.2 (SHA-512) steps 1 to 4 on a block | `compress::compress_block` against `spec::compress`, `compress512::compress_block` against `spec512::compress` |
| Over many blocks, they compute H(n) from H(0) | `compress_blocks` in each, against `hash_blocks` |
| Ch and Maj in their one-operation-shorter forms are Ch and Maj | `ch`, `maj` in each (bit-vector proofs) |
| Whatever the sizes of the pieces given to `update`, `finalize` returns the hash of all of them in order: padding (§5.1.1, §5.1.2), the bit length modulo 2^64 or 2^128, one or two final blocks | `Sha256`, `Sha224` against `spec::sha256`, `spec::sha224`; `Sha512`, `Sha384`, `Sha512_224`, `Sha512_256` against `spec512::sha512`, `sha384`, `sha512_224`, `sha512_256` |
| The 128-bit byte count of the SHA-512 family, kept as two 64-bit halves, is the message length modulo 2^128 | `hash512::Engine512::add_count` |
| The rounds that take K_t + W_t precomputed, as a vectorized schedule gives it, are the rounds (addition modulo 2^n is associative) | `compress_block_kw` in each |
| The pipelined kernels: each pair of blocks is compressed while the next pair's schedule is computed between its round groups, and the loop over pairs computes H(n) | `pair_kw` and `compress_blocks_pipe` in each, given the AVX2 schedule's contract |
| The one-shot functions | `sha256`, `sha224`, `sha512`, `sha384`, `sha512_224`, `sha512_256` against the same |

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
- `src/spec512.rs`, `src/compress512.rs`, `src/hash512.rs`: the same for
  the 64-bit family, with 128-byte blocks, 80 rounds and a 128-bit
  length. The rounds are the same generated text over 64-bit words. The
  byte count is two 64-bit halves rather than a `u128`, so the hasher fits
  OpenSSL's 216-byte `SHA512_CTX`.
- `src/cpu.rs`: the kernel dispatch and the SHA-NI and ARMv8 kernels
  (trusted, below).
- `src/avx2.rs`: the AVX2 message schedules, two blocks at once, whole or
  a few words at a time for the pipelined kernels (trusted, below).
- `src/store.rs`: big-endian stores of a word (trusted, below).
- `src/capi.rs`: the C API (an unverified adapter).

## Trusted base

What the proofs here assume rather than prove:

- `src/spec.rs` and `src/spec512.rs`: the specification. The constants
  are also derived again from their definitions by `tests/vectors.rs` and
  `tests/vectors512.rs`: K and the SHA-224, SHA-256, SHA-384 and SHA-512
  H(0) come from the fractional parts of cube and square roots of primes,
  computed with exact integer roots, and the SHA-512/224 and SHA-512/256
  H(0) come from running FIPS 180-4's IV generation function (§5.3.6).
- `src/cpu.rs`, the two `external_body` functions `compress_blocks` and
  `compress512_blocks`: that the SHA-NI kernel (x86-64), the ARMv8 SHA2
  kernel and the ARMv8.2 SHA512 kernel (AArch64) compute what the
  verified portable kernels compute. They are tested against them
  (`tests/kernels.rs`, `tests/kernels512.rs`: every length up to 40 and
  24 blocks, from random states) and against RustCrypto's `sha2` and
  OpenSSL. CI runs the ARMv8 kernels on an Arm runner and under qemu.
  Without those instructions the verified kernels run, with nothing
  assumed. On x86-64 with BMI2 they run compiled a second time with BMI2
  enabled: the same verified code with other instruction selection, as
  verilith-core does for Adler-32 with AVX2, and tested the same way.
  `pair_avx2` and `pair256_avx2` are in the same position: each is the
  verified `pair_kw` compiled with AVX2 and out of line, trusted only to
  be that function.
- `src/avx2.rs`, eight `external_body` functions (`schedule512x2`,
  `sched_start`, `sched_steps2` and the three SHA-256 ones, and the opaque
  `Sched512`/`Sched256`): that they compute K_t + W_t as
  `spec512::schedule` and `spec::schedule` define them, which is what
  their `ensures` say. The rounds that use them are verified. They are
  tested against FIPS 180-4's schedule written out directly
  (`tests/kernels.rs`), and the kernels built on them against the
  portable ones at every length up to 20 blocks. Each step passes its
  result through an empty `asm!`, which only keeps LLVM from moving it.
- `src/store.rs`: `put_u32_be` and `put_u64_be`, one line each
  (`to_be_bytes` copied into place), whose `ensures` are the bytes
  written. LLVM does not merge the verified form's byte stores.
- From [verilith-core](../core): `prims::copy_in` (trusted, one
  `copy_nonoverlapping`). `prims::get` is verified there.
- vstd's specifications of `slice_subrange`, `wrapping_add` and
  `wrapping_mul`.
- `src/capi.rs`: the C API is not verified. It converts pointers to slices
  and stores the hasher in the caller's context.
- Verus, Z3 and the Rust compiler.

## The specification on NIST's vectors

The tests below run the code, which is proven to compute `spec.rs` and
`spec512.rs`, so they speak for the specification only through the
proofs. `spec-tests/` checks the specification on its own, with no code
and no proof in between: each message of NIST's CAVP SHA-2 ShortMsg
vectors becomes an `assert(sha256(msg) == digest) by (compute_only)`,
which Verus proves by evaluating the spec function on the message.

- SHA-224 and SHA-256: all 65 ShortMsg messages each, every length from
  0 to 64 bytes, so the padding is checked at every length, including the
  ones that need a second block. All agree with NIST.
- SHA-384, SHA-512, SHA-512/224 and SHA-512/256: the empty message only,
  which checks each one's initial value, rounds and truncation. All agree.
  Verus's evaluator takes about six minutes per SHA-512 block (against
  about twelve seconds per SHA-256 block), too long to run all 129
  lengths of each in CI.

Run it with `scripts/spec-tests.sh sha2` from the repository root; CI
runs it too.

## C API

`SHA256_Init`, `SHA256_Update`, `SHA256_Final`, `SHA256`, and the same
four for SHA-224, SHA-384 and SHA-512, with OpenSSL's signatures and
return values. They are exported as `vsha2_SHA256_Init` and so on. With the `openssl-abi`
feature they take OpenSSL's own names, so the static library can be
linked ahead of libcrypto for these functions.

Departures from OpenSSL:

- `SHA256_CTX` and `SHA512_CTX` have OpenSSL's sizes (112 and 216 bytes)
  and alignments, so callers' stack allocations are unchanged, but not
  its fields. Code that reads `h`, `Nl`, `Nh` or `num` directly gets
  other values.
- `SHA256_Transform` and `SHA512_Transform` (one block, no padding) are
  not provided. Neither are SHA-512/224 and SHA-512/256 in C, which
  OpenSSL offers only through its EVP interface.
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
- `tests/vectors512.rs`, `tests/kernels512.rs`, `tests/openssl512.rs`:
  the same for the 64-bit family. They cover FIPS 180-2's SHA-384 and
  SHA-512 examples and NIST's SHA-512/t examples, every length up to
  2200 for all four hashes against RustCrypto, and SHA-384 and SHA-512
  through the C API against libcrypto.

## Performance

`cargo run --release --example speed` compares against RustCrypto's
`sha2` 0.10 and the system OpenSSL (3.0, through `SHA256()` and
`SHA512()`). On an x86-64 cloud VM (with SHA-NI, AVX2 and BMI2), in MB/s,
medians of 25 rounds that alternate the three. A shared VM moves by 5 to
10% from run to run, so compare within a row.

| SHA-256, bytes | verilith-sha2 | RustCrypto sha2 | OpenSSL |
| ---: | ---: | ---: | ---: |
| 16 | 303 | 255 | 52 |
| 64 | 802 | 791 | 184 |
| 1024 | 1728 | 1732 | 1205 |
| 8192 | 1850 | 1836 | 1729 |
| 1 MiB | 1856 | 1858 | 1851 |

| SHA-512, bytes | verilith-sha2 | RustCrypto sha2 | OpenSSL |
| ---: | ---: | ---: | ---: |
| 16 | 71 | 69 | 34 |
| 128 | 309 | 311 | 208 |
| 1024 | 647 | 626 | 600 |
| 8192 | 771 | 701 | 782 |
| 1 MiB | 800 | 685 | 825 |

SHA-256 without SHA-NI (Haswell to Comet Lake, Skylake and Cascade Lake
Xeons), 1 MiB, measured on the same machine with OpenSSL told not to use
SHA-NI (`OPENSSL_ia32cap`) and RustCrypto's portable code: verilith-sha2
492, RustCrypto 380, OpenSSL 523.

What the speed rests on:

- The eight-round groups are called with constant t, so that once inlined
  every index into the schedule window and into K is a constant.
- On x86-64 with AVX2, the message schedule of two blocks at a time is
  computed with AVX2 while the verified rounds of the previous two run,
  between their round groups, as OpenSSL does: the vector work takes the
  ports the rounds' dependency chains leave idle. The rounds alone, over
  a ready schedule, run at OpenSSL's speed, and the pipelined kernels
  within a few percent of them.
- Short messages pay no kernel call for zero blocks and no clearing for
  the padding: the buffer is kept zero past its bytes.

## Not yet

- HMAC.
- A kernel for x86-64's own SHA-512 instructions (Arrow Lake, Lunar
  Lake). There was no CPU with them to test on.
- Verifying the AVX2 schedules too, against verilith-simd's
  specifications of the intrinsics; that needs 64-bit lane shifts added
  there.
- `no_std`: the crate needs `std` for run-time CPU detection.
- RustCrypto's `digest` traits, for a drop-in `sha2` replacement.
- A [vbench](../../bench) suite against OpenSSL through the drop-in C API.
- Verifying the SHA-NI and ARMv8 kernels against specifications of the
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

## License

Licensed under either of the [Apache License, Version 2.0](LICENSE-APACHE)
or the [MIT license](LICENSE-MIT), at your option.

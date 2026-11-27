# verilith-aes

AES-128-GCM and AES-256-GCM (NIST SP 800-38D over FIPS 197) in Rust,
proven with [Verus](https://github.com/verus-lang/verus) for the code that
actually runs: the x86-64 AES-NI and PCLMULQDQ kernels, the 16-block
VAES and VPCLMULQDQ kernel for AVX-512 CPUs, and the AArch64 FEAT_AES and
FEAT_PMULL kernels, with additional data, every length, and the partial
last block. The AES block cipher alone is there too, for QUIC header
protection.

`cargo verus verify` (or `scripts/verify.sh`) checks 332 functions and
lemmas with no errors and no `assume`. What is assumed instead is listed
under [Trusted base](#trusted-base) and in full in [TRUST.md](https://github.com/verilith/verilith/blob/main/crates/aes/TRUST.md):
the specifications, one-line wrappers of the instructions, CPU detection,
and verified code compiled with target features.

```rust
// `None` on a CPU without the AES instructions.
let Some(k) = verilith_aes::AesGcm::new(&[0u8; 16]) else { return };
let iv = [0u8; 12];
let mut buf = b"hello".to_vec();
let mut tag = [0u8; 16];
assert!(k.seal(&iv, b"header", &mut buf, &mut tag));
assert!(k.open(&iv, b"header", &mut buf, &tag));
assert_eq!(buf, b"hello");

let b = verilith_aes::Aes::new(&[0u8; 16]).unwrap();
let mut block = [0u8; 16];
b.encrypt_block(&mut block);
```

`AesGcm::new` and `Aes::new` return `None` on a CPU without the
instructions (and on targets other than x86-64 and little-endian
AArch64): the caller keeps another implementation for those.
`verilith-tls-aws-lc` falls back to aws-lc.

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety, no overflow, no panic; every loop terminates | every function |
| `seal` returns GCM-AE_K(IV, P, A) of SP 800-38D §7.1, ciphertext and 128-bit tag, for any lengths within §5.2.1.1's limits, and refuses (changing nothing) beyond them | `AesGcm::seal` against `spec::gcm_seal` |
| `open` returns GCM-AD_K(IV, C, A, T) of §7.2: the plaintext if T is the tag, else failure, with the buffer zeroed | `AesGcm::open` against `spec::gcm_open` |
| `encrypt_block` is CIPHER(in) of FIPS 197 §5.1 | `Aes::encrypt_block` against `spec::cipher` |
| The key expansion is KEYEXPANSION() of §5.2, with SubWord from `AESENCLAST` or `AESE` on a broadcast word | `gcm::expand` against `spec::w` and `round_key` |
| `AESENC`/`AESENCLAST` (x86) and `AESE`/`AESMC` (Arm), round by round, compute CIPHER; the two instruction sets put the round key at opposite ends of a round, and each keeps its own state between rounds | `Isa::first`, `round`, `last` in `ni.rs` and `arm.rs`, against `spec::rounds` and `cipher` |
| GF(2^128) multiplication as four carry-less 64-bit products and a shift-and-XOR reduction is SP 800-38D Algorithm 1; it is commutative, associative and distributes over XOR | `gf::lemma_gf_mul_prod`, `lemma_gf_comm`, `lemma_gf_assoc`, `lemma_gf_xor_l` |
| GHASH of n blocks as one sum of products by H^n .. H^1 with a single reduction (aggregated reduction) is GHASH of §6.4 | `gf::lemma_ghash_dsum`, `kernels::ghash_x` (up to 16 blocks), `vaes::ghash16_z` (16 blocks over four 512-bit registers, then a lane fold) |
| CTR of 1, 8 and 16 blocks at a time, with the counter in a register lane, is GCTR of §6.5 with inc32 | `kernels::ctr1_x`, `ctr8_x`, `vaes::ctr16_z`, and `gcm::crypt` over the whole text |
| When sealing, GHASH runs a chunk behind CTR (so the two are independent work) and still hashes exactly the ciphertext | `gcm::crypt` |
| The run-time choice of kernel: whichever runs, the result is the specification's | `AesGcm::new`, `seal`, `open` over `aead::detect` |

The kernels and GCM are written and proven once, generically over the
`Isa` trait (`arch.rs`): its methods are the operations with their
specifications. `ni.rs` (x86-64) and `arm.rs` (AArch64) implement it from
the instruction wrappers and are proven to meet it, so one proof of GCM
covers both instruction sets.

Narrowings of the specification, all of which TLS 1.3 and QUIC meet: no
AES-192, 96-bit IVs only, 128-bit tags only.

## Trusted base

- `src/spec.rs`: FIPS 197 and SP 800-38D, each function naming what it
  transcribes. The S-box is derived again from its definition by
  `tests/vectors.rs`, which also runs FIPS 197's and the GCM test cases'
  known answers. Every length up to 600 bytes of text and 300 of
  additional data, and longer ones, are compared with RustCrypto's
  `aes-gcm` (`tests/rustcrypto.rs`).
- `src/isa.rs`: what each instruction computes, from the vendors'
  manuals. `tests/isa.rs` runs every wrapper on random operands against
  `src/isa_ref.rs`, verified implementations of the same specifications,
  natively on x86-64 and on AArch64 natively or under qemu.
- `src/x86.rs`, `src/neon.rs`: one `external_body` wrapper per
  intrinsic, whose `ensures` is its `isa` specification and whose
  `requires` is that the CPU has the extension; run-time detection.
- `src/aead.rs`: the trampolines that compile the verified functions with
  `#[target_feature]`, trusted only to be those functions.

## Performance

Against aws-lc (aws-lc-rs 1.19), on a cloud Xeon at 2.3 GHz with AVX-512
and VAES, `crates/tls-aws-lc/bench` (best of 7 runs of 200 ms), GB/s:

| | aws-lc | verilith-aes |
|---|---:|---:|
| AES-128-GCM seal, 16 KiB | 16.7 | 13.6 |
| AES-128-GCM open, 16 KiB (with a copy) | 14.4 | 12.6 |
| AES-128-GCM seal, 1200 B | 6.2 | 6.4 |
| AES-128-GCM open, 1200 B (with a copy) | 5.2 | 6.3 |
| AES-128-GCM seal, 256 B | 1.8 | 3.5 |
| AES-128-GCM seal, 64 B | 0.52 | 0.80 |
| AES-256-GCM seal, 16 KiB | 13.9 | 12.2 |
| AES-128 header protection mask | 0.036 us | 0.034 us |

aws-lc's large-record lead is its stitched AVX-512 assembly, which
interleaves CTR and GHASH instruction by instruction. Under 1200 bytes
verilith-aes is faster: its per-call cost is lower. The AArch64 kernels
are tested under qemu and not yet measured on Arm hardware.

## Constant time

There are no table lookups: AES is the AES instructions, and GHASH is
carry-less multiplication. `./ci.sh ct` runs `examples/ctgrind.rs` under
Valgrind's memcheck with the key, plaintext, additional data and blocks
marked secret, and fails on any branch or address that depends on them
(the 128-bit path: Valgrind's CPU has AES-NI and PCLMULQDQ, not AVX-512).
`open` compares tags without branching, then branches once on the result.

## Layout

- `spec.rs`, `isa.rs`: the specifications (trusted, above).
- `gf.rs`: GF(2^128) and GHASH algebra.
- `lemmas.rs`: bytes and registers, rounds, counter blocks, padding.
- `arch.rs`: the `Isa` and `Wide` traits.
- `kernels.rs`: the GHASH multiply and reduction, CTR of 1 and 8 blocks,
  GHASH of up to 16 blocks, over `Isa`.
- `gcm.rs`: key expansion, H and its powers, GCM-AE and GCM-AD, over
  `Isa`.
- `x86.rs`, `ni.rs`, `vaes.rs`: x86-64: the wrappers, the `Isa`
  implementation, and the 16-block kernel.
- `neon.rs`, `arm.rs`: AArch64: the wrappers and the `Isa` implementation.
  On other hosts the wrappers are `isa_ref`, so `tests/emulated.rs` runs
  the Arm kernels everywhere.
- `isa_ref.rs`: the verified reference implementations of `isa`.
- `aead.rs`: the public API and the trampolines.

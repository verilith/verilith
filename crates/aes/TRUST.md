# What verilith-aes trusts

Verus checks every proof in verilith-aes, but a proof means something only
relative to what it starts from. This is everything assumed rather than
proven, and how each part is checked another way.
[TRUST-LEDGER.md](../../TRUST-LEDGER.md) lists the same items as the
scanner finds them.

## The specifications

- `src/spec.rs`: FIPS 197 (SubBytes, ShiftRows, MixColumns, AddRoundKey,
  KeyExpansion, Cipher) and SP 800-38D (multiplication in GF(2^128) as
  Algorithm 1, GHASH, GCTR, GCM-AE and GCM-AD), each function naming the
  section it transcribes. It narrows SP 800-38D to 96-bit IVs and 128-bit
  tags, and FIPS 197 to 128- and 256-bit keys. Checked by
  `tests/vectors.rs` (the S-box derived from §5.1.1's definition, FIPS
  197's Appendix C examples, the GCM test cases 1 to 4 and 13 to 16) and
  `tests/rustcrypto.rs` (RustCrypto's `aes-gcm` and `aes` on every text
  length up to 600 bytes, additional data up to 300, and longer texts,
  through every kernel).
- `src/isa.rs`: what the instructions compute, from the vendors'
  pseudocode: `AESENC`, `AESENCLAST` (and VAES's per-lane forms),
  `PCLMULQDQ` (and `VPCLMULQDQ`), `PSHUFB`, `PADDD`, the lane and byte
  shifts, and AArch64's `AESE`, `AESMC` and `PMULL`/`PMULL2`. The kernels
  are proven against these, and these against nothing: `tests/isa.rs`
  runs every wrapper on random operands (with zero, all-one and one-bit
  values mixed in) against `src/isa_ref.rs`, verified implementations of
  the same functions, natively on x86-64 (the 512-bit ones where the CPU
  has them) and on AArch64 natively or under qemu (`ci.sh`).

## The instructions (each an `external_body` around one intrinsic)

- `src/x86.rs`: `x_load`, `x_store`, `x_load16`, `x_store16`,
  `x_load_u128`, `x_set`, `x_get`, `x_xor`, `x_aesenc`, `x_aesenclast`,
  `x_clmul`, `x_pshufb`, `x_add32`, `x_sll64`, `x_srl64`, `x_bsll8`,
  `x_bsrl8`, and for 512-bit registers `z_load`, `z_store`, `z_load_u128`,
  `z_bcast`, `z_bcast_x`, `z_from_x`, `z_lane`, `z_xor`, `z_aesenc`,
  `z_aesenclast`, `z_clmul`, `z_pshufb`, `z_add32`, `z_xor3`; the types
  `__m128i` and `__m512i`, seen through the uninterpreted `xv` and `zl`,
  and one axiom, `axiom_zl_len`: a 512-bit register has four 128-bit
  lanes.
- `src/neon.rs`: `n_load`, `n_store`, `n_load16`, `n_store16`,
  `n_load_u128`, `n_set`, `n_get`, `n_xor`, `n_aese`, `n_aesmc`,
  `n_clmul`, `n_tbl`, `n_add32`, `n_sll64`, `n_srl64`, `n_bsll8`,
  `n_bsrl8`, over the register type `N128`, seen through `nv`. On other
  targets each body is the `isa_ref` function of its `ensures`.

Each `requires` that the CPU has the extension (`ni()`, `vaes()`,
`arm_aes()`), so verified code reaches them only after detection.

## CPU detection and compilation with target features

- `x86::has_ni`, `x86::has_vaes`, `neon::has_arm_aes`: run-time
  detection (`is_x86_feature_detected!`, `is_aarch64_feature_detected!`,
  or the compile-time target features without `std`), trusted to say that
  the CPU has the extension.
- `aead::expand_tf`, `enc_tf`, `new_tf`, `seal_tf`, `open_tf`: each calls
  one verified function compiled with `#[target_feature]` (which Verus
  does not accept on verified code) in `aead::tf`, trusted only to be that
  function. The choice between the 128-bit and 16-block kernels is
  verified (`AesGcm::new`).

## The constant-time check

- `src/ct.rs`: `declassify`, an `external_body` identity on `bool`, kept
  out of line so that `open`'s one decision (whether the tag matched) is
  on its result. The binary check treats that result, and only it, as
  public.
- `scripts/ctcheck.py` (the static check of the machine code) trusts:
  capstone 5.0.7's decoding, and its lists of the registers and flags
  each instruction reads and writes; LLVM's stack-frame-layout remark, for
  which stack slots are variables (a store through an index or a pointer
  can reach only those, since the code is memory safe; spill slots are
  addressed only at fixed offsets); its summaries of `memcpy`, `memmove`
  and `memset` (time independent of the bytes) and the rule that a
  function whose name says it panics does not return; and its
  transcription of Intel's data-operand-independent-timing list and Arm's
  FEAT_DIT list. `ctcheck.json` says which memory is public: an expanded
  key's round count, nothing else.
- `examples/ctcheck.rs`: the controls, which must be reported.

## Not covered

- Timing: Verus proves what the code computes, not how long it takes. That
  no branch, address or variable-time instruction depends on a secret is
  shown instead by the type of the generic code (secrets are `A::R`) and,
  on the machine code, by `ci.sh ctstatic` (see the README).
- The Rust compiler and LLVM, as for all of this repository.

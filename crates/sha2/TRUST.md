# What verilith-sha2 trusts

Verus checks every proof in verilith-sha2, but a proof means something only
relative to what it starts from. This is everything assumed rather than
proven, and how each part is checked another way.
[TRUST-LEDGER.md](../../TRUST-LEDGER.md) lists the same items as the
scanner finds them.

## The specifications

- `src/spec.rs`, `src/spec512.rs`: FIPS 180-4, each function naming the
  section it transcribes. The constants are also derived again from their
  definitions by `tests/vectors.rs` and `tests/vectors512.rs`: K and the
  SHA-224, SHA-256, SHA-384 and SHA-512 H(0) come from the fractional
  parts of cube and square roots of primes, computed with exact integer
  roots, and the SHA-512/224 and SHA-512/256 H(0) from running FIPS
  180-4's IV generation function (§5.3.6). The hashes are run on FIPS
  180-2's examples and against RustCrypto's `sha2` and OpenSSL.
- `src/spec_hmac.rs`: FIPS 198-1's HMAC. Also checked by running the MACs
  on RFC 4231's examples (`tests/hmac.rs`).
- verilith-simd's `src/sha.rs` (re-exported here as `isa`): what the SHA
  instructions compute, transcribed from the
  vendors' pseudocode (not from FIPS 180-4) as functions on lanes: x86's
  `SHA256RNDS2`, `SHA256MSG1`, `SHA256MSG2` and `PBLENDW` from Intel's
  Software Developer's Manual, AArch64's `SHA256H`, `SHA256H2`,
  `SHA256SU0`, `SHA256SU1`, `SHA512H`, `SHA512H2`, `SHA512SU0`,
  `SHA512SU1`, `REV32`, `REV64` and 64-bit `ADD` from the Arm
  Architecture Reference Manual. The kernels are proven against these,
  and these against nothing: that they describe the silicon is checked by
  `tests/isa.rs`, which runs every instruction on 200,000 random operands
  (with zero, all-one and one-bit words mixed in) against verilith-simd's `src/sha_ref.rs` (`isa_ref`),
  verified implementations of the same functions. It runs natively on
  x86-64 with SHA-NI, and on AArch64 natively and under qemu (`ci.sh`).
  Deliberate one-bit errors in the specification fail it.

## The instructions (each an `external_body` around one intrinsic)

As verilith-simd does for the AVX2 and NEON intrinsics and verilith-core
for `pclmulqdq` and `crc32`, each instruction is a one-line wrapper whose
`ensures` is its `isa` specification and whose `requires` is that the CPU
has the extension:

They live in verilith-simd, so other crates can use them:

- `src/sha_x86.rs` (re-exported by `shani`): `sha256rnds2`, `sha256msg1`, `sha256msg2`,
  `blend_epi16`. The other instructions the kernel uses (`pshufd`,
  `palignr`, `pshufb`, `paddd`, loads and stores) are verilith-simd's.
- `src/sha_neon.rs` (re-exported by `armv8`): `vsha256hq`, `vsha256h2q`, `vsha256su0q`, `vsha256su1q`,
  `vsha512hq`, `vsha512h2q`, `vsha512su0q`, `vsha512su1q`, `vrev32q_u8`,
  `vrev64q_u8`, `vaddq_u64`, and the 64-bit lane loads and stores
  `vld1q_u64_at` and `vst1q_u64_at`. On other targets their bodies are the
  verified `isa_ref` functions, so `tests/isa.rs` also runs the AArch64
  kernels over that emulation against the portable kernels on every
  target.

The three kernels themselves (`shani::compress_blocks_body`,
`armv8::compress_blocks_body`, `armv8::compress512_blocks_body`) are
verified: they compute `hash_blocks` of FIPS 180-4 from those
instruction specifications.

## CPU detection and compilation with target features

- `shani::has_shani`, `armv8::has_sha2`, `armv8::has_sha512` (verilith-simd's, re-exported): run-time
  detection (`is_x86_feature_detected!`, `is_aarch64_feature_detected!`,
  or the compile-time target features without `std`), trusted to say that
  the CPU has the extension. The uninterpreted predicates `shani()`,
  `sha2_ext()` and `sha512_ext()` stand for that fact.
- `shani::compress_blocks`, `armv8::compress_blocks`,
  `armv8::compress512_blocks`: each calls the verified body compiled with
  the extension enabled (`#[target_feature]`, which Verus does not accept
  on verified code), trusted only to be that function.
- `cpu.rs`: `bmi2_256`, `bmi2_512`, `avx2_256`, `avx2_512`, `pair256_avx2`,
  `pair_avx2`: the verified portable and pipelined kernels compiled a
  second time with BMI2, or AVX2 and BMI2, enabled, trusted only to be
  those functions. The dispatch in `cpu::compress_blocks` and
  `cpu::compress512_blocks` that chooses among the kernels is verified.
- `avx2.rs`: `schedule512x2` and `schedule256x2`, the verified schedules
  compiled with AVX2, trusted the same way; and `barrier`, the empty
  `asm!` each pipelined step's result passes through, whose `ensures` is
  that it returns its argument.

Every kernel is also tested against the portable one and against
RustCrypto's `sha2` (`tests/kernels.rs`, `tests/kernels512.rs`).

## Other primitives

- From [verilith-simd](../simd): the specifications of the AVX2 and NEON
  intrinsics and of the 128-bit loads and stores, each checked against the
  CPU there (`tests/difftest.rs`).
- `src/store.rs`: `put_u32_be` and `put_u64_be`, one line each
  (`to_be_bytes` copied into place), whose `ensures` are the bytes
  written. LLVM does not merge the verified form's byte stores.
- vstd's specifications of `slice_subrange`, `wrapping_add` and
  `wrapping_mul`.

## Constant time

Verus proves what the code computes, not how long it takes. That the time
does not depend on secrets (the message, the key, the chaining state, the
tag given to `verify`) is checked mechanically instead, on the compiled
code, by `./ci.sh ct` (`examples/ctgrind.rs`), with the method of Adam
Langley's ctgrind: the secrets are marked undefined to Valgrind's
memcheck, which follows undefinedness through every instruction and
reports any conditional branch or memory address that depends on it. It
runs the portable SHA-256 and SHA-512 kernels and their BMI2 and AVX2
builds, the six hashers over every length up to 300 split in four ways,
and the six MACs with every key length up to 300 and `verify` on right,
wrong and wrong-length tags, and memcheck reports nothing. Two controls
that do leak (a compare that returns at the first difference, and a
table lookup at a secret index) are run first and must be reported, and
replacing `ct_eq` with an early-exit compare makes the check fail.

What it does not cover:

- Lengths are public: `verify` returns early on a tag of the wrong
  length, and the number of blocks compressed depends on the message
  length.
- Valgrind's virtual CPU has no SHA extensions, so the SHA-NI kernel is
  checked on its machine code instead: `ci.sh ct` requires that it has
  exactly two conditional jumps (on the length: is there a block, is there
  another) and no calls; its loads and stores are at the state, the round
  constants and the block offset. `ci.sh ctstatic` checks it, and the
  ARMv8 kernels, on their machine code by taint analysis (below).
- That an instruction takes the same time for any operands is the CPU's
  promise (Intel's data-operand-independent timing, Arm's FEAT_DIT), not
  something a test of the program can show.
- It checks the code built for x86-64 by this compiler, at the
  optimization level `ci.sh` uses. Other targets and compilers build other
  code.

`./ci.sh ctstatic` adds a static check of the machine code
(`scripts/ctcheck.py`, shared with verilith-aes): a taint analysis over
every path, for every input, of every kernel (portable, BMI2, AVX2,
SHA-NI, the dispatch, and the portable and ARMv8 kernels on AArch64) and,
on x86-64, of SHA-256 and SHA-512, on the binaries as built for x86-64 and
AArch64. It reports no branch, memory address or instruction outside
Intel's and Arm's data-independent-timing lists that depends on the
message or the state, and it reports both controls. Its own trusted base
is its model of each instruction, the two vendor lists as written into
it, and the summaries of `memcpy`, `memmove` and `memset`. The MACs, and
the hashers on AArch64, are checked by Valgrind only: the static check
cannot tell the public buffered length in a hasher's state from the
secret bytes beside it once the state is in memory, and reports leaks
that are not there. The CPU's promise and what neither check covers are
as above.

## Unverified adapters

- `src/capi.rs`: the C API. It converts pointers to slices and stores the
  hasher in the caller's context.
- `src/digest_impls.rs`: RustCrypto's `digest` traits. Each method calls
  the verified method of the same name and copies its array into the
  trait's output type.

## Tools

Verus, Z3 and the Rust compiler.

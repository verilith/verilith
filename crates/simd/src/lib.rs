#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// Verus specifications for x86 (SSE2 to AVX2) and AArch64 NEON SIMD
// intrinsics.
//
// - `lanes`: a vector as bytes, and its 16/32/64-bit lane views.
// - `ops`: what each intrinsic computes, as functions on lanes.
// - `x86` (trusted): `assume_specification`s tying `core::arch` intrinsics
//   to `ops` on x86-64, and the same specifications of `emu` elsewhere
//   (`x86_emu.rs`).
// - `arch`: the intrinsics themselves, `core::arch::x86_64` on x86-64 and
//   the portable emulation in `emu` elsewhere, so code written against
//   these specs builds on every target.
// - `mem` (trusted): slice-indexed loads and stores.
// - `avx512` (trusted, x86-64 only): the AVX-512 intrinsics, as safe
//   wrappers with specifications.
// - `scalar` (trusted): `popcnt`.
// - `mask`: `movemask`, bit by bit.
// - `sse2`: proven wrappers over the SSE2 instructions byte scanners use
//   (16-byte loads, compares, `pmovmskb`) and their 16-bit masks.
// - `cpu` (trusted): CPU-feature predicates and run-time detection.
// - `neon` (trusted): wrappers over the AArch64 NEON intrinsics, with
//   specs in terms of `ops`; off AArch64 they call `emu_neon`.
// - `refs`: verified scalar implementations of every `ops` function, which
//   `tests/difftest.rs` compares with the CPU.
// A normal build erases ghost code, so a variable, import, field or value
// used only by proofs looks unused there, and the `verus!` syntax leaves
// some redundant braces and parentheses. These lints are off in that build
// only.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports, dead_code))]
pub mod lanes;
pub mod ops;
pub mod cpu;
#[cfg(target_arch = "x86_64")]
pub mod x86;
/// Off x86-64, the same specifications stated of `crate::emu`, so code that
/// names x86 intrinsics verifies on every target.
#[cfg(not(target_arch = "x86_64"))]
#[path = "x86_emu.rs"]
pub mod x86;
#[cfg(target_arch = "x86_64")]
pub mod safe;
pub mod emu;
pub mod neon;
pub mod emu_neon;
pub mod neon_mask;

/// The x86 vector types and intrinsics: `core::arch::x86_64` on x86-64,
/// and the portable emulation in [`emu`] elsewhere.
pub mod arch {
    // On x86-64: `core::arch::x86_64`, with each specified intrinsic replaced
    // by its safe wrapper from `crate::safe` (see there for why).
    #[cfg(target_arch = "x86_64")]
    pub use crate::safe::*;
    // The AVX-512 wrappers shadow the raw intrinsics of the same names.
    #[cfg(target_arch = "x86_64")]
    pub use crate::avx512::{
        _mm512_add_epi32, _mm512_and_si512, _mm512_broadcast_i32x4, _mm512_castsi512_si128,
        _mm512_cmpeq_epi8_mask, _mm512_cmple_epu8_mask, _mm512_cvtepu8_epi32,
        _mm512_extracti32x4_epi32, _mm512_maskz_compress_epi8, _mm512_or_si512, _mm512_set1_epi32,
        _mm512_set1_epi8, _mm512_shuffle_epi8, _mm512_srli_epi16, _mm512_subs_epu8,
        _mm512_test_epi8_mask, _mm512_xor_si512,
    };
    #[cfg(not(target_arch = "x86_64"))]
    pub use crate::emu::*;
}
pub mod mem;
/// AVX-512 (x86-64 only; see the module).
#[cfg(target_arch = "x86_64")]
pub mod avx512;
pub mod mask;
pub mod sse2;
pub mod scalar;
pub mod refs;
pub mod refs_neon;
pub mod patterns;

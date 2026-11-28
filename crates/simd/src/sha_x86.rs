//! The x86-64 SHA extensions (TRUSTED): `SHA256RNDS2`, `SHA256MSG1` and
//! `SHA256MSG2`, and SSE4.1's `pblendw`, one wrapper each with the
//! specification of [`crate::sha`], and run-time detection (`has_shani`).
//! verilith-sha2's `tests/isa.rs` checks every one against
//! [`crate::sha_ref`] on random operands.
#![allow(missing_docs)]
use crate::sha as isa;
use crate::arch::*;
#[cfg(verus_only)]
use crate::cpu::{sse41, ssse3};
use crate::lanes::*;
use vstd::prelude::*;

// Run-time detection needs `std`; a `no_std` build uses only the features
// the target is compiled for.
#[cfg(feature = "std")]
macro_rules! x86_has { ($f:tt) => { std::is_x86_feature_detected!($f) }; }
#[cfg(not(feature = "std"))]
macro_rules! x86_has { ($f:tt) => { cfg!(target_feature = $f) }; }

verus! {

broadcast use {crate::lanes::group_lanes, crate::cpu::group_cpu};

/// The CPU running this program has the SHA extensions.
pub uninterp spec fn shani() -> bool;

/// Whether the CPU has the SHA extensions and SSE4.1 (and so SSSE3),
/// detected at run time.
#[verifier::external_body]
#[inline]
pub fn has_shani() -> (r: bool)
    ensures
        r ==> shani() && sse41() && ssse3(),
{
    x86_has!("sha") && x86_has!("sse4.1")
}

/// [`_mm_sha256rnds2_epu32`](core::arch::x86_64::_mm_sha256rnds2_epu32).
#[verifier::external_body]
#[inline(always)]
pub fn sha256rnds2(a: __m128i, b: __m128i, k: __m128i) -> (r: __m128i)
    requires
        shani(),
    ensures
        u32x4(r) == isa::sha256rnds2(u32x4(a), u32x4(b), u32x4(k)),
{
    // SAFETY: the CPU has the SHA extensions (the precondition).
    unsafe { core::arch::x86_64::_mm_sha256rnds2_epu32(a, b, k) }
}

/// [`_mm_sha256msg1_epu32`](core::arch::x86_64::_mm_sha256msg1_epu32).
#[verifier::external_body]
#[inline(always)]
pub fn sha256msg1(a: __m128i, b: __m128i) -> (r: __m128i)
    requires
        shani(),
    ensures
        u32x4(r) == isa::sha256msg1(u32x4(a), u32x4(b)),
{
    // SAFETY: the CPU has the SHA extensions (the precondition).
    unsafe { core::arch::x86_64::_mm_sha256msg1_epu32(a, b) }
}

/// [`_mm_sha256msg2_epu32`](core::arch::x86_64::_mm_sha256msg2_epu32).
#[verifier::external_body]
#[inline(always)]
pub fn sha256msg2(a: __m128i, b: __m128i) -> (r: __m128i)
    requires
        shani(),
    ensures
        u32x4(r) == isa::sha256msg2(u32x4(a), u32x4(b)),
{
    // SAFETY: the CPU has the SHA extensions (the precondition).
    unsafe { core::arch::x86_64::_mm_sha256msg2_epu32(a, b) }
}

/// [`_mm_blend_epi16`](core::arch::x86_64::_mm_blend_epi16).
#[verifier::external_body]
#[inline(always)]
pub fn blend_epi16<const IMM8: i32>(a: __m128i, b: __m128i) -> (r: __m128i)
    requires
        sse41(),
        0 <= IMM8 <= 255,
    ensures
        b128(r) == isa::blend16(b128(a), b128(b), IMM8 as int),
{
    // SAFETY: the CPU has SSE4.1 (the precondition).
    unsafe { core::arch::x86_64::_mm_blend_epi16::<IMM8>(a, b) }
}

} // verus!

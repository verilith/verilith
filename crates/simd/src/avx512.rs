//! Specifications of the AVX-512 intrinsics (TRUSTED, x86-64 only).
//!
//! Each function has the name of one `core::arch::x86_64` intrinsic, and
//! its body is the single call to it, as in `crate::safe`. The `ensures`
//! state what the intrinsic computes in terms of `crate::ops`; Verus takes
//! them on trust. They are checked, not proven: `tests/ext.rs` runs every
//! function here against the verified reference implementation of its
//! spec (`crate::refs`) on a CPU that has AVX-512.
//!
//! Every function requires its CPU-feature predicate from `crate::cpu`,
//! so verified code reaches it only after detection. There is no portable
//! emulation of these: the module exists on x86-64 only.
#![allow(unused_imports, unused_unsafe, non_snake_case)]
use crate::cpu::*;
use crate::lanes::*;
use crate::ops::*;
pub use core::arch::x86_64::__m512i;
use core::arch::x86_64::{__m128i, __m256i};
use vstd::prelude::*;

verus! {

/// Tells Verus about `__m512i`, an opaque type here: its contents are seen through the lane views.
#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExM512i(__m512i);

/// The 64 bytes of a 512-bit vector, lane 0 first.
pub uninterp spec fn b512(v: __m512i) -> Seq<u8>;

pub broadcast axiom fn axiom_b512_len(v: __m512i)
    ensures
        #[trigger] b512(v).len() == 64,
;

pub open spec fn u16x32(v: __m512i) -> Seq<u16> {
    u16s(b512(v))
}

pub open spec fn u32x16(v: __m512i) -> Seq<u32> {
    u32s(b512(v))
}

// ---------------------------------------------------------------------------
// Memory
// ---------------------------------------------------------------------------

/// The 64 bytes at `s[i..i + 64]`.
#[verifier::external_body]
#[inline(always)]
pub fn load512_u8(s: &[u8], i: usize) -> (r: __m512i)
    requires
        avx512f(),
        i + 64 <= s@.len(),
    ensures
        b512(r) == s@.subrange(i as int, i + 64),
{
    debug_assert!(i + 64 <= s.len());
    unsafe { core::arch::x86_64::_mm512_loadu_si512(s.as_ptr().add(i) as *const __m512i) }
}

/// Stores the sixteen 32-bit lanes to `s[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn store512_u32(s: &mut [u32], i: usize, v: __m512i)
    requires
        avx512f(),
        i + 16 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u32x16(v) + old(s)@.subrange(i + 16, old(s)@.len() as int),
{
    debug_assert!(i + 16 <= s.len());
    unsafe { core::arch::x86_64::_mm512_storeu_si512(s.as_mut_ptr().add(i) as *mut __m512i, v) }
}

// ---------------------------------------------------------------------------
// Constructors and conversions (AVX-512F)
// ---------------------------------------------------------------------------

/// [`_mm512_set1_epi8`](core::arch::x86_64::_mm512_set1_epi8) as a safe function, with the specification Verus checks callers against:
///
/// ```text
/// requires avx512f()
/// ensures  b512(r) == splat8(u8_of_i8(x), 64)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_set1_epi8(x: i8) -> (r: __m512i)
    requires
        avx512f(),
    ensures
        b512(r) == splat8(u8_of_i8(x), 64),
{
    unsafe { core::arch::x86_64::_mm512_set1_epi8(x) }
}

/// [`_mm512_set1_epi32`](core::arch::x86_64::_mm512_set1_epi32) as a safe function, with the specification Verus checks callers against:
///
/// ```text
/// requires avx512f()
/// ensures  u32x16(r) == splat32(u32_of_i32(x), 16)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_set1_epi32(x: i32) -> (r: __m512i)
    requires
        avx512f(),
    ensures
        u32x16(r) == splat32(u32_of_i32(x), 16),
{
    unsafe { core::arch::x86_64::_mm512_set1_epi32(x) }
}

/// `vbroadcasti32x4`: the 16 bytes of `a`, four times.
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_broadcast_i32x4(a: __m128i) -> (r: __m512i)
    requires
        avx512f(),
    ensures
        b512(r) == b128(a) + b128(a) + b128(a) + b128(a),
{
    unsafe { core::arch::x86_64::_mm512_broadcast_i32x4(a) }
}

/// `vpmovzxbd`: 16 bytes zero-extended to 16 dwords.
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_cvtepu8_epi32(a: __m128i) -> (r: __m512i)
    requires
        avx512f(),
    ensures
        u32x16(r) == zext8_32(b128(a)),
{
    unsafe { core::arch::x86_64::_mm512_cvtepu8_epi32(a) }
}

/// [`_mm512_castsi512_si128`](core::arch::x86_64::_mm512_castsi512_si128) as a safe function, with the specification Verus checks callers against:
///
/// ```text
/// requires avx512f()
/// ensures  b128(r) == b512(a).subrange(0, 16)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_castsi512_si128(a: __m512i) -> (r: __m128i)
    requires
        avx512f(),
    ensures
        b128(r) == b512(a).subrange(0, 16),
{
    unsafe { core::arch::x86_64::_mm512_castsi512_si128(a) }
}

/// [`_mm512_extracti32x4_epi32`](core::arch::x86_64::_mm512_extracti32x4_epi32) as a safe function, with the specification Verus checks callers against:
///
/// ```text
/// requires avx512f()
///          0 <= IMM2 < 4
/// ensures  b128(r) == b512(a).subrange(16 * IMM2, 16 * IMM2 + 16)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_extracti32x4_epi32<const IMM2: i32>(a: __m512i) -> (r: __m128i)
    requires
        avx512f(),
        0 <= IMM2 < 4,
    ensures
        b128(r) == b512(a).subrange(16 * IMM2, 16 * IMM2 + 16),
{
    unsafe { core::arch::x86_64::_mm512_extracti32x4_epi32::<IMM2>(a) }
}

// ---------------------------------------------------------------------------
// Lane arithmetic
// ---------------------------------------------------------------------------

/// [`_mm512_and_si512`](core::arch::x86_64::_mm512_and_si512) as a safe function, with the specification Verus checks callers against:
///
/// ```text
/// requires avx512f()
/// ensures  b512(r) == and8(b512(a), b512(b))
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_and_si512(a: __m512i, b: __m512i) -> (r: __m512i)
    requires
        avx512f(),
    ensures
        b512(r) == and8(b512(a), b512(b)),
{
    unsafe { core::arch::x86_64::_mm512_and_si512(a, b) }
}

/// [`_mm512_or_si512`](core::arch::x86_64::_mm512_or_si512) as a safe function, with the specification Verus checks callers against:
///
/// ```text
/// requires avx512f()
/// ensures  b512(r) == or8(b512(a), b512(b))
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_or_si512(a: __m512i, b: __m512i) -> (r: __m512i)
    requires
        avx512f(),
    ensures
        b512(r) == or8(b512(a), b512(b)),
{
    unsafe { core::arch::x86_64::_mm512_or_si512(a, b) }
}

/// [`_mm512_xor_si512`](core::arch::x86_64::_mm512_xor_si512) as a safe function, with the specification Verus checks callers against:
///
/// ```text
/// requires avx512f()
/// ensures  b512(r) == xor8(b512(a), b512(b))
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_xor_si512(a: __m512i, b: __m512i) -> (r: __m512i)
    requires
        avx512f(),
    ensures
        b512(r) == xor8(b512(a), b512(b)),
{
    unsafe { core::arch::x86_64::_mm512_xor_si512(a, b) }
}

/// [`_mm512_add_epi32`](core::arch::x86_64::_mm512_add_epi32) as a safe function, with the specification Verus checks callers against:
///
/// ```text
/// requires avx512f()
/// ensures  u32x16(r) == add32(u32x16(a), u32x16(b))
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_add_epi32(a: __m512i, b: __m512i) -> (r: __m512i)
    requires
        avx512f(),
    ensures
        u32x16(r) == add32(u32x16(a), u32x16(b)),
{
    unsafe { core::arch::x86_64::_mm512_add_epi32(a, b) }
}

/// [`_mm512_subs_epu8`](core::arch::x86_64::_mm512_subs_epu8) as a safe function, with the specification Verus checks callers against:
///
/// ```text
/// requires avx512bw()
/// ensures  b512(r) == subs_u8(b512(a), b512(b))
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_subs_epu8(a: __m512i, b: __m512i) -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        b512(r) == subs_u8(b512(a), b512(b)),
{
    unsafe { core::arch::x86_64::_mm512_subs_epu8(a, b) }
}

/// `vpshufb`, within each 16-byte lane.
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_shuffle_epi8(a: __m512i, b: __m512i) -> (r: __m512i)
    requires
        avx512bw(),
    ensures
        b512(r) == shuffle8_lanes(b512(a), b512(b)),
{
    unsafe { core::arch::x86_64::_mm512_shuffle_epi8(a, b) }
}

/// [`_mm512_srli_epi16`](core::arch::x86_64::_mm512_srli_epi16) as a safe function, with the specification Verus checks callers against:
///
/// ```text
/// requires avx512bw()
///          IMM8 <= 255
/// ensures  u16x32(r) == srli16(u16x32(a), IMM8 as int)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_srli_epi16<const IMM8: u32>(a: __m512i) -> (r: __m512i)
    requires
        avx512bw(),
        IMM8 <= 255,
    ensures
        u16x32(r) == srli16(u16x32(a), IMM8 as int),
{
    unsafe { core::arch::x86_64::_mm512_srli_epi16::<IMM8>(a) }
}

// ---------------------------------------------------------------------------
// Mask registers
// ---------------------------------------------------------------------------

/// `vpcmpeqb` into a mask register: bit `k` is set where the lanes are
/// equal.
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_cmpeq_epi8_mask(a: __m512i, b: __m512i) -> (r: u64)
    requires
        avx512bw(),
    ensures
        r as nat == movemask(cmpeq8(b512(a), b512(b))),
{
    unsafe { core::arch::x86_64::_mm512_cmpeq_epi8_mask(a, b) }
}

/// `vpcmpub` with "less or equal" into a mask register.
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_cmple_epu8_mask(a: __m512i, b: __m512i) -> (r: u64)
    requires
        avx512bw(),
    ensures
        r as nat == movemask(cmple_u8(b512(a), b512(b))),
{
    unsafe { core::arch::x86_64::_mm512_cmple_epu8_mask(a, b) }
}

/// `vptestmb`: bit `k` is set where `a & b` is nonzero.
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_test_epi8_mask(a: __m512i, b: __m512i) -> (r: u64)
    requires
        avx512bw(),
    ensures
        r as nat == movemask(testm8(b512(a), b512(b))),
{
    unsafe { core::arch::x86_64::_mm512_test_epi8_mask(a, b) }
}

/// `vpcompressb` with zero masking.
#[verifier::external_body]
#[inline(always)]
pub fn _mm512_maskz_compress_epi8(k: u64, a: __m512i) -> (r: __m512i)
    requires
        avx512vbmi2(),
    ensures
        b512(r) == compress8(k, b512(a)),
{
    unsafe { core::arch::x86_64::_mm512_maskz_compress_epi8(k, a) }
}

} // verus!

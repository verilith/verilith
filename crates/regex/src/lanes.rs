#![allow(unused_unsafe)]
//! The six SSE2 operations the first-byte scans use on x86-64, with what
//! each is trusted to compute. On AArch64 the scan uses NEON through
//! vsimd instead (`crate::find`), but this code still builds there (vsimd
//! emulates it), so one generic scanner, verified for both, serves both.
//! These wrappers are trusted: see TRUST.md.
use vstd::prelude::*;

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))]
use verilith_simd::arch::*;

verus! {

/// Bit `k` of a 32-bit mask.
pub open spec fn bit(m: u32, k: u32) -> bool {
    (m >> k) & 1u32 == 1u32
}

} // verus!

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))]
verus! {

// `__m128i` is declared to Verus by vsimd.

/// The 16 bytes of a 128-bit register.
pub uninterp spec fn b16(v: __m128i) -> Seq<u8>;

/// `movdqu`: `s[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn load16(s: &[u8], i: usize) -> (r: __m128i)
    requires
        i + 16 <= s@.len(),
    ensures
        b16(r) == s@.subrange(i as int, i + 16),
{
    unsafe { _mm_loadu_si128(s.as_ptr().add(i) as *const __m128i) }
}

/// Every lane is `c`.
#[verifier::external_body]
#[inline(always)]
pub fn splat16(c: u8) -> (r: __m128i)
    ensures
        b16(r) == Seq::new(16, |k: int| c),
{
    unsafe { _mm_set1_epi8(c as i8) }
}

/// `pcmpeqb`: `0xFF` where the lanes are equal, else 0.
#[verifier::external_body]
#[inline(always)]
pub fn eq16(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        b16(r) == Seq::new(16, |k: int| if b16(a)[k] == b16(b)[k] { 0xFFu8 } else { 0u8 }),
{
    unsafe { _mm_cmpeq_epi8(a, b) }
}

/// `psubusb`: each lane of `a` less the lane of `b`, stopping at 0.
#[verifier::external_body]
#[inline(always)]
pub fn subs16(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        b16(r) == Seq::new(
            16,
            |k: int|
                if b16(a)[k] < b16(b)[k] {
                    0u8
                } else {
                    (b16(a)[k] - b16(b)[k]) as u8
                },
        ),
{
    unsafe { _mm_subs_epu8(a, b) }
}

/// `por`: the lanes or-ed.
#[verifier::external_body]
#[inline(always)]
pub fn or16(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        b16(r) == Seq::new(16, |k: int| b16(a)[k] | b16(b)[k]),
{
    unsafe { _mm_or_si128(a, b) }
}

/// `pmovmskb`: bit `k` is the top bit of lane `k`.
#[verifier::external_body]
#[inline(always)]
pub fn movemask16(a: __m128i) -> (r: u32)
    ensures
        r < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(r, k) == (b16(a)[k as int] >= 0x80),
{
    unsafe { _mm_movemask_epi8(a) as u32 }
}

} // verus!

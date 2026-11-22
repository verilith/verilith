//! Proven wrappers over the SSE2 instructions byte scanners use, on
//! 16-byte registers, and the 16-bit masks they give.
//!
//! Each function wraps one instruction and proves, from this crate's
//! specification of it (`ops`, `x86`), the contract the callers are
//! verified against: `b16(r)` of the result as a sequence of 16 bytes, and
//! `bit(m, k)` of a mask. Nothing here is trusted beyond what the
//! specifications already assume. verilith-json and verilith-xml use them.
//! SSE2 is part of x86-64, so no feature detection is needed; the
//! register functions exist on x86-64 only.
use vstd::prelude::*;

#[cfg(target_arch = "x86_64")]
use crate::arch::*;
#[cfg(target_arch = "x86_64")]
use crate::mem::*;
#[allow(unused_imports)]
use crate::lanes::*;
#[allow(unused_imports)]
use crate::mask as vm;
#[allow(unused_imports)]
use crate::ops as vo;
#[cfg(verus_only)]
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;

verus! {

/// Bit `k` of a mask.
pub open spec fn bit(m: u32, k: u32) -> bool {
    (m >> k) & 1u32 == 1u32
}

#[verifier::bit_vector]
pub proof fn lemma_guard_bit(m: u32, k: u32)
    requires
        m < 0x10000,
    ensures
        k < 16 ==> (((m | 0x10000u32) >> k) & 1u32 == 1u32) == ((m >> k) & 1u32 == 1u32),
        ((m | 0x10000u32) >> 16u32) & 1u32 == 1u32,
        m | 0x10000u32 != 0,
{
}

/// The index of the lowest set bit of a 16-bit mask, or 16 if none: every
/// lower bit is clear.
#[inline(always)]
pub fn first_set16(m: u32) -> (r: usize)
    requires
        m < 0x10000,
    ensures
        r <= 16,
        forall|k: u32| k < r ==> !#[trigger] bit(m, k),
        r < 16 ==> bit(m, r as u32),
{
    let g = m | 0x10000u32;
    let tz = g.trailing_zeros();
    proof {
        vstd::std_specs::bits::axiom_u32_trailing_zeros(g);
        lemma_guard_bit(m, tz);
        assert forall|k: u32| k < tz implies !#[trigger] bit(m, k) by {
            lemma_guard_bit(m, k);
        }
        if tz > 16 {
            assert((g >> 16u32) & 1u32 == 0u32);
        }
    }
    tz as usize
}

/// The top bit of an OR is the OR of the top bits.
#[verifier::bit_vector]
pub proof fn lemma_top_or(a: u8, b: u8)
    ensures
        ((a | b) >= 0x80u8) == (a >= 0x80u8 || b >= 0x80u8),
{
}

} // verus!

#[cfg(target_arch = "x86_64")]
verus! {

broadcast use crate::lanes::group_lanes;

/// The 16 bytes of a 128-bit register.
pub open spec fn b16(v: __m128i) -> Seq<u8> {
    b128(v)
}

/// A byte as the `i8` an intrinsic takes.
#[inline(always)]
pub fn i8_of(c: u8) -> (r: i8)
    ensures
        vo::u8_of_i8(r) == c,
{
    if c < 128 {
        c as i8
    } else {
        (c as i16 - 256) as i8
    }
}

/// An `i32` (a `movemask` result) as the `u32` with the same bits.
#[inline(always)]
pub fn u32_from(x: i32) -> (r: u32)
    ensures
        r == vo::u32_of_i32(x),
{
    if x >= 0 {
        x as u32
    } else {
        (x as i64 + 0x1_0000_0000) as u32
    }
}

/// Bit `k` of a `u32` is bit `k` of it as a `u64`, as `mask` states them.
pub proof fn lemma_bit_u32(r: u32, k: u32)
    requires
        k < 32,
    ensures
        bit(r, k) == vm::bit64(r as u64, k as int),
{
    assert(((r >> k) & 1u32 == 1u32) == (((r as u64) >> (k as u64)) & 1u64 == 1u64)) by (bit_vector)
        requires
            k < 32,
    ;
}

/// `movdqu`: `s[i..i + 16]`.
#[inline(always)]
pub fn load16(s: &[u8], i: usize) -> (r: __m128i)
    requires
        i + 16 <= s@.len(),
    ensures
        b16(r) == s@.subrange(i as int, i + 16),
{
    let r = load128_u8(s, i);
    proof {
        assert(b16(r) =~= s@.subrange(i as int, i + 16));
    }
    r
}

/// Every lane is `c`.
#[inline(always)]
pub fn splat16(c: u8) -> (r: __m128i)
    ensures
        b16(r) == Seq::new(16, |k: int| c),
{
    let r = _mm_set1_epi8(i8_of(c));
    proof {
        assert(b16(r) =~= Seq::new(16, |k: int| c));
    }
    r
}

/// `pcmpeqb`: `0xFF` where the lanes are equal, else 0.
#[inline(always)]
pub fn eq16(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        b16(r) == Seq::new(16, |k: int| if b16(a)[k] == b16(b)[k] { 0xFFu8 } else { 0u8 }),
{
    let r = _mm_cmpeq_epi8(a, b);
    proof {
        assert(b16(r) =~= Seq::new(16, |k: int| if b16(a)[k] == b16(b)[k] { 0xFFu8 } else { 0u8 }));
    }
    r
}

/// `por`.
#[inline(always)]
pub fn or16(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        b16(r) == Seq::new(16, |k: int| b16(a)[k] | b16(b)[k]),
{
    let r = _mm_or_si128(a, b);
    proof {
        assert(b16(r) =~= Seq::new(16, |k: int| b16(a)[k] | b16(b)[k]));
    }
    r
}

/// `pminub`: unsigned minimum.
#[inline(always)]
pub fn min16(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        b16(r) == Seq::new(16, |k: int| if b16(a)[k] <= b16(b)[k] { b16(a)[k] } else { b16(b)[k] }),
{
    let r = _mm_min_epu8(a, b);
    proof {
        assert(b16(r) =~= Seq::new(16, |k: int| if b16(a)[k] <= b16(b)[k] { b16(a)[k] } else { b16(b)[k] }));
    }
    r
}

/// `pmovmskb`: bit `k` is the top bit of lane `k`.
#[inline(always)]
pub fn movemask16(a: __m128i) -> (r: u32)
    ensures
        r < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(r, k) == (b16(a)[k as int] >= 0x80),
{
    let m = _mm_movemask_epi8(a);
    proof {
        vm::lemma_movemask_bound(b128(a));
        lemma2_to64();
    }
    let r = u32_from(m);
    proof {
        vm::lemma_movemask_bits(b128(a), r as u64);
        assert forall|k: u32| k < 16 implies #[trigger] bit(r, k) == (b16(a)[k as int] >= 0x80) by {
            assert(vm::bit64(r as u64, k as int) == (b128(a)[k as int] >= 128));
            lemma_bit_u32(r, k);
        }
    }
    r
}

} // verus!

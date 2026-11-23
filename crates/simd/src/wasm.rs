//! Specifications of the WebAssembly SIMD128 instructions (TRUSTED).
//!
//! Each function is one SIMD128 instruction, with an `ensures` that states
//! what the WebAssembly specification (the "SIMD" chapter of the core
//! spec, 2.0) says it computes, on the vector's bytes `n8` or on its
//! little-endian 16-, 32- and 64-bit lanes. They are stated from that
//! specification, not from NEON: where the two differ the difference is
//! in the spec, and `crate::wasm_neon` has to prove its way around it.
//! The ones that matter:
//!
//! - shifts take the count modulo the lane width (`i8x16.shr_u` by 8
//!   shifts by 0), where NEON's `ushr #8` gives 0;
//! - `i8x16.swizzle` gives 0 for an index of 16 or more, the same as
//!   NEON's `tbl` (proven there, not assumed);
//! - there is no byte multiply and no 32-to-64-bit pairwise add; those are
//!   built from 16-bit multiplies, shuffles and widening.
//!
//! `i8x16.shuffle` takes its sixteen indices as constants, so each
//! permutation used gets its own wrapper, its indices in the `ensures`
//! and in the body side by side.
//!
//! On `wasm32` with `simd128` each body is the `core::arch::wasm32`
//! intrinsic; elsewhere (`imp` below) the same operation in plain Rust,
//! so the verified code above it builds and its proofs are checked on any
//! machine. `tests/neon.rs`, run on `wasm32-wasip1` under a WebAssembly
//! engine, checks the NEON contracts built on these against the verified
//! references.
//!
//! Every function requires `neon()`: on WebAssembly that predicate means
//! the module was built with `simd128` (which `has_neon` reports there).
#![allow(unused_imports, unsafe_op_in_unsafe_fn)]
use crate::lanes::*;
#[cfg(verus_only)]
use crate::neon::{n8, neon};
use crate::neon::uint8x16_t;
use crate::ops::*;
use vstd::prelude::*;

verus! {

broadcast use crate::neon::group_neon;

/// `i8x16.shuffle`'s result: index `k < 16` picks `a[k]`, else `b[k - 16]`.
pub open spec fn shuf(a: Seq<u8>, b: Seq<u8>, ix: Seq<int>) -> Seq<u8> {
    Seq::new(16, |i: int| if ix[i] < 16 { a[ix[i]] } else { b[ix[i] - 16] })
}

// ---------------------------------------------------------------------------
// Memory
// ---------------------------------------------------------------------------

/// `v128.load` of `s[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn w_load(s: &[u8], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        n8(r) == s@.subrange(i as int, i + 16),
{
    assert!(i + 16 <= s.len());
    unsafe { imp::load(s.as_ptr().add(i)) }
}

/// `v128.load` of the eight `u16`s at `s[i..]` (memory is little-endian).
#[verifier::external_body]
#[inline(always)]
pub fn w_load16(s: &[u16], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 8 <= s@.len(),
    ensures
        u16s(n8(r)) == s@.subrange(i as int, i + 8),
{
    assert!(i + 8 <= s.len());
    unsafe { imp::load(s.as_ptr().add(i) as *const u8) }
}

/// `v128.load` of the four `u32`s at `s[i..]`.
#[verifier::external_body]
#[inline(always)]
pub fn w_load32(s: &[u32], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 4 <= s@.len(),
    ensures
        u32s(n8(r)) == s@.subrange(i as int, i + 4),
{
    assert!(i + 4 <= s.len());
    unsafe { imp::load(s.as_ptr().add(i) as *const u8) }
}

/// `v128.store` to `s[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn w_store(s: &mut [u8], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 16 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + n8(v) + old(s)@.subrange(i + 16, old(s)@.len() as int),
{
    assert!(i + 16 <= s.len());
    unsafe { imp::store(s.as_mut_ptr().add(i), v) }
}

/// `v128.store` of eight `u16`s to `s[i..i + 8]`.
#[verifier::external_body]
#[inline(always)]
pub fn w_store16(s: &mut [u16], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 8 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u16s(n8(v)) + old(s)@.subrange(i + 8, old(s)@.len() as int),
{
    assert!(i + 8 <= s.len());
    unsafe { imp::store(s.as_mut_ptr().add(i) as *mut u8, v) }
}

// ---------------------------------------------------------------------------
// Bytes
// ---------------------------------------------------------------------------

/// `i8x16.splat`.
#[verifier::external_body]
#[inline(always)]
pub fn w_splat8(x: u8) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| x),
{
    imp::splat8(x)
}

/// `v128.and`.
#[verifier::external_body]
#[inline(always)]
pub fn w_and(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| n8(a)[i] & n8(b)[i]),
{
    imp::and(a, b)
}

/// `v128.or`.
#[verifier::external_body]
#[inline(always)]
pub fn w_or(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| n8(a)[i] | n8(b)[i]),
{
    imp::or(a, b)
}

/// `v128.xor`.
#[verifier::external_body]
#[inline(always)]
pub fn w_xor(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| n8(a)[i] ^ n8(b)[i]),
{
    imp::xor(a, b)
}

/// `i8x16.add`: modulo 256.
#[verifier::external_body]
#[inline(always)]
pub fn w_add8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| ((n8(a)[i] + n8(b)[i]) % 256) as u8),
{
    imp::add8(a, b)
}

/// `i8x16.sub_sat_u`: `a - b`, or 0 below 0.
#[verifier::external_body]
#[inline(always)]
pub fn w_sub_sat_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| if n8(a)[i] < n8(b)[i] { 0u8 } else { (n8(a)[i] - n8(b)[i]) as u8 }),
{
    imp::sub_sat_u8(a, b)
}

/// `i8x16.eq`: all ones where equal.
#[verifier::external_body]
#[inline(always)]
pub fn w_eq8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| if n8(a)[i] == n8(b)[i] { 0xffu8 } else { 0u8 }),
{
    imp::eq8(a, b)
}

/// `i8x16.le_u`: all ones where `a <= b`, unsigned.
#[verifier::external_body]
#[inline(always)]
pub fn w_le_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| if n8(a)[i] <= n8(b)[i] { 0xffu8 } else { 0u8 }),
{
    imp::le_u8(a, b)
}

/// `i8x16.max_u`.
#[verifier::external_body]
#[inline(always)]
pub fn w_max_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| if n8(a)[i] >= n8(b)[i] { n8(a)[i] } else { n8(b)[i] }),
{
    imp::max_u8(a, b)
}

/// `i8x16.shr_u`: the count is taken modulo 8.
#[verifier::external_body]
#[inline(always)]
pub fn w_shr_u8(a: uint8x16_t, n: u32) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| n8(a)[i] >> ((n % 8) as u8)),
{
    imp::shr_u8(a, n)
}

/// `i8x16.swizzle`: lane `i` is `t[ix[i]]`, or 0 when `ix[i] >= 16`.
#[verifier::external_body]
#[inline(always)]
pub fn w_swizzle(t: uint8x16_t, ix: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| if n8(ix)[i] < 16 { n8(t)[n8(ix)[i] as int] } else { 0u8 }),
{
    imp::swizzle(t, ix)
}

/// `i8x16.extract_lane_u 0`.
#[verifier::external_body]
#[inline(always)]
pub fn w_extract8_0(a: uint8x16_t) -> (r: u8)
    requires
        neon(),
    ensures
        r == n8(a)[0],
{
    imp::extract8_0(a)
}

// ---------------------------------------------------------------------------
// Byte shuffles (`i8x16.shuffle` with the indices given)
// ---------------------------------------------------------------------------

/// Indices 0, 16, 1, 17, ..., 7, 23.
#[verifier::external_body]
#[inline(always)]
pub fn w_zip_lo8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![0int, 16, 1, 17, 2, 18, 3, 19, 4, 20, 5, 21, 6, 22, 7, 23]),
{
    imp::zip_lo8(a, b)
}

/// Indices 8, 24, 9, 25, ..., 15, 31.
#[verifier::external_body]
#[inline(always)]
pub fn w_zip_hi8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![8int, 24, 9, 25, 10, 26, 11, 27, 12, 28, 13, 29, 14, 30, 15, 31]),
{
    imp::zip_hi8(a, b)
}

/// Indices 0, 2, 4, ..., 30: the even bytes of `a`, then of `b`.
#[verifier::external_body]
#[inline(always)]
pub fn w_even8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![0int, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30]),
{
    imp::even8(a, b)
}

/// Indices 1, 3, 5, ..., 31: the odd bytes of `a`, then of `b`.
#[verifier::external_body]
#[inline(always)]
pub fn w_odd8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![1int, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31]),
{
    imp::odd8(a, b)
}

/// Indices 0, 16, 2, 18, ..., 14, 30: even bytes of `a` and `b`, alternating.
#[verifier::external_body]
#[inline(always)]
pub fn w_mix_even8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![0int, 16, 2, 18, 4, 20, 6, 22, 8, 24, 10, 26, 12, 28, 14, 30]),
{
    imp::mix_even8(a, b)
}

/// `a` rotated down by `K` bytes (indices `(i + K) % 16` of `a`), for
/// `K` in 1, 2, 4, 8.
#[verifier::external_body]
#[inline(always)]
pub fn w_rot8<const K: u32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        K == 1 || K == 2 || K == 4 || K == 8,
    ensures
        n8(r) == Seq::new(16, |i: int| n8(a)[(i + K) % 16]),
{
    imp::rot8::<K>(a)
}

// ---------------------------------------------------------------------------
// 16-, 32- and 64-bit lanes
// ---------------------------------------------------------------------------

/// `i16x8.shr_u`: the count is taken modulo 16.
#[verifier::external_body]
#[inline(always)]
pub fn w_shr_u16(a: uint8x16_t, n: u32) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| u16s(n8(a))[i] >> ((n % 16) as u16)),
{
    imp::shr_u16(a, n)
}

/// `i16x8.max_u`.
#[verifier::external_body]
#[inline(always)]
pub fn w_max_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| if u16s(n8(a))[i] >= u16s(n8(b))[i] { u16s(n8(a))[i] } else { u16s(n8(b))[i] }),
{
    imp::max_u16(a, b)
}

/// `i16x8.shuffle` (as `i8x16.shuffle` on lane pairs): `a` rotated down by
/// `K` 16-bit lanes, for `K` in 1, 2, 4.
#[verifier::external_body]
#[inline(always)]
pub fn w_rot16<const K: u32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        K == 1 || K == 2 || K == 4,
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| u16s(n8(a))[(i + K) % 8]),
{
    match K {
        1 => imp::rot8::<2>(a),
        2 => imp::rot8::<4>(a),
        _ => imp::rot8::<8>(a),
    }
}

/// `i16x8.extract_lane_u 0`.
#[verifier::external_body]
#[inline(always)]
pub fn w_extract16_0(a: uint8x16_t) -> (r: u16)
    requires
        neon(),
    ensures
        r == u16s(n8(a))[0],
{
    imp::extract16_0(a)
}

/// `i16x8.mul`: the low 16 bits of each product.
#[verifier::external_body]
#[inline(always)]
pub fn w_mul16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| ((u16s(n8(a))[i] * u16s(n8(b))[i]) % 0x10000) as u16),
{
    imp::mul16(a, b)
}

/// `i32x4.mul`: the low 32 bits of each product.
#[verifier::external_body]
#[inline(always)]
pub fn w_mul32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == Seq::new(4, |i: int| ((u32s(n8(a))[i] * u32s(n8(b))[i]) % 0x1_0000_0000) as u32),
{
    imp::mul32(a, b)
}

/// `i16x8.extadd_pairwise_i8x16_u`: sums of adjacent byte pairs.
#[verifier::external_body]
#[inline(always)]
pub fn w_extadd8(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| (n8(a)[2 * i] + n8(a)[2 * i + 1]) as u16),
{
    imp::extadd8(a)
}

/// `i32x4.extadd_pairwise_i16x8_u`: sums of adjacent 16-bit pairs.
#[verifier::external_body]
#[inline(always)]
pub fn w_extadd16(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == Seq::new(4, |i: int| (u16s(n8(a))[2 * i] + u16s(n8(a))[2 * i + 1]) as u32),
{
    imp::extadd16(a)
}

/// `i32x4.shuffle` (as `i8x16.shuffle` on lane quads) with lanes 0, 2, 1, 3.
#[verifier::external_body]
#[inline(always)]
pub fn w_shuf32_0213(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == seq![u32s(n8(a))[0], u32s(n8(a))[2], u32s(n8(a))[1], u32s(n8(a))[3]],
{
    imp::shuf32_0213(a)
}

/// `i64x2.extend_low_i32x4_u`: 32-bit lanes 0 and 1, zero-extended.
#[verifier::external_body]
#[inline(always)]
pub fn w_extend_lo32(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == seq![u32s(n8(a))[0] as u64, u32s(n8(a))[1] as u64],
{
    imp::extend_lo32(a)
}

/// `i64x2.extend_high_i32x4_u`: 32-bit lanes 2 and 3, zero-extended.
#[verifier::external_body]
#[inline(always)]
pub fn w_extend_hi32(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == seq![u32s(n8(a))[2] as u64, u32s(n8(a))[3] as u64],
{
    imp::extend_hi32(a)
}

/// `i64x2.add`: modulo 2^64.
#[verifier::external_body]
#[inline(always)]
pub fn w_add64(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == Seq::new(2, |i: int| ((u64s(n8(a))[i] + u64s(n8(b))[i]) % 0x1_0000_0000_0000_0000) as u64),
{
    imp::add64(a, b)
}

/// `i64x2.extract_lane L`, for `L` in 0, 1.
#[verifier::external_body]
#[inline(always)]
pub fn w_extract64<const L: u32>(a: uint8x16_t) -> (r: u64)
    requires
        neon(),
        L < 2,
    ensures
        r == u64s(n8(a))[L as int],
{
    imp::extract64::<L>(a)
}

} // verus!

/// The instructions.
#[cfg(all(target_arch = "wasm32", target_feature = "simd128"))]
mod imp {
    use super::uint8x16_t;
    use core::arch::wasm32::*;
    use core::mem::transmute;

    #[inline(always)]
    fn v(a: uint8x16_t) -> v128 {
        unsafe { transmute(a) }
    }
    #[inline(always)]
    fn u(a: v128) -> uint8x16_t {
        unsafe { transmute(a) }
    }

    #[inline(always)]
    pub unsafe fn load(p: *const u8) -> uint8x16_t {
        u(v128_load(p as *const v128))
    }
    #[inline(always)]
    pub unsafe fn store(p: *mut u8, a: uint8x16_t) {
        v128_store(p as *mut v128, v(a))
    }
    #[inline(always)]
    pub fn splat8(x: u8) -> uint8x16_t {
        u(u8x16_splat(x))
    }
    #[inline(always)]
    pub fn and(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(v128_and(v(a), v(b)))
    }
    #[inline(always)]
    pub fn or(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(v128_or(v(a), v(b)))
    }
    #[inline(always)]
    pub fn xor(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(v128_xor(v(a), v(b)))
    }
    #[inline(always)]
    pub fn add8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(u8x16_add(v(a), v(b)))
    }
    #[inline(always)]
    pub fn sub_sat_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(u8x16_sub_sat(v(a), v(b)))
    }
    #[inline(always)]
    pub fn eq8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(u8x16_eq(v(a), v(b)))
    }
    #[inline(always)]
    pub fn le_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(u8x16_le(v(a), v(b)))
    }
    #[inline(always)]
    pub fn max_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(u8x16_max(v(a), v(b)))
    }
    #[inline(always)]
    pub fn shr_u8(a: uint8x16_t, n: u32) -> uint8x16_t {
        u(u8x16_shr(v(a), n))
    }
    #[inline(always)]
    pub fn swizzle(t: uint8x16_t, ix: uint8x16_t) -> uint8x16_t {
        u(u8x16_swizzle(v(t), v(ix)))
    }
    #[inline(always)]
    pub fn extract8_0(a: uint8x16_t) -> u8 {
        u8x16_extract_lane::<0>(v(a))
    }
    #[inline(always)]
    pub fn zip_lo8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(i8x16_shuffle::<0, 16, 1, 17, 2, 18, 3, 19, 4, 20, 5, 21, 6, 22, 7, 23>(v(a), v(b)))
    }
    #[inline(always)]
    pub fn zip_hi8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(i8x16_shuffle::<8, 24, 9, 25, 10, 26, 11, 27, 12, 28, 13, 29, 14, 30, 15, 31>(v(a), v(b)))
    }
    #[inline(always)]
    pub fn even8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(i8x16_shuffle::<0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30>(v(a), v(b)))
    }
    #[inline(always)]
    pub fn odd8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(i8x16_shuffle::<1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31>(v(a), v(b)))
    }
    #[inline(always)]
    pub fn mix_even8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(i8x16_shuffle::<0, 16, 2, 18, 4, 20, 6, 22, 8, 24, 10, 26, 12, 28, 14, 30>(v(a), v(b)))
    }
    #[inline(always)]
    pub fn rot8<const K: u32>(a: uint8x16_t) -> uint8x16_t {
        let x = v(a);
        u(match K {
            1 => i8x16_shuffle::<1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0>(x, x),
            2 => i8x16_shuffle::<2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1>(x, x),
            4 => i8x16_shuffle::<4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3>(x, x),
            8 => i8x16_shuffle::<8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7>(x, x),
            _ => unreachable!(),
        })
    }
    #[inline(always)]
    pub fn shr_u16(a: uint8x16_t, n: u32) -> uint8x16_t {
        u(u16x8_shr(v(a), n))
    }
    #[inline(always)]
    pub fn max_u16(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(u16x8_max(v(a), v(b)))
    }
    #[inline(always)]
    pub fn extract16_0(a: uint8x16_t) -> u16 {
        u16x8_extract_lane::<0>(v(a))
    }
    #[inline(always)]
    pub fn mul16(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(i16x8_mul(v(a), v(b)))
    }
    #[inline(always)]
    pub fn mul32(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(i32x4_mul(v(a), v(b)))
    }
    #[inline(always)]
    pub fn extadd8(a: uint8x16_t) -> uint8x16_t {
        u(u16x8_extadd_pairwise_u8x16(v(a)))
    }
    #[inline(always)]
    pub fn extadd16(a: uint8x16_t) -> uint8x16_t {
        u(u32x4_extadd_pairwise_u16x8(v(a)))
    }
    #[inline(always)]
    pub fn shuf32_0213(a: uint8x16_t) -> uint8x16_t {
        u(i32x4_shuffle::<0, 2, 1, 3>(v(a), v(a)))
    }
    #[inline(always)]
    pub fn extend_lo32(a: uint8x16_t) -> uint8x16_t {
        u(u64x2_extend_low_u32x4(v(a)))
    }
    #[inline(always)]
    pub fn extend_hi32(a: uint8x16_t) -> uint8x16_t {
        u(u64x2_extend_high_u32x4(v(a)))
    }
    #[inline(always)]
    pub fn add64(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        u(i64x2_add(v(a), v(b)))
    }
    #[inline(always)]
    pub fn extract64<const L: u32>(a: uint8x16_t) -> u64 {
        if L == 0 { u64x2_extract_lane::<0>(v(a)) } else { u64x2_extract_lane::<1>(v(a)) }
    }
}

/// Elsewhere: the same operations on the byte arrays, so the verified code
/// builds; never selected at run time (`has_neon` is false off AArch64
/// and SIMD128 WebAssembly).
#[cfg(not(all(target_arch = "wasm32", target_feature = "simd128")))]
mod imp {
    use super::uint8x16_t;

    fn map(a: uint8x16_t, b: uint8x16_t, f: impl Fn(u8, u8) -> u8) -> uint8x16_t {
        uint8x16_t(core::array::from_fn(|i| f(a.0[i], b.0[i])))
    }
    fn shuf(a: uint8x16_t, b: uint8x16_t, ix: [usize; 16]) -> uint8x16_t {
        uint8x16_t(ix.map(|k| if k < 16 { a.0[k] } else { b.0[k - 16] }))
    }
    fn h(a: uint8x16_t) -> [u16; 8] {
        core::array::from_fn(|i| u16::from_le_bytes([a.0[2 * i], a.0[2 * i + 1]]))
    }
    fn hb(x: [u16; 8]) -> uint8x16_t {
        uint8x16_t(core::array::from_fn(|i| x[i / 2].to_le_bytes()[i % 2]))
    }
    fn w(a: uint8x16_t) -> [u32; 4] {
        core::array::from_fn(|i| u32::from_le_bytes(a.0[4 * i..4 * i + 4].try_into().unwrap()))
    }
    fn wb(x: [u32; 4]) -> uint8x16_t {
        uint8x16_t(core::array::from_fn(|i| x[i / 4].to_le_bytes()[i % 4]))
    }
    fn d(a: uint8x16_t) -> [u64; 2] {
        core::array::from_fn(|i| u64::from_le_bytes(a.0[8 * i..8 * i + 8].try_into().unwrap()))
    }
    fn db(x: [u64; 2]) -> uint8x16_t {
        uint8x16_t(core::array::from_fn(|i| x[i / 8].to_le_bytes()[i % 8]))
    }

    pub unsafe fn load(p: *const u8) -> uint8x16_t {
        core::ptr::read_unaligned(p as *const uint8x16_t)
    }
    pub unsafe fn store(p: *mut u8, a: uint8x16_t) {
        core::ptr::write_unaligned(p as *mut uint8x16_t, a)
    }
    pub fn splat8(x: u8) -> uint8x16_t {
        uint8x16_t([x; 16])
    }
    pub fn and(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        map(a, b, |x, y| x & y)
    }
    pub fn or(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        map(a, b, |x, y| x | y)
    }
    pub fn xor(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        map(a, b, |x, y| x ^ y)
    }
    pub fn add8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        map(a, b, u8::wrapping_add)
    }
    pub fn sub_sat_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        map(a, b, u8::saturating_sub)
    }
    pub fn eq8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        map(a, b, |x, y| if x == y { 0xff } else { 0 })
    }
    pub fn le_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        map(a, b, |x, y| if x <= y { 0xff } else { 0 })
    }
    pub fn max_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        map(a, b, u8::max)
    }
    pub fn shr_u8(a: uint8x16_t, n: u32) -> uint8x16_t {
        uint8x16_t(a.0.map(|x| x >> (n % 8)))
    }
    pub fn swizzle(t: uint8x16_t, ix: uint8x16_t) -> uint8x16_t {
        uint8x16_t(ix.0.map(|k| if k < 16 { t.0[k as usize] } else { 0 }))
    }
    pub fn extract8_0(a: uint8x16_t) -> u8 {
        a.0[0]
    }
    pub fn zip_lo8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        shuf(a, b, [0, 16, 1, 17, 2, 18, 3, 19, 4, 20, 5, 21, 6, 22, 7, 23])
    }
    pub fn zip_hi8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        shuf(a, b, [8, 24, 9, 25, 10, 26, 11, 27, 12, 28, 13, 29, 14, 30, 15, 31])
    }
    pub fn even8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        shuf(a, b, [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30])
    }
    pub fn odd8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        shuf(a, b, [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31])
    }
    pub fn mix_even8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        shuf(a, b, [0, 16, 2, 18, 4, 20, 6, 22, 8, 24, 10, 26, 12, 28, 14, 30])
    }
    pub fn rot8<const K: u32>(a: uint8x16_t) -> uint8x16_t {
        uint8x16_t(core::array::from_fn(|i| a.0[(i + K as usize) % 16]))
    }
    pub fn shr_u16(a: uint8x16_t, n: u32) -> uint8x16_t {
        hb(h(a).map(|x| x >> (n % 16)))
    }
    pub fn max_u16(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        let (x, y) = (h(a), h(b));
        hb(core::array::from_fn(|i| x[i].max(y[i])))
    }
    pub fn extract16_0(a: uint8x16_t) -> u16 {
        h(a)[0]
    }
    pub fn mul16(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        let (x, y) = (h(a), h(b));
        hb(core::array::from_fn(|i| x[i].wrapping_mul(y[i])))
    }
    pub fn mul32(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        let (x, y) = (w(a), w(b));
        wb(core::array::from_fn(|i| x[i].wrapping_mul(y[i])))
    }
    pub fn extadd8(a: uint8x16_t) -> uint8x16_t {
        hb(core::array::from_fn(|i| a.0[2 * i] as u16 + a.0[2 * i + 1] as u16))
    }
    pub fn extadd16(a: uint8x16_t) -> uint8x16_t {
        let x = h(a);
        wb(core::array::from_fn(|i| x[2 * i] as u32 + x[2 * i + 1] as u32))
    }
    pub fn shuf32_0213(a: uint8x16_t) -> uint8x16_t {
        let x = w(a);
        wb([x[0], x[2], x[1], x[3]])
    }
    pub fn extend_lo32(a: uint8x16_t) -> uint8x16_t {
        let x = w(a);
        db([x[0] as u64, x[1] as u64])
    }
    pub fn extend_hi32(a: uint8x16_t) -> uint8x16_t {
        let x = w(a);
        db([x[2] as u64, x[3] as u64])
    }
    pub fn add64(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
        let (x, y) = (d(a), d(b));
        db([x[0].wrapping_add(y[0]), x[1].wrapping_add(y[1])])
    }
    pub fn extract64<const L: u32>(a: uint8x16_t) -> u64 {
        d(a)[L as usize]
    }
}

//! The NEON wrappers' contracts, proven on WebAssembly SIMD128.
//!
//! Each function here has the name, signature, `requires` and `ensures` of
//! the wrapper of the same name in `crate::neon`, and is verified against
//! the trusted SIMD128 instruction specifications in `crate::wasm`. On
//! `wasm32` with `simd128`, `crate::neon`'s wrappers call these, so the
//! NEON kernels' proofs (JSON, UTF-8, URL, HTTP, regex, JPEG, WebP) hold
//! there on the strength of the WebAssembly specification, not of NEON.
//!
//! What it takes to match NEON, beyond renaming:
//!
//! - `vshrq_n_u8::<8>` is 0 on NEON, but `i8x16.shr_u` takes the count
//!   modulo 8, so a shift by 8 would return the input: 8 is a splat of 0.
//! - `vqtbl1q_u8` is `i8x16.swizzle`: both give 0 for an index of 16 or
//!   more, which `vqtbl1q_u8`'s proof checks rather than assumes.
//! - `vmaxvq_u8`/`vmaxvq_u16`, horizontal maxima, are four (three)
//!   rounds of max with the vector rotated by 8, 4, 2, 1 lanes.
//! - `vmulq_u8`: SIMD128 has no byte multiply. Even bytes are the low
//!   bytes of the 16-bit products; odd bytes those of the products of the
//!   lanes shifted down by 8.
//! - `vpaddlq_u32` widens the even and odd 32-bit lanes to 64 bits and adds.
//! - `vpaddq_u8` adds the even and odd bytes; `vshrn4_u64` shifts the
//!   16-bit lanes by 4 and takes their low bytes.
//! - `vshrq_n_s8::<8>` is a shift by 7, the same result, since `shr_s`
//!   would take 8 modulo 8.
//! - `vqdmulhq_s16`: `i16x8.q15mulr_sat_s` rounds, `sqdmulh` truncates, so
//!   it is the 32-bit products shifted by 15 and narrowed with saturation
//!   (only -32768 squared saturates, as on NEON).
//! - Rounding shifts (`vrshrq_n_s32`, `vrshrn`): `(x + 2^(n-1)) >> n` is
//!   `(x >> (n - 1)) - (x >> n)`, which cannot overflow, proven for any
//!   sign by floor division.
//! - Multiply-accumulate by lane (`vmlal`/`vmull` by element) splats the
//!   lane and uses `extmul_low`/`extmul_high`; `vaddlvq_u16` is a widening
//!   pairwise add and two rotations.
//! - `vabdq_u8` is the `or` of two saturating differences; `vbicq_u8` is
//!   `andnot` with its operands in WebAssembly's order.
//! - `vst3q_u8_at` interleaves with six `i8x16.shuffle`s and three stores.
//!
//! `tools/check_wasm_neon.py` checks that each contract here is, word for
//! word, the one in `crate::neon`, and that each wrapper there forwards here.
#![allow(unused_imports)]
use crate::lanes::*;
#[cfg(verus_only)]
use crate::neon::{n8, neon};
use crate::neon::uint8x16_t;
use crate::ops::*;
use crate::wasm::*;
use vstd::prelude::*;

verus! {

broadcast use crate::neon::group_neon;

// ---------------------------------------------------------------------------
// Loads and stores
// ---------------------------------------------------------------------------

#[inline(always)]
pub fn vld1q_u8_at(s: &[u8], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 16 <= s@.len(),
    ensures
        n8(r) == s@.subrange(i as int, i + 16),
{
    w_load(s, i)
}

#[inline(always)]
pub fn vst1q_u8_at(s: &mut [u8], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 16 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + n8(v) + old(s)@.subrange(i + 16, old(s)@.len() as int),
{
    w_store(s, i, v)
}

#[inline(always)]
pub fn vld1q_u16_at(s: &[u16], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 8 <= s@.len(),
    ensures
        u16s(n8(r)) == s@.subrange(i as int, i + 8),
{
    w_load16(s, i)
}

#[inline(always)]
pub fn vst1q_u16_at(s: &mut [u16], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 8 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u16s(n8(v)) + old(s)@.subrange(i + 8, old(s)@.len() as int),
{
    w_store16(s, i, v)
}

#[inline(always)]
pub fn vld1q_u32_at(s: &[u32], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 4 <= s@.len(),
    ensures
        u32s(n8(r)) == s@.subrange(i as int, i + 4),
{
    w_load32(s, i)
}

// ---------------------------------------------------------------------------
// One instruction each
// ---------------------------------------------------------------------------

#[inline(always)]
pub fn vdupq_n_u8(x: u8) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == splat8(x, 16),
{
    let r = w_splat8(x);
    assert(n8(r) =~= splat8(x, 16));
    r
}

#[inline(always)]
pub fn vandq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == and8(n8(a), n8(b)),
{
    let r = w_and(a, b);
    assert(n8(r) =~= and8(n8(a), n8(b)));
    r
}

#[inline(always)]
pub fn vorrq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == or8(n8(a), n8(b)),
{
    let r = w_or(a, b);
    assert(n8(r) =~= or8(n8(a), n8(b)));
    r
}

#[inline(always)]
pub fn veorq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == xor8(n8(a), n8(b)),
{
    let r = w_xor(a, b);
    assert(n8(r) =~= xor8(n8(a), n8(b)));
    r
}

#[inline(always)]
pub fn vaddq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == add8(n8(a), n8(b)),
{
    let r = w_add8(a, b);
    assert(n8(r) =~= add8(n8(a), n8(b)));
    r
}

#[inline(always)]
pub fn vqsubq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == subs_u8(n8(a), n8(b)),
{
    let r = w_sub_sat_u8(a, b);
    assert(n8(r) =~= subs_u8(n8(a), n8(b)));
    r
}

#[inline(always)]
pub fn vceqq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == cmpeq8(n8(a), n8(b)),
{
    let r = w_eq8(a, b);
    assert(n8(r) =~= cmpeq8(n8(a), n8(b)));
    r
}

#[inline(always)]
pub fn vcleq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == cmple_u8(n8(a), n8(b)),
{
    let r = w_le_u8(a, b);
    assert(n8(r) =~= cmple_u8(n8(a), n8(b)));
    r
}

/// `tbl` and `swizzle` agree, including on indices of 16 or more.
#[inline(always)]
pub fn vqtbl1q_u8(t: uint8x16_t, idx: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == tbl1(n8(t), n8(idx)),
{
    let r = w_swizzle(t, idx);
    assert(n8(r) =~= tbl1(n8(t), n8(idx)));
    r
}

#[inline(always)]
pub fn vzip1q_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == unpacklo8_lanes(n8(a), n8(b)),
{
    let r = w_zip_lo8(a, b);
    assert(n8(r) =~= unpacklo8_lanes(n8(a), n8(b)));
    r
}

#[inline(always)]
pub fn vzip2q_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == unpackhi8_lanes(n8(a), n8(b)),
{
    let r = w_zip_hi8(a, b);
    assert(n8(r) =~= unpackhi8_lanes(n8(a), n8(b)));
    r
}

#[inline(always)]
pub fn vuzp1q_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == uzp1_8(n8(a), n8(b)),
{
    let r = w_even8(a, b);
    assert(n8(r) =~= uzp1_8(n8(a), n8(b)));
    r
}

#[inline(always)]
pub fn vmulq_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == mullo16(u16s(n8(a)), u16s(n8(b))),
{
    let r = w_mul16(a, b);
    assert(u16s(n8(r)) =~= mullo16(u16s(n8(a)), u16s(n8(b))));
    r
}

#[inline(always)]
pub fn vmulq_u32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == mullo32(u32s(n8(a)), u32s(n8(b))),
{
    let r = w_mul32(a, b);
    assert(u32s(n8(r)) =~= mullo32(u32s(n8(a)), u32s(n8(b))));
    r
}

#[inline(always)]
pub fn vpaddlq_u8(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == paddl8(n8(a)),
{
    let r = w_extadd8(a);
    assert(u16s(n8(r)) =~= paddl8(n8(a)));
    r
}

#[inline(always)]
pub fn vpaddlq_u16(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == paddl16(u16s(n8(a))),
{
    let r = w_extadd16(a);
    assert(u32s(n8(r)) =~= paddl16(u16s(n8(a))));
    r
}

#[inline(always)]
pub fn vgetq_lane_u64_0(a: uint8x16_t) -> (r: u64)
    requires
        neon(),
    ensures
        r == u64s(n8(a))[0],
{
    w_extract64::<0>(a)
}

#[inline(always)]
pub fn vgetq_lane_u64_1(a: uint8x16_t) -> (r: u64)
    requires
        neon(),
    ensures
        r == u64s(n8(a))[1],
{
    w_extract64::<1>(a)
}

// ---------------------------------------------------------------------------
// Shifts: the count modulo 8
// ---------------------------------------------------------------------------

#[inline(always)]
pub fn vshrq_n_u8<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 8,
    ensures
        n8(r) == shr8(n8(a), N as int),
{
    reveal_with_fuel(pow2_spec, 9);
    if N == 8 {
        // `i8x16.shr_u` by 8 is a shift by 0; NEON's is 0.
        let r = w_splat8(0);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] n8(r)[i] == shr8(n8(a), N as int)[i] by {
            assert(pow2_spec(8) == 256);
        }
        assert(n8(r) =~= shr8(n8(a), N as int));
        r
    } else {
        let r = w_shr_u8(a, N as u32);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] n8(r)[i] == shr8(n8(a), N as int)[i] by {
            let x = n8(a)[i];
            lemma_shr_u8(x, N as u8);
        }
        assert(n8(r) =~= shr8(n8(a), N as int));
        r
    }
}

proof fn lemma_shr_u8(x: u8, n: u8)
    requires
        1 <= n <= 7,
    ensures
        (x >> ((n as u32 % 8) as u8)) as nat == x as nat / pow2_spec(n as nat),
{
    reveal_with_fuel(pow2_spec, 8);
    assert((n as u32 % 8) as u8 == n);
    if n == 1 {
        assert(x >> 1u8 == x / 2) by (bit_vector);
    } else if n == 2 {
        assert(x >> 2u8 == x / 4) by (bit_vector);
    } else if n == 3 {
        assert(x >> 3u8 == x / 8) by (bit_vector);
    } else if n == 4 {
        assert(x >> 4u8 == x / 16) by (bit_vector);
    } else if n == 5 {
        assert(x >> 5u8 == x / 32) by (bit_vector);
    } else if n == 6 {
        assert(x >> 6u8 == x / 64) by (bit_vector);
    } else {
        assert(x >> 7u8 == x / 128) by (bit_vector);
    }
}

// ---------------------------------------------------------------------------
// Horizontal maxima
// ---------------------------------------------------------------------------

pub open spec fn hmax8(x: u8, y: u8) -> u8 {
    if x >= y { x } else { y }
}

/// After the rounds before a rotation by `k`, lane `i` is the largest of
/// `a[(i + d) % n]` over the `d` that are multiples of `2 k`, and is one
/// of them.
pub open spec fn round_inv8(a: Seq<u8>, x: Seq<u8>, n: int, step: int) -> bool {
    &&& x.len() == n
    &&& forall|i: int, d: int| 0 <= i < n && 0 <= d < n && d % step == 0 ==> #[trigger] a[(i + d) % n] <= x[i]
    &&& forall|i: int| 0 <= i < n ==> #[trigger] in8(a, x[i], n)
}

/// `v` is one of `a[0..n]`.
pub open spec fn in8(a: Seq<u8>, v: u8, n: int) -> bool {
    exists|j: int| 0 <= j < n && a[j] == v
}

proof fn lemma_round8(a: Seq<u8>, x: Seq<u8>, y: Seq<u8>, k: int)
    requires
        k == 1 || k == 2 || k == 4 || k == 8,
        a.len() == 16,
        round_inv8(a, x, 16, 2 * k),
        y == Seq::new(16, |i: int| hmax8(x[i], x[(i + k) % 16])),
    ensures
        round_inv8(a, y, 16, k),
{
    assert forall|i: int, d: int| 0 <= i < 16 && 0 <= d < 16 && d % k == 0 implies #[trigger] a[(i + d) % 16]
        <= y[i] by {
        if d % (2 * k) == 0 {
            assert(a[(i + d) % 16] <= x[i]);
        } else {
            let i2 = (i + k) % 16;
            let d2 = if d >= k { d - k } else { d - k + 16 };
            assert(d2 % (2 * k) == 0);
            assert((i2 + d2) % 16 == (i + d) % 16);
            assert(a[(i2 + d2) % 16] <= x[i2]);
        }
    }
    assert forall|i: int| 0 <= i < 16 implies #[trigger] in8(a, y[i], 16) by {
        if x[i] >= x[(i + k) % 16] {
            assert(y[i] == x[i]);
            assert(in8(a, x[i], 16));
        } else {
            let i2 = (i + k) % 16;
            assert(y[i] == x[i2]);
            assert(in8(a, x[i2], 16));
        }
    }
}

#[inline(always)]
fn max_round8<const K: u32>(x: uint8x16_t, Ghost(a): Ghost<Seq<u8>>) -> (y: uint8x16_t)
    requires
        neon(),
        K == 1 || K == 2 || K == 4 || K == 8,
        a.len() == 16,
        round_inv8(a, n8(x), 16, 2 * K),
    ensures
        round_inv8(a, n8(y), 16, K as int),
{
    let t = w_rot8::<K>(x);
    let y = w_max_u8(x, t);
    proof {
        assert(n8(y) =~= Seq::new(16, |i: int| hmax8(n8(x)[i], n8(x)[(i + K) % 16])));
        lemma_round8(a, n8(x), n8(y), K as int);
    }
    y
}

#[inline(always)]
pub fn vmaxvq_u8(a: uint8x16_t) -> (r: u8)
    requires
        neon(),
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] n8(a)[i] <= r,
        exists|i: int| 0 <= i < 16 && #[trigger] n8(a)[i] == r,
{
    let ghost s = n8(a);
    proof {
        assert forall|i: int, d: int| 0 <= i < 16 && 0 <= d < 16 && d % 16 == 0 implies #[trigger] s[(i + d) % 16]
            <= s[i] by {
            assert(d == 0);
        }
        assert forall|i: int| 0 <= i < 16 implies #[trigger] in8(s, s[i], 16) by {
            assert(s[i] == s[i]);
        }
    }
    let x = max_round8::<8>(a, Ghost(s));
    let x = max_round8::<4>(x, Ghost(s));
    let x = max_round8::<2>(x, Ghost(s));
    let x = max_round8::<1>(x, Ghost(s));
    let r = w_extract8_0(x);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] s[i] <= r by {
            assert(s[(0 + i) % 16] <= n8(x)[0]);
        }
        assert(in8(s, n8(x)[0], 16));
    }
    r
}

pub open spec fn hmax16(x: u16, y: u16) -> u16 {
    if x >= y { x } else { y }
}

pub open spec fn round_inv16(a: Seq<u16>, x: Seq<u16>, n: int, step: int) -> bool {
    &&& x.len() == n
    &&& forall|i: int, d: int| 0 <= i < n && 0 <= d < n && d % step == 0 ==> #[trigger] a[(i + d) % n] <= x[i]
    &&& forall|i: int| 0 <= i < n ==> #[trigger] in16(a, x[i], n)
}

pub open spec fn in16(a: Seq<u16>, v: u16, n: int) -> bool {
    exists|j: int| 0 <= j < n && a[j] == v
}

proof fn lemma_round16(a: Seq<u16>, x: Seq<u16>, y: Seq<u16>, k: int)
    requires
        k == 1 || k == 2 || k == 4,
        a.len() == 8,
        round_inv16(a, x, 8, 2 * k),
        y == Seq::new(8, |i: int| hmax16(x[i], x[(i + k) % 8])),
    ensures
        round_inv16(a, y, 8, k),
{
    assert forall|i: int, d: int| 0 <= i < 8 && 0 <= d < 8 && d % k == 0 implies #[trigger] a[(i + d) % 8]
        <= y[i] by {
        if d % (2 * k) == 0 {
            assert(a[(i + d) % 8] <= x[i]);
        } else {
            let i2 = (i + k) % 8;
            let d2 = if d >= k { d - k } else { d - k + 8 };
            assert(d2 % (2 * k) == 0);
            assert((i2 + d2) % 8 == (i + d) % 8);
            assert(a[(i2 + d2) % 8] <= x[i2]);
        }
    }
    assert forall|i: int| 0 <= i < 8 implies #[trigger] in16(a, y[i], 8) by {
        if x[i] >= x[(i + k) % 8] {
            assert(y[i] == x[i]);
            assert(in16(a, x[i], 8));
        } else {
            let i2 = (i + k) % 8;
            assert(y[i] == x[i2]);
            assert(in16(a, x[i2], 8));
        }
    }
}

#[inline(always)]
fn max_round16<const K: u32>(x: uint8x16_t, Ghost(a): Ghost<Seq<u16>>) -> (y: uint8x16_t)
    requires
        neon(),
        K == 1 || K == 2 || K == 4,
        a.len() == 8,
        round_inv16(a, u16s(n8(x)), 8, 2 * K),
    ensures
        round_inv16(a, u16s(n8(y)), 8, K as int),
{
    let t = w_rot16::<K>(x);
    let y = w_max_u16(x, t);
    proof {
        assert(u16s(n8(y)) =~= Seq::new(8, |i: int| hmax16(u16s(n8(x))[i], u16s(n8(x))[(i + K) % 8])));
        lemma_round16(a, u16s(n8(x)), u16s(n8(y)), K as int);
    }
    y
}

#[inline(always)]
pub fn vmaxvq_u16(a: uint8x16_t) -> (r: u16)
    requires
        neon(),
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] u16s(n8(a))[i] <= r,
        exists|i: int| 0 <= i < 8 && #[trigger] u16s(n8(a))[i] == r,
{
    let ghost s = u16s(n8(a));
    proof {
        assert forall|i: int, d: int| 0 <= i < 8 && 0 <= d < 8 && d % 8 == 0 implies #[trigger] s[(i + d) % 8]
            <= s[i] by {
            assert(d == 0);
        }
        assert forall|i: int| 0 <= i < 8 implies #[trigger] in16(s, s[i], 8) by {
            assert(s[i] == s[i]);
        }
    }
    let x = max_round16::<4>(a, Ghost(s));
    let x = max_round16::<2>(x, Ghost(s));
    let x = max_round16::<1>(x, Ghost(s));
    let r = w_extract16_0(x);
    proof {
        assert forall|i: int| 0 <= i < 8 implies #[trigger] s[i] <= r by {
            assert(s[(0 + i) % 8] <= u16s(n8(x))[0]);
        }
        assert(in16(s, u16s(n8(x))[0], 8));
    }
    r
}

// ---------------------------------------------------------------------------
// Compositions
// ---------------------------------------------------------------------------

/// Byte `2j` of a vector is the low byte of 16-bit lane `j`, byte `2j + 1`
/// its high byte.
proof fn lemma_lane_bytes(b: Seq<u8>, j: int)
    requires
        b.len() == 16,
        0 <= j < 8,
    ensures
        b[2 * j] as int == u16s(b)[j] % 256,
        b[2 * j + 1] as int == u16s(b)[j] / 256,
{
    lemma_u16_lane_bytes(b, j);
    lemma_byte16_lo(u16s(b)[j]);
}

/// No byte multiply: the even bytes from the 16-bit products, the odd
/// bytes from the products of the lanes shifted down by 8.
#[inline(always)]
pub fn vmulq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == mullo8(n8(a), n8(b)),
{
    let e = w_mul16(a, b);
    let ah = w_shr_u16(a, 8);
    let bh = w_shr_u16(b, 8);
    let o = w_mul16(ah, bh);
    let r = w_mix_even8(e, o);
    proof {
        let (x, y) = (n8(a), n8(b));
        assert forall|i: int| 0 <= i < 16 implies #[trigger] n8(r)[i] == mullo8(x, y)[i] by {
            let j = i / 2;
            lemma_lane_bytes(x, j);
            lemma_lane_bytes(y, j);
            let (x0, x1, y0, y1) = (x[2 * j] as int, x[2 * j + 1] as int, y[2 * j] as int, y[2 * j + 1] as int);
            let (xl, yl) = (u16s(x)[j] as int, u16s(y)[j] as int);
            assert(xl == x0 + 256 * x1 && yl == y0 + 256 * y1) by {
                lemma_le16_value(x[2 * j], x[2 * j + 1]);
                lemma_le16_value(y[2 * j], y[2 * j + 1]);
            }
            if i % 2 == 0 {
                assert(i == 2 * j);
                lemma_lane_bytes(n8(e), j);
                assert(u16s(n8(e))[j] as int == (xl * yl) % 0x10000);
                let m = x0 * y1 + x1 * y0 + 256 * x1 * y1;
                assert(xl * yl == m * 256 + x0 * y0) by (nonlinear_arith)
                    requires xl == x0 + 256 * x1, yl == y0 + 256 * y1, m == x0 * y1 + x1 * y0 + 256 * x1 * y1;
                vstd::arithmetic::div_mod::lemma_mod_mod(xl * yl, 256, 256);
                vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(m, x0 * y0, 256);
            } else {
                assert(i == 2 * j + 1);
                lemma_lane_bytes(n8(o), j);
                assert((u16s(x)[j] >> 8u16) as int == x1) by {
                    let v = u16s(x)[j];
                    assert(v >> 8u16 == v / 256) by (bit_vector);
                }
                assert((u16s(y)[j] >> 8u16) as int == y1) by {
                    let v = u16s(y)[j];
                    assert(v >> 8u16 == v / 256) by (bit_vector);
                }
                assert(u16s(n8(ah))[j] as int == x1);
                assert(u16s(n8(bh))[j] as int == y1);
                assert(u16s(n8(o))[j] as int == (x1 * y1) % 0x10000);
                vstd::arithmetic::div_mod::lemma_mod_mod(x1 * y1, 256, 256);
            }
        }
        assert(n8(r) =~= mullo8(x, y));
    }
    r
}

/// `uaddlp` on 32-bit lanes: lanes 0, 2 and 1, 3 widened, then added.
#[inline(always)]
pub fn vpaddlq_u32(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == paddl32(u32s(n8(a))),
{
    let s = w_shuf32_0213(a);
    let lo = w_extend_lo32(s);
    let hi = w_extend_hi32(s);
    let r = w_add64(lo, hi);
    assert(u64s(n8(r)) =~= paddl32(u32s(n8(a))));
    r
}

/// `addp` on bytes: the even bytes of `a` then `b`, plus the odd bytes.
#[inline(always)]
pub fn vpaddq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == padd8(n8(a), n8(b)),
{
    let e = w_even8(a, b);
    let o = w_odd8(a, b);
    let r = w_add8(e, o);
    assert(n8(r) =~= padd8(n8(a), n8(b)));
    r
}

/// `shrn #4`: the 16-bit lanes shifted down by 4, their low bytes packed
/// into 64 bits.
#[inline(always)]
pub fn vshrn4_u64(a: uint8x16_t) -> (r: u64)
    requires
        neon(),
    ensures
        forall|k: u64|
            k < 16 ==> #[trigger] ((r >> (4 * k)) & 15) == (if k % 2 == 0 {
                (n8(a)[k as int] >> 4u8) as u64
            } else {
                (n8(a)[k as int] & 15u8) as u64
            }),
{
    let s = w_shr_u16(a, 4);
    let e = w_even8(s, s);
    let r = w_extract64::<0>(e);
    proof {
        let x = n8(a);
        let b = n8(e);
        // Byte j of e is the low byte of lane j of s: bits 4..12 of lane j of a.
        assert forall|j: int| 0 <= j < 8 implies (#[trigger] b[j] & 15u8) == (x[2 * j] >> 4u8) && (b[j] >> 4u8)
            == (x[2 * j + 1] & 15u8) by {
            assert(b[j] == n8(s)[2 * j]);
            lemma_u16_lane_bytes(n8(s), j);
            let (x0, x1) = (x[2 * j], x[2 * j + 1]);
            assert(u16s(x)[j] == le16(x0, x1));
            let t = (le16(x0, x1) >> 4u16);
            assert(u16s(n8(s))[j] == t);
            assert(b[j] == byte16(t, 0));
            assert((((((x0 as u16) | ((x1 as u16) << 8u16)) >> 4u16) & 0xff) as u8 & 15u8) == (x0 >> 4u8))
                by (bit_vector);
            assert(((((((x0 as u16) | ((x1 as u16) << 8u16)) >> 4u16) & 0xff) as u8) >> 4u8) == (x1 & 15u8))
                by (bit_vector);
        }
        // r is e's low eight bytes, little-endian.
        lemma_u64_bytes(b);
        assert forall|k: u64| k < 16 implies #[trigger] ((r >> (4 * k)) & 15) == (if k % 2 == 0 {
            (x[k as int] >> 4u8) as u64
        } else {
            (x[k as int] & 15u8) as u64
        }) by {
            let j = (k / 2) as int;
            let bj = b[j];
            assert(((r >> (8 * (k / 2))) & 0xff) == bj as u64);
            let h = k / 2;
            if k % 2 == 0 {
                assert(k == 2 * h);
                assert(((r >> (8 * h)) & 0xff) == bj as u64 ==> ((r >> (4 * (2 * h))) & 15) == (bj & 15u8) as u64)
                    by (bit_vector) requires h < 8;
            } else {
                assert(k == 2 * h + 1);
                assert(((r >> (8 * h)) & 0xff) == bj as u64 ==> ((r >> (4 * (2 * h + 1))) & 15) == (bj >> 4u8) as u64)
                    by (bit_vector) requires h < 8;
            }
        }
    }
    r
}

/// The low 64-bit lane, read by bytes.
proof fn lemma_u64_bytes(b: Seq<u8>)
    requires
        b.len() == 16,
    ensures
        forall|h: u64| h < 8 ==> #[trigger] ((u64s(b)[0] >> (8 * h)) & 0xff) == b[h as int] as u64,
{
    let (b0, b1, b2, b3, b4, b5, b6, b7) = (b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
    let w0 = le32(b0, b1, b2, b3);
    let w1 = le32(b4, b5, b6, b7);
    assert(u32s(b)[0] == w0 && u32s(b)[1] == w1);
    let v = u64s(b)[0];
    assert(v == le64(w0, w1));
    assert forall|h: u64| h < 8 implies #[trigger] ((v >> (8 * h)) & 0xff) == b[h as int] as u64 by {
        assert(v == ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) as u64
            | ((((b4 as u32) | ((b5 as u32) << 8u32) | ((b6 as u32) << 16u32) | ((b7 as u32) << 24u32)) as u64)
            << 32u64));
        if h == 0 {
            assert(v == ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) as u64
                | ((((b4 as u32) | ((b5 as u32) << 8u32) | ((b6 as u32) << 16u32) | ((b7 as u32) << 24u32)) as u64)
                << 32u64) ==> ((v >> 0u64) & 0xff) == b0 as u64) by (bit_vector);
        } else if h == 1 {
            assert(v == ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) as u64
                | ((((b4 as u32) | ((b5 as u32) << 8u32) | ((b6 as u32) << 16u32) | ((b7 as u32) << 24u32)) as u64)
                << 32u64) ==> ((v >> 8u64) & 0xff) == b1 as u64) by (bit_vector);
        } else if h == 2 {
            assert(v == ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) as u64
                | ((((b4 as u32) | ((b5 as u32) << 8u32) | ((b6 as u32) << 16u32) | ((b7 as u32) << 24u32)) as u64)
                << 32u64) ==> ((v >> 16u64) & 0xff) == b2 as u64) by (bit_vector);
        } else if h == 3 {
            assert(v == ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) as u64
                | ((((b4 as u32) | ((b5 as u32) << 8u32) | ((b6 as u32) << 16u32) | ((b7 as u32) << 24u32)) as u64)
                << 32u64) ==> ((v >> 24u64) & 0xff) == b3 as u64) by (bit_vector);
        } else if h == 4 {
            assert(v == ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) as u64
                | ((((b4 as u32) | ((b5 as u32) << 8u32) | ((b6 as u32) << 16u32) | ((b7 as u32) << 24u32)) as u64)
                << 32u64) ==> ((v >> 32u64) & 0xff) == b4 as u64) by (bit_vector);
        } else if h == 5 {
            assert(v == ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) as u64
                | ((((b4 as u32) | ((b5 as u32) << 8u32) | ((b6 as u32) << 16u32) | ((b7 as u32) << 24u32)) as u64)
                << 32u64) ==> ((v >> 40u64) & 0xff) == b5 as u64) by (bit_vector);
        } else if h == 6 {
            assert(v == ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) as u64
                | ((((b4 as u32) | ((b5 as u32) << 8u32) | ((b6 as u32) << 16u32) | ((b7 as u32) << 24u32)) as u64)
                << 32u64) ==> ((v >> 48u64) & 0xff) == b6 as u64) by (bit_vector);
        } else {
            assert(v == ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) as u64
                | ((((b4 as u32) | ((b5 as u32) << 8u32) | ((b6 as u32) << 16u32) | ((b7 as u32) << 24u32)) as u64)
                << 32u64) ==> ((v >> 56u64) & 0xff) == b7 as u64) by (bit_vector);
        }
    }
}


// ---------------------------------------------------------------------------
// For the JPEG and WebP kernels
// ---------------------------------------------------------------------------

/// Absolute value of each signed 16-bit lane (`abs`); `-0x8000` stays
/// `0x8000`.
#[inline(always)]
pub fn vabsq_s16(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == abs16(u16s(n8(a))),
{
    let r = w_abs16(a);
    assert(u16s(n8(r)) =~= abs16(u16s(n8(a))));
    r
}

/// Wrapping 16-bit addition.
#[inline(always)]
pub fn vaddq_s16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == add16(u16s(n8(a)), u16s(n8(b))),
{
    let r = w_add16(a, b);
    assert(u16s(n8(r)) =~= add16(u16s(n8(a)), u16s(n8(b))));
    r
}

/// Wrapping 32-bit addition.
#[inline(always)]
pub fn vaddq_u32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == add32(u32s(n8(a)), u32s(n8(b))),
{
    let r = w_add32(a, b);
    assert(u32s(n8(r)) =~= add32(u32s(n8(a)), u32s(n8(b))));
    r
}

/// Wrapping 16-bit subtraction.
#[inline(always)]
pub fn vsubq_s16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == sub16(u16s(n8(a)), u16s(n8(b))),
{
    let r = w_sub16(a, b);
    assert(u16s(n8(r)) =~= sub16(u16s(n8(a)), u16s(n8(b))));
    r
}

/// Wrapping 32-bit subtraction.
#[inline(always)]
pub fn vsubq_u32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == sub32(u32s(n8(a)), u32s(n8(b))),
{
    let r = w_sub32(a, b);
    assert(u32s(n8(r)) =~= sub32(u32s(n8(a)), u32s(n8(b))));
    r
}

/// Wrapping byte subtraction.
#[inline(always)]
pub fn vsubq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == sub8(n8(a), n8(b)),
{
    let r = w_sub8(a, b);
    assert(n8(r) =~= sub8(n8(a), n8(b)));
    r
}

/// The vector whose low 64 bits are `lo` and whose high 64 bits are `hi`,
/// little-endian (`fmov d, x` and `mov v.d[1], x`; `vcombine_u64` of two
/// `vcreate_u64`).
#[inline(always)]
pub fn vcombine_u64(lo: u64, hi: u64) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == seq![lo, hi],
{
    let r = w_make64(lo, hi);
    assert(u64s(n8(r)) =~= seq![lo, hi]);
    r
}

/// 32-bit lane 3 of `a` in each 32-bit lane.
#[inline(always)]
pub fn vdupq_laneq_u32_3(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == splat32(u32s(n8(a))[3], 4),
{
    let r = w_dup32_3(a, a);
    assert(u32s(n8(r)) =~= splat32(u32s(n8(a))[3], 4));
    r
}

/// `x` in each 32-bit lane.
#[inline(always)]
pub fn vdupq_n_u32(x: u32) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == splat32(x, 4),
{
    let r = w_splat32(x);
    assert(u32s(n8(r)) =~= splat32(x, 4));
    r
}

/// Bytes `N..N + 16` of `a` followed by `b`.
#[inline(always)]
pub fn vextq_u8<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= N <= 15,
    ensures
        n8(r) == alignr_lanes(n8(b), n8(a), N as int),
{
    let r = w_ext::<N>(a, b);
    assert(n8(r) =~= alignr_lanes(n8(b), n8(a), N as int));
    r
}

/// The eight 16-bit values at `s[i..i + 8]`, as their bits.
#[inline(always)]
pub fn vld1q_s16_at(s: &[i16], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 8 <= s@.len(),
    ensures
        u16s(n8(r)) == s@.subrange(i as int, i + 8).map_values(|x: i16| x as u16),
{
    let r = w_load_s16(s, i);
    assert(u16s(n8(r)) =~= s@.subrange(i as int, i + 8).map_values(|x: i16| x as u16));
    r
}

/// The 8 bytes at `s[i..i + 8]` in the low half, zeros in the high half
/// (`ldr d`; `vcombine_u8` of `vld1_u8` and zero).
#[inline(always)]
pub fn vld1q_u8_low_at(s: &[u8], i: usize) -> (r: uint8x16_t)
    requires
        neon(),
        i + 8 <= s@.len(),
    ensures
        n8(r) == s@.subrange(i as int, i + 8) + splat8(0u8, 8),
{
    let r = w_load64_zero(s, i);
    assert(n8(r) =~= s@.subrange(i as int, i + 8) + splat8(0u8, 8));
    r
}

/// Unsigned 16-bit maximum (`umax`).
#[inline(always)]
pub fn vmaxq_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == max_u16(u16s(n8(a)), u16s(n8(b))),
{
    let r = w_max_u16(a, b);
    assert(u16s(n8(r)) =~= max_u16(u16s(n8(a)), u16s(n8(b))));
    r
}

/// Unsigned byte maximum (`umax`).
#[inline(always)]
pub fn vmaxq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == max_u8(n8(a), n8(b)),
{
    let r = w_max_u8(a, b);
    assert(n8(r) =~= max_u8(n8(a), n8(b)));
    r
}

/// The signed products of the low four 16-bit lanes, as 32-bit lanes
/// (`smull`; `vmull_s16` of `vget_low_s16`).
#[inline(always)]
pub fn vmull_lo_s16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == mull_lo_s16(u16s(n8(a)), u16s(n8(b))),
{
    let r = w_extmul_lo16(a, b);
    assert(u32s(n8(r)) =~= mull_lo_s16(u16s(n8(a)), u16s(n8(b))));
    r
}

/// The signed products of the high four 16-bit lanes, as 32-bit lanes
/// (`smull2`; `vmull_high_s16`).
#[inline(always)]
pub fn vmull_hi_s16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == mull_hi_s16(u16s(n8(a)), u16s(n8(b))),
{
    let r = w_extmul_hi16(a, b);
    assert(u32s(n8(r)) =~= mull_hi_s16(u16s(n8(a)), u16s(n8(b))));
    r
}

/// Signed saturating byte addition (`sqadd`).
#[inline(always)]
pub fn vqaddq_s8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == adds_s8(n8(a), n8(b)),
{
    let r = w_add_sat_s8(a, b);
    assert(n8(r) =~= adds_s8(n8(a), n8(b)));
    r
}

/// Unsigned saturating 16-bit addition (`uqadd`).
#[inline(always)]
pub fn vqaddq_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == adds_u16(u16s(n8(a)), u16s(n8(b))),
{
    let r = w_add_sat_u16(a, b);
    assert(u16s(n8(r)) =~= adds_u16(u16s(n8(a)), u16s(n8(b))));
    r
}

/// Unsigned saturating byte addition (`uqadd`).
#[inline(always)]
pub fn vqaddq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == adds_u8(n8(a), n8(b)),
{
    let r = w_add_sat_u8(a, b);
    assert(n8(r) =~= adds_u8(n8(a), n8(b)));
    r
}

/// Signed saturating byte subtraction (`sqsub`).
#[inline(always)]
pub fn vqsubq_s8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == subs_s8(n8(a), n8(b)),
{
    let r = w_sub_sat_s8(a, b);
    assert(n8(r) =~= subs_s8(n8(a), n8(b)));
    r
}

/// Unsigned saturating 16-bit subtraction (`uqsub`).
#[inline(always)]
pub fn vqsubq_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == subs_u16(u16s(n8(a)), u16s(n8(b))),
{
    let r = w_sub_sat_u16(a, b);
    assert(u16s(n8(r)) =~= subs_u16(u16s(n8(a)), u16s(n8(b))));
    r
}

/// Unsigned rounding halving add (`urhadd`): `(a + b + 1) >> 1` per byte.
#[inline(always)]
pub fn vrhaddq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == avg_u8(n8(a), n8(b)),
{
    let r = w_avgr_u8(a, b);
    assert(n8(r) =~= avg_u8(n8(a), n8(b)));
    r
}

/// Shift left of each 32-bit lane by `N` (0 to 31).
#[inline(always)]
pub fn vshlq_n_u32<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= N <= 31,
    ensures
        u32s(n8(r)) == slli32(u32s(n8(a)), N as int),
{
    let r = w_shl32(a, N as u32);
    assert(u32s(n8(r)) =~= slli32(u32s(n8(a)), N as int));
    r
}

/// Arithmetic shift right of each signed 16-bit lane by `N` (1 to 15).
#[inline(always)]
pub fn vshrq_n_s16<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 15,
    ensures
        u16s(n8(r)) == srai16(u16s(n8(a)), N as int),
{
    let r = w_shr_s16(a, N as u32);
    assert(u16s(n8(r)) =~= srai16(u16s(n8(a)), N as int));
    r
}

/// The odd 16-bit lanes of `a`, then those of `b` (`uzp2`).
#[inline(always)]
pub fn vuzp2q_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == uzp2_16(u16s(n8(a)), u16s(n8(b))),
{
    let r = w_odd16(a, b);
    assert(u16s(n8(r)) =~= uzp2_16(u16s(n8(a)), u16s(n8(b))));
    r
}

/// Interleaves the low four 16-bit lanes of `a` and `b`.
#[inline(always)]
pub fn vzip1q_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == unpacklo16_lanes(u16s(n8(a)), u16s(n8(b))),
{
    let r = w_zip_lo16(a, b);
    assert(u16s(n8(r)) =~= unpacklo16_lanes(u16s(n8(a)), u16s(n8(b))));
    r
}

/// Interleaves the high four 16-bit lanes of `a` and `b`.
#[inline(always)]
pub fn vzip2q_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == unpackhi16_lanes(u16s(n8(a)), u16s(n8(b))),
{
    let r = w_zip_hi16(a, b);
    assert(u16s(n8(r)) =~= unpackhi16_lanes(u16s(n8(a)), u16s(n8(b))));
    r
}

/// Interleaves the low two 32-bit lanes of `a` and `b`.
#[inline(always)]
pub fn vzip1q_u32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == unpacklo32_lanes(u32s(n8(a)), u32s(n8(b))),
{
    let r = w_zip_lo32(a, b);
    assert(u32s(n8(r)) =~= unpacklo32_lanes(u32s(n8(a)), u32s(n8(b))));
    r
}

/// Interleaves the high two 32-bit lanes of `a` and `b`.
#[inline(always)]
pub fn vzip2q_u32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == unpackhi32_lanes(u32s(n8(a)), u32s(n8(b))),
{
    let r = w_zip_hi32(a, b);
    assert(u32s(n8(r)) =~= unpackhi32_lanes(u32s(n8(a)), u32s(n8(b))));
    r
}

/// The low 64 bits of `a`, then those of `b`.
#[inline(always)]
pub fn vzip1q_u64(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == unpacklo64_lanes(u64s(n8(a)), u64s(n8(b))),
{
    let r = w_zip_lo64(a, b);
    assert(u64s(n8(r)) =~= unpacklo64_lanes(u64s(n8(a)), u64s(n8(b))));
    r
}

/// The high 64 bits of `a`, then those of `b`.
#[inline(always)]
pub fn vzip2q_u64(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == unpackhi64_lanes(u64s(n8(a)), u64s(n8(b))),
{
    let r = w_zip_hi64(a, b);
    assert(u64s(n8(r)) =~= unpackhi64_lanes(u64s(n8(a)), u64s(n8(b))));
    r
}

/// Stores `v` as four 32-bit values at `s[i..i + 4]`.
#[inline(always)]
pub fn vst1q_u32_at(s: &mut [u32], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 4 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u32s(n8(v)) + old(s)@.subrange(i + 4, old(s)@.len() as int),
{
    w_store32(s, i, v)
}

/// Stores `v` as eight 16-bit values at `s[i..i + 8]`.
#[inline(always)]
pub fn vst1q_s16_at(s: &mut [i16], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 8 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u16s(n8(v)).map_values(|x: u16| x as i16)
            + old(s)@.subrange(i + 8, old(s)@.len() as int),
{
    w_store_s16(s, i, v)
}

/// Stores the low 8 bytes of `v` at `s[i..i + 8]` (`str d`; `vst1_u8` of
/// `vget_low_u8`).
#[inline(always)]
pub fn vst1q_u8_low_at(s: &mut [u8], i: usize, v: uint8x16_t)
    requires
        neon(),
        i + 8 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + n8(v).subrange(0, 8) + old(s)@.subrange(i + 8, old(s)@.len() as int),
{
    w_store64_lo(s, i, v)
}

/// Stores 32-bit lane `N` of `v`, its bytes `4 * N..4 * N + 4`, at
/// `s[i..i + 4]` (`str s` for lane 0, `st1 v.s[N]` otherwise;
/// `vgetq_lane_u32` and an unaligned store).
#[inline(always)]
pub fn vst1q_lane_u32_at<const N: i32>(s: &mut [u8], i: usize, v: uint8x16_t)
    requires
        neon(),
        0 <= N <= 3,
        i + 4 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + n8(v).subrange(4 * N, 4 * N + 4) + old(s)@.subrange(i + 4, old(s)@.len() as int),
{
    w_store32_lane::<N>(s, i, v)
}

/// The signed products of the low four 16-bit lanes of `a` with lane `L`
/// of `c`, as 32-bit lanes (`smull` by element; `vmull_laneq_s16` of
/// `vget_low_s16`).
#[inline(always)]
pub fn vmull_lo_laneq_s16<const L: i32>(a: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        u32s(n8(r)) == mull_lo_lane_s16(u16s(n8(a)), u16s(n8(c)), L as int),
{
    let d = w_dup16::<L>(c);
    let r = w_extmul_lo16(a, d);
    assert(u32s(n8(r)) =~= mull_lo_lane_s16(u16s(n8(a)), u16s(n8(c)), L as int));
    r
}

/// The signed products of the high four 16-bit lanes of `a` with lane `L`
/// of `c`, as 32-bit lanes (`smull2` by element; `vmull_high_laneq_s16`).
#[inline(always)]
pub fn vmull_hi_laneq_s16<const L: i32>(a: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        u32s(n8(r)) == mull_hi_lane_s16(u16s(n8(a)), u16s(n8(c)), L as int),
{
    let d = w_dup16::<L>(c);
    let r = w_extmul_hi16(a, d);
    assert(u32s(n8(r)) =~= mull_hi_lane_s16(u16s(n8(a)), u16s(n8(c)), L as int));
    r
}

/// `acc` plus the signed products of the low four 16-bit lanes of `a` with
/// lane `L` of `c`, wrapping (`smlal` by element; `vmlal_laneq_s16` of
/// `vget_low_s16`).
#[inline(always)]
pub fn vmlal_lo_laneq_s16<const L: i32>(acc: uint8x16_t, a: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        u32s(n8(r)) == mlal_lo_lane_s16(u32s(n8(acc)), u16s(n8(a)), u16s(n8(c)), L as int),
{
    let d = w_dup16::<L>(c);
    let p = w_extmul_lo16(a, d);
    let r = w_add32(acc, p);
    proof {
        assert forall|i: int| 0 <= i < 4 implies #[trigger] u32s(n8(r))[i] == mlal_lo_lane_s16(
            u32s(n8(acc)),
            u16s(n8(a)),
            u16s(n8(c)),
            L as int,
        )[i] by {
            let m = s16(u16s(n8(a))[i]) * s16(u16s(n8(c))[L as int]);
            lemma_add_mod32(u32s(n8(acc))[i] as int, m);
        }
        assert(u32s(n8(r)) =~= mlal_lo_lane_s16(u32s(n8(acc)), u16s(n8(a)), u16s(n8(c)), L as int));
    }
    r
}

/// `acc` plus the signed products of the high four 16-bit lanes of `a`
/// with lane `L` of `c`, wrapping (`smlal2` by element;
/// `vmlal_high_laneq_s16`).
#[inline(always)]
pub fn vmlal_hi_laneq_s16<const L: i32>(acc: uint8x16_t, a: uint8x16_t, c: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        u32s(n8(r)) == mlal_hi_lane_s16(u32s(n8(acc)), u16s(n8(a)), u16s(n8(c)), L as int),
{
    let d = w_dup16::<L>(c);
    let p = w_extmul_hi16(a, d);
    let r = w_add32(acc, p);
    proof {
        assert forall|i: int| 0 <= i < 4 implies #[trigger] u32s(n8(r))[i] == mlal_hi_lane_s16(
            u32s(n8(acc)),
            u16s(n8(a)),
            u16s(n8(c)),
            L as int,
        )[i] by {
            let m = s16(u16s(n8(a))[4 + i]) * s16(u16s(n8(c))[L as int]);
            lemma_add_mod32(u32s(n8(acc))[i] as int, m);
        }
        assert(u32s(n8(r)) =~= mlal_hi_lane_s16(u32s(n8(acc)), u16s(n8(a)), u16s(n8(c)), L as int));
    }
    r
}

/// `a & !b` (`bic`: the second operand is the one complemented).
#[inline(always)]
pub fn vbicq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == andnot8(n8(b), n8(a)),
{
    let r = w_andnot(a, b);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] n8(r)[i] == andnot8(n8(b), n8(a))[i] by {
            let (x, y) = (n8(a)[i], n8(b)[i]);
            assert(x & !y == !y & x) by (bit_vector);
        }
        assert(n8(r) =~= andnot8(n8(b), n8(a)));
    }
    r
}

/// Absolute difference of unsigned bytes (`uabd`).
#[inline(always)]
pub fn vabdq_u8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == abd_u8(n8(a), n8(b)),
{
    let x = w_sub_sat_u8(a, b);
    let y = w_sub_sat_u8(b, a);
    let r = w_or(x, y);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] n8(r)[i] == abd_u8(n8(a), n8(b))[i] by {
            let (p, q) = (n8(x)[i], n8(y)[i]);
            assert(p | 0u8 == p && 0u8 | q == q) by (bit_vector);
        }
        assert(n8(r) =~= abd_u8(n8(a), n8(b)));
    }
    r
}

/// `x` in each 16-bit lane.
#[inline(always)]
pub fn vdupq_n_s16(x: i16) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == splat16(u16_of_i16(x), 8),
{
    // `u16_of_i16`, written out so the cast never truncates.
    let u: u16 = if x < 0 {
        (x as i32 + 0x1_0000) as u16
    } else {
        x as u16
    };
    let r = w_splat16(u);
    proof {
        assert(u16s(n8(r)) =~= splat16(u16_of_i16(x), 8));
    }
    r
}

/// Arithmetic shift right of each signed byte by `N` (1 to 8) (`sshr`).
#[inline(always)]
pub fn vshrq_n_s8<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 8,
    ensures
        n8(r) == sra8(n8(a), N as int),
{
    reveal_with_fuel(pow2_spec, 9);
    // `i8x16.shr_s` by 8 is a shift by 0; NEON's `sshr #8` fills with the sign.
    let r = w_shr_s8(a, if N == 8 { 7 } else { N as u32 });
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] n8(r)[i] == sra8(n8(a), N as int)[i] by {
            let v = s8(n8(a)[i]);
            if N == 8 {
                assert(v / 128 == v / 256) by {
                    assert(-128 <= v < 128);
                }
            }
        }
        assert(n8(r) =~= sra8(n8(a), N as int));
    }
    r
}

/// The low eight bytes of `a`, zero-extended to 16-bit lanes and shifted
/// left by `N` (0 to 8) (`ushll`; `vshll_n_u8` of `vget_low_u8`). The
/// 16-bit view of `a`'s low bytes interleaved with zeros is those bytes
/// zero-extended.
#[inline(always)]
pub fn vshll_low_n_u8<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= N <= 8,
    ensures
        u16s(n8(r)) == slli16(u16s(unpacklo8_lanes(n8(a), splat8(0, 16))), N as int),
{
    let e = w_extend_lo8(a);
    let r = w_shl16(e, N as u32);
    proof {
        let z = unpacklo8_lanes(n8(a), splat8(0, 16));
        assert forall|i: int| 0 <= i < 8 implies #[trigger] u16s(z)[i] == u16s(n8(e))[i] by {
            assert(z[2 * i] == n8(a)[i] && z[2 * i + 1] == 0);
            lemma_le16_value(n8(a)[i], 0);
        }
        assert(u16s(z) =~= u16s(n8(e)));
        assert(u16s(n8(r)) =~= slli16(u16s(z), N as int));
    }
    r
}

/// The high eight bytes of `a`, zero-extended to 16-bit lanes and shifted
/// left by `N` (0 to 8) (`ushll2`).
#[inline(always)]
pub fn vshll_high_n_u8<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= N <= 8,
    ensures
        u16s(n8(r)) == slli16(u16s(unpackhi8_lanes(n8(a), splat8(0, 16))), N as int),
{
    let e = w_extend_hi8(a);
    let r = w_shl16(e, N as u32);
    proof {
        let z = unpackhi8_lanes(n8(a), splat8(0, 16));
        assert forall|i: int| 0 <= i < 8 implies #[trigger] u16s(z)[i] == u16s(n8(e))[i] by {
            assert(z[2 * i] == n8(a)[8 + i] && z[2 * i + 1] == 0);
            lemma_le16_value(n8(a)[8 + i], 0);
        }
        assert(u16s(z) =~= u16s(n8(e)));
        assert(u16s(n8(r)) =~= slli16(u16s(z), N as int));
    }
    r
}

/// The sum of the eight 16-bit lanes (`uaddlv`).
#[inline(always)]
pub fn vaddlvq_u16(a: uint8x16_t) -> (r: u32)
    requires
        neon(),
    ensures
        r as int == sum_u16(u16s(n8(a))),
{
    let e = w_extadd16(a);
    let e2 = w_rot32_2(e, e);
    let f = w_add32(e, e2);
    let f1 = w_rot32_1(f, f);
    let g = w_add32(f, f1);
    let r = w_extract32_0(g);
    proof {
        let h = u16s(n8(a));
        reveal_with_fuel(sum_u16, 9);
        assert(h.drop_last().drop_last().drop_last().drop_last().drop_last().drop_last().drop_last().drop_last()
            =~= Seq::<u16>::empty());
        assert(sum_u16(h) == h[0] + h[1] + h[2] + h[3] + h[4] + h[5] + h[6] + h[7]);
    }
    r
}

/// Signed saturating doubling multiply, high half (`sqdmulh`).
#[inline(always)]
pub fn vqdmulhq_s16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == qdmulh_s16(u16s(n8(a)), u16s(n8(b))),
{
    let lo = w_extmul_lo16(a, b);
    let hi = w_extmul_hi16(a, b);
    let lo2 = w_shr_s32(lo, 15);
    let hi2 = w_shr_s32(hi, 15);
    let r = w_narrow_s32(lo2, hi2);
    proof {
        reveal_with_fuel(pow2_spec, 16);
        assert(pow2_spec(15) == 0x8000);
        let (x, y) = (u16s(n8(a)), u16s(n8(b)));
        assert forall|i: int| 0 <= i < 8 implies #[trigger] u16s(n8(r))[i] == qdmulh_s16(x, y)[i] by {
            let p = s16(x[i]) * s16(y[i]);
            lemma_qdmulh_lane(s16(x[i]), s16(y[i]));
            let k = if i < 4 { i } else { i - 4 };
            let w = if i < 4 { lo } else { hi };
            let w2 = if i < 4 { lo2 } else { hi2 };
            assert(u32s(n8(w))[k] == (p % 0x1_0000_0000) as u32);
            lemma_s32_small(p);
            assert(u32s(n8(w2))[k] == ((p / 0x8000) % 0x1_0000_0000) as u32);
            lemma_s32_small(p / 0x8000);
        }
        assert(u16s(n8(r)) =~= qdmulh_s16(x, y));
    }
    r
}

/// Rounding arithmetic shift right of each signed 32-bit lane by `N` (1 to
/// 31) (`srshr`).
#[inline(always)]
pub fn vrshrq_n_s32<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 31,
    ensures
        u32s(n8(r)) == rshr_s32(u32s(n8(a)), N as int),
{
    let q = w_shr_s32(a, (N - 1) as u32);
    let h = w_shr_s32(a, N as u32);
    let r = w_sub32(q, h);
    proof {
        assert forall|i: int| 0 <= i < 4 implies #[trigger] u32s(n8(r))[i] == rshr_s32(u32s(n8(a)), N as int)[i] by {
            let v = s32(u32s(n8(a))[i]);
            lemma_rshr(v, N as nat);
            let p = pow2_spec((N - 1) as nat) as int;
            let qq = v / p;
            let hh = v / pow2_spec(N as nat) as int;
            lemma_sub_mod32(qq, hh);
        }
        assert(u32s(n8(r)) =~= rshr_s32(u32s(n8(a)), N as int));
    }
    r
}

/// Each signed 32-bit lane of `a` shifted right by `N` (1 to 16) with
/// rounding and cut to 16 bits, in the low half; zeros in the high half
/// (`rshrn`; `vcombine_s16` of `vrshrn_n_s32` and zero).
#[inline(always)]
pub fn vrshrn_lo_n_s32<const N: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 16,
    ensures
        u16s(n8(r)) == rshrn_s32(u32s(n8(a)), N as int) + splat16(0, 4),
{
    let t = vrshrq_n_s32::<N>(a);
    let z = w_splat32(0);
    let r = w_even16(t, z);
    proof {
        lemma_low16(n8(t));
        lemma_low16(n8(z));
        assert forall|k: int| 0 <= k < 4 implies #[trigger] u16s(n8(r))[k] == rshrn_s32(u32s(n8(a)), N as int)[k] by {
            let v = (s32(u32s(n8(a))[k]) + pow2_spec((N - 1) as nat)) / pow2_spec(N as nat) as int;
            vstd::arithmetic::div_mod::lemma_mod_mod(v, 0x10000, 0x10000);
        }
        assert(u16s(n8(r)) =~= rshrn_s32(u32s(n8(a)), N as int) + splat16(0, 4));
    }
    r
}

/// Each signed 32-bit lane of `a`, then of `b`, shifted right by `N` (1 to
/// 16) with rounding and cut to 16 bits (`rshrn` and `rshrn2`;
/// `vrshrn_high_n_s32` of `vrshrn_n_s32`).
#[inline(always)]
pub fn vrshrn2_n_s32<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 16,
    ensures
        u16s(n8(r)) == rshrn_s32(u32s(n8(a)), N as int) + rshrn_s32(u32s(n8(b)), N as int),
{
    let ta = vrshrq_n_s32::<N>(a);
    let tb = vrshrq_n_s32::<N>(b);
    let r = w_even16(ta, tb);
    proof {
        lemma_low16(n8(ta));
        lemma_low16(n8(tb));
        assert forall|k: int| 0 <= k < 8 implies #[trigger] u16s(n8(r))[k] == (rshrn_s32(u32s(n8(a)), N as int)
            + rshrn_s32(u32s(n8(b)), N as int))[k] by {
            let s = if k < 4 { u32s(n8(a))[k] } else { u32s(n8(b))[k - 4] };
            let v = (s32(s) + pow2_spec((N - 1) as nat)) / pow2_spec(N as nat) as int;
            vstd::arithmetic::div_mod::lemma_mod_mod(v, 0x10000, 0x10000);
        }
        assert(u16s(n8(r)) =~= rshrn_s32(u32s(n8(a)), N as int) + rshrn_s32(u32s(n8(b)), N as int));
    }
    r
}

/// Each signed 16-bit lane of `a`, then of `b`, shifted right by `N` (1 to
/// 8) and saturated to a signed byte (`sqshrn` and `sqshrn2`;
/// `vqshrn_high_n_s16` of `vqshrn_n_s16`).
#[inline(always)]
pub fn vqshrn2_n_s16<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 8,
    ensures
        n8(r) == packs16_lanes(srai16(u16s(n8(a)), N as int), srai16(u16s(n8(b)), N as int)),
{
    let sa = w_shr_s16(a, N as u32);
    let sb = w_shr_s16(b, N as u32);
    let r = w_narrow_s16(sa, sb);
    proof {
        reveal_with_fuel(pow2_spec, 9);
        assert(u16s(n8(sa)) =~= srai16(u16s(n8(a)), N as int));
        assert(u16s(n8(sb)) =~= srai16(u16s(n8(b)), N as int));
        assert(n8(r) =~= packs16_lanes(srai16(u16s(n8(a)), N as int), srai16(u16s(n8(b)), N as int)));
    }
    r
}

/// Each signed 16-bit lane of `a`, then of `b`, shifted right by `N` (1 to
/// 8) and saturated to an unsigned byte (`sqshrun` and `sqshrun2`;
/// `vqshrun_high_n_s16` of `vqshrun_n_s16`).
#[inline(always)]
pub fn vqshrun2_n_s16<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 8,
    ensures
        n8(r) == packus16_lanes(srai16(u16s(n8(a)), N as int), srai16(u16s(n8(b)), N as int)),
{
    let sa = w_shr_s16(a, N as u32);
    let sb = w_shr_s16(b, N as u32);
    let r = w_narrow_u16(sa, sb);
    proof {
        reveal_with_fuel(pow2_spec, 9);
        assert(u16s(n8(sa)) =~= srai16(u16s(n8(a)), N as int));
        assert(u16s(n8(sb)) =~= srai16(u16s(n8(b)), N as int));
        assert(n8(r) =~= packus16_lanes(srai16(u16s(n8(a)), N as int), srai16(u16s(n8(b)), N as int)));
    }
    r
}

/// Each unsigned 16-bit lane of `a`, then of `b`, shifted right by `N` (1
/// to 8) and saturated to a byte (`uqshrn` and `uqshrn2`;
/// `vqshrn_high_n_u16` of `vqshrn_n_u16`). A lane shifted right by at least
/// one is below 2^15, so the signed saturation of `packus16_lanes` sees it
/// as it is.
#[inline(always)]
pub fn vqshrn2_n_u16<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        1 <= N <= 8,
    ensures
        n8(r) == packus16_lanes(srli16(u16s(n8(a)), N as int), srli16(u16s(n8(b)), N as int)),
{
    let sa = w_shr_u16(a, N as u32);
    let sb = w_shr_u16(b, N as u32);
    let r = w_narrow_u16(sa, sb);
    proof {
        reveal_with_fuel(pow2_spec, 9);
        assert forall|j: int| 0 <= j < 8 implies #[trigger] u16s(n8(sa))[j] == srli16(u16s(n8(a)), N as int)[j] by {
            lemma_shr_u16(u16s(n8(a))[j], N as u16);
        }
        assert forall|j: int| 0 <= j < 8 implies #[trigger] u16s(n8(sb))[j] == srli16(u16s(n8(b)), N as int)[j] by {
            lemma_shr_u16(u16s(n8(b))[j], N as u16);
        }
        assert(u16s(n8(sa)) =~= srli16(u16s(n8(a)), N as int));
        assert(u16s(n8(sb)) =~= srli16(u16s(n8(b)), N as int));
        assert(n8(r) =~= packus16_lanes(srli16(u16s(n8(a)), N as int), srli16(u16s(n8(b)), N as int)));
    }
    r
}

/// Stores the bytes of `a`, `b` and `c` interleaved at `s[i..i + 48]`
/// (`st3`): `a[0], b[0], c[0], a[1], ...`.
#[inline(always)]
pub fn vst3q_u8_at(s: &mut [u8], i: usize, a: uint8x16_t, b: uint8x16_t, c: uint8x16_t)
    requires
        neon(),
        i + 48 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + interleave3(n8(a), n8(b), n8(c)) + old(s)@.subrange(
            i + 48,
            old(s)@.len() as int,
        ),
{
    let o0 = w_st3_c0(w_st3_ab0(a, b), c);
    let o1 = w_st3_c1(w_st3_ab1(a, b), c);
    let o2 = w_st3_c2(w_st3_ab2(a, b), c);
    let ghost s0 = s@;
    let ghost x = interleave3(n8(a), n8(b), n8(c));
    proof {
        assert(n8(o0) =~= x.subrange(0, 16));
        assert(n8(o1) =~= x.subrange(16, 32));
        assert(n8(o2) =~= x.subrange(32, 48));
    }
    let n = s.len();
    assert(i + 48 <= n);
    w_store(s, i, o0);
    w_store(s, i + 16, o1);
    w_store(s, i + 32, o2);
    proof {
        assert(s@ =~= s0.subrange(0, i as int) + x + s0.subrange(i + 48, s0.len() as int));
    }
}

// ---------------------------------------------------------------------------
// Lemmas for the JPEG and WebP operations
// ---------------------------------------------------------------------------

proof fn lemma_pow2_pos(n: nat)
    ensures
        pow2_spec(n) > 0,
    decreases n,
{
    if n > 0 {
        lemma_pow2_pos((n - 1) as nat);
    }
}

/// Adding modulo 2^32 to a lane already reduced.
proof fn lemma_add_mod32(acc: int, m: int)
    requires
        0 <= acc < 0x1_0000_0000,
    ensures
        ((acc + ((m % 0x1_0000_0000) as u32) as int) % 0x1_0000_0000) == (acc + m) % 0x1_0000_0000,
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop(acc, m, 0x1_0000_0000);
    vstd::arithmetic::div_mod::lemma_small_mod(acc as nat, 0x1_0000_0000);
}

/// Subtracting two lanes reduced modulo 2^32.
proof fn lemma_sub_mod32(x: int, y: int)
    ensures
        ((((x % 0x1_0000_0000) as u32) as int - ((y % 0x1_0000_0000) as u32) as int + 0x1_0000_0000)
            % 0x1_0000_0000) == (x - y) % 0x1_0000_0000,
{
    vstd::arithmetic::div_mod::lemma_sub_mod_noop(x, y, 0x1_0000_0000);
    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(
        (x % 0x1_0000_0000) - (y % 0x1_0000_0000),
        0x1_0000_0000,
    );
}

/// A value that fits in 32 signed bits survives the trip through a lane.
proof fn lemma_s32_small(p: int)
    requires
        -0x8000_0000 <= p < 0x8000_0000,
    ensures
        s32((p % 0x1_0000_0000) as u32) == p,
{
    if p >= 0 {
        vstd::arithmetic::div_mod::lemma_small_mod(p as nat, 0x1_0000_0000);
    } else {
        vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(p, 0x1_0000_0000);
        vstd::arithmetic::div_mod::lemma_small_mod((p + 0x1_0000_0000) as nat, 0x1_0000_0000);
    }
}

/// `sqdmulh`'s `(2 x y) >> 16` is `(x y) >> 15`, and in range.
proof fn lemma_qdmulh_lane(x: int, y: int)
    requires
        -0x8000 <= x < 0x8000,
        -0x8000 <= y < 0x8000,
    ensures
        -0x4000_0000 <= x * y <= 0x4000_0000,
        (2 * x * y) / 0x10000 == (x * y) / 0x8000,
        -0x8000 <= (x * y) / 0x8000 <= 0x8000,
{
    assert(-0x4000_0000 <= x * y <= 0x4000_0000) by (nonlinear_arith)
        requires -0x8000 <= x < 0x8000, -0x8000 <= y < 0x8000;
    assert(2 * x * y == 2 * (x * y)) by (nonlinear_arith);
    lemma_div_double(x * y, 0x8000);
}

/// `(2 z) / (2 d) == z / d`, for any sign of `z`.
proof fn lemma_div_double(z: int, d: int)
    requires
        d > 0,
    ensures
        (2 * z) / (2 * d) == z / d,
{
    let q = z / d;
    let r = z % d;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(z, d);
    assert(2 * z == (2 * d) * q + 2 * r) by (nonlinear_arith) requires z == d * q + r;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(2 * z, 2 * d, q, 2 * r);
}

/// `x / (2 d) == (x / d) / 2`, for any sign of `x` (floor division).
proof fn lemma_div_halve(x: int, d: int)
    requires
        d > 0,
    ensures
        x / (d * 2) == (x / d) / 2,
{
    let q = x / d;
    let r = x % d;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, d);
    let q2 = q / 2;
    let t = q % 2;
    assert(x == (d * 2) * q2 + (d * t + r)) by (nonlinear_arith)
        requires x == d * q + r, q == 2 * q2 + t;
    assert(0 <= d * t + r < d * 2) by (nonlinear_arith) requires 0 <= t < 2, 0 <= r < d, d > 0;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, d * 2, q2, d * t + r);
}

/// Rounding shift right by `n` as two plain shifts: with `p = 2^(n-1)`,
/// `(v + p) >> n == (v >> (n - 1)) - (v >> n)`, which cannot overflow.
proof fn lemma_rshr(v: int, n: nat)
    requires
        1 <= n <= 31,
    ensures
        pow2_spec((n - 1) as nat) > 0,
        pow2_spec(n) == 2 * pow2_spec((n - 1) as nat),
        (v + pow2_spec((n - 1) as nat)) / pow2_spec(n) as int == v / pow2_spec((n - 1) as nat) as int - v
            / pow2_spec(n) as int,
{
    let p = pow2_spec((n - 1) as nat) as int;
    lemma_pow2_pos((n - 1) as nat);
    assert(pow2_spec(n) == 2 * pow2_spec((n - 1) as nat));
    let q = v / p;
    let r = v % p;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v, p);
    assert(v + p == (q + 1) * p + r) by (nonlinear_arith) requires v == p * q + r;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(v + p, p, q + 1, r);
    lemma_div_halve(v + p, p);
    lemma_div_halve(v, p);
    assert(p * 2 == pow2_spec(n) as int);
    assert((q + 1) / 2 == q - q / 2);
}

/// The even 16-bit lanes are the low halves of the 32-bit lanes.
proof fn lemma_low16(b: Seq<u8>)
    requires
        b.len() == 16,
    ensures
        forall|k: int| 0 <= k < 4 ==> #[trigger] u16s(b)[2 * k] as int == u32s(b)[k] as int % 0x10000,
{
    lemma_u16s_of_u32s(b);
    assert forall|k: int| 0 <= k < 4 implies #[trigger] u16s(b)[2 * k] as int == u32s(b)[k] as int % 0x10000 by {
        let w = u32s(b)[k];
        assert((w & 0xffff) as u16 as int == w as int % 0x10000) by (bit_vector);
    }
}

proof fn lemma_shr_u16(x: u16, n: u16)
    requires
        1 <= n <= 8,
    ensures
        x >> (((n as u32) % 16) as u16) == (x as nat / pow2_spec(n as nat)) as u16,
{
    reveal_with_fuel(pow2_spec, 9);
    assert(((n as u32) % 16) as u16 == n);
    if n == 1 {
        assert(x >> 1u16 == x / 2) by (bit_vector);
    } else if n == 2 {
        assert(x >> 2u16 == x / 4) by (bit_vector);
    } else if n == 3 {
        assert(x >> 3u16 == x / 8) by (bit_vector);
    } else if n == 4 {
        assert(x >> 4u16 == x / 16) by (bit_vector);
    } else if n == 5 {
        assert(x >> 5u16 == x / 32) by (bit_vector);
    } else if n == 6 {
        assert(x >> 6u16 == x / 64) by (bit_vector);
    } else if n == 7 {
        assert(x >> 7u16 == x / 128) by (bit_vector);
    } else {
        assert(x >> 8u16 == x / 256) by (bit_vector);
    }
}

} // verus!

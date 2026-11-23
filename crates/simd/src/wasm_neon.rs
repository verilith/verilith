//! The NEON wrappers' contracts, proven on WebAssembly SIMD128.
//!
//! Each function here has the name, signature, `requires` and `ensures` of
//! the wrapper of the same name in `crate::neon`, and is verified against
//! the trusted SIMD128 instruction specifications in `crate::wasm`. On
//! `wasm32` with `simd128`, `crate::neon`'s wrappers call these, so the
//! NEON kernels' proofs (JSON, UTF-8, URL, HTTP, regex) hold there on the
//! strength of the WebAssembly specification, not of NEON.
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

pub open spec fn max_u8(x: u8, y: u8) -> u8 {
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
        y == Seq::new(16, |i: int| max_u8(x[i], x[(i + k) % 16])),
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
        assert(n8(y) =~= Seq::new(16, |i: int| max_u8(n8(x)[i], n8(x)[(i + K) % 16])));
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

pub open spec fn max_u16(x: u16, y: u16) -> u16 {
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
        y == Seq::new(8, |i: int| max_u16(x[i], x[(i + k) % 8])),
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
        assert(u16s(n8(y)) =~= Seq::new(8, |i: int| max_u16(u16s(n8(x))[i], u16s(n8(x))[(i + K) % 8])));
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

} // verus!

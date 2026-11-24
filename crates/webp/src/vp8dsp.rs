//! VP8 reconstruction kernels, bit-exact with libwebp 1.6.0 as built for
//! x86-64 (`src/dsp/dec.c`, `dec_sse2.c`): the inverse DCT, intra
//! prediction (RFC 6386 section 12) and the loop filter (section 15).
//!
//! Prediction and the transforms work in libwebp's scratch layout: rows of
//! `BPS = 32` bytes, the block at offset `d` with its top row at `d - BPS`
//! and its left column at `d - 1`.
use crate::vp8spec::*;
use verilith_core::prims::*;
use verilith_simd::arch::*;
use verilith_simd::lanes::*;
use verilith_simd::mem::*;
use verilith_simd::ops::*;
use verilith_simd::neon::*;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::neon::group_neon};

pub const BPS: usize = 32;

// ---------------------------------------------------------------------------
// Inverse transforms
// ---------------------------------------------------------------------------

/// `x` modulo 2^16 as a signed 16-bit value (C's conversion to `int16_t`).
pub open spec fn wrap16(x: int) -> int {
    let m = x % 0x1_0000;
    if m >= 0x8000 {
        m - 0x1_0000
    } else {
        m
    }
}

/// Wraps to 16 bits.
#[inline(always)]
pub fn w16(x: i32) -> (r: i16)
    ensures
        r as int == wrap16(x as int),
{
    let u = x & 0xffff;
    proof {
        assert(0 <= u < 0x1_0000 && u as int == (x as int) % 0x1_0000) by (bit_vector)
            requires
                u == x & 0xffff,
        ;
    }
    if u >= 0x8000 {
        (u - 0x1_0000) as i16
    } else {
        u as i16
    }
}

/// How many times 2^16 `wrap16` takes off.
pub open spec fn wk(x: int) -> int {
    (x + 0x8000) / 0x1_0000
}

pub proof fn lemma_wk(x: int)
    ensures
        wrap16(x) == x - 0x1_0000 * wk(x),
        -0x8000 <= wrap16(x) <= 0x7fff,
{
}

/// A 16-bit value that differs from `e` by a multiple of 2^16 is `e`
/// wrapped.
pub proof fn lemma_wrap16_unique(v: int, e: int, k: int)
    requires
        -0x8000 <= v <= 0x7fff,
        v == e - 0x1_0000 * k,
    ensures
        v == wrap16(e),
{
    lemma_wk(e);
    let j = wk(e);
    assert(v - wrap16(e) == 0x1_0000 * (j - k));
    assert(j == k) by (nonlinear_arith)
        requires
            -0x1_0000 < 0x1_0000 * (j - k) < 0x1_0000,
    ;
}

/// `x >> k` is the floor of `x / 2^k`, for the two shifts used here.
proof fn lemma_sar16(x: i32)
    ensures
        (x >> 16u32) as int == (x as int) / 0x1_0000,
{
    let q = x >> 16u32;
    assert(-0x8000 <= (x >> 16u32) <= 0x7fff && mul(x >> 16u32, 0x1_0000) <= x && x <= add(
        mul(x >> 16u32, 0x1_0000),
        0xffff,
    )) by (bit_vector);
    assert(mul(q, 0x1_0000) == q * 0x1_0000);
    assert(add(mul(q, 0x1_0000), 0xffff) == q * 0x1_0000 + 0xffff);
}

proof fn lemma_sar3_16(x: i16)
    ensures
        (x >> 3u32) as int == (x as int) / 8,
        -0x1000 <= (x >> 3u32) <= 0x0fff,
{
    let q = x >> 3u32;
    assert(-0x1000 <= (x >> 3u32) <= 0x0fff && mul(x >> 3u32, 8) <= x && x <= add(mul(x >> 3u32, 8), 7)) by (bit_vector);
    assert(mul(q, 8) == q * 8);
    assert(add(mul(q, 8), 7) == q * 8 + 7);
}

/// `_mm_mulhi_epi16`.
#[inline(always)]
pub fn mulhi(a: i16, k: i16) -> (r: i16)
    ensures
        r as int == (a as int * k as int) / 0x1_0000,
{
    proof {
        assert(-0x4000_0000 <= a as i32 * k as i32 <= 0x4000_0000) by (nonlinear_arith);
        lemma_sar16((a as i32 * k as i32) as i32);
    }
    ((a as i32 * k as i32) >> 16u32) as i16
}

#[inline(always)]
fn add16(a: i16, b: i16) -> (r: i16)
    ensures
        r as int == wrap16(a + b),
{
    a.wrapping_add(b)
}

#[inline(always)]
fn sub16(a: i16, b: i16) -> (r: i16)
    ensures
        r as int == wrap16(a - b),
{
    a.wrapping_sub(b)
}

/// `clip_8b`.
#[inline(always)]
pub fn clip8(v: i32) -> (r: u8)
    ensures
        r == clip_to(v as int, 255),
{
    if v < 0 {
        0
    } else if v > 255 {
        255
    } else {
        v as u8
    }
}

/// `clip_8b` of a pixel plus a 16-bit residual, in 16 bits (the sum
/// fits: residuals are at most 0x1000 in size after the final shift).
#[inline(always)]
fn clip8_16(v: i16) -> (r: u8)
    ensures
        r == clip_to(v as int, 255),
{
    let c = if v > 255 { 255 } else { v };
    (if c < 0 { 0 } else { c }) as u8
}

/// `x >> 3` for a 16-bit `x`.
#[inline(always)]
fn shr3(x: i32) -> (r: i32)
    requires
        -0x4_0000 <= x <= 0x4_0000,
    ensures
        -0x8000 <= r <= 0x8000,
        r == (x as int) / 8,
{
    proof {
        assert(-0x4_0000 <= x <= 0x4_0000 ==> -0x8000 <= (x >> 3u32) <= 0x8000 && mul(x >> 3u32, 8) <= x && x <= add(
            mul(x >> 3u32, 8),
            7,
        )) by (bit_vector);
        let q = x >> 3u32;
        assert(mul(q, 8) == q * 8);
        assert(add(mul(q, 8), 7) == q * 8 + 7);
    }
    x >> 3u32
}

const K1: i16 = 20091;
const K2: i16 = -30068;

/// One pass of the inverse DCT as 16-bit lanes compute it.
pub open spec fn lane_1d(x0: int, x1: int, x2: int, x3: int) -> (int, int, int, int) {
    let r = idct_1d(x0, x1, x2, x3);
    (wrap16(r.0), wrap16(r.1), wrap16(r.2), wrap16(r.3))
}

/// The two constants give the specification's products, less the factor
/// itself (`K2` is `sinpi8sqrt2` minus 2^16).
proof fn lemma_mulhi_k(x: int)
    ensures
        (x * 20091) / 0x1_0000 == idct_mul1(x) - x,
        (x * (-30068)) / 0x1_0000 == idct_mul2(x) - x,
{
    assert(x * 35468 == x * (-30068) + 0x1_0000 * x);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x * 35468, 0x1_0000);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x * (-30068), 0x1_0000);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        x * 35468,
        0x1_0000,
        (x * (-30068)) / 0x1_0000 + x,
        (x * (-30068)) % 0x1_0000,
    );
}

/// One butterfly of `Transform_SSE2`: the four outputs of a 1-D inverse
/// DCT of `(x0, x1, x2, x3)`, in 16-bit lane arithmetic.
#[inline(always)]
fn idct1(x0: i16, x1: i16, x2: i16, x3: i16) -> (r: (i16, i16, i16, i16))
    ensures
        (r.0 as int, r.1 as int, r.2 as int, r.3 as int) == lane_1d(x0 as int, x1 as int, x2 as int, x3 as int),
{
    let a = add16(x0, x2);
    let b = sub16(x0, x2);
    let m12 = mulhi(x1, K2);
    let m31 = mulhi(x3, K1);
    let m11 = mulhi(x1, K1);
    let m32 = mulhi(x3, K2);
    let c0 = sub16(x1, x3);
    let c1 = sub16(m12, m31);
    let c = add16(c0, c1);
    let d0 = add16(x1, x3);
    let d1 = add16(m11, m32);
    let d = add16(d0, d1);
    let r = (add16(a, d), add16(b, c), sub16(b, c), sub16(a, d));
    proof {
        lemma_mulhi_k(x1 as int);
        lemma_mulhi_k(x3 as int);
        let e = idct_1d(x0 as int, x1 as int, x2 as int, x3 as int);
        lemma_wk(x0 + x2);
        lemma_wk(x0 - x2);
        lemma_wk(x1 - x3);
        lemma_wk(m12 - m31);
        lemma_wk(c0 + c1);
        lemma_wk(x1 + x3);
        lemma_wk(m11 + m32);
        lemma_wk(d0 + d1);
        lemma_wk(a + d);
        lemma_wk(b + c);
        lemma_wk(b - c);
        lemma_wk(a - d);
        let ka = wk(x0 + x2);
        let kb = wk(x0 - x2);
        let kc = wk(x1 - x3) + wk(m12 - m31) + wk(c0 + c1);
        let kd = wk(x1 + x3) + wk(m11 + m32) + wk(d0 + d1);
        assert(c == idct_mul2(x1 as int) - idct_mul1(x3 as int) - 0x1_0000 * kc);
        assert(d == idct_mul1(x1 as int) + idct_mul2(x3 as int) - 0x1_0000 * kd);
        lemma_wrap16_unique(r.0 as int, e.0, ka + kd + wk(a + d));
        lemma_wrap16_unique(r.1 as int, e.1, kb + kc + wk(b + c));
        lemma_wrap16_unique(r.2 as int, e.2, kb - kc + wk(b - c));
        lemma_wrap16_unique(r.3 as int, e.3, ka - kd + wk(a - d));
    }
    r
}

/// Adding a multiple of 2^16 to the first input does not change a lane
/// pass.
proof fn lemma_lane_bias(y: int, x1: int, x2: int, x3: int)
    ensures
        lane_1d(wrap16(y), x1, x2, x3) == lane_1d(y, x1, x2, x3),
{
    lemma_wk(y);
    let k = wk(y);
    let e = idct_1d(y, x1, x2, x3);
    let f = idct_1d(wrap16(y), x1, x2, x3);
    lemma_wk(f.0);
    lemma_wk(f.1);
    lemma_wk(f.2);
    lemma_wk(f.3);
    lemma_wrap16_unique(wrap16(f.0), e.0, k + wk(f.0));
    lemma_wrap16_unique(wrap16(f.1), e.1, k + wk(f.1));
    lemma_wrap16_unique(wrap16(f.2), e.2, k + wk(f.2));
    lemma_wrap16_unique(wrap16(f.3), e.3, k + wk(f.3));
}

/// The sixteen coefficients of the block at `inp[i]`.
pub open spec fn cblk(inp: Seq<i16>, i: int) -> Seq<int> {
    Seq::new(16, |k: int| inp[i + k] as int)
}

/// What the two lane passes and transposes of `Transform_SSE2` compute
/// for the block in lanes `h..h + 4`: the specification's values before
/// the final shift, when they fit in 16 bits.
proof fn lemma_lane_idct(cb: Seq<int>, x: Seq<i16>, t1: Seq<i16>, u1: Seq<i16>, t2: Seq<i16>, u2: Seq<i16>, h: int)
    requires
        cb.len() == 16,
        h == 0 || h == 4,
        forall|k: int, c: int| 0 <= k < 4 && 0 <= c < 4 ==> #[trigger] xl(x, k, h + c) == cb[4 * k + c],
        forall|i: int|
            0 <= i < 8 ==> #[trigger] lanes_at(t1, i) == lane_1d(x[i] + 0, x[8 + i] as int, x[16 + i] as int, x[24 + i] as int),
        transposed(t1, u1),
        forall|i: int|
            0 <= i < 8 ==> #[trigger] lanes_at(t2, i) == lane_1d(
                u1[i] + 4,
                u1[8 + i] as int,
                u1[16 + i] as int,
                u1[24 + i] as int,
            ),
        transposed(t2, u2),
        idct_tame(cb),
    ensures
        forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 ==> #[trigger] xl(u2, r, h + c) == idct_pre(cb, r, c),
{
    hide(idct_1d);
    assert forall|col: int, y: int| 0 <= col < 4 && 0 <= y < 4 implies #[trigger] xl(t1, y, h + col) == idct_v(
        cb,
        col,
        y,
    ) by {
        let i = h + col;
        assert(lanes_at(t1, i) == lane_1d(x[i] + 0, x[8 + i] as int, x[16 + i] as int, x[24 + i] as int));
        assert(xl(x, 0, h + col) == cb[4 * 0 + col]);
        assert(xl(x, 1, h + col) == cb[4 * 1 + col]);
        assert(xl(x, 2, h + col) == cb[4 * 2 + col]);
        assert(xl(x, 3, h + col) == cb[4 * 3 + col]);
        assert(fits16(idct_v(cb, col, y)));
    }
    assert forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 implies #[trigger] xl(u1, r, h + c) == idct_v(cb, r, c) by {
        assert(xl(u1, r, c) == xl(t1, c, r) && xh(u1, r, c) == xh(t1, c, r));
        assert(xl(t1, c, h + r) == idct_v(cb, r, c));
    }
    assert forall|j: int, xx: int| 0 <= j < 4 && 0 <= xx < 4 implies #[trigger] xl(t2, xx, h + j) == idct_pre(cb, j, xx) by {
        let i = h + j;
        assert(lanes_at(t2, i) == lane_1d(u1[i] + 4, u1[8 + i] as int, u1[16 + i] as int, u1[24 + i] as int));
        assert(xl(u1, 0, h + j) == idct_v(cb, 0, j));
        assert(xl(u1, 1, h + j) == idct_v(cb, 1, j));
        assert(xl(u1, 2, h + j) == idct_v(cb, 2, j));
        assert(xl(u1, 3, h + j) == idct_v(cb, 3, j));
        assert(fits16(idct_pre(cb, j, xx)));
    }
    assert forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 implies #[trigger] xl(u2, r, h + c) == idct_pre(cb, r, c) by {
        assert(xl(u2, r, c) == xl(t2, c, r) && xh(u2, r, c) == xh(t2, c, r));
        assert(xl(t2, c, h + r) == idct_pre(cb, r, c));
    }
}

/// The last step of `Transform_SSE2`: adds `u >> 3`, lane by lane, to four
/// rows of `w` pixels at `d`.
#[inline(always)]
fn add_rows(dst: &mut [u8], d: usize, u: &[i16; 32], w: usize)
    requires
        w == 4 || w == 8,
        d + 3 * BPS + w <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        forall|j: int|
            0 <= j < old(dst)@.len() ==> #[trigger] final(dst)@[j] == (if in_blk(j - d, w as int) {
                clip_to(old(dst)@[j] + (xl(u@, (j - d) / 32, (j - d) % 32) as int) / 8, 255) as u8
            } else {
                old(dst)@[j]
            }),
{
    proof {
        assert(dst@.len() == dst.len());
    }
    let mut r: usize = 0;
    while r < 4
        invariant
            dst@.len() <= usize::MAX,
            w == 4 || w == 8,
            r <= 4,
            d + 3 * BPS + w <= dst@.len(),
            dst@.len() == old(dst)@.len(),
            forall|j: int|
                0 <= j < dst@.len() ==> #[trigger] dst@[j] == (if in_blk(j - d, w as int) && (j - d) / 32 < r {
                    clip_to(old(dst)@[j] + (xl(u@, (j - d) / 32, (j - d) % 32) as int) / 8, 255) as u8
                } else {
                    old(dst)@[j]
                }),
        decreases 4 - r,
    {
        let p = d + r * BPS;
        let mut c: usize = 0;
        while c < w
            invariant
                dst@.len() <= usize::MAX,
                w == 4 || w == 8,
                r < 4,
                c <= w,
                p == d + r * BPS,
                d + 3 * BPS + w <= dst@.len(),
                dst@.len() == old(dst)@.len(),
                forall|j: int|
                    0 <= j < dst@.len() ==> #[trigger] dst@[j] == (if in_blk(j - d, w as int) && ((j - d) / 32 < r || ((j
                        - d) / 32 == r && (j - d) % 32 < c)) {
                        clip_to(old(dst)@[j] + (xl(u@, (j - d) / 32, (j - d) % 32) as int) / 8, 255) as u8
                    } else {
                        old(dst)@[j]
                    }),
            decreases w - c,
        {
            let v = u[8 * r + c];
            proof {
                lemma_sar3_16(v);
                assert((p + c - d) / 32 == r && (p + c - d) % 32 == c);
            }
            set(dst, p + c, clip8_16(get(dst, p + c) as i16 + (v >> 3u32)));
            c = c + 1;
        }
        r = r + 1;
    }
}

/// `Transform_SSE2` on one 4x4 block: adds the inverse DCT of
/// `inp[i..i + 16]` to the block at `dst[d]`.
///
/// It is RFC 6386 section 14.4's (`vp8spec::idct`) for a block whose
/// intermediate values fit in 16 bits.
pub fn transform_one(inp: &[i16], i: usize, dst: &mut [u8], d: usize)
    requires
        i + 16 <= inp@.len(),
        d + 3 * BPS + 4 <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        idct_tame(cblk(inp@, i as int)) ==> final(dst)@ == add_res(old(dst)@, d as int, idct(cblk(inp@, i as int))),
{
    proof {assert(inp@.len() == inp.len()); assert(dst@.len() == dst.len());}
    let ghost cb = cblk(inp@, i as int);
    // `transform_two`'s eight-lane passes, the second block's lanes zero
    // (four lanes do not vectorize as well).
    let mut x: [i16; 32] = [0; 32];
    let mut k: usize = 0;
    while k < 4
        invariant
            inp@.len() <= usize::MAX,
            k <= 4,
            i + 16 <= inp@.len(),
            forall|kk: int, cc: int|
                0 <= kk < k && 0 <= cc < 4 ==> #[trigger] xl(x@, kk, cc) == inp@[i + 4 * kk + cc],
        decreases 4 - k,
    {
        let mut c: usize = 0;
        while c < 4
            invariant
                inp@.len() <= usize::MAX,
                k < 4,
                c <= 4,
                i + 16 <= inp@.len(),
                forall|kk: int, cc: int|
                    0 <= kk < 4 && 0 <= cc < 4 && (kk < k || (kk == k && cc < c)) ==> #[trigger] xl(x@, kk, cc) == inp@[i
                        + 4 * kk + cc],
            decreases 4 - c,
        {
            let ghost x0 = x@;
            x[8 * k + c] = get16(inp, i + 4 * k + c);
            proof {
                assert(x@ == x0.update(8 * k + c, inp@[i + 4 * k + c]));
                assert forall|kk: int, cc: int|
                    0 <= kk < 4 && 0 <= cc < 4 && (kk < k || (kk == k && cc < c + 1)) implies #[trigger] xl(x@, kk, cc)
                    == inp@[i + 4 * kk + cc] by {
                    if kk == k && cc == c {
                    } else {
                        assert(8 * kk + cc != 8 * k + c);
                        assert(xl(x0, kk, cc) == inp@[i + 4 * kk + cc]);
                    }
                }
            }
            c = c + 1;
        }
        k = k + 1;
    }
    let mut t: [i16; 32] = [0; 32];
    let mut u: [i16; 32] = [0; 32];
    idct_pass(&x, &mut t, 0, 0);
    let ghost t1 = t@;
    transpose_halves(&t, &mut u);
    let ghost u1 = u@;
    idct_pass(&u, &mut t, 4, 0);
    let ghost t2 = t@;
    transpose_halves(&t, &mut u);
    add_rows(dst, d, &u, 4);
    proof {
        if idct_tame(cb) {
            assert forall|kk: int, cc: int| 0 <= kk < 4 && 0 <= cc < 4 implies #[trigger] xl(x@, kk, 0 + cc) == cb[4 * kk
                + cc] by {}
            lemma_lane_idct(cb, x@, t1, u1, t2, u@, 0);
            let want = add_res(old(dst)@, d as int, idct(cb));
            assert forall|j: int| 0 <= j < dst@.len() implies dst@[j] == want[j] by {
                if in_blk(j - d, 4) {
                    let r = (j - d) / 32;
                    let c = (j - d) % 32;
                    assert(xl(u@, r, 0 + c) == idct_pre(cb, r, c));
                    assert((4 * r + c) / 4 == r && (4 * r + c) % 4 == c);
                }
            }
            assert(dst@ =~= want);
        }
    }
}

/// One pass of `Transform_SSE2` on eight lanes (two blocks' columns or
/// rows): lane `i` of row `k` at `x[8 * k + i]`, `bias` added to row 0 and
/// the outputs shifted down by `sh`. Separate passes over memory, so each
/// vectorizes as eight 16-bit lanes.
/// Lane `i` of the four rows of an eight-lane block.
pub open spec fn lanes_at(t: Seq<i16>, i: int) -> (int, int, int, int) {
    (t[i] as int, t[8 + i] as int, t[16 + i] as int, t[24 + i] as int)
}

#[inline(always)]
fn idct_pass(x: &[i16; 32], t: &mut [i16; 32], bias: i16, sh: u32)
    requires
        sh <= 3,
    ensures
        sh == 0 ==> forall|i: int|
            0 <= i < 8 ==> #[trigger] lanes_at(final(t)@, i) == lane_1d(
                x@[i] + bias,
                x@[8 + i] as int,
                x@[16 + i] as int,
                x@[24 + i] as int,
            ),
{
    hide(lane_1d);
    if sh == 0 && has_neon() {
        idct_pass_neon(x, t, bias);
        return;
    }
    let mut i: usize = 0;
    while i < 8
        invariant
            i <= 8,
            sh <= 3,
            sh == 0 ==> forall|j: int|
                0 <= j < i ==> #[trigger] lanes_at(t@, j) == lane_1d(
                    x@[j] + bias,
                    x@[8 + j] as int,
                    x@[16 + j] as int,
                    x@[24 + j] as int,
                ),
        decreases 8 - i,
    {
        let x0 = add16(x[i], bias);
        let (a, b, c, d) = idct1(x0, x[i + 8], x[i + 16], x[i + 24]);
        let ghost want = lane_1d(x@[i as int] + bias, x@[8 + i] as int, x@[16 + i] as int, x@[24 + i] as int);
        let ghost t0 = t@;
        proof {
            lemma_lane_bias(x@[i as int] + bias, x@[8 + i] as int, x@[16 + i] as int, x@[24 + i] as int);
            assert(x0 as int == wrap16(x@[i as int] + bias));
            assert((a as int, b as int, c as int, d as int) == want);
            assert(sh == 0 ==> (a >> sh) == a && (b >> sh) == b && (c >> sh) == c && (d >> sh) == d) by (bit_vector);
        }
        t[i] = a >> sh;
        t[8 + i] = b >> sh;
        t[16 + i] = c >> sh;
        t[24 + i] = d >> sh;
        proof {
            if sh == 0 {
                assert(lanes_at(t@, i as int) == want);
                assert forall|j: int| 0 <= j < i implies #[trigger] lanes_at(t@, j) == lane_1d(
                    x@[j] + bias,
                    x@[8 + j] as int,
                    x@[16 + j] as int,
                    x@[24 + j] as int,
                ) by {
                    assert(lanes_at(t@, j) == lanes_at(t0, j));
                }
            }
        }
        i = i + 1;
    }
}

/// `idct1`'s arithmetic on integers: the 16-bit lane operations, each
/// wrapped.
pub open spec fn lane_calc(x0: int, x1: int, x2: int, x3: int) -> (int, int, int, int) {
    let a = wrap16(x0 + x2);
    let b = wrap16(x0 - x2);
    let m12 = (x1 * (-30068)) / 0x1_0000;
    let m31 = (x3 * 20091) / 0x1_0000;
    let m11 = (x1 * 20091) / 0x1_0000;
    let m32 = (x3 * (-30068)) / 0x1_0000;
    let c = wrap16(wrap16(x1 - x3) + wrap16(m12 - m31));
    let d = wrap16(wrap16(x1 + x3) + wrap16(m11 + m32));
    (wrap16(a + d), wrap16(b + c), wrap16(b - c), wrap16(a - d))
}

/// The wrapped lane operations compute a lane pass.
proof fn lemma_lane_calc(x0: int, x1: int, x2: int, x3: int)
    ensures
        lane_calc(x0, x1, x2, x3) == lane_1d(x0, x1, x2, x3),
{
    let a = wrap16(x0 + x2);
    let b = wrap16(x0 - x2);
    let m12 = (x1 * (-30068)) / 0x1_0000;
    let m31 = (x3 * 20091) / 0x1_0000;
    let m11 = (x1 * 20091) / 0x1_0000;
    let m32 = (x3 * (-30068)) / 0x1_0000;
    let c0 = wrap16(x1 - x3);
    let c1 = wrap16(m12 - m31);
    let c = wrap16(c0 + c1);
    let d0 = wrap16(x1 + x3);
    let d1 = wrap16(m11 + m32);
    let d = wrap16(d0 + d1);
    let r = lane_calc(x0, x1, x2, x3);
    lemma_mulhi_k(x1);
    lemma_mulhi_k(x3);
    let e = idct_1d(x0, x1, x2, x3);
    lemma_wk(x0 + x2);
    lemma_wk(x0 - x2);
    lemma_wk(x1 - x3);
    lemma_wk(m12 - m31);
    lemma_wk(c0 + c1);
    lemma_wk(x1 + x3);
    lemma_wk(m11 + m32);
    lemma_wk(d0 + d1);
    lemma_wk(a + d);
    lemma_wk(b + c);
    lemma_wk(b - c);
    lemma_wk(a - d);
    let ka = wk(x0 + x2);
    let kb = wk(x0 - x2);
    let kc = wk(x1 - x3) + wk(m12 - m31) + wk(c0 + c1);
    let kd = wk(x1 + x3) + wk(m11 + m32) + wk(d0 + d1);
    assert(c == idct_mul2(x1) - idct_mul1(x3) - 0x1_0000 * kc);
    assert(d == idct_mul1(x1) + idct_mul2(x3) - 0x1_0000 * kd);
    lemma_wrap16_unique(r.0, e.0, ka + kd + wk(a + d));
    lemma_wrap16_unique(r.1, e.1, kb + kc + wk(b + c));
    lemma_wrap16_unique(r.2, e.2, kb - kc + wk(b - c));
    lemma_wrap16_unique(r.3, e.3, ka - kd + wk(a - d));
}

/// A lane of a wrapping 16-bit vector sum, as a signed value.
proof fn lemma_vadd16(a: Seq<u16>, b: Seq<u16>, i: int)
    requires
        a.len() == 8,
        b.len() == 8,
        0 <= i < 8,
    ensures
        s16(verilith_simd::ops::add16(a, b)[i]) == wrap16(s16(a[i]) + s16(b[i])),
        s16(verilith_simd::ops::sub16(a, b)[i]) == wrap16(s16(a[i]) - s16(b[i])),
{
}

/// `sqdmulh` by one of the transform's constants, halved, is
/// `_mm_mulhi_epi16`: the doubled product never saturates.
proof fn lemma_vmulhi(a: Seq<u16>, k: i16, i: int)
    requires
        a.len() == 8,
        0 <= i < 8,
        k == 20091 || k == -30068,
    ensures
        s16(srai16(qdmulh_s16(a, splat16(u16_of_i16(k), 8)), 1)[i]) == (s16(a[i]) * k) / 0x1_0000,
{
    let x = s16(a[i]);
    let kk = k as int;
    assert(s16(u16_of_i16(k)) == kk);
    let p = x * kk;
    assert(-0x3fff_0000 < p < 0x3fff_0000 && 2 * x * kk == 2 * p) by (nonlinear_arith)
        requires
            -0x8000 <= x <= 0x7fff,
            kk == 20091 || kk == -30068,
            p == x * kk,
    ;
    let q = (2 * p) / 0x1_0000;
    assert(-0x8000 <= q <= 0x7fff);
    assert(q / 2 == p / 0x1_0000);
    let v = qdmulh_s16(a, splat16(u16_of_i16(k), 8))[i];
    assert(v == (sat_s16(q) % 0x10000) as u16);
    assert(s16(v) == q);
    let h = p / 0x1_0000;
    assert(-0x4000 <= h < 0x4000);
    assert(pow2_spec(1) == 2) by (compute);
    let w = srai16(qdmulh_s16(a, splat16(u16_of_i16(k), 8)), 1)[i];
    assert(w == ((s16(v) / 2) % 0x10000) as u16);
    assert(s16(w) == h);
}

/// One lane of `idct_pass_neon`'s vectors.
proof fn lemma_pass_lane(
    r0: Seq<u16>, r1: Seq<u16>, r2: Seq<u16>, r3: Seq<u16>, bias: i16,
    o0: Seq<u16>, o1: Seq<u16>, o2: Seq<u16>, o3: Seq<u16>, i: int,
)
    requires
        r0.len() == 8,
        r1.len() == 8,
        r2.len() == 8,
        r3.len() == 8,
        0 <= i < 8,
        ({
            let k1 = splat16(u16_of_i16(20091i16), 8);
            let k2 = splat16(u16_of_i16(-30068i16), 8);
            let x0 = verilith_simd::ops::add16(r0, splat16(u16_of_i16(bias), 8));
            let a = verilith_simd::ops::add16(x0, r2);
            let b = verilith_simd::ops::sub16(x0, r2);
            let m12 = srai16(qdmulh_s16(r1, k2), 1);
            let m31 = srai16(qdmulh_s16(r3, k1), 1);
            let m11 = srai16(qdmulh_s16(r1, k1), 1);
            let m32 = srai16(qdmulh_s16(r3, k2), 1);
            let c = verilith_simd::ops::add16(verilith_simd::ops::sub16(r1, r3), verilith_simd::ops::sub16(m12, m31));
            let d = verilith_simd::ops::add16(verilith_simd::ops::add16(r1, r3), verilith_simd::ops::add16(m11, m32));
            &&& o0 == verilith_simd::ops::add16(a, d)
            &&& o1 == verilith_simd::ops::add16(b, c)
            &&& o2 == verilith_simd::ops::sub16(b, c)
            &&& o3 == verilith_simd::ops::sub16(a, d)
        }),
    ensures
        (s16(o0[i]), s16(o1[i]), s16(o2[i]), s16(o3[i])) == lane_1d(
            s16(r0[i]) + bias,
            s16(r1[i]),
            s16(r2[i]),
            s16(r3[i]),
        ),
{
    let k1 = splat16(u16_of_i16(20091i16), 8);
    let k2 = splat16(u16_of_i16(-30068i16), 8);
    let vb = splat16(u16_of_i16(bias), 8);
    let x0 = verilith_simd::ops::add16(r0, vb);
    let a = verilith_simd::ops::add16(x0, r2);
    let b = verilith_simd::ops::sub16(x0, r2);
    let m12 = srai16(qdmulh_s16(r1, k2), 1);
    let m31 = srai16(qdmulh_s16(r3, k1), 1);
    let m11 = srai16(qdmulh_s16(r1, k1), 1);
    let m32 = srai16(qdmulh_s16(r3, k2), 1);
    let c0 = verilith_simd::ops::sub16(r1, r3);
    let c1 = verilith_simd::ops::sub16(m12, m31);
    let c = verilith_simd::ops::add16(c0, c1);
    let d0 = verilith_simd::ops::add16(r1, r3);
    let d1 = verilith_simd::ops::add16(m11, m32);
    let d = verilith_simd::ops::add16(d0, d1);
    assert(s16(vb[i]) == bias as int);
    lemma_vadd16(r0, vb, i);
    lemma_vadd16(x0, r2, i);
    lemma_vmulhi(r1, -30068i16, i);
    lemma_vmulhi(r3, 20091i16, i);
    lemma_vmulhi(r1, 20091i16, i);
    lemma_vmulhi(r3, -30068i16, i);
    lemma_vadd16(r1, r3, i);
    lemma_vadd16(m12, m31, i);
    lemma_vadd16(c0, c1, i);
    lemma_vadd16(m11, m32, i);
    lemma_vadd16(d0, d1, i);
    lemma_vadd16(a, d, i);
    lemma_vadd16(b, c, i);
    let y = wrap16(s16(r0[i]) + bias);
    assert((s16(o0[i]), s16(o1[i]), s16(o2[i]), s16(o3[i])) == lane_calc(y, s16(r1[i]), s16(r2[i]), s16(r3[i])));
    lemma_lane_calc(y, s16(r1[i]), s16(r2[i]), s16(r3[i]));
    lemma_lane_bias(s16(r0[i]) + bias, s16(r1[i]), s16(r2[i]), s16(r3[i]));
}

/// A 16-bit value's bits read back as signed.
proof fn lemma_s16_bits(x: i16, y: u16)
    ensures
        s16(x as u16) == x as int,
        (y as i16) as int == s16(y),
{
    assert(x >= 0 ==> (x as u16) as int == x as int) by (bit_vector);
    assert(x < 0 ==> (x as u16) as int == x as int + 0x1_0000) by (bit_vector);
    assert(y < 0x8000 ==> (y as i16) as int == y as int) by (bit_vector);
    assert(y >= 0x8000 ==> (y as i16) as int == y as int - 0x1_0000) by (bit_vector);
}

/// `idct_pass` without a shift, on NEON: the butterfly of `idct1` on eight
/// lanes at once, with `sqdmulh` and a halving shift for the products.
#[inline(always)]
fn idct_pass_neon(x: &[i16; 32], t: &mut [i16; 32], bias: i16)
    requires
        neon(),
    ensures
        forall|i: int|
            0 <= i < 8 ==> #[trigger] lanes_at(final(t)@, i) == lane_1d(
                x@[i] + bias,
                x@[8 + i] as int,
                x@[16 + i] as int,
                x@[24 + i] as int,
            ),
{
    hide(lane_1d);
    hide(u16s);
    hide(verilith_simd::ops::add16);
    hide(verilith_simd::ops::sub16);
    hide(srai16);
    hide(qdmulh_s16);
    let xs: &[i16] = x;
    let ts: &mut [i16] = t;
    proof {
        assert(xs@.len() == 32);
        assert(ts@.len() == 32);
    }
    let r0 = vld1q_s16_at(xs, 0);
    let r1 = vld1q_s16_at(xs, 8);
    let r2 = vld1q_s16_at(xs, 16);
    let r3 = vld1q_s16_at(xs, 24);
    let k1 = vdupq_n_s16(K1);
    let k2 = vdupq_n_s16(K2);
    let x0 = vaddq_s16(r0, vdupq_n_s16(bias));
    let a = vaddq_s16(x0, r2);
    let b = vsubq_s16(x0, r2);
    let m12 = vshrq_n_s16::<1>(vqdmulhq_s16(r1, k2));
    let m31 = vshrq_n_s16::<1>(vqdmulhq_s16(r3, k1));
    let m11 = vshrq_n_s16::<1>(vqdmulhq_s16(r1, k1));
    let m32 = vshrq_n_s16::<1>(vqdmulhq_s16(r3, k2));
    let c = vaddq_s16(vsubq_s16(r1, r3), vsubq_s16(m12, m31));
    let d = vaddq_s16(vaddq_s16(r1, r3), vaddq_s16(m11, m32));
    let o0 = vaddq_s16(a, d);
    let o1 = vaddq_s16(b, c);
    let o2 = vsubq_s16(b, c);
    let o3 = vsubq_s16(a, d);
    proof {
        lemma_u16s_len(n8(r0));
        lemma_u16s_len(n8(r1));
        lemma_u16s_len(n8(r2));
        lemma_u16s_len(n8(r3));
        lemma_u16s_len(n8(o0));
        lemma_u16s_len(n8(o1));
        lemma_u16s_len(n8(o2));
        lemma_u16s_len(n8(o3));
    }
    vst1q_s16_at(ts, 0, o0);
    vst1q_s16_at(ts, 8, o1);
    vst1q_s16_at(ts, 16, o2);
    vst1q_s16_at(ts, 24, o3);
    proof {
        let (w0, w1, w2, w3) = (u16s(n8(r0)), u16s(n8(r1)), u16s(n8(r2)), u16s(n8(r3)));
        let (p0, p1, p2, p3) = (u16s(n8(o0)), u16s(n8(o1)), u16s(n8(o2)), u16s(n8(o3)));
        assert forall|i: int| 0 <= i < 8 implies #[trigger] lanes_at(ts@, i) == lane_1d(
            xs@[i] + bias,
            xs@[8 + i] as int,
            xs@[16 + i] as int,
            xs@[24 + i] as int,
        ) by {
            lemma_pass_lane(w0, w1, w2, w3, bias, p0, p1, p2, p3, i);
            lemma_s16_bits(xs@[i], p0[i]);
            lemma_s16_bits(xs@[8 + i], p1[i]);
            lemma_s16_bits(xs@[16 + i], p2[i]);
            lemma_s16_bits(xs@[24 + i], p3[i]);
            assert(w0[i] == xs@[i] as u16);
            assert(w1[i] == xs@[8 + i] as u16);
            assert(w2[i] == xs@[16 + i] as u16);
            assert(w3[i] == xs@[24 + i] as u16);
            assert(ts@[i] == p0[i] as i16);
            assert(ts@[8 + i] == p1[i] as i16);
            assert(ts@[16 + i] == p2[i] as i16);
            assert(ts@[24 + i] == p3[i] as i16);
        }
    }
}

/// Lane `c` of row `k` of an eight-lane block.
pub open spec fn xl(x: Seq<i16>, k: int, c: int) -> i16 {
    x[8 * k + c]
}

/// Lane `4 + c` of row `k`: the second block's half.
pub open spec fn xh(x: Seq<i16>, k: int, c: int) -> i16 {
    x[8 * k + 4 + c]
}

/// `u` holds each 4x4 half of the eight-lane block `t` transposed.
pub open spec fn transposed(t: Seq<i16>, u: Seq<i16>) -> bool {
    &&& forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 ==> #[trigger] xl(u, r, c) == xl(t, c, r)
    &&& forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 ==> #[trigger] xh(u, r, c) == xh(t, c, r)
}

proof fn lemma_transposed_all(ts: Seq<i16>, us: Seq<i16>)
    requires
        us[0] == ts[0],
        us[4] == ts[4],
        us[1] == ts[8],
        us[5] == ts[12],
        us[2] == ts[16],
        us[6] == ts[20],
        us[3] == ts[24],
        us[7] == ts[28],
        us[8] == ts[1],
        us[12] == ts[5],
        us[9] == ts[9],
        us[13] == ts[13],
        us[10] == ts[17],
        us[14] == ts[21],
        us[11] == ts[25],
        us[15] == ts[29],
        us[16] == ts[2],
        us[20] == ts[6],
        us[17] == ts[10],
        us[21] == ts[14],
        us[18] == ts[18],
        us[22] == ts[22],
        us[19] == ts[26],
        us[23] == ts[30],
        us[24] == ts[3],
        us[28] == ts[7],
        us[25] == ts[11],
        us[29] == ts[15],
        us[26] == ts[19],
        us[30] == ts[23],
        us[27] == ts[27],
        us[31] == ts[31],
    ensures
        transposed(ts, us),
{
    assert forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 implies #[trigger] xl(us, r, c) == xl(ts, c, r) by {
        assert(r == 0 || r == 1 || r == 2 || r == 3);
        assert(c == 0 || c == 1 || c == 2 || c == 3);
    }
    assert forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 implies #[trigger] xh(us, r, c) == xh(ts, c, r) by {
        assert(r == 0 || r == 1 || r == 2 || r == 3);
        assert(c == 0 || c == 1 || c == 2 || c == 3);
    }
}

/// The 16-bit lanes of a 16-bit interleave.
proof fn lemma_unpack16(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>, hi: bool)
    requires
        a.len() == 16,
        b.len() == 16,
        r.len() == 16,
        u16s(r) == (if hi {
            unpackhi16_lanes(u16s(a), u16s(b))
        } else {
            unpacklo16_lanes(u16s(a), u16s(b))
        }),
    ensures
        u16s(a).len() == 8,
        u16s(b).len() == 8,
        u16s(r).len() == 8,
        ({
            let o: int = if hi {
                4
            } else {
                0
            };
            u16s(r) =~= seq![
                u16s(a)[o],
                u16s(b)[o],
                u16s(a)[o + 1],
                u16s(b)[o + 1],
                u16s(a)[o + 2],
                u16s(b)[o + 2],
                u16s(a)[o + 3],
                u16s(b)[o + 3],
            ]
        }),
{
}

proof fn lemma_u16s_len(b: Seq<u8>)
    requires
        b.len() == 16,
    ensures
        u16s(b).len() == 8,
{
}

proof fn lemma_rt16(x: i16)
    ensures
        ((x as u16) as i16) == x,
{
    assert(((x as u16) as i16) == x) by (bit_vector);
}

/// The 16-bit lanes of a 32-bit interleave.
proof fn lemma_unpack32(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>, hi: bool)
    requires
        a.len() == 16,
        b.len() == 16,
        r.len() == 16,
        u32s(r) == (if hi {
            unpackhi32_lanes(u32s(a), u32s(b))
        } else {
            unpacklo32_lanes(u32s(a), u32s(b))
        }),
    ensures
        ({
            let o: int = if hi {
                4
            } else {
                0
            };
            u16s(r) =~= seq![
                u16s(a)[o],
                u16s(a)[o + 1],
                u16s(b)[o],
                u16s(b)[o + 1],
                u16s(a)[o + 2],
                u16s(a)[o + 3],
                u16s(b)[o + 2],
                u16s(b)[o + 3],
            ]
        }),
{
    lemma_u16s_of_u32s(a);
    lemma_u16s_of_u32s(b);
    lemma_u16s_of_u32s(r);
    assert(u16s(r)[2 * 0int] == (u32s(r)[0] & 0xffff) as u16);
    assert(u16s(r)[2 * 1int] == (u32s(r)[1] & 0xffff) as u16);
    assert(u16s(r)[2 * 2int] == (u32s(r)[2] & 0xffff) as u16);
    assert(u16s(r)[2 * 3int] == (u32s(r)[3] & 0xffff) as u16);
    assert(u16s(a)[2 * 0int] == (u32s(a)[0] & 0xffff) as u16);
    assert(u16s(a)[2 * 1int] == (u32s(a)[1] & 0xffff) as u16);
    assert(u16s(a)[2 * 2int] == (u32s(a)[2] & 0xffff) as u16);
    assert(u16s(a)[2 * 3int] == (u32s(a)[3] & 0xffff) as u16);
    assert(u16s(b)[2 * 0int] == (u32s(b)[0] & 0xffff) as u16);
    assert(u16s(b)[2 * 1int] == (u32s(b)[1] & 0xffff) as u16);
    assert(u16s(b)[2 * 2int] == (u32s(b)[2] & 0xffff) as u16);
    assert(u16s(b)[2 * 3int] == (u32s(b)[3] & 0xffff) as u16);
}

proof fn lemma_le64_inj(a0: u32, a1: u32, b0: u32, b1: u32)
    requires
        le64(a0, a1) == le64(b0, b1),
    ensures
        a0 == b0,
        a1 == b1,
{
    assert(((a0 as u64) | ((a1 as u64) << 32u64)) == ((b0 as u64) | ((b1 as u64) << 32u64)) ==> a0 == b0 && a1 == b1)
        by (bit_vector);
}

/// The 16-bit lanes of a 64-bit interleave.
proof fn lemma_unpack64(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>, hi: bool)
    requires
        a.len() == 16,
        b.len() == 16,
        r.len() == 16,
        u64s(r) == (if hi {
            unpackhi64_lanes(u64s(a), u64s(b))
        } else {
            unpacklo64_lanes(u64s(a), u64s(b))
        }),
    ensures
        ({
            let o: int = if hi {
                4
            } else {
                0
            };
            u16s(r) =~= seq![
                u16s(a)[o],
                u16s(a)[o + 1],
                u16s(a)[o + 2],
                u16s(a)[o + 3],
                u16s(b)[o],
                u16s(b)[o + 1],
                u16s(b)[o + 2],
                u16s(b)[o + 3],
            ]
        }),
{
    let k: int = if hi {
        1
    } else {
        0
    };
    assert(u64s(r)[0] == u64s(a)[k]);
    assert(u64s(r)[1] == u64s(b)[k]);
    lemma_le64_inj(u32s(r)[2 * 0int], u32s(r)[2 * 0int + 1], u32s(a)[2 * k], u32s(a)[2 * k + 1]);
    lemma_le64_inj(u32s(r)[2 * 1int], u32s(r)[2 * 1int + 1], u32s(b)[2 * k], u32s(b)[2 * k + 1]);
    lemma_u16s_of_u32s(a);
    lemma_u16s_of_u32s(b);
    lemma_u16s_of_u32s(r);
    assert(u16s(r)[2 * 0int] == (u32s(r)[0] & 0xffff) as u16);
    assert(u16s(r)[2 * 1int] == (u32s(r)[1] & 0xffff) as u16);
    assert(u16s(r)[2 * 2int] == (u32s(r)[2] & 0xffff) as u16);
    assert(u16s(r)[2 * 3int] == (u32s(r)[3] & 0xffff) as u16);
    assert(u16s(a)[2 * 0int] == (u32s(a)[0] & 0xffff) as u16);
    assert(u16s(a)[2 * 1int] == (u32s(a)[1] & 0xffff) as u16);
    assert(u16s(a)[2 * 2int] == (u32s(a)[2] & 0xffff) as u16);
    assert(u16s(a)[2 * 3int] == (u32s(a)[3] & 0xffff) as u16);
    assert(u16s(b)[2 * 0int] == (u32s(b)[0] & 0xffff) as u16);
    assert(u16s(b)[2 * 1int] == (u32s(b)[1] & 0xffff) as u16);
    assert(u16s(b)[2 * 2int] == (u32s(b)[2] & 0xffff) as u16);
    assert(u16s(b)[2 * 3int] == (u32s(b)[3] & 0xffff) as u16);
}

/// The interleaves of `transpose_halves`, lane by lane: output row `k`
/// holds lane `k` of the four input rows, then lane `4 + k`.
proof fn lemma_transpose(
    r0: Seq<u8>,
    r1: Seq<u8>,
    r2: Seq<u8>,
    r3: Seq<u8>,
    a0: Seq<u8>,
    a1: Seq<u8>,
    b0: Seq<u8>,
    b1: Seq<u8>,
    c0: Seq<u8>,
    c1: Seq<u8>,
    d0: Seq<u8>,
    d1: Seq<u8>,
    o0: Seq<u8>,
    o1: Seq<u8>,
    o2: Seq<u8>,
    o3: Seq<u8>,
)
    requires
        r0.len() == 16 && r1.len() == 16 && r2.len() == 16 && r3.len() == 16,
        a0.len() == 16 && a1.len() == 16 && b0.len() == 16 && b1.len() == 16,
        c0.len() == 16 && c1.len() == 16 && d0.len() == 16 && d1.len() == 16,
        o0.len() == 16 && o1.len() == 16 && o2.len() == 16 && o3.len() == 16,
        u16s(a0) == unpacklo16_lanes(u16s(r0), u16s(r1)),
        u16s(a1) == unpacklo16_lanes(u16s(r2), u16s(r3)),
        u16s(b0) == unpackhi16_lanes(u16s(r0), u16s(r1)),
        u16s(b1) == unpackhi16_lanes(u16s(r2), u16s(r3)),
        u32s(c0) == unpacklo32_lanes(u32s(a0), u32s(a1)),
        u32s(c1) == unpackhi32_lanes(u32s(a0), u32s(a1)),
        u32s(d0) == unpacklo32_lanes(u32s(b0), u32s(b1)),
        u32s(d1) == unpackhi32_lanes(u32s(b0), u32s(b1)),
        u64s(o0) == unpacklo64_lanes(u64s(c0), u64s(d0)),
        u64s(o1) == unpackhi64_lanes(u64s(c0), u64s(d0)),
        u64s(o2) == unpacklo64_lanes(u64s(c1), u64s(d1)),
        u64s(o3) == unpackhi64_lanes(u64s(c1), u64s(d1)),
    ensures
        u16s(o0) =~= seq![u16s(r0)[0], u16s(r1)[0], u16s(r2)[0], u16s(r3)[0], u16s(r0)[4], u16s(r1)[4], u16s(r2)[4], u16s(r3)[4]],
        u16s(o1) =~= seq![u16s(r0)[1], u16s(r1)[1], u16s(r2)[1], u16s(r3)[1], u16s(r0)[5], u16s(r1)[5], u16s(r2)[5], u16s(r3)[5]],
        u16s(o2) =~= seq![u16s(r0)[2], u16s(r1)[2], u16s(r2)[2], u16s(r3)[2], u16s(r0)[6], u16s(r1)[6], u16s(r2)[6], u16s(r3)[6]],
        u16s(o3) =~= seq![u16s(r0)[3], u16s(r1)[3], u16s(r2)[3], u16s(r3)[3], u16s(r0)[7], u16s(r1)[7], u16s(r2)[7], u16s(r3)[7]],
{
    hide(u16s);
    hide(u32s);
    hide(u64s);
    hide(unpacklo16_lanes);
    hide(unpackhi16_lanes);
    hide(unpacklo32_lanes);
    hide(unpackhi32_lanes);
    hide(unpacklo64_lanes);
    hide(unpackhi64_lanes);
    lemma_unpack16(r0, r1, a0, false);
    lemma_unpack16(r2, r3, a1, false);
    lemma_unpack16(r0, r1, b0, true);
    lemma_unpack16(r2, r3, b1, true);
    lemma_unpack32(a0, a1, c0, false);
    lemma_unpack32(a0, a1, c1, true);
    lemma_unpack32(b0, b1, d0, false);
    lemma_unpack32(b0, b1, d1, true);
    lemma_unpack64(c0, d0, o0, false);
    lemma_unpack64(c0, d0, o1, true);
    lemma_unpack64(c1, d1, o2, false);
    lemma_unpack64(c1, d1, o3, true);
}

/// Transposes each 4x4 half of an eight-lane block (four rows of eight
/// 16-bit lanes): 16-, 32- and 64-bit interleaves, on SSE2 or NEON.
#[inline(always)]
fn transpose_halves(t: &[i16; 32], u: &mut [i16; 32])
    ensures
        transposed(t@, final(u)@),
{
    hide(u16s);
    hide(u32s);
    hide(u64s);
    hide(unpacklo16_lanes);
    hide(unpackhi16_lanes);
    hide(unpacklo32_lanes);
    hide(unpackhi32_lanes);
    hide(unpacklo64_lanes);
    hide(unpackhi64_lanes);
    let ts: &[i16] = t;
    let us: &mut [i16] = u;
    proof {
        assert(ts@.len() == 32);
        assert(us@.len() == 32);
    }
    if has_neon() {
        let r0 = vld1q_s16_at(ts, 0);
        let r1 = vld1q_s16_at(ts, 8);
        let r2 = vld1q_s16_at(ts, 16);
        let r3 = vld1q_s16_at(ts, 24);
        let a0 = vzip1q_u16(r0, r1);
        let a1 = vzip1q_u16(r2, r3);
        let b0 = vzip2q_u16(r0, r1);
        let b1 = vzip2q_u16(r2, r3);
        let c0 = vzip1q_u32(a0, a1);
        let c1 = vzip2q_u32(a0, a1);
        let d0 = vzip1q_u32(b0, b1);
        let d1 = vzip2q_u32(b0, b1);
        let o0 = vzip1q_u64(c0, d0);
        let o1 = vzip2q_u64(c0, d0);
        let o2 = vzip1q_u64(c1, d1);
        let o3 = vzip2q_u64(c1, d1);
        proof {
            lemma_u16s_len(n8(r0));
            lemma_u16s_len(n8(r1));
            lemma_u16s_len(n8(r2));
            lemma_u16s_len(n8(r3));
            lemma_u16s_len(n8(o0));
            lemma_u16s_len(n8(o1));
            lemma_u16s_len(n8(o2));
            lemma_u16s_len(n8(o3));
        }
        vst1q_s16_at(us, 0, o0);
        vst1q_s16_at(us, 8, o1);
        vst1q_s16_at(us, 16, o2);
        vst1q_s16_at(us, 24, o3);
        proof {
            lemma_transpose(
                n8(r0),
                n8(r1),
                n8(r2),
                n8(r3),
                n8(a0),
                n8(a1),
                n8(b0),
                n8(b1),
                n8(c0),
                n8(c1),
                n8(d0),
                n8(d1),
                n8(o0),
                n8(o1),
                n8(o2),
                n8(o3),
            );
            lemma_rt16(ts@[0]);
            lemma_rt16(ts@[1]);
            lemma_rt16(ts@[2]);
            lemma_rt16(ts@[3]);
            lemma_rt16(ts@[4]);
            lemma_rt16(ts@[5]);
            lemma_rt16(ts@[6]);
            lemma_rt16(ts@[7]);
            lemma_rt16(ts@[8]);
            lemma_rt16(ts@[9]);
            lemma_rt16(ts@[10]);
            lemma_rt16(ts@[11]);
            lemma_rt16(ts@[12]);
            lemma_rt16(ts@[13]);
            lemma_rt16(ts@[14]);
            lemma_rt16(ts@[15]);
            lemma_rt16(ts@[16]);
            lemma_rt16(ts@[17]);
            lemma_rt16(ts@[18]);
            lemma_rt16(ts@[19]);
            lemma_rt16(ts@[20]);
            lemma_rt16(ts@[21]);
            lemma_rt16(ts@[22]);
            lemma_rt16(ts@[23]);
            lemma_rt16(ts@[24]);
            lemma_rt16(ts@[25]);
            lemma_rt16(ts@[26]);
            lemma_rt16(ts@[27]);
            lemma_rt16(ts@[28]);
            lemma_rt16(ts@[29]);
            lemma_rt16(ts@[30]);
            lemma_rt16(ts@[31]);
            assert(us@[0] == ts@[0] && us@[4] == ts@[4]);
            assert(us@[1] == ts@[8] && us@[5] == ts@[12]);
            assert(us@[2] == ts@[16] && us@[6] == ts@[20]);
            assert(us@[3] == ts@[24] && us@[7] == ts@[28]);
            assert(us@[8] == ts@[1] && us@[12] == ts@[5]);
            assert(us@[9] == ts@[9] && us@[13] == ts@[13]);
            assert(us@[10] == ts@[17] && us@[14] == ts@[21]);
            assert(us@[11] == ts@[25] && us@[15] == ts@[29]);
            assert(us@[16] == ts@[2] && us@[20] == ts@[6]);
            assert(us@[17] == ts@[10] && us@[21] == ts@[14]);
            assert(us@[18] == ts@[18] && us@[22] == ts@[22]);
            assert(us@[19] == ts@[26] && us@[23] == ts@[30]);
            assert(us@[24] == ts@[3] && us@[28] == ts@[7]);
            assert(us@[25] == ts@[11] && us@[29] == ts@[15]);
            assert(us@[26] == ts@[19] && us@[30] == ts@[23]);
            assert(us@[27] == ts@[27] && us@[31] == ts@[31]);
            lemma_transposed_all(ts@, us@);
        }
    } else {
        // SSE2 is part of x86-64 (and emulated elsewhere).
        transpose_halves_sse2(ts, us);
    }
}

fn transpose_halves_sse2(ts: &[i16], us: &mut [i16])
    requires
        ts@.len() == 32,
        old(us)@.len() == 32,
    ensures
        final(us)@.len() == 32,
        transposed(ts@, final(us)@),
{
    hide(u16s);
    hide(u32s);
    hide(u64s);
    hide(unpacklo16_lanes);
    hide(unpackhi16_lanes);
    hide(unpacklo32_lanes);
    hide(unpackhi32_lanes);
    hide(unpacklo64_lanes);
    hide(unpackhi64_lanes);
    let r0 = load128_i16(ts, 0);
    let r1 = load128_i16(ts, 8);
    let r2 = load128_i16(ts, 16);
    let r3 = load128_i16(ts, 24);
    let a0 = _mm_unpacklo_epi16(r0, r1);
    let a1 = _mm_unpacklo_epi16(r2, r3);
    let b0 = _mm_unpackhi_epi16(r0, r1);
    let b1 = _mm_unpackhi_epi16(r2, r3);
    let c0 = _mm_unpacklo_epi32(a0, a1);
    let c1 = _mm_unpackhi_epi32(a0, a1);
    let d0 = _mm_unpacklo_epi32(b0, b1);
    let d1 = _mm_unpackhi_epi32(b0, b1);
    let o0 = _mm_unpacklo_epi64(c0, d0);
    let o1 = _mm_unpackhi_epi64(c0, d0);
    let o2 = _mm_unpacklo_epi64(c1, d1);
    let o3 = _mm_unpackhi_epi64(c1, d1);
    proof {
        lemma_u16s_len(b128(r0));
        lemma_u16s_len(b128(r1));
        lemma_u16s_len(b128(r2));
        lemma_u16s_len(b128(r3));
        lemma_u16s_len(b128(o0));
        lemma_u16s_len(b128(o1));
        lemma_u16s_len(b128(o2));
        lemma_u16s_len(b128(o3));
    }
    store128_i16(us, 0, o0);
    store128_i16(us, 8, o1);
    store128_i16(us, 16, o2);
    store128_i16(us, 24, o3);
    proof {
        lemma_transpose(
            b128(r0),
            b128(r1),
            b128(r2),
            b128(r3),
            b128(a0),
            b128(a1),
            b128(b0),
            b128(b1),
            b128(c0),
            b128(c1),
            b128(d0),
            b128(d1),
            b128(o0),
            b128(o1),
            b128(o2),
            b128(o3),
        );
        lemma_rt16(ts@[0]);
        lemma_rt16(ts@[1]);
        lemma_rt16(ts@[2]);
        lemma_rt16(ts@[3]);
        lemma_rt16(ts@[4]);
        lemma_rt16(ts@[5]);
        lemma_rt16(ts@[6]);
        lemma_rt16(ts@[7]);
        lemma_rt16(ts@[8]);
        lemma_rt16(ts@[9]);
        lemma_rt16(ts@[10]);
        lemma_rt16(ts@[11]);
        lemma_rt16(ts@[12]);
        lemma_rt16(ts@[13]);
        lemma_rt16(ts@[14]);
        lemma_rt16(ts@[15]);
        lemma_rt16(ts@[16]);
        lemma_rt16(ts@[17]);
        lemma_rt16(ts@[18]);
        lemma_rt16(ts@[19]);
        lemma_rt16(ts@[20]);
        lemma_rt16(ts@[21]);
        lemma_rt16(ts@[22]);
        lemma_rt16(ts@[23]);
        lemma_rt16(ts@[24]);
        lemma_rt16(ts@[25]);
        lemma_rt16(ts@[26]);
        lemma_rt16(ts@[27]);
        lemma_rt16(ts@[28]);
        lemma_rt16(ts@[29]);
        lemma_rt16(ts@[30]);
        lemma_rt16(ts@[31]);
        assert(us@[0] == ts@[0] && us@[4] == ts@[4]);
        assert(us@[1] == ts@[8] && us@[5] == ts@[12]);
        assert(us@[2] == ts@[16] && us@[6] == ts@[20]);
        assert(us@[3] == ts@[24] && us@[7] == ts@[28]);
        assert(us@[8] == ts@[1] && us@[12] == ts@[5]);
        assert(us@[9] == ts@[9] && us@[13] == ts@[13]);
        assert(us@[10] == ts@[17] && us@[14] == ts@[21]);
        assert(us@[11] == ts@[25] && us@[15] == ts@[29]);
        assert(us@[16] == ts@[2] && us@[20] == ts@[6]);
        assert(us@[17] == ts@[10] && us@[21] == ts@[14]);
        assert(us@[18] == ts@[18] && us@[22] == ts@[22]);
        assert(us@[19] == ts@[26] && us@[23] == ts@[30]);
        assert(us@[24] == ts@[3] && us@[28] == ts@[7]);
        assert(us@[25] == ts@[11] && us@[29] == ts@[15]);
        assert(us@[26] == ts@[19] && us@[30] == ts@[23]);
        assert(us@[27] == ts@[27] && us@[31] == ts@[31]);
        lemma_transposed_all(ts@, us@);
    }
}

/// Eight lanes added to two blocks side by side are the two residuals
/// added one after the other.
proof fn lemma_two_blocks(b0: Seq<u8>, b1: Seq<u8>, d: int, u: Seq<i16>, ra: Seq<int>, rb: Seq<int>)
    requires
        b1.len() == b0.len(),
        0 <= d,
        forall|j: int|
            0 <= j < b0.len() ==> #[trigger] b1[j] == (if in_blk(j - d, 8) {
                clip_to(b0[j] + (xl(u, (j - d) / 32, (j - d) % 32) as int) / 8, 255) as u8
            } else {
                b0[j]
            }),
        forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 ==> (#[trigger] xl(u, r, c) as int) / 8 == ra[4 * r + c],
        forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 ==> (#[trigger] xh(u, r, c) as int) / 8 == rb[4 * r + c],
    ensures
        b1 == add_res(add_res(b0, d, ra), d + 4, rb),
{
    let mid = add_res(b0, d, ra);
    let want = add_res(mid, d + 4, rb);
    assert forall|j: int| 0 <= j < b1.len() implies b1[j] == want[j] by {
        if in_blk(j - d, 8) {
            let r = (j - d) / 32;
            let c = (j - d) % 32;
            if c < 4 {
                assert(xl(u, r, c) as int / 8 == ra[4 * r + c]);
                assert(!in_blk(j - (d + 4), 4));
            } else {
                assert(xh(u, r, c - 4) as int / 8 == rb[4 * r + (c - 4)]);
                assert(xh(u, r, c - 4) == xl(u, r, c));
                assert((j - (d + 4)) / 32 == r && (j - (d + 4)) % 32 == c - 4);
                assert(!in_blk(j - d, 4));
            }
        } else {
            assert(!in_blk(j - d, 4));
            assert(!in_blk(j - (d + 4), 4));
        }
    }
    assert(b1 =~= want);
}

/// `TransformTwo` (`Transform_SSE2` with `do_two`): `transform_one` on the
/// blocks `inp[i..i + 16]` at `dst[d]` and `inp[i + 16..i + 32]` at
/// `dst[d + 4]`, computed together.
pub fn transform_two(inp: &[i16], i: usize, dst: &mut [u8], d: usize)
    requires
        i + 32 <= inp@.len(),
        d + 3 * BPS + 8 <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        idct_tame(cblk(inp@, i as int)) && idct_tame(cblk(inp@, i + 16)) ==> final(dst)@ == add_res(
            add_res(old(dst)@, d as int, idct(cblk(inp@, i as int))),
            d + 4,
            idct(cblk(inp@, i + 16)),
        ),
{
    hide(add_res);
    hide(idct);
    hide(idct_pre);
    proof {assert(inp@.len() == inp.len()); assert(dst@.len() == dst.len());}
    let ghost ca = cblk(inp@, i as int);
    let ghost cb = cblk(inp@, i + 16);
    // Row `k` of both blocks side by side: lanes 0..4 the first block's
    // columns, 4..8 the second's.
    let mut x: [i16; 32] = [0; 32];
    let mut k: usize = 0;
    while k < 4
        invariant
            inp@.len() <= usize::MAX,
            k <= 4,
            i + 32 <= inp@.len(),
            forall|kk: int, cc: int|
                0 <= kk < k && 0 <= cc < 4 ==> #[trigger] xl(x@, kk, cc) == inp@[i + 4 * kk + cc],
            forall|kk: int, cc: int|
                0 <= kk < k && 0 <= cc < 4 ==> #[trigger] xh(x@, kk, cc) == inp@[i + 16 + 4 * kk + cc],
        decreases 4 - k,
    {
        let mut c: usize = 0;
        while c < 4
            invariant
                inp@.len() <= usize::MAX,
                k < 4,
                c <= 4,
                i + 32 <= inp@.len(),
                forall|kk: int, cc: int|
                    0 <= kk < 4 && 0 <= cc < 4 && (kk < k || (kk == k && cc < c)) ==> #[trigger] xl(x@, kk, cc) == inp@[i
                        + 4 * kk + cc],
                forall|kk: int, cc: int|
                    0 <= kk < 4 && 0 <= cc < 4 && (kk < k || (kk == k && cc < c)) ==> #[trigger] xh(x@, kk, cc) == inp@[i
                        + 16 + 4 * kk + cc],
            decreases 4 - c,
        {
            let ghost x0 = x@;
            x[8 * k + c] = get16(inp, i + 4 * k + c);
            x[8 * k + 4 + c] = get16(inp, i + 16 + 4 * k + c);
            proof {
                assert(x@ == x0.update(8 * k + c, inp@[i + 4 * k + c]).update(8 * k + 4 + c, inp@[i + 16 + 4 * k + c]));
                assert forall|kk: int, cc: int|
                    0 <= kk < 4 && 0 <= cc < 4 && (kk < k || (kk == k && cc < c + 1)) implies #[trigger] xl(x@, kk, cc)
                    == inp@[i + 4 * kk + cc] by {
                    assert(8 * kk + cc != 8 * k + 4 + c);
                    if kk == k && cc == c {
                    } else {
                        assert(8 * kk + cc != 8 * k + c);
                        assert(xl(x0, kk, cc) == inp@[i + 4 * kk + cc]);
                    }
                }
                assert forall|kk: int, cc: int|
                    0 <= kk < 4 && 0 <= cc < 4 && (kk < k || (kk == k && cc < c + 1)) implies #[trigger] xh(x@, kk, cc)
                    == inp@[i + 16 + 4 * kk + cc] by {
                    assert(8 * kk + 4 + cc != 8 * k + c);
                    if kk == k && cc == c {
                    } else {
                        assert(8 * kk + 4 + cc != 8 * k + 4 + c);
                        assert(xh(x0, kk, cc) == inp@[i + 16 + 4 * kk + cc]);
                    }
                }
            }
            c = c + 1;
        }
        k = k + 1;
    }
    let mut t: [i16; 32] = [0; 32];
    let mut u: [i16; 32] = [0; 32];
    idct_pass(&x, &mut t, 0, 0);
    let ghost t1 = t@;
    transpose_halves(&t, &mut u);
    let ghost u1 = u@;
    idct_pass(&u, &mut t, 4, 0);
    let ghost t2 = t@;
    transpose_halves(&t, &mut u);
    add_rows(dst, d, &u, 8);
    proof {
        if idct_tame(ca) && idct_tame(cb) {
            assert forall|kk: int, cc: int| 0 <= kk < 4 && 0 <= cc < 4 implies #[trigger] xl(x@, kk, 0 + cc) == ca[4 * kk
                + cc] by {
                assert(xl(x@, kk, cc) == inp@[i + 4 * kk + cc]);
            }
            assert forall|kk: int, cc: int| 0 <= kk < 4 && 0 <= cc < 4 implies #[trigger] xl(x@, kk, 4 + cc) == cb[4 * kk
                + cc] by {
                assert(xh(x@, kk, cc) == inp@[i + 16 + 4 * kk + cc]);
            }
            lemma_lane_idct(ca, x@, t1, u1, t2, u@, 0);
            lemma_lane_idct(cb, x@, t1, u1, t2, u@, 4);
            let ra = idct(ca);
            let rb = idct(cb);
            assert forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 implies (#[trigger] xl(u@, r, c) as int) / 8 == ra[4 * r
                + c] by {
                assert(xl(u@, r, 0 + c) == idct_pre(ca, r, c));
                lemma_idct_at(ca, r, c);
            }
            assert forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 implies (#[trigger] xh(u@, r, c) as int) / 8 == rb[4 * r
                + c] by {
                assert(xl(u@, r, 4 + c) == idct_pre(cb, r, c));
                lemma_idct_at(cb, r, c);
            }
            lemma_two_blocks(old(dst)@, dst@, d as int, u@, ra, rb);
        }
    }
}

/// `WEBP_TRANSFORM_AC3_MUL1`.
#[inline(always)]
fn mul1(a: i32) -> (r: i32)
    requires
        -0x8000 <= a <= 0x8000,
    ensures
        -0xc000 <= r <= 0xc000,
        r == idct_mul1(a as int),
{
    let m = a * 20091;
    proof {
        assert(-0x8000 * 20091 <= m <= 0x8000 * 20091) by (nonlinear_arith)
            requires m == a * 20091, -0x8000 <= a <= 0x8000;
        assert(-0x8000 * 20091 <= m <= 0x8000 * 20091 ==> -0x4000 <= (m >> 16u32) <= 0x4000) by (bit_vector);
        lemma_sar16(m);
    }
    (m >> 16u32) + a
}

/// `WEBP_TRANSFORM_AC3_MUL2`.
#[inline(always)]
fn mul2(a: i32) -> (r: i32)
    requires
        -0x8000 <= a <= 0x8000,
    ensures
        -0x8000 <= r <= 0x8000,
        r == idct_mul2(a as int),
{
    let m = a * 35468;
    proof {
        assert(-0x8000 * 35468 <= m <= 0x8000 * 35468) by (nonlinear_arith)
            requires m == a * 35468, -0x8000 <= a <= 0x8000;
        assert(-0x8000 * 35468 <= m <= 0x8000 * 35468 ==> -0x8000 <= (m >> 16u32) <= 0x8000) by (bit_vector);
        lemma_sar16(m);
    }
    m >> 16u32
}

/// `add_res` at the pixel in row `r`, column `c` of the block, and away
/// from the block.
proof fn lemma_add_res_at(b: Seq<u8>, d: int, res: Seq<int>, r: int, c: int)
    requires
        0 <= r < 4,
        0 <= c < 4,
        0 <= d,
        d + 32 * r + c < b.len(),
    ensures
        add_res(b, d, res)[d + 32 * r + c] == clip_to(b[d + 32 * r + c] + res[4 * r + c], 255) as u8,
        in_blk(32 * r + c, 4),
        (32 * r + c) / 32 == r,
        (32 * r + c) % 32 == c,
{
}

proof fn lemma_add_res_out(b: Seq<u8>, d: int, res: Seq<int>)
    ensures
        add_res(b, d, res).len() == b.len(),
        forall|j: int| 0 <= j < b.len() && !in_blk(j - d, 4) ==> #[trigger] add_res(b, d, res)[j] == b[j],
{
}

proof fn lemma_idct_at(cb: Seq<int>, r: int, c: int)
    requires
        0 <= r < 4,
        0 <= c < 4,
    ensures
        idct(cb)[4 * r + c] == idct_pre(cb, r, c) / 8,
{
    assert((4 * r + c) / 4 == r && (4 * r + c) % 4 == c);
}

/// The inverse DCT of a block with three coefficients.
proof fn lemma_idct_ac3(cb: Seq<int>, r: int, c: int)
    requires
        cb.len() == 16,
        only_ac3(cb),
        0 <= r < 4,
        0 <= c < 4,
    ensures
        idct_pre(cb, r, c) == cb[0] + 4 + (if r == 0 {
            idct_mul1(cb[4])
        } else if r == 1 {
            idct_mul2(cb[4])
        } else if r == 2 {
            -idct_mul2(cb[4])
        } else {
            -idct_mul1(cb[4])
        }) + (if c == 0 {
            idct_mul1(cb[1])
        } else if c == 1 {
            idct_mul2(cb[1])
        } else if c == 2 {
            -idct_mul2(cb[1])
        } else {
            -idct_mul1(cb[1])
        }),
{
    assert(cb[2] == 0 && cb[3] == 0 && cb[5] == 0 && cb[6] == 0 && cb[7] == 0 && cb[8] == 0 && cb[9] == 0 && cb[10] == 0
        && cb[11] == 0 && cb[12] == 0 && cb[13] == 0 && cb[14] == 0 && cb[15] == 0);
    assert(idct_mul1(0) == 0 && idct_mul2(0) == 0);
    assert(idct_v(cb, 1, r) == cb[1]);
    assert(idct_v(cb, 2, r) == 0);
    assert(idct_v(cb, 3, r) == 0);
}

/// `TransformAC3_C`: the transform of a block whose only nonzero
/// coefficients are 0, 1 and 4. For such a block it is `vp8spec::idct`.
pub fn transform_ac3(inp: &[i16], i: usize, dst: &mut [u8], d: usize)
    requires
        i + 16 <= inp@.len(),
        d + 3 * BPS + 4 <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        only_ac3(cblk(inp@, i as int)) ==> final(dst)@ == add_res(old(dst)@, d as int, idct(cblk(inp@, i as int))),
{
    hide(add_res);
    hide(idct);
    hide(idct_pre);
    proof {assert(inp@.len() == inp.len()); assert(dst@.len() == dst.len());}
    let ghost cb = cblk(inp@, i as int);
    let ghost want = add_res(old(dst)@, d as int, idct(cb));
    let a = inp[i] as i32 + 4;
    let c4 = mul2(inp[i + 4] as i32);
    let d4 = mul1(inp[i + 4] as i32);
    let c1 = mul2(inp[i + 1] as i32);
    let d1 = mul1(inp[i + 1] as i32);
    proof {
        assert(cb[0] == inp@[i as int] && cb[1] == inp@[i + 1] && cb[4] == inp@[i + 4]);
    }
    let mut r: usize = 0;
    while r < 4
        invariant
            -0x8000 <= a <= 0x8004,
            -0xc000 <= d4 <= 0xc000,
            -0x8000 <= c4 <= 0x8000,
            -0xc000 <= d1 <= 0xc000,
            -0x8000 <= c1 <= 0x8000,
            inp@.len() <= usize::MAX,
            dst@.len() <= usize::MAX,
            r <= 4,
            d + 3 * BPS + 4 <= dst@.len(),
            dst@.len() == old(dst)@.len(),
            a == cb[0] + 4,
            c4 == idct_mul2(cb[4]),
            d4 == idct_mul1(cb[4]),
            c1 == idct_mul2(cb[1]),
            d1 == idct_mul1(cb[1]),
            cb.len() == 16,
            want == add_res(old(dst)@, d as int, idct(cb)),
            only_ac3(cb) ==> forall|j: int|
                0 <= j < dst@.len() ==> #[trigger] dst@[j] == (if in_blk(j - d, 4) && (j - d) / 32 < r {
                    want[j]
                } else {
                    old(dst)@[j]
                }),
        decreases 4 - r,
    {
        let dc = if r == 0 {
            a + d4
        } else if r == 1 {
            a + c4
        } else if r == 2 {
            a - c4
        } else {
            a - d4
        };
        let p = d + r * BPS;
        let ghost b0 = dst@;
        proof {
            if only_ac3(cb) {
                lemma_idct_ac3(cb, r as int, 0);
                lemma_idct_ac3(cb, r as int, 1);
                lemma_idct_ac3(cb, r as int, 2);
                lemma_idct_ac3(cb, r as int, 3);
                lemma_idct_at(cb, r as int, 0);
                lemma_idct_at(cb, r as int, 1);
                lemma_idct_at(cb, r as int, 2);
                lemma_idct_at(cb, r as int, 3);
                lemma_add_res_at(old(dst)@, d as int, idct(cb), r as int, 0);
                lemma_add_res_at(old(dst)@, d as int, idct(cb), r as int, 1);
                lemma_add_res_at(old(dst)@, d as int, idct(cb), r as int, 2);
                lemma_add_res_at(old(dst)@, d as int, idct(cb), r as int, 3);
                assert(p == d + 32 * r);
                assert(b0[p as int] == old(dst)@[p as int] && b0[p + 1] == old(dst)@[p + 1] && b0[p + 2] == old(dst)@[p
                    + 2] && b0[p + 3] == old(dst)@[p + 3]);
            }
        }
        set(dst, p, clip8(get(dst, p) as i32 + shr3(dc + d1)));
        set(dst, p + 1, clip8(get(dst, p + 1) as i32 + shr3(dc + c1)));
        set(dst, p + 2, clip8(get(dst, p + 2) as i32 + shr3(dc - c1)));
        set(dst, p + 3, clip8(get(dst, p + 3) as i32 + shr3(dc - d1)));
        proof {
            if only_ac3(cb) {
                assert forall|j: int| 0 <= j < dst@.len() implies #[trigger] dst@[j] == (if in_blk(j - d, 4) && (j - d)
                    / 32 < r + 1 {
                    want[j]
                } else {
                    old(dst)@[j]
                }) by {
                    if j == p || j == p + 1 || j == p + 2 || j == p + 3 {
                        assert((j - d) / 32 == r);
                    } else {
                        assert(dst@[j] == b0[j]);
                        assert(!(in_blk(j - d, 4) && (j - d) / 32 == r));
                    }
                }
            }
        }
        r = r + 1;
    }
    proof {
        if only_ac3(cb) {
            lemma_add_res_out(old(dst)@, d as int, idct(cb));
            assert(dst@ =~= want);
        }
    }
}

/// The inverse DCT of a block with only a DC coefficient.
proof fn lemma_idct_dc(cb: Seq<int>, r: int, c: int)
    requires
        cb.len() == 16,
        only_dc(cb),
        0 <= r < 4,
        0 <= c < 4,
    ensures
        idct_pre(cb, r, c) == cb[0] + 4,
{
    assert(cb[1] == 0 && cb[4] == 0);
    assert(only_ac3(cb));
    lemma_idct_ac3(cb, r, c);
    assert(idct_mul1(0) == 0 && idct_mul2(0) == 0);
}

/// `TransformDC_C`: a block with only a DC coefficient. For such a block
/// it is `vp8spec::idct`.
pub fn transform_dc(inp: &[i16], i: usize, dst: &mut [u8], d: usize)
    requires
        i < inp@.len(),
        d + 3 * BPS + 4 <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        i + 16 <= inp@.len() && only_dc(cblk(inp@, i as int)) ==> final(dst)@ == add_res(
            old(dst)@,
            d as int,
            idct(cblk(inp@, i as int)),
        ),
{
    hide(add_res);
    hide(idct);
    hide(idct_pre);
    proof {assert(inp@.len() == inp.len()); assert(dst@.len() == dst.len());}
    let ghost cb = cblk(inp@, i as int);
    let ghost want = add_res(old(dst)@, d as int, idct(cb));
    let ghost ok = i + 16 <= inp@.len() && only_dc(cb);
    let dc = shr3(inp[i] as i32 + 4);
    let mut r: usize = 0;
    while r < 4
        invariant
            inp@.len() <= usize::MAX,
            dst@.len() <= usize::MAX,
            r <= 4,
            d + 3 * BPS + 4 <= dst@.len(),
            dst@.len() == old(dst)@.len(),
            -0x8000 <= dc <= 0x8000,
            dc == (inp@[i as int] + 4) / 8,
            cb == cblk(inp@, i as int),
            want == add_res(old(dst)@, d as int, idct(cb)),
            ok == (i + 16 <= inp@.len() && only_dc(cb)),
            ok ==> forall|j: int|
                0 <= j < dst@.len() ==> #[trigger] dst@[j] == (if in_blk(j - d, 4) && (j - d) / 32 < r {
                    want[j]
                } else {
                    old(dst)@[j]
                }),
        decreases 4 - r,
    {
        let p = d + r * BPS;
        let mut x: usize = 0;
        while x < 4
            invariant
                inp@.len() <= usize::MAX,
                dst@.len() <= usize::MAX,
                x <= 4,
                r < 4,
                p == d + r * BPS,
                d + 3 * BPS + 4 <= dst@.len(),
                dst@.len() == old(dst)@.len(),
                -0x8000 <= dc <= 0x8000,
                dc == (inp@[i as int] + 4) / 8,
                cb == cblk(inp@, i as int),
                want == add_res(old(dst)@, d as int, idct(cb)),
                ok == (i + 16 <= inp@.len() && only_dc(cb)),
                ok ==> forall|j: int|
                    0 <= j < dst@.len() ==> #[trigger] dst@[j] == (if in_blk(j - d, 4) && ((j - d) / 32 < r || ((j - d)
                        / 32 == r && (j - d) % 32 < x)) {
                        want[j]
                    } else {
                        old(dst)@[j]
                    }),
            decreases 4 - x,
        {
            proof {
                if ok {
                    lemma_idct_dc(cb, r as int, x as int);
                    lemma_idct_at(cb, r as int, x as int);
                    lemma_add_res_at(old(dst)@, d as int, idct(cb), r as int, x as int);
                    assert(p + x == d + 32 * r + x);
                    assert(cb[0] == inp@[i as int]);
                }
            }
            set(dst, p + x, clip8(get(dst, p + x) as i32 + dc));
            x = x + 1;
        }
        r = r + 1;
    }
    proof {
        if ok {
            lemma_add_res_out(old(dst)@, d as int, idct(cb));
            assert(dst@ =~= want);
        }
    }
}

/// The transform selector `k` (two bits of `non_zero_y`) is right for the
/// block `cb`: 0 for a block of zeros, 1 for a DC alone, 2 for
/// coefficients 0, 1 and 4, and 3 for a block the 16-bit transform is
/// exact on.
pub open spec fn kind_ok(k: int, cb: Seq<int>) -> bool {
    &&& k == 0 ==> only_dc(cb) && cb[0] == 0
    &&& k == 1 ==> only_dc(cb)
    &&& k == 2 ==> only_ac3(cb)
    &&& k == 3 ==> idct_tame(cb)
}

/// A block of zeros has no residual.
pub proof fn lemma_add_zero(b: Seq<u8>, d: int, cb: Seq<int>)
    requires
        cb.len() == 16,
        only_dc(cb),
        cb[0] == 0,
    ensures
        add_res(b, d, idct(cb)) == b,
{
    assert forall|j: int| 0 <= j < b.len() implies add_res(b, d, idct(cb))[j] == b[j] by {
        if in_blk(j - d, 4) {
            let r = (j - d) / 32;
            let c = (j - d) % 32;
            lemma_idct_dc(cb, r, c);
            assert((4 * r + c) / 4 == r && (4 * r + c) % 4 == c);
        }
    }
    assert(add_res(b, d, idct(cb)) =~= b);
}

/// `non_zero_y` as it stands when block `n` is reached: two bits further
/// up for each block before it.
pub open spec fn bits_at(b: u32, n: nat) -> u32
    decreases n,
{
    if n == 0 {
        b
    } else {
        bits_at(b, (n - 1) as nat) << 2u32
    }
}

pub proof fn lemma_bits_zero(n: nat)
    ensures
        bits_at(0, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_bits_zero((n - 1) as nat);
        assert(0u32 << 2u32 == 0) by (bit_vector);
    }
}

/// The two bits `non_zero_y` holds for luma block `n` are sound for the
/// block's coefficients `co[16 n..]`, and unless they say the block is
/// empty, the buffer holds those coefficients.
pub open spec fn y_ok(bits0: u32, buf: Seq<i16>, co: Seq<int>, n: int) -> bool {
    let k = bits_at(bits0, n as nat) >> 30u32;
    let cb = blk(co, 16 * n);
    if k == 0 {
        zero_blk(cb)
    } else {
        cblk(buf, 16 * n) == cb && kind_ok(k as int, cb)
    }
}

/// The same for the byte of `non_zero_uv` of a chroma block's four
/// subblocks, whose coefficients start at `co[i]`.
pub open spec fn uv_ok(bits: u32, buf: Seq<i16>, co: Seq<int>, i: int) -> bool {
    if bits & 0xff == 0 {
        forall|n: int| 0 <= n < 4 ==> zero_blk(#[trigger] blk(co, i + 16 * n))
    } else {
        &&& forall|n: int| 0 <= n < 4 ==> #[trigger] cblk(buf, i + 16 * n) == blk(co, i + 16 * n)
        &&& uv_kind_ok(bits, buf, i)
    }
}

pub proof fn lemma_res16_zero(w: Seq<u8>, co: Seq<int>, k: int)
    requires
        0 <= k,
        forall|n: int| 0 <= n < k ==> zero_blk(#[trigger] blk(co, 16 * n)),
    ensures
        rec_res16(w, co, k) == w,
    decreases k,
{
    if k > 0 {
        lemma_res16_zero(w, co, k - 1);
        assert(zero_blk(blk(co, 16 * (k - 1))));
        lemma_add_zero(w, s_y() + scan(k - 1), blk(co, 16 * (k - 1)));
    }
}

/// `do_uv_transform` under `uv_ok` adds the residuals of the
/// specification's coefficients.
pub proof fn lemma_uv_ok(bits: u32, buf: Seq<i16>, co: Seq<int>, i: int, w0: Seq<u8>, w1: Seq<u8>, d: int)
    requires
        uv_ok(bits, buf, co, i),
        uv_kind_ok(bits, buf, i) ==> w1 == add_res4(w0, d, buf, i),
        bits & 0xff == 0 ==> w1 == w0,
    ensures
        w1 == rec_chroma(w0, d, co, i),
{
    assert(blk(co, i + 16 * 0) == blk(co, i));
    assert(blk(co, i + 16 * 1) == blk(co, i + 16));
    assert(blk(co, i + 16 * 2) == blk(co, i + 32));
    assert(blk(co, i + 16 * 3) == blk(co, i + 48));
    if bits & 0xff == 0 {
        lemma_add_zero(w0, d, blk(co, i));
        lemma_add_zero(w0, d + 4, blk(co, i + 16));
        lemma_add_zero(w0, d + 4 * 32, blk(co, i + 32));
        lemma_add_zero(w0, d + 4 * 32 + 4, blk(co, i + 48));
    } else {
        assert(cblk(buf, i + 16 * 0) == cblk(buf, i));
        assert(cblk(buf, i + 16 * 1) == cblk(buf, i + 16));
        assert(cblk(buf, i + 16 * 2) == cblk(buf, i + 32));
        assert(cblk(buf, i + 16 * 3) == cblk(buf, i + 48));
    }
}

/// `DoTransform`: the transform a Y block's two `non_zero_y` bits ask for.
pub fn do_transform(bits: u32, inp: &[i16], i: usize, dst: &mut [u8], d: usize)
    requires
        i + 16 <= inp@.len(),
        d + 3 * BPS + 4 <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        kind_ok((bits >> 30u32) as int, cblk(inp@, i as int)) ==> final(dst)@ == add_res(
            old(dst)@,
            d as int,
            idct(cblk(inp@, i as int)),
        ),        (bits >> 30u32) == 0 ==> final(dst)@ == old(dst)@,
{
    proof {assert(inp@.len() == inp.len()); assert(dst@.len() == dst.len());}
    let k = bits >> 30u32;
    proof {
        assert((bits >> 30u32) <= 3) by (bit_vector);
    }
    if k == 3 {
        transform_one(inp, i, dst, d);
    } else if k == 2 {
        transform_ac3(inp, i, dst, d);
    } else if k == 1 {
        transform_dc(inp, i, dst, d);
    } else {
        proof {
            if kind_ok(k as int, cblk(inp@, i as int)) {
                lemma_add_zero(dst@, d as int, cblk(inp@, i as int));
            }
        }
    }
}

/// The four blocks of a chroma plane at `inp[i]`, added at `d`.
pub open spec fn add_res4(b: Seq<u8>, d: int, inp: Seq<i16>, i: int) -> Seq<u8> {
    let b1 = add_res(b, d, idct(cblk(inp, i)));
    let b2 = add_res(b1, d + 4, idct(cblk(inp, i + 16)));
    let b3 = add_res(b2, d + 4 * 32, idct(cblk(inp, i + 32)));
    add_res(b3, d + 4 * 32 + 4, idct(cblk(inp, i + 48)))
}

/// The selector byte `bits` of a chroma plane is right for its four
/// blocks: no bit set only if they are all zero, no high bit of a pair
/// set only if each has at most a DC, and the 16-bit transform is exact
/// on them otherwise.
pub open spec fn uv_kind_ok(bits: u32, inp: Seq<i16>, i: int) -> bool {
    forall|n: int|
        0 <= n < 4 ==> {
            let cb = #[trigger] cblk(inp, i + 16 * n);
            &&& bits & 0xff == 0 ==> only_dc(cb) && cb[0] == 0
            &&& bits & 0xaa == 0 ==> only_dc(cb)
            &&& bits & 0xaa != 0 ==> idct_tame(cb)
        }
}

/// `transform_dc` if the block has a DC.
#[inline(always)]
fn dc_if(inp: &[i16], i: usize, dst: &mut [u8], d: usize)
    requires
        i + 16 <= inp@.len(),
        d + 3 * BPS + 4 <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        only_dc(cblk(inp@, i as int)) ==> final(dst)@ == add_res(old(dst)@, d as int, idct(cblk(inp@, i as int))),
{
    proof {assert(inp@.len() == inp.len()); assert(dst@.len() == dst.len());}
    if inp[i] != 0 {
        transform_dc(inp, i, dst, d);
    } else {
        proof {
            if only_dc(cblk(inp@, i as int)) {
                lemma_add_zero(dst@, d as int, cblk(inp@, i as int));
            }
        }
    }
}

/// `DoUVTransform`: the four blocks of one chroma plane.
pub fn do_uv_transform(bits: u32, inp: &[i16], i: usize, dst: &mut [u8], d: usize)
    requires
        i + 64 <= inp@.len(),
        d + 7 * BPS + 8 <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        uv_kind_ok(bits, inp@, i as int) ==> final(dst)@ == add_res4(old(dst)@, d as int, inp@, i as int),        bits & 0xff == 0 ==> final(dst)@ == old(dst)@,
{
    proof {assert(inp@.len() == inp.len()); assert(dst@.len() == dst.len());}
    let ghost ok = uv_kind_ok(bits, inp@, i as int);
    proof {
        if ok {
            assert(cblk(inp@, i + 16 * 0) == cblk(inp@, i as int));
            assert(cblk(inp@, i + 16 * 1) == cblk(inp@, i + 16));
            assert(cblk(inp@, i + 16 * 2) == cblk(inp@, i + 32));
            assert(cblk(inp@, i + 16 * 3) == cblk(inp@, i + 48));
        }
    }
    if bits & 0xff != 0 {
        if bits & 0xaa != 0 {
            transform_two(inp, i, dst, d);
            transform_two(inp, i + 32, dst, d + 4 * BPS);
        } else {
            dc_if(inp, i, dst, d);
            dc_if(inp, i + 16, dst, d + 4);
            dc_if(inp, i + 32, dst, d + 4 * BPS);
            dc_if(inp, i + 48, dst, d + 4 * BPS + 4);
        }
    } else {
        proof {
            if ok {
                assert(bits & 0xff == 0 ==> bits & 0xaa == 0) by (bit_vector);
                lemma_add_zero(dst@, d as int, cblk(inp@, i as int));
                lemma_add_zero(dst@, d + 4, cblk(inp@, i + 16));
                lemma_add_zero(dst@, d + 4 * 32, cblk(inp@, i + 32));
                lemma_add_zero(dst@, d + 4 * 32 + 4, cblk(inp@, i + 48));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Intra prediction
// ---------------------------------------------------------------------------

/// The requirement for predicting a `size`-square block at `d`: its top
/// row (with four bytes to the right for 4x4 blocks), left column and top
/// left corner are inside `b`.
pub open spec fn pred_ok(blen: nat, d: int, size: int) -> bool {
    d >= BPS + 1 && d + (size - 1) * BPS + size + 4 <= blen
}

/// Offset `o` is in the part of an `n`-wide block that a raster scan has
/// covered when it stands at row `y`, column `x`.
pub open spec fn scanned(o: int, n: int, y: int, x: int) -> bool {
    0 <= o && o % 32 < n && (o / 32 < y || (o / 32 == y && o % 32 < x))
}

/// The scratch buffer with the `n`-square block at `d` set to `v`.
pub open spec fn fill_sq(b: Seq<u8>, d: int, n: int, v: u8) -> Seq<u8> {
    Seq::new(b.len(), |j: int| if in_sq(j - d, n) { v } else { b[j] })
}

pub open spec fn sel4(i: int, v0: u8, v1: u8, v2: u8, v3: u8) -> u8 {
    if i == 0 { v0 } else if i == 1 { v1 } else if i == 2 { v2 } else { v3 }
}

pub open spec fn sel7(i: int, p0: u8, p1: u8, p2: u8, p3: u8, p4: u8, p5: u8, p6: u8) -> u8 {
    if i == 0 { p0 } else if i == 1 { p1 } else if i == 2 { p2 } else if i == 3 { p3 } else if i == 4 { p4 } else if i == 5 { p5 } else { p6 }
}

/// Row `r` of the subblock at `d` holds `p[k0..k0 + 4]`.
pub open spec fn row7(b: Seq<u8>, d: int, r: int, k0: int, p0: u8, p1: u8, p2: u8, p3: u8, p4: u8, p5: u8, p6: u8) -> bool {
    &&& b[d + 32 * r] == sel7(k0, p0, p1, p2, p3, p4, p5, p6)
    &&& b[d + 32 * r + 1] == sel7(k0 + 1, p0, p1, p2, p3, p4, p5, p6)
    &&& b[d + 32 * r + 2] == sel7(k0 + 2, p0, p1, p2, p3, p4, p5, p6)
    &&& b[d + 32 * r + 3] == sel7(k0 + 3, p0, p1, p2, p3, p4, p5, p6)
}

/// `in_sq(o, 4)` without division.
pub open spec fn in_sq4(o: int) -> bool {
    (0 <= o < 4) || (32 <= o < 36) || (64 <= o < 68) || (96 <= o < 100)
}

/// Row `r` of the subblock at `d` in `b1` is the prediction from `b0`.
pub open spec fn row_ok(b0: Seq<u8>, b1: Seq<u8>, d: int, mode: int, r: int) -> bool {
    let a = nb_above(b0, d, 8);
    let l = nb_left(b0, d, 4);
    &&& b1[d + 32 * r] == pred4_px(mode, a, l, r, 0) as u8
    &&& b1[d + 32 * r + 1] == pred4_px(mode, a, l, r, 1) as u8
    &&& b1[d + 32 * r + 2] == pred4_px(mode, a, l, r, 2) as u8
    &&& b1[d + 32 * r + 3] == pred4_px(mode, a, l, r, 3) as u8
}

pub proof fn lemma_paint4_cells(b0: Seq<u8>, b1: Seq<u8>, d: int, mode: int)
    requires
        b1.len() == b0.len(),
        forall|j: int| 0 <= j < b0.len() && !in_sq4(j - d) ==> #[trigger] b1[j] == b0[j],
        row_ok(b0, b1, d, mode, 0),
        row_ok(b0, b1, d, mode, 1),
        row_ok(b0, b1, d, mode, 2),
        row_ok(b0, b1, d, mode, 3),
    ensures
        b1 == paint4(b0, d, mode),
{
    hide(pred4_px);
    hide(nb_above);
    hide(nb_left);
    assert forall|j: int| 0 <= j < b0.len() implies b1[j] == #[trigger] paint4(b0, d, mode)[j] by {
        let o = j - d;
        assert(in_sq4(o) == in_sq(o, 4));
        if in_sq(o, 4) {
            let r = o / 32;
            let c = o % 32;
            assert(j == d + 32 * r + c);
            assert(0 <= r < 4 && 0 <= c < 4);
            if r == 0 {
                assert(row_ok(b0, b1, d, mode, 0));
            } else if r == 1 {
                assert(row_ok(b0, b1, d, mode, 1));
            } else if r == 2 {
                assert(row_ok(b0, b1, d, mode, 2));
            } else {
                assert(row_ok(b0, b1, d, mode, 3));
            }
        }
    }
    assert(b1 =~= paint4(b0, d, mode));
}

#[inline(always)]
fn avg3(a: u8, b: u8, c: u8) -> (r: u8)
    ensures
        r == spec_avg3(a as int, b as int, c as int),
{
    let s = a as u32 + 2 * b as u32 + c as u32 + 2;
    assert(s <= 1022 ==> (s >> 2u32) == s / 4 && (s >> 2u32) <= 255) by (bit_vector);
    (s >> 2u32) as u8
}

#[inline(always)]
fn avg2(a: u8, b: u8) -> (r: u8)
    ensures
        r == spec_avg2(a as int, b as int),
{
    let s = a as u32 + b as u32 + 1;
    assert(s <= 511 ==> (s >> 1u32) == s / 2 && (s >> 1u32) <= 255) by (bit_vector);
    (s >> 1u32) as u8
}

/// Fills a `size`-square block at `d` with `v`.
fn fill(b: &mut [u8], d: usize, size: usize, v: u8)
    requires
        size <= 16,
        d + (size - 1) * BPS + size <= old(b)@.len(),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == fill_sq(old(b)@, d as int, size as int, v),
{
    proof {assert(b@.len() == b.len());}
    let mut y: usize = 0;
    while y < size
        invariant
            b@.len() <= usize::MAX,
            y <= size <= 16,
            d + (size - 1) * BPS + size <= b@.len(),
            b@.len() == old(b)@.len(),
            forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, size as int, y as int, 0) { v } else { old(b)@[j] },
        decreases size - y,
    {
        let mut x: usize = 0;
        while x < size
            invariant
                b@.len() <= usize::MAX,
                x <= size,
                y < size <= 16,
                d + (size - 1) * BPS + size <= b@.len(),
                b@.len() == old(b)@.len(),
                forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, size as int, y as int, x as int) { v } else { old(b)@[j] },
            decreases size - x,
        {
            set(b, d + y * BPS + x, v);
            x = x + 1;
        }
        y = y + 1;
    }
    assert(b@ =~= fill_sq(old(b)@, d as int, size as int, v));
}

/// `TrueMotion`: `left + top - top_left`, clipped.
fn true_motion(b: &mut [u8], d: usize, size: usize)
    requires
        size <= 16,
        d >= BPS + 1,
        d + (size - 1) * BPS + size <= old(b)@.len(),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint_big(old(b)@, d as int, size as int, 1),
{
    proof {assert(b@.len() == b.len());}
    let tl = get(b, d - BPS - 1) as i32;
    let mut y: usize = 0;
    while y < size
        invariant
            b@.len() <= usize::MAX,
            y <= size <= 16,
            d >= BPS + 1,
            d + (size - 1) * BPS + size <= b@.len(),
            b@.len() == old(b)@.len(),
            tl == old(b)@[d - 33],
            forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, size as int, y as int, 0) { clip_to(old(b)@[d - 32 + (j - d) % 32] + old(b)@[d + 32 * ((j - d) / 32) - 1] - old(b)@[d - 33], 255) as u8 } else { old(b)@[j] },
        decreases size - y,
    {
        let l = get(b, d + y * BPS - 1) as i32;
        assert(!scanned(32 * y - 1, size as int, y as int, 0));
        let mut x: usize = 0;
        while x < size
            invariant
                b@.len() <= usize::MAX,
                x <= size,
                y < size <= 16,
                d >= BPS + 1,
                d + (size - 1) * BPS + size <= b@.len(),
                b@.len() == old(b)@.len(),
                tl == old(b)@[d - 33],
                l == old(b)@[d + 32 * y - 1],
                forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, size as int, y as int, x as int) { clip_to(old(b)@[d - 32 + (j - d) % 32] + old(b)@[d + 32 * ((j - d) / 32) - 1] - old(b)@[d - 33], 255) as u8 } else { old(b)@[j] },
            decreases size - x,
        {
            let t = get(b, d - BPS + x) as i32;
            assert(!scanned(x - 32, size as int, y as int, x as int));
            set(b, d + y * BPS + x, clip8(t + l - tl));
            x = x + 1;
        }
        y = y + 1;
    }
    assert(b@ =~= paint_big(old(b)@, d as int, size as int, 1));
}

/// Copies the row above into each row (`VE16`, `VE8uv`).
fn vertical(b: &mut [u8], d: usize, size: usize)
    requires
        size <= 16,
        d >= BPS,
        d + (size - 1) * BPS + size <= old(b)@.len(),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint_big(old(b)@, d as int, size as int, 2),
{
    proof {assert(b@.len() == b.len());}
    let mut y: usize = 0;
    while y < size
        invariant
            b@.len() <= usize::MAX,
            y <= size <= 16,
            d >= BPS,
            d + (size - 1) * BPS + size <= b@.len(),
            b@.len() == old(b)@.len(),
            forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, size as int, y as int, 0) { old(b)@[d - 32 + (j - d) % 32] } else { old(b)@[j] },
        decreases size - y,
    {
        let mut x: usize = 0;
        while x < size
            invariant
                b@.len() <= usize::MAX,
                x <= size,
                y < size <= 16,
                d >= BPS,
                d + (size - 1) * BPS + size <= b@.len(),
                b@.len() == old(b)@.len(),
                forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, size as int, y as int, x as int) { old(b)@[d - 32 + (j - d) % 32] } else { old(b)@[j] },
            decreases size - x,
        {
            let t = get(b, d - BPS + x);
            assert(!scanned(x - 32, size as int, y as int, x as int));
            set(b, d + y * BPS + x, t);
            x = x + 1;
        }
        y = y + 1;
    }
    assert(b@ =~= paint_big(old(b)@, d as int, size as int, 2));
}

/// Fills each row with its left neighbour (`HE16`, `HE8uv`).
fn horizontal(b: &mut [u8], d: usize, size: usize)
    requires
        size <= 16,
        d >= 1,
        d + (size - 1) * BPS + size <= old(b)@.len(),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint_big(old(b)@, d as int, size as int, 3),
{
    proof {assert(b@.len() == b.len());}
    let mut y: usize = 0;
    while y < size
        invariant
            b@.len() <= usize::MAX,
            y <= size <= 16,
            d >= 1,
            d + (size - 1) * BPS + size <= b@.len(),
            b@.len() == old(b)@.len(),
            forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, size as int, y as int, 0) { old(b)@[d + 32 * ((j - d) / 32) - 1] } else { old(b)@[j] },
        decreases size - y,
    {
        let l = get(b, d + y * BPS - 1);
        assert(!scanned(32 * y - 1, size as int, y as int, 0));
        let mut x: usize = 0;
        while x < size
            invariant
                b@.len() <= usize::MAX,
                x <= size,
                y < size <= 16,
                d >= 1,
                d + (size - 1) * BPS + size <= b@.len(),
                b@.len() == old(b)@.len(),
                l == old(b)@[d + 32 * y - 1],
                forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, size as int, y as int, x as int) { old(b)@[d + 32 * ((j - d) / 32) - 1] } else { old(b)@[j] },
            decreases size - x,
        {
            set(b, d + y * BPS + x, l);
            x = x + 1;
        }
        y = y + 1;
    }
    assert(b@ =~= paint_big(old(b)@, d as int, size as int, 3));
}

/// The sum of the `size` samples above the block.
fn sum_top(b: &[u8], d: usize, size: usize) -> (s: u32)
    requires
        size <= 16,
        d >= BPS,
        d - BPS + size <= b@.len(),
    ensures
        s <= 255 * size,
        s == sum_range(nb_above(b@, d as int, size as int), 1, size + 1),
{
    proof {assert(b@.len() == b.len());}
    let mut s: u32 = 0;
    let mut x: usize = 0;
    while x < size
        invariant
            b@.len() <= usize::MAX,
            x <= size <= 16,
            d >= BPS,
            d - BPS + size <= b@.len(),
            s <= 255 * x,
            s == sum_range(nb_above(b@, d as int, size as int), 1, x + 1),
        decreases size - x,
    {
        assert(nb_above(b@, d as int, size as int)[x + 1] == b@[d - 32 + x]);
        assert(sum_range(nb_above(b@, d as int, size as int), 1, x + 2) == sum_range(nb_above(b@, d as int, size as int), 1, x + 1) + b@[d - 32 + x]);
        s = s + get(b, d - BPS + x) as u32;
        x = x + 1;
    }
    s
}

/// The sum of the `size` samples left of the block.
fn sum_left(b: &[u8], d: usize, size: usize) -> (s: u32)
    requires
        size <= 16,
        d >= 1,
        d + (size - 1) * BPS <= b@.len(),
    ensures
        s <= 255 * size,
        s == sum_range(nb_left(b@, d as int, size as int), 0, size as int),
{
    proof {assert(b@.len() == b.len());}
    let mut s: u32 = 0;
    let mut y: usize = 0;
    while y < size
        invariant
            b@.len() <= usize::MAX,
            y <= size <= 16,
            d >= 1,
            d + (size - 1) * BPS <= b@.len(),
            s <= 255 * y,
            s == sum_range(nb_left(b@, d as int, size as int), 0, y as int),
        decreases size - y,
    {
        assert(nb_left(b@, d as int, size as int)[y as int] == b@[d + 32 * y - 1]);
        assert(sum_range(nb_left(b@, d as int, size as int), 0, y + 1) == sum_range(nb_left(b@, d as int, size as int), 0, y as int) + b@[d + 32 * y - 1]);
        s = s + get(b, d + y * BPS - 1) as u32;
        y = y + 1;
    }
    s
}

/// `VP8PredLuma16[mode]` (or `VP8PredChroma8` for `size == 8`): modes
/// 0 DC, 1 TM, 2 V, 3 H, 4 DC without top, 5 DC without left, 6 DC with
/// neither.
pub fn pred_block(b: &mut [u8], d: usize, size: usize, mode: u8)
    requires
        size == 8 || size == 16,
        mode < 7,
        d >= BPS + 1,
        d + (size - 1) * BPS + size <= old(b)@.len(),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint_big(old(b)@, d as int, size as int, mode as int),
{
    proof {assert(b@.len() == b.len());}
    let shift: u32 = if size == 16 {
        4
    } else {
        3
    };
    if mode == 0 {
        let s = sum_top(b, d, size) + sum_left(b, d, size);
        let t = s + size as u32;
        assert(t <= 8176 ==> (t >> 5u32) == t / 32 && (t >> 5u32) <= 255) by (bit_vector);
        assert(t <= 4088 ==> (t >> 4u32) == t / 16 && (t >> 4u32) <= 255) by (bit_vector);
        assert(size == 8 ==> t <= 4088);
        let v = (t >> (shift + 1)) as u8;
        assert(v == (s + size) / (2 * size)) by {
            if size == 16 {
                assert(2 * size == 32);
            } else {
                assert(2 * size == 16);
            }
        }
        fill(b, d, size, v);
    } else if mode == 1 {
        true_motion(b, d, size);
    } else if mode == 2 {
        vertical(b, d, size);
    } else if mode == 3 {
        horizontal(b, d, size);
    } else if mode == 4 {
        let s = sum_left(b, d, size);
        let t = s + (size / 2) as u32;
        assert(t <= 4088 ==> (t >> 4u32) == t / 16 && (t >> 3u32) == t / 8) by (bit_vector);
        let v = (t >> shift) as u8;
        assert(v == (s + size / 2) / (size as int));
        fill(b, d, size, v);
    } else if mode == 5 {
        let s = sum_top(b, d, size);
        let t = s + (size / 2) as u32;
        assert(t <= 4088 ==> (t >> 4u32) == t / 16 && (t >> 3u32) == t / 8) by (bit_vector);
        let v = (t >> shift) as u8;
        assert(v == (s + size / 2) / (size as int));
        fill(b, d, size, v);
    } else {
        fill(b, d, size, 0x80);
    }
    assert(b@ =~= paint_big(old(b)@, d as int, size as int, mode as int));
}

/// `sum_top` and `sum_left` for a 4x4 block, written out: as loops with
/// the size a parameter they are vectorized into a wide masked load, which
/// stalls on the bytes the previous block has just stored.
#[inline(always)]
pub fn sum4(b: &[u8], d: usize) -> (s: u32)
    requires
        d >= BPS,
        d - BPS + 4 <= b@.len(),
        d + 3 * BPS <= b@.len(),
    ensures
        s <= 255 * 8,
        s == sum_range(nb_above(b@, d as int, 4), 1, 5) + sum_range(nb_left(b@, d as int, 4), 0, 4),
{
    proof {
        assert(b@.len() == b.len());
        reveal_with_fuel(sum_range, 6);
    }
    let top = d - BPS;
    get(b, top) as u32 + get(b, top + 1) as u32 + get(b, top + 2) as u32 + get(b, top + 3) as u32 + get(b, d - 1) as u32
        + get(b, d + BPS - 1) as u32 + get(b, d + 2 * BPS - 1) as u32 + get(b, d + 3 * BPS - 1) as u32
}

/// `VP8PredLuma4[mode]`: the ten 4x4 modes (DC, TM, VE, HE, RD, VR, LD,
/// VL, HD, HU).
pub fn pred4(b: &mut [u8], d: usize, mode: u8)
    requires
        mode < 10,
        pred_ok(old(b)@.len(), d as int, 4),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint4(old(b)@, d as int, mode as int),
{
    proof {assert(b@.len() == b.len());}
    match mode {
    0 => {
        let s = sum4(b, d);
        proof {
            lemma_sum_range_eq(nb_above(b@, d as int, 4), nb_above(b@, d as int, 8), 1, 5);
        }
        let t = s + 4;
        assert(t <= 2044 ==> (t >> 3u32) == t / 8) by (bit_vector);
        fill(b, d, 4, (t >> 3u32) as u8);
    }
    1 => {
        true_motion(b, d, 4);
    }
    2 => {
        pred4_ve(b, d);
    }
    3 => {
        pred4_he(b, d);
    }
    4 => {
        pred4_rd(b, d);
    }
    5 => {
        pred4_vr(b, d);
    }
    6 => {
        pred4_ld(b, d);
    }
    7 => {
        pred4_vl(b, d);
    }
    8 => {
        pred4_hd(b, d);
    }
    _ => {
        pred4_hu(b, d);
    }
    }
    assert(b@ =~= paint4(old(b)@, d as int, mode as int));
}

proof fn lemma_pred4_vr(a: Seq<int>, l: Seq<int>)
    ensures
        pred4_px(5, a, l, 0, 0) == spec_avg2(a[0], a[1]),
        pred4_px(5, a, l, 0, 1) == spec_avg2(a[1], a[2]),
        pred4_px(5, a, l, 0, 2) == spec_avg2(a[2], a[3]),
        pred4_px(5, a, l, 0, 3) == spec_avg2(a[3], a[4]),
        pred4_px(5, a, l, 1, 0) == spec_avg3(l[0], a[0], a[1]),
        pred4_px(5, a, l, 1, 1) == spec_avg3(a[0], a[1], a[2]),
        pred4_px(5, a, l, 1, 2) == spec_avg3(a[1], a[2], a[3]),
        pred4_px(5, a, l, 1, 3) == spec_avg3(a[2], a[3], a[4]),
        pred4_px(5, a, l, 2, 0) == spec_avg3(l[1], l[0], a[0]),
        pred4_px(5, a, l, 2, 1) == spec_avg2(a[0], a[1]),
        pred4_px(5, a, l, 2, 2) == spec_avg2(a[1], a[2]),
        pred4_px(5, a, l, 2, 3) == spec_avg2(a[2], a[3]),
        pred4_px(5, a, l, 3, 0) == spec_avg3(l[2], l[1], l[0]),
        pred4_px(5, a, l, 3, 1) == spec_avg3(l[0], a[0], a[1]),
        pred4_px(5, a, l, 3, 2) == spec_avg3(a[0], a[1], a[2]),
        pred4_px(5, a, l, 3, 3) == spec_avg3(a[1], a[2], a[3]),
{
}

proof fn lemma_pred4_vl(a: Seq<int>, l: Seq<int>)
    ensures
        pred4_px(7, a, l, 0, 0) == spec_avg2(a[1], a[2]),
        pred4_px(7, a, l, 0, 1) == spec_avg2(a[2], a[3]),
        pred4_px(7, a, l, 0, 2) == spec_avg2(a[3], a[4]),
        pred4_px(7, a, l, 0, 3) == spec_avg2(a[4], a[5]),
        pred4_px(7, a, l, 1, 0) == spec_avg3(a[1], a[2], a[3]),
        pred4_px(7, a, l, 1, 1) == spec_avg3(a[2], a[3], a[4]),
        pred4_px(7, a, l, 1, 2) == spec_avg3(a[3], a[4], a[5]),
        pred4_px(7, a, l, 1, 3) == spec_avg3(a[4], a[5], a[6]),
        pred4_px(7, a, l, 2, 0) == spec_avg2(a[2], a[3]),
        pred4_px(7, a, l, 2, 1) == spec_avg2(a[3], a[4]),
        pred4_px(7, a, l, 2, 2) == spec_avg2(a[4], a[5]),
        pred4_px(7, a, l, 2, 3) == spec_avg3(a[5], a[6], a[7]),
        pred4_px(7, a, l, 3, 0) == spec_avg3(a[2], a[3], a[4]),
        pred4_px(7, a, l, 3, 1) == spec_avg3(a[3], a[4], a[5]),
        pred4_px(7, a, l, 3, 2) == spec_avg3(a[4], a[5], a[6]),
        pred4_px(7, a, l, 3, 3) == spec_avg3(a[6], a[7], a[8]),
{
}

proof fn lemma_pred4_hd(a: Seq<int>, l: Seq<int>)
    ensures
        pred4_px(8, a, l, 0, 0) == spec_avg2(l[0], a[0]),
        pred4_px(8, a, l, 0, 1) == spec_avg3(l[0], a[0], a[1]),
        pred4_px(8, a, l, 0, 2) == spec_avg3(a[0], a[1], a[2]),
        pred4_px(8, a, l, 0, 3) == spec_avg3(a[1], a[2], a[3]),
        pred4_px(8, a, l, 1, 0) == spec_avg2(l[1], l[0]),
        pred4_px(8, a, l, 1, 1) == spec_avg3(l[1], l[0], a[0]),
        pred4_px(8, a, l, 1, 2) == spec_avg2(l[0], a[0]),
        pred4_px(8, a, l, 1, 3) == spec_avg3(l[0], a[0], a[1]),
        pred4_px(8, a, l, 2, 0) == spec_avg2(l[2], l[1]),
        pred4_px(8, a, l, 2, 1) == spec_avg3(l[2], l[1], l[0]),
        pred4_px(8, a, l, 2, 2) == spec_avg2(l[1], l[0]),
        pred4_px(8, a, l, 2, 3) == spec_avg3(l[1], l[0], a[0]),
        pred4_px(8, a, l, 3, 0) == spec_avg2(l[3], l[2]),
        pred4_px(8, a, l, 3, 1) == spec_avg3(l[3], l[2], l[1]),
        pred4_px(8, a, l, 3, 2) == spec_avg2(l[2], l[1]),
        pred4_px(8, a, l, 3, 3) == spec_avg3(l[2], l[1], l[0]),
{
}

proof fn lemma_pred4_hu(a: Seq<int>, l: Seq<int>)
    ensures
        pred4_px(9, a, l, 0, 0) == spec_avg2(l[0], l[1]),
        pred4_px(9, a, l, 0, 1) == spec_avg3(l[0], l[1], l[2]),
        pred4_px(9, a, l, 0, 2) == spec_avg2(l[1], l[2]),
        pred4_px(9, a, l, 0, 3) == spec_avg3(l[1], l[2], l[3]),
        pred4_px(9, a, l, 1, 0) == spec_avg2(l[1], l[2]),
        pred4_px(9, a, l, 1, 1) == spec_avg3(l[1], l[2], l[3]),
        pred4_px(9, a, l, 1, 2) == spec_avg2(l[2], l[3]),
        pred4_px(9, a, l, 1, 3) == spec_avg3(l[2], l[3], l[3]),
        pred4_px(9, a, l, 2, 0) == spec_avg2(l[2], l[3]),
        pred4_px(9, a, l, 2, 1) == spec_avg3(l[2], l[3], l[3]),
        pred4_px(9, a, l, 2, 2) == l[3],
        pred4_px(9, a, l, 2, 3) == l[3],
        pred4_px(9, a, l, 3, 0) == l[3],
        pred4_px(9, a, l, 3, 1) == l[3],
        pred4_px(9, a, l, 3, 2) == l[3],
        pred4_px(9, a, l, 3, 3) == l[3],
{
}

#[inline(always)]
fn pred4_ve(b: &mut [u8], d: usize)
    requires
        pred_ok(old(b)@.len(), d as int, 4),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint4(old(b)@, d as int, 2),
{
    proof {assert(b@.len() == b.len());}
    let top = d - BPS;
    let v0 = avg3(get(b, top - 1), get(b, top), get(b, top + 1));
    let v1 = avg3(get(b, top), get(b, top + 1), get(b, top + 2));
    let v2 = avg3(get(b, top + 1), get(b, top + 2), get(b, top + 3));
    let v3 = avg3(get(b, top + 2), get(b, top + 3), get(b, top + 4));
    let mut y: usize = 0;
    while y < 4
        invariant
            b@.len() <= usize::MAX,
            y <= 4,
            pred_ok(b@.len(), d as int, 4),
            b@.len() == old(b)@.len(),
            forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, 4, y as int, 0) { sel4((j - d) % 32, v0, v1, v2, v3) } else { old(b)@[j] },
        decreases 4 - y,
    {
        set(b, d + y * BPS, v0);
        set(b, d + y * BPS + 1, v1);
        set(b, d + y * BPS + 2, v2);
        set(b, d + y * BPS + 3, v3);
        y = y + 1;
    }
    proof {
        assert(row_ok(old(b)@, b@, d as int, 2, 0));
        assert(row_ok(old(b)@, b@, d as int, 2, 1));
        assert(row_ok(old(b)@, b@, d as int, 2, 2));
        assert(row_ok(old(b)@, b@, d as int, 2, 3));
        lemma_paint4_cells(old(b)@, b@, d as int, 2);
    }
}

#[inline(always)]
fn pred4_he(b: &mut [u8], d: usize)
    requires
        pred_ok(old(b)@.len(), d as int, 4),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint4(old(b)@, d as int, 3),
{
    proof {assert(b@.len() == b.len());}
    let top = d - BPS;
    let a = get(b, d - 1 - BPS);
    let bb = get(b, d - 1);
    let c = get(b, d - 1 + BPS);
    let dd = get(b, d - 1 + 2 * BPS);
    let e = get(b, d - 1 + 3 * BPS);
    let r0 = avg3(a, bb, c);
    let r1 = avg3(bb, c, dd);
    let r2 = avg3(c, dd, e);
    let r3 = avg3(dd, e, e);
    let mut x: usize = 0;
    while x < 4
        invariant
            b@.len() <= usize::MAX,
            x <= 4,
            pred_ok(b@.len(), d as int, 4),
            b@.len() == old(b)@.len(),
            forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if in_sq(j - d, 4) && (j - d) % 32 < x { sel4((j - d) / 32, r0, r1, r2, r3) } else { old(b)@[j] },
        decreases 4 - x,
    {
        set(b, d + x, r0);
        set(b, d + BPS + x, r1);
        set(b, d + 2 * BPS + x, r2);
        set(b, d + 3 * BPS + x, r3);
        x = x + 1;
    }
    proof {
        assert(row_ok(old(b)@, b@, d as int, 3, 0));
        assert(row_ok(old(b)@, b@, d as int, 3, 1));
        assert(row_ok(old(b)@, b@, d as int, 3, 2));
        assert(row_ok(old(b)@, b@, d as int, 3, 3));
        lemma_paint4_cells(old(b)@, b@, d as int, 3);
    }
}

#[inline(always)]
fn pred4_rd(b: &mut [u8], d: usize)
    requires
        pred_ok(old(b)@.len(), d as int, 4),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint4(old(b)@, d as int, 4),
{
    proof {assert(b@.len() == b.len());}
    let top = d - BPS;
    // RD4
    let i = get(b, d - 1);
    let j = get(b, d - 1 + BPS);
    let k = get(b, d - 1 + 2 * BPS);
    let l = get(b, d - 1 + 3 * BPS);
    let x = get(b, top - 1);
    let a = get(b, top);
    let bb = get(b, top + 1);
    let c = get(b, top + 2);
    let dd = get(b, top + 3);
    let p0 = avg3(j, k, l);
    let p1 = avg3(i, j, k);
    let p2 = avg3(x, i, j);
    let p3 = avg3(a, x, i);
    let p4 = avg3(bb, a, x);
    let p5 = avg3(c, bb, a);
    let p6 = avg3(dd, c, bb);
    // DST(x, y) = p[3 - y + x]
    put4x4_diag(b, d, p0, p1, p2, p3, p4, p5, p6);
    proof {
        assert(row_ok(old(b)@, b@, d as int, 4, 0));
        assert(row_ok(old(b)@, b@, d as int, 4, 1));
        assert(row_ok(old(b)@, b@, d as int, 4, 2));
        assert(row_ok(old(b)@, b@, d as int, 4, 3));
        lemma_paint4_cells(old(b)@, b@, d as int, 4);
    }
}

#[inline(always)]
#[verifier::rlimit(30)]
fn pred4_vr(b: &mut [u8], d: usize)
    requires
        pred_ok(old(b)@.len(), d as int, 4),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint4(old(b)@, d as int, 5),
{
    hide(pred4_px);
    proof {assert(b@.len() == b.len());}
    let top = d - BPS;
    // VR4
    let i = get(b, d - 1);
    let j = get(b, d - 1 + BPS);
    let k = get(b, d - 1 + 2 * BPS);
    let x = get(b, top - 1);
    let a = get(b, top);
    let bb = get(b, top + 1);
    let c = get(b, top + 2);
    let dd = get(b, top + 3);
    set(b, d, avg2(x, a));
    set(b, d + 1 + 2 * BPS, avg2(x, a));
    set(b, d + 1, avg2(a, bb));
    set(b, d + 2 + 2 * BPS, avg2(a, bb));
    set(b, d + 2, avg2(bb, c));
    set(b, d + 3 + 2 * BPS, avg2(bb, c));
    set(b, d + 3, avg2(c, dd));
    set(b, d + 3 * BPS, avg3(k, j, i));
    set(b, d + 2 * BPS, avg3(j, i, x));
    set(b, d + BPS, avg3(i, x, a));
    set(b, d + 1 + 3 * BPS, avg3(i, x, a));
    set(b, d + 1 + BPS, avg3(x, a, bb));
    set(b, d + 2 + 3 * BPS, avg3(x, a, bb));
    set(b, d + 2 + BPS, avg3(a, bb, c));
    set(b, d + 3 + 3 * BPS, avg3(a, bb, c));
    set(b, d + 3 + BPS, avg3(bb, c, dd));
    proof {
        lemma_pred4_vr(nb_above(old(b)@, d as int, 8), nb_left(old(b)@, d as int, 4));
        assert(row_ok(old(b)@, b@, d as int, 5, 0));
        assert(row_ok(old(b)@, b@, d as int, 5, 1));
        assert(row_ok(old(b)@, b@, d as int, 5, 2));
        assert(row_ok(old(b)@, b@, d as int, 5, 3));
        lemma_paint4_cells(old(b)@, b@, d as int, 5);
    }
}

#[inline(always)]
fn pred4_ld(b: &mut [u8], d: usize)
    requires
        pred_ok(old(b)@.len(), d as int, 4),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint4(old(b)@, d as int, 6),
{
    proof {assert(b@.len() == b.len());}
    let top = d - BPS;
    // LD4
    let a = get(b, top);
    let bb = get(b, top + 1);
    let c = get(b, top + 2);
    let dd = get(b, top + 3);
    let e = get(b, top + 4);
    let f = get(b, top + 5);
    let g = get(b, top + 6);
    let h = get(b, top + 7);
    let p0 = avg3(a, bb, c);
    let p1 = avg3(bb, c, dd);
    let p2 = avg3(c, dd, e);
    let p3 = avg3(dd, e, f);
    let p4 = avg3(e, f, g);
    let p5 = avg3(f, g, h);
    let p6 = avg3(g, h, h);
    // DST(x, y) = p[x + y]
    put4x4_anti(b, d, p0, p1, p2, p3, p4, p5, p6);
    proof {
        assert(row_ok(old(b)@, b@, d as int, 6, 0));
        assert(row_ok(old(b)@, b@, d as int, 6, 1));
        assert(row_ok(old(b)@, b@, d as int, 6, 2));
        assert(row_ok(old(b)@, b@, d as int, 6, 3));
        lemma_paint4_cells(old(b)@, b@, d as int, 6);
    }
}

#[inline(always)]
fn pred4_vl(b: &mut [u8], d: usize)
    requires
        pred_ok(old(b)@.len(), d as int, 4),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint4(old(b)@, d as int, 7),
{
    hide(pred4_px);
    proof {assert(b@.len() == b.len());}
    let top = d - BPS;
    // VL4
    let a = get(b, top);
    let bb = get(b, top + 1);
    let c = get(b, top + 2);
    let dd = get(b, top + 3);
    let e = get(b, top + 4);
    let f = get(b, top + 5);
    let g = get(b, top + 6);
    let h = get(b, top + 7);
    set(b, d, avg2(a, bb));
    set(b, d + 1, avg2(bb, c));
    set(b, d + 2 * BPS, avg2(bb, c));
    set(b, d + 2, avg2(c, dd));
    set(b, d + 1 + 2 * BPS, avg2(c, dd));
    set(b, d + 3, avg2(dd, e));
    set(b, d + 2 + 2 * BPS, avg2(dd, e));
    set(b, d + BPS, avg3(a, bb, c));
    set(b, d + 1 + BPS, avg3(bb, c, dd));
    set(b, d + 3 * BPS, avg3(bb, c, dd));
    set(b, d + 2 + BPS, avg3(c, dd, e));
    set(b, d + 1 + 3 * BPS, avg3(c, dd, e));
    set(b, d + 3 + BPS, avg3(dd, e, f));
    set(b, d + 2 + 3 * BPS, avg3(dd, e, f));
    set(b, d + 3 + 2 * BPS, avg3(e, f, g));
    set(b, d + 3 + 3 * BPS, avg3(f, g, h));
    proof {
        lemma_pred4_vl(nb_above(old(b)@, d as int, 8), nb_left(old(b)@, d as int, 4));
        assert(row_ok(old(b)@, b@, d as int, 7, 0));
        assert(row_ok(old(b)@, b@, d as int, 7, 1));
        assert(row_ok(old(b)@, b@, d as int, 7, 2));
        assert(row_ok(old(b)@, b@, d as int, 7, 3));
        lemma_paint4_cells(old(b)@, b@, d as int, 7);
    }
}

#[inline(always)]
fn pred4_hd(b: &mut [u8], d: usize)
    requires
        pred_ok(old(b)@.len(), d as int, 4),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint4(old(b)@, d as int, 8),
{
    hide(pred4_px);
    proof {assert(b@.len() == b.len());}
    let top = d - BPS;
    // HD4
    let i = get(b, d - 1);
    let j = get(b, d - 1 + BPS);
    let k = get(b, d - 1 + 2 * BPS);
    let l = get(b, d - 1 + 3 * BPS);
    let x = get(b, top - 1);
    let a = get(b, top);
    let bb = get(b, top + 1);
    let c = get(b, top + 2);
    set(b, d, avg2(i, x));
    set(b, d + 2 + BPS, avg2(i, x));
    set(b, d + BPS, avg2(j, i));
    set(b, d + 2 + 2 * BPS, avg2(j, i));
    set(b, d + 2 * BPS, avg2(k, j));
    set(b, d + 2 + 3 * BPS, avg2(k, j));
    set(b, d + 3 * BPS, avg2(l, k));
    set(b, d + 3, avg3(a, bb, c));
    set(b, d + 2, avg3(x, a, bb));
    set(b, d + 1, avg3(i, x, a));
    set(b, d + 3 + BPS, avg3(i, x, a));
    set(b, d + 1 + BPS, avg3(j, i, x));
    set(b, d + 3 + 2 * BPS, avg3(j, i, x));
    set(b, d + 1 + 2 * BPS, avg3(k, j, i));
    set(b, d + 3 + 3 * BPS, avg3(k, j, i));
    set(b, d + 1 + 3 * BPS, avg3(l, k, j));
    proof {
        lemma_pred4_hd(nb_above(old(b)@, d as int, 8), nb_left(old(b)@, d as int, 4));
        assert(row_ok(old(b)@, b@, d as int, 8, 0));
        assert(row_ok(old(b)@, b@, d as int, 8, 1));
        assert(row_ok(old(b)@, b@, d as int, 8, 2));
        assert(row_ok(old(b)@, b@, d as int, 8, 3));
        lemma_paint4_cells(old(b)@, b@, d as int, 8);
    }
}

#[inline(always)]
fn pred4_hu(b: &mut [u8], d: usize)
    requires
        pred_ok(old(b)@.len(), d as int, 4),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint4(old(b)@, d as int, 9),
{
    hide(pred4_px);
    proof {assert(b@.len() == b.len());}
    let top = d - BPS;
    // HU4
    let i = get(b, d - 1);
    let j = get(b, d - 1 + BPS);
    let k = get(b, d - 1 + 2 * BPS);
    let l = get(b, d - 1 + 3 * BPS);
    set(b, d, avg2(i, j));
    set(b, d + 2, avg2(j, k));
    set(b, d + BPS, avg2(j, k));
    set(b, d + 2 + BPS, avg2(k, l));
    set(b, d + 2 * BPS, avg2(k, l));
    set(b, d + 1, avg3(i, j, k));
    set(b, d + 3, avg3(j, k, l));
    set(b, d + 1 + BPS, avg3(j, k, l));
    set(b, d + 3 + BPS, avg3(k, l, l));
    set(b, d + 1 + 2 * BPS, avg3(k, l, l));
    set(b, d + 3 + 2 * BPS, l);
    set(b, d + 2 + 2 * BPS, l);
    set(b, d + 3 * BPS, l);
    set(b, d + 1 + 3 * BPS, l);
    set(b, d + 2 + 3 * BPS, l);
    set(b, d + 3 + 3 * BPS, l);
    proof {
        lemma_pred4_hu(nb_above(old(b)@, d as int, 8), nb_left(old(b)@, d as int, 4));
        assert(row_ok(old(b)@, b@, d as int, 9, 0));
        assert(row_ok(old(b)@, b@, d as int, 9, 1));
        assert(row_ok(old(b)@, b@, d as int, 9, 2));
        assert(row_ok(old(b)@, b@, d as int, 9, 3));
        lemma_paint4_cells(old(b)@, b@, d as int, 9);
    }
}

/// `DST(x, y) = p[3 - y + x]`.
fn put4x4_diag(b: &mut [u8], d: usize, p0: u8, p1: u8, p2: u8, p3: u8, p4: u8, p5: u8, p6: u8)
    requires
        d + 3 * BPS + 4 <= old(b)@.len(),
    ensures
        final(b)@.len() == old(b)@.len(),
        forall|j: int| 0 <= j < old(b)@.len() && !in_sq4(j - d) ==> #[trigger] final(b)@[j] == old(b)@[j],
        row7(final(b)@, d as int, 0, 3 - 0, p0, p1, p2, p3, p4, p5, p6),
        row7(final(b)@, d as int, 1, 3 - 1, p0, p1, p2, p3, p4, p5, p6),
        row7(final(b)@, d as int, 2, 3 - 2, p0, p1, p2, p3, p4, p5, p6),
        row7(final(b)@, d as int, 3, 3 - 3, p0, p1, p2, p3, p4, p5, p6),
{
    proof {assert(b@.len() == b.len());}
    let p: [u8; 7] = [p0, p1, p2, p3, p4, p5, p6];
    let mut y: usize = 0;
    while y < 4
        invariant
            b@.len() <= usize::MAX,
            y <= 4,
            d + 3 * BPS + 4 <= b@.len(),
            b@.len() == old(b)@.len(),
            forall|i: int| 0 <= i < 7 ==> #[trigger] p@[i] == sel7(i, p0, p1, p2, p3, p4, p5, p6),
            forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, 4, y as int, 0) { sel7(3 - (j - d) / 32 + (j - d) % 32, p0, p1, p2, p3, p4, p5, p6) } else { old(b)@[j] },
        decreases 4 - y,
    {
        let mut x: usize = 0;
        while x < 4
            invariant
                b@.len() <= usize::MAX,
                x <= 4,
                y < 4,
                d + 3 * BPS + 4 <= b@.len(),
                b@.len() == old(b)@.len(),
                forall|i: int| 0 <= i < 7 ==> #[trigger] p@[i] == sel7(i, p0, p1, p2, p3, p4, p5, p6),
                forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, 4, y as int, x as int) { sel7(3 - (j - d) / 32 + (j - d) % 32, p0, p1, p2, p3, p4, p5, p6) } else { old(b)@[j] },
            decreases 4 - x,
        {
            set(b, d + y * BPS + x, p[3 - y + x]);
            x = x + 1;
        }
        y = y + 1;
    }
    proof {
        assert(row7(b@, d as int, 0, 3 - 0, p0, p1, p2, p3, p4, p5, p6));
        assert(row7(b@, d as int, 1, 3 - 1, p0, p1, p2, p3, p4, p5, p6));
        assert(row7(b@, d as int, 2, 3 - 2, p0, p1, p2, p3, p4, p5, p6));
        assert(row7(b@, d as int, 3, 3 - 3, p0, p1, p2, p3, p4, p5, p6));
    }
}

/// `DST(x, y) = p[x + y]`.
fn put4x4_anti(b: &mut [u8], d: usize, p0: u8, p1: u8, p2: u8, p3: u8, p4: u8, p5: u8, p6: u8)
    requires
        d + 3 * BPS + 4 <= old(b)@.len(),
    ensures
        final(b)@.len() == old(b)@.len(),
        forall|j: int| 0 <= j < old(b)@.len() && !in_sq4(j - d) ==> #[trigger] final(b)@[j] == old(b)@[j],
        row7(final(b)@, d as int, 0, 0, p0, p1, p2, p3, p4, p5, p6),
        row7(final(b)@, d as int, 1, 1, p0, p1, p2, p3, p4, p5, p6),
        row7(final(b)@, d as int, 2, 2, p0, p1, p2, p3, p4, p5, p6),
        row7(final(b)@, d as int, 3, 3, p0, p1, p2, p3, p4, p5, p6),
{
    proof {assert(b@.len() == b.len());}
    let p: [u8; 7] = [p0, p1, p2, p3, p4, p5, p6];
    let mut y: usize = 0;
    while y < 4
        invariant
            b@.len() <= usize::MAX,
            y <= 4,
            d + 3 * BPS + 4 <= b@.len(),
            b@.len() == old(b)@.len(),
            forall|i: int| 0 <= i < 7 ==> #[trigger] p@[i] == sel7(i, p0, p1, p2, p3, p4, p5, p6),
            forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, 4, y as int, 0) { sel7((j - d) / 32 + (j - d) % 32, p0, p1, p2, p3, p4, p5, p6) } else { old(b)@[j] },
        decreases 4 - y,
    {
        let mut x: usize = 0;
        while x < 4
            invariant
                b@.len() <= usize::MAX,
                x <= 4,
                y < 4,
                d + 3 * BPS + 4 <= b@.len(),
                b@.len() == old(b)@.len(),
                forall|i: int| 0 <= i < 7 ==> #[trigger] p@[i] == sel7(i, p0, p1, p2, p3, p4, p5, p6),
                forall|j: int| 0 <= j < b@.len() ==> #[trigger] b@[j] == if scanned(j - d, 4, y as int, x as int) { sel7((j - d) / 32 + (j - d) % 32, p0, p1, p2, p3, p4, p5, p6) } else { old(b)@[j] },
            decreases 4 - x,
        {
            set(b, d + y * BPS + x, p[x + y]);
            x = x + 1;
        }
        y = y + 1;
    }
    proof {
        assert(row7(b@, d as int, 0, 0, p0, p1, p2, p3, p4, p5, p6));
        assert(row7(b@, d as int, 1, 1, p0, p1, p2, p3, p4, p5, p6));
        assert(row7(b@, d as int, 2, 2, p0, p1, p2, p3, p4, p5, p6));
        assert(row7(b@, d as int, 3, 3, p0, p1, p2, p3, p4, p5, p6));
    }
}

// ---------------------------------------------------------------------------
// Loop filter
// ---------------------------------------------------------------------------

/// `x >> k` for small `x`, with its bounds.
#[inline(always)]
fn sar(x: i32, k: u32) -> (r: i32)
    requires
        -0x1_0000 <= x <= 0x1_0000,
        1 <= k <= 7,
    ensures
        -0x1_0000 <= r <= 0x1_0000,
        k == 1 && -15 <= x <= 16 ==> -8 <= r <= 8,
        k == 7 && -27 * 128 + 63 <= x <= 27 * 127 + 63 ==> -27 <= r <= 27,
        k == 1 ==> r as int == (x as int) / 2,
        k == 3 ==> r as int == (x as int) / 8,
        k == 7 ==> r as int == (x as int) / 128,
{
    proof {
        let q = x >> k;
        assert(-0x1_0000 <= x <= 0x1_0000 && k == 1 && q == x >> k ==> -0x1_0000 <= q <= 0x1_0000 && mul(q, 2) <= x
            && x <= add(mul(q, 2), 1)) by (bit_vector);
        assert(-0x1_0000 <= x <= 0x1_0000 && k == 3 && q == x >> k ==> -0x1_0000 <= q <= 0x1_0000 && mul(q, 8) <= x
            && x <= add(mul(q, 8), 7)) by (bit_vector);
        assert(-0x1_0000 <= x <= 0x1_0000 && k == 7 && q == x >> k ==> -0x1_0000 <= q <= 0x1_0000 && mul(q, 128)
            <= x && x <= add(mul(q, 128), 127)) by (bit_vector);
        assert(-0x1_0000 <= x <= 0x1_0000 && 1 <= k <= 7 ==> -0x1_0000 <= (x >> k) <= 0x1_0000) by (bit_vector);
        assert(k == 1 && -15 <= x <= 16 ==> -8 <= (x >> k) <= 8) by (bit_vector);
        assert(k == 7 && -27 * 128 + 63 <= x <= 27 * 127 + 63 ==> -27 <= (x >> k) <= 27) by (bit_vector);
    }
    x >> k
}

/// `VP8ksclip1`: clamps to `[-128, 127]`.
#[inline(always)]
fn sclip1(v: i32) -> (r: i32)
    ensures
        -128 <= r <= 127,
        r as int == lf_c(v as int),
{
    if v < -128 {
        -128
    } else if v > 127 {
        127
    } else {
        v
    }
}

/// `VP8ksclip2`: clamps to `[-16, 15]`.
#[inline(always)]
fn sclip2(v: i32) -> (r: i32)
    ensures
        -16 <= r <= 15,
        r as int == (if v < -16 { -16 } else if v > 15 { 15 } else { v as int }),
{
    if v < -16 {
        -16
    } else if v > 15 {
        15
    } else {
        v
    }
}

#[inline(always)]
fn abs0(v: i32) -> (r: i32)
    requires
        -0x1_0000 <= v <= 0x1_0000,
    ensures
        r >= 0,
        r == v || r == -v,
        r as int == lf_abs(v as int),
{
    if v < 0 {
        -v
    } else {
        v
    }
}

/// The inner-edge filter where the variance is low (`subblock_filter`'s
/// second branch).
pub open spec fn lf_inner4(x: Edge8) -> Edge8 {
    let a = (lf_a(false, x) + 1) / 2;
    Edge8 { p1: lf_adj(x.p1, a), q1: lf_adj(x.q1, -a), ..lf_common(false, x) }
}

/// The macroblock-edge filter where the variance is low (`MBfilter`'s
/// first branch).
pub open spec fn lf_mb6(x: Edge8) -> Edge8 {
    let w = lf_w(true, x);
    let a0 = lf_c((27 * w + 63) / 128);
    let a1 = lf_c((18 * w + 63) / 128);
    let a2 = lf_c((9 * w + 63) / 128);
    Edge8 {
        p3: x.p3,
        p2: lf_adj(x.p2, a2),
        p1: lf_adj(x.p1, a1),
        p0: lf_adj(x.p0, a0),
        q0: lf_adj(x.q0, -a0),
        q1: lf_adj(x.q1, -a1),
        q2: lf_adj(x.q2, -a2),
        q3: x.q3,
    }
}

/// Eight pixels.
pub open spec fn px8(x: Edge8) -> bool {
    &&& 0 <= x.p3 <= 255
    &&& 0 <= x.p2 <= 255
    &&& 0 <= x.p1 <= 255
    &&& 0 <= x.p0 <= 255
    &&& 0 <= x.q0 <= 255
    &&& 0 <= x.q1 <= 255
    &&& 0 <= x.q2 <= 255
    &&& 0 <= x.q3 <= 255
}

/// libwebp's `DoFilter2_C`/`DoFilter4_C` arithmetic (the sum unclamped, and
/// the shifted values clamped to `[-16, 15]`) is `common_adjust`'s.
proof fn lemma_lf_common(outer: bool, x: Edge8)
    requires
        px8(x),
    ensures
        ({
            let a = 3 * (x.q0 - x.p0) + (if outer { lf_c(x.p1 - x.q1) } else { 0 });
            let a1 = (a + 4) / 8;
            let a2 = (a + 3) / 8;
            &&& lf_a(outer, x) == (if a1 < -16 { -16 } else if a1 > 15 { 15 } else { a1 })
            &&& lf_b(outer, x) == (if a2 < -16 { -16 } else if a2 > 15 { 15 } else { a2 })
        }),
{
}

/// The requirement for filtering across the edge at `p` with `step`: the
/// four pixels on each side are inside `b`.
pub open spec fn edge_ok(blen: nat, p: int, step: int) -> bool {
    1 <= step && p >= 4 * step && p + 3 * step < blen
}

/// `DoFilter2_C`: adjusts the two pixels next to the edge.
#[inline(always)]
fn do_filter2(b: &mut [u8], p: usize, step: usize)
    requires
        edge_ok(old(b)@.len(), p as int, step as int),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == lf_put(old(b)@, p as int, step as int, lf_common(true, lf_lane(old(b)@, p as int, step as int))),
{
    proof {assert(b@.len() == b.len());}
    let ghost x = lf_lane(b@, p as int, step as int);
    proof {
        lemma_lf_common(true, x);
    }
    let p1 = get(b, p - 2 * step) as i32;
    let p0 = get(b, p - step) as i32;
    let q0 = get(b, p) as i32;
    let q1 = get(b, p + step) as i32;
    let a = 3 * (q0 - p0) + sclip1(p1 - q1);
    let a1 = sclip2(sar(a + 4, 3));
    let a2 = sclip2(sar(a + 3, 3));
    set(b, p - step, clip8(p0 + a2));
    set(b, p, clip8(q0 - a1));
    proof {
        assert(b@ =~= lf_put(old(b)@, p as int, step as int, lf_common(true, x)));
    }
}

/// `DoFilter4_C`: the inner-edge filter, adjusting two pixels on each side.
#[inline(always)]
fn do_filter4(b: &mut [u8], p: usize, step: usize)
    requires
        edge_ok(old(b)@.len(), p as int, step as int),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == lf_put(old(b)@, p as int, step as int, lf_inner4(lf_lane(old(b)@, p as int, step as int))),
{
    proof {assert(b@.len() == b.len());}
    let ghost x = lf_lane(b@, p as int, step as int);
    proof {
        lemma_lf_common(false, x);
    }
    let p1 = get(b, p - 2 * step) as i32;
    let p0 = get(b, p - step) as i32;
    let q0 = get(b, p) as i32;
    let q1 = get(b, p + step) as i32;
    let a = 3 * (q0 - p0);
    let a1 = sclip2(sar(a + 4, 3));
    let a2 = sclip2(sar(a + 3, 3));
    let a3 = sar(a1 + 1, 1);
    set(b, p - 2 * step, clip8(p1 + a3));
    set(b, p - step, clip8(p0 + a2));
    set(b, p, clip8(q0 - a1));
    set(b, p + step, clip8(q1 - a3));
    proof {
        assert(b@ =~= lf_put(old(b)@, p as int, step as int, lf_inner4(x)));
    }
}

/// `DoFilter6_C`: the macroblock-edge filter, adjusting three pixels on
/// each side.
#[inline(always)]
fn do_filter6(b: &mut [u8], p: usize, step: usize)
    requires
        edge_ok(old(b)@.len(), p as int, step as int),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == lf_put(old(b)@, p as int, step as int, lf_mb6(lf_lane(old(b)@, p as int, step as int))),
{
    proof {assert(b@.len() == b.len());}
    let ghost x = lf_lane(b@, p as int, step as int);
    let p2 = get(b, p - 3 * step) as i32;
    let p1 = get(b, p - 2 * step) as i32;
    let p0 = get(b, p - step) as i32;
    let q0 = get(b, p) as i32;
    let q1 = get(b, p + step) as i32;
    let q2 = get(b, p + 2 * step) as i32;
    let a = sclip1(3 * (q0 - p0) + sclip1(p1 - q1));
    let a1 = sar(27 * a + 63, 7);
    let a2 = sar(18 * a + 63, 7);
    let a3 = sar(9 * a + 63, 7);
    set(b, p - 3 * step, clip8(p2 + a3));
    set(b, p - 2 * step, clip8(p1 + a2));
    set(b, p - step, clip8(p0 + a1));
    set(b, p, clip8(q0 - a1));
    set(b, p + step, clip8(q1 - a2));
    set(b, p + 2 * step, clip8(q2 - a3));
    proof {
        assert(b@ =~= lf_put(old(b)@, p as int, step as int, lf_mb6(x)));
    }
}

/// `Hev`: high edge variance.
#[inline(always)]
fn hev(b: &[u8], p: usize, step: usize, thresh: i32) -> (r: bool)
    requires
        edge_ok(b@.len(), p as int, step as int),
    ensures
        r == lf_hev(lf_lane(b@, p as int, step as int), thresh as int),
{
    proof {assert(b@.len() == b.len());}
    let p1 = get(b, p - 2 * step) as i32;
    let p0 = get(b, p - step) as i32;
    let q0 = get(b, p) as i32;
    let q1 = get(b, p + step) as i32;
    abs0(p1 - p0) > thresh || abs0(q1 - q0) > thresh
}

/// `NeedsFilter_C`.
#[inline(always)]
fn needs_filter(b: &[u8], p: usize, step: usize, t: i32) -> (r: bool)
    requires
        edge_ok(b@.len(), p as int, step as int),
    ensures
        t % 2 == 1 ==> r == lf_simple_yes(lf_lane(b@, p as int, step as int), (t - 1) / 2),
{
    proof {assert(b@.len() == b.len());}
    let p1 = get(b, p - 2 * step) as i32;
    let p0 = get(b, p - step) as i32;
    let q0 = get(b, p) as i32;
    let q1 = get(b, p + step) as i32;
    4 * abs0(p0 - q0) + abs0(p1 - q1) <= t
}

/// `NeedsFilter2_C`.
#[inline(always)]
fn needs_filter2(b: &[u8], p: usize, step: usize, t: i32, it: i32) -> (r: bool)
    requires
        edge_ok(b@.len(), p as int, step as int),
    ensures
        t % 2 == 1 ==> r == lf_normal_yes(lf_lane(b@, p as int, step as int), (t - 1) / 2, it as int),
{
    proof {assert(b@.len() == b.len());}
    let p3 = get(b, p - 4 * step) as i32;
    let p2 = get(b, p - 3 * step) as i32;
    let p1 = get(b, p - 2 * step) as i32;
    let p0 = get(b, p - step) as i32;
    let q0 = get(b, p) as i32;
    let q1 = get(b, p + step) as i32;
    let q2 = get(b, p + 2 * step) as i32;
    let q3 = get(b, p + 3 * step) as i32;
    if 4 * abs0(p0 - q0) + abs0(p1 - q1) > t {
        return false;
    }
    abs0(p3 - p2) <= it && abs0(p2 - p1) <= it && abs0(p1 - p0) <= it && abs0(q3 - q2) <= it && abs0(q2 - q1) <= it
        && abs0(q1 - q0) <= it
}

/// Writing a lane's own pixels back changes nothing.
proof fn lemma_put_same(b: Seq<u8>, p: int, step: int)
    requires
        edge_ok(b.len(), p, step),
    ensures
        lf_put(b, p, step, lf_lane(b, p, step)) == b,
{
    assert(lf_put(b, p, step, lf_lane(b, p, step)) =~= b);
}

/// The simple filter has no inner form, interior limit or hev threshold.
pub proof fn lemma_run_simple(b: Seq<u8>, p: int, hs: int, vs: int, n: nat, e: int, inner: bool, i: int, h: int)
    ensures
        lf_run(b, p, hs, vs, n, true, inner, e, i, h) == lf_run(b, p, hs, vs, n, true, false, e, 0, 0),
    decreases n,
{
    if n > 0 {
        lemma_run_simple(b, p, hs, vs, (n - 1) as nat, e, inner, i, h);
    }
}

/// The requirement for filtering `size` edge pixels from `p`, `vstride`
/// apart, across edges in direction `hstride`.
pub open spec fn run_ok(blen: nat, p: int, hstride: int, vstride: int, size: int) -> bool {
    &&& 1 <= hstride
    &&& 1 <= vstride
    &&& 1 <= size <= 16
    &&& p >= 4 * hstride
    &&& p + (size - 1) * vstride + 3 * hstride < blen
}

/// The simple filter along `size` pixels (`SimpleVFilter16`, `SimpleHFilter16`),
/// one pixel at a time: the reference for `simple_filter`.
pub fn simple_filter_ref(b: &mut [u8], p: usize, hstride: usize, vstride: usize, size: usize, thresh: i32)
    requires
        run_ok(old(b)@.len(), p as int, hstride as int, vstride as int, size as int),
        0 <= thresh <= 0x1000,
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == lf_run(
            old(b)@,
            p as int,
            hstride as int,
            vstride as int,
            size as nat,
            true,
            false,
            thresh as int,
            0,
            0,
        ),
{
    proof {assert(b@.len() == b.len());}
    let thresh2 = 2 * thresh + 1;
    let mut i: usize = 0;
    while i < size
        invariant
            b@.len() <= usize::MAX,
            i <= size,
            run_ok(b@.len(), p as int, hstride as int, vstride as int, size as int),
            b@.len() == old(b)@.len(),
            thresh2 == 2 * thresh + 1,
            b@ == lf_run(old(b)@, p as int, hstride as int, vstride as int, i as nat, true, false, thresh as int, 0, 0),
        decreases size - i,
    {
        proof {
            assert(i * vstride <= (size - 1) * vstride) by (nonlinear_arith)
                requires i < size, vstride >= 1;
        }
        let q = p + i * vstride;
        let ghost b0 = b@;
        if needs_filter(b, q, hstride, thresh2) {
            do_filter2(b, q, hstride);
        }
        proof {
            lemma_put_same(b0, q as int, hstride as int);
            assert(b@ == lf_filter(b0, q as int, hstride as int, true, false, thresh as int, 0, 0));
        }
        i = i + 1;
    }
}

/// `FilterLoop26_C` (`inner == false`) and `FilterLoop24_C` (`inner`), one
/// pixel at a time: the reference for `filter_loop`.
pub fn filter_loop_ref(
    b: &mut [u8],
    p: usize,
    hstride: usize,
    vstride: usize,
    size: usize,
    thresh: i32,
    ithresh: i32,
    hev_thresh: i32,
    inner: bool,
)
    requires
        run_ok(old(b)@.len(), p as int, hstride as int, vstride as int, size as int),
        0 <= thresh <= 0x1000,
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == lf_run(
            old(b)@,
            p as int,
            hstride as int,
            vstride as int,
            size as nat,
            false,
            inner,
            thresh as int,
            ithresh as int,
            hev_thresh as int,
        ),
{
    proof {assert(b@.len() == b.len());}
    let thresh2 = 2 * thresh + 1;
    let mut i: usize = 0;
    while i < size
        invariant
            b@.len() <= usize::MAX,
            i <= size,
            run_ok(b@.len(), p as int, hstride as int, vstride as int, size as int),
            b@.len() == old(b)@.len(),
            thresh2 == 2 * thresh + 1,
            b@ == lf_run(
                old(b)@,
                p as int,
                hstride as int,
                vstride as int,
                i as nat,
                false,
                inner,
                thresh as int,
                ithresh as int,
                hev_thresh as int,
            ),
        decreases size - i,
    {
        proof {
            assert(i * vstride <= (size - 1) * vstride) by (nonlinear_arith)
                requires i < size, vstride >= 1;
        }
        let q = p + i * vstride;
        let ghost b0 = b@;
        proof {
            lemma_put_same(b0, q as int, hstride as int);
        }
        if needs_filter2(b, q, hstride, thresh2, ithresh) {
            if hev(b, q, hstride, hev_thresh) {
                do_filter2(b, q, hstride);
            } else if inner {
                do_filter4(b, q, hstride);
            } else {
                do_filter6(b, q, hstride);
            }
        }
        proof {
            assert(b@ == lf_filter(
                b0,
                q as int,
                hstride as int,
                false,
                inner,
                thresh as int,
                ithresh as int,
                hev_thresh as int,
            ));
        }
        i = i + 1;
    }
}

// ---------------------------------------------------------------------------
// The loop filter, sixteen pixels at a time
// ---------------------------------------------------------------------------
//
// The pixels along an edge are filtered independently of each other (each
// reads and writes only the eight pixels across the edge in its own lane),
// so the filters below gather up to sixteen lanes into a `[u8; 128]` block
// (row `k` of lane `i` at `r[16 * k + i]`, rows `p3 p2 p1 p0 q0 q1 q2 q3`),
// filter every lane with the same branch-free byte arithmetic, and write
// rows `p2..q2` back. The arithmetic is that of libwebp's SSE2 filters
// (`src/dsp/dec_sse2.c`): signed bytes (pixels with the sign bit flipped)
// and saturating adds, which libwebp computes the same pixels with as its
// C kernels above. Written as lane loops it compiles to SSE2 or NEON byte
// vectors. Both forms are proven to compute `vp8spec`'s filters (`lf_run`):
// the lane form whenever the lanes do not overlap (`lanes_apart`), as it
// reads every lane before writing any. `tests::filters_match_reference`
// also checks one against the other.

/// A 16-bit value saturated to a signed byte (`_mm_packs_epi16`).
#[inline(always)]
fn sat8(x: i16) -> (r: i8)
    ensures
        r as int == lf_c(x as int),
{
    // Upper bound first: in this order LLVM recognizes `adds`/`subs` as
    // saturating byte adds.
    let y = if x > 127 {
        127
    } else {
        x
    };
    (if y < -128 {
        -128
    } else {
        y
    }) as i8
}

/// `_mm_adds_epi8`.
#[inline(always)]
fn adds(a: i8, b: i8) -> (r: i8)
    ensures
        r as int == lf_c(a as int + b as int),
{
    sat8(a as i16 + b as i16)
}

/// `_mm_subs_epi8`.
#[inline(always)]
fn subs(a: i8, b: i8) -> (r: i8)
    ensures
        r as int == lf_c(a as int - b as int),
{
    sat8(a as i16 - b as i16)
}

/// A pixel as a signed byte (the sign bit flipped).
#[inline(always)]
fn sb(x: u8) -> (r: i8)
    ensures
        r as int == x as int - 128,
{
    proof {
        assert(((x ^ 0x80u8) as i8) as i32 == (x as i32) - 128) by (bit_vector);
    }
    (x ^ 0x80u8) as i8
}

/// `sb`'s inverse.
#[inline(always)]
fn ub(x: i8) -> (r: u8)
    ensures
        r as int == x as int + 128,
{
    proof {
        assert((((x as u8) ^ 0x80u8) as i32) == (x as i32) + 128) by (bit_vector);
    }
    (x as u8) ^ 0x80u8
}

/// `MM_ABS`: `|a - b|`.
#[inline(always)]
fn absd8(a: u8, b: u8) -> (r: u8)
    ensures
        r as int == lf_abs(a as int - b as int),
{
    if a > b {
        a - b
    } else {
        b - a
    }
}

/// `_mm_adds_epu8`.
#[inline(always)]
fn addus(a: u8, b: u8) -> (r: u8)
    ensures
        r as int == (if a + b > 255 { 255 } else { a + b }),
{
    let s = a as u16 + b as u16;
    (if s > 255 {
        255
    } else {
        s
    }) as u8
}

/// `_mm_adds_epi8` with a small constant, through the unsigned saturating
/// add (the signed form's dead lower clamp keeps LLVM from vectorizing it
/// as a byte add).
#[inline(always)]
fn addc(a: i8, c: u8) -> (r: i8)
    ensures
        r as int == (if a + c > 127 { 127 } else { a + c }),
{
    proof {
        let u = (a as u8) ^ 0x80u8;
        assert((((a as u8) ^ 0x80u8) as i32) == (a as i32) + 128) by (bit_vector);
        let t = u.saturating_add(c);
        assert(((t ^ 0x80u8) as i8) as i32 == (t as i32) - 128) by (bit_vector);
    }
    ((((a as u8) ^ 0x80u8).saturating_add(c)) ^ 0x80u8) as i8
}

/// `SignedShift8b_SSE2`: `x >> 3`, arithmetic.
#[inline(always)]
fn sshr3(x: i8) -> (r: i8)
    ensures
        r as int == (x as int) / 8,
{
    let w = x as i16;
    proof {
        assert(-128 <= w <= 127 ==> -16 <= (w >> 3u32) <= 15) by (bit_vector);
        let q = w >> 3u32;
        assert(-128 <= w <= 127 && q == w >> 3u32 ==> mul(q, 8) <= w && w <= add(mul(q, 8), 7)) by (bit_vector);
    }
    (w >> 3u32) as i8
}

/// `(x >> 7)` of a 16-bit sum, packed with saturation.
#[inline(always)]
fn shr7(x: i16) -> (r: i8)
    ensures
        r as int == lf_c((x as int) / 128),
{
    proof {
        let q = x >> 7u32;
        let x2 = x as i32;
        let q2 = q as i32;
        assert(q == x >> 7u32 && x2 == x as i32 && q2 == q as i32 ==> mul(q2, 128) <= x2 && x2 <= add(mul(q2, 128), 127))
            by (bit_vector);
    }
    sat8(x >> 7u32)
}

/// All ones where `b`.
#[inline(always)]
fn bmask(b: bool) -> (r: u8)
    ensures
        r == (if b { 0xffu8 } else { 0u8 }),
{
    if b {
        0xff
    } else {
        0
    }
}

/// `a & m` on a signed byte.
#[inline(always)]
fn and8(a: i8, m: u8) -> (r: i8)
    ensures
        m == 0xff ==> r == a,
        m == 0 ==> r == 0,
{
    proof {
        assert(((a as u8) & 0xffu8) as i8 == a) by (bit_vector);
        assert(((a as u8) & 0u8) as i8 == 0i8) by (bit_vector);
    }
    ((a as u8) & m) as i8
}

/// `GetBaseDelta_SSE2`: `p1 - q1 + 3 * (q0 - p0)`, saturating in this order.
#[inline(always)]
fn base_delta(p1: i8, p0: i8, q0: i8, q1: i8) -> (r: i8)
    ensures
        r as int == lf_c(lf_c(p1 as int - q1 as int) + 3 * (q0 as int - p0 as int)),
{
    let p1_q1 = subs(p1, q1);
    let q0_p0 = subs(q0, p0);
    let s1 = adds(p1_q1, q0_p0);
    let s2 = adds(q0_p0, s1);
    adds(q0_p0, s2)
}

/// `NeedsFilter_SSE2`: `2 * |p0 - q0| + |p1 - q1| / 2 <= thresh`, saturating.
#[inline(always)]
fn needs_filter8(p1: u8, p0: u8, q0: u8, q1: u8, thresh: u8) -> (r: bool)
    ensures
        thresh <= 254 ==> r == (lf_abs(p0 as int - q0 as int) * 2 + lf_abs(p1 as int - q1 as int) / 2 <= thresh as int),
{
    let t3 = absd8(p1, q1) / 2;
    let t4 = absd8(p0, q0);
    addus(addus(t4, t4), t3) <= thresh
}

/// Lane `i` of a block in rows: the eight pixels across the edge.
pub open spec fn blk_lane(r: Seq<u8>, i: int) -> Edge8 {
    Edge8 {
        p3: r[i] as int,
        p2: r[16 + i] as int,
        p1: r[32 + i] as int,
        p0: r[48 + i] as int,
        q0: r[64 + i] as int,
        q1: r[80 + i] as int,
        q2: r[96 + i] as int,
        q3: r[112 + i] as int,
    }
}

/// Whether `gather` leaves the block lane-major (`to_rows` needed).
pub open spec fn lane_major(hstride: usize, vstride: usize) -> bool {
    vstride != 1 && hstride == 1
}

/// Lane `i` of a lane-major block: its eight pixels are contiguous.
pub open spec fn lm_lane(r: Seq<u8>, i: int) -> Edge8 {
    Edge8 {
        p3: r[8 * i] as int,
        p2: r[8 * i + 1] as int,
        p1: r[8 * i + 2] as int,
        p0: r[8 * i + 3] as int,
        q0: r[8 * i + 4] as int,
        q1: r[8 * i + 5] as int,
        q2: r[8 * i + 6] as int,
        q3: r[8 * i + 7] as int,
    }
}

/// Where a perfect shuffle of 128 bytes takes byte `j` from: the 7 bits
/// of `j` rotated right by one.
pub open spec fn rot7(j: int) -> int {
    j / 2 + 64 * (j % 2)
}

/// One perfect shuffle of a 128-byte block.
pub open spec fn shuf1(s: Seq<u8>) -> Seq<u8> {
    Seq::new(128, |j: int| s[rot7(j)])
}

/// `n` perfect shuffles.
pub open spec fn shuf(s: Seq<u8>, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        s
    } else {
        shuf1(shuf(s, (n - 1) as nat))
    }
}

/// Eight 16-byte rows as one block.
pub open spec fn flat8(m: Seq<Seq<u8>>) -> Seq<u8> {
    Seq::new(128, |j: int| m[j / 16][j % 16])
}

/// `c` is one shuffle round of the rows `a`.
pub open spec fn zipped(a: Seq<Seq<u8>>, c: Seq<Seq<u8>>) -> bool {
    &&& a.len() == 8
    &&& c.len() == 8
    &&& forall|k: int| 0 <= k < 8 ==> (#[trigger] a[k]).len() == 16
    &&& c[0] == unpacklo8_lanes(a[0], a[4])
    &&& c[1] == unpackhi8_lanes(a[0], a[4])
    &&& c[2] == unpacklo8_lanes(a[1], a[5])
    &&& c[3] == unpackhi8_lanes(a[1], a[5])
    &&& c[4] == unpacklo8_lanes(a[2], a[6])
    &&& c[5] == unpackhi8_lanes(a[2], a[6])
    &&& c[6] == unpacklo8_lanes(a[3], a[7])
    &&& c[7] == unpackhi8_lanes(a[3], a[7])
}

proof fn lemma_zip(a: Seq<Seq<u8>>, c: Seq<Seq<u8>>)
    requires
        zipped(a, c),
    ensures
        flat8(c) == shuf1(flat8(a)),
{
    assert forall|j: int| 0 <= j < 128 implies flat8(c)[j] == shuf1(flat8(a))[j] by {
        let row = j / 16;
        let col = j % 16;
        let k = row / 2;
        let t = rot7(j);
        assert(t / 16 == k + 4 * (col % 2));
        assert(t % 16 == 8 * (row % 2) + col / 2);
        assert(col / 16 == 0);
        assert(col % 16 == col);
        if row == 0 {
        } else if row == 1 {
        } else if row == 2 {
        } else if row == 3 {
        } else if row == 4 {
        } else if row == 5 {
        } else if row == 6 {
        } else {
            assert(row == 7);
        }
    }
    assert(flat8(c) =~= shuf1(flat8(a)));
}

proof fn lemma_rot4(j: int)
    requires
        0 <= j < 128,
    ensures
        rot7(rot7(rot7(rot7(j)))) == 8 * (j % 16) + j / 16,
        0 <= rot7(j) < 128,
{
}

proof fn lemma_rot3(j: int)
    requires
        0 <= j < 128,
    ensures
        rot7(rot7(rot7(j))) == 16 * (j % 8) + j / 8,
        0 <= rot7(j) < 128,
{
}

/// Four shuffles turn a lane-major block into rows.
#[verifier::rlimit(60)]
proof fn lemma_shuf4(s: Seq<u8>)
    requires
        s.len() == 128,
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] blk_lane(shuf(s, 4), i) == lm_lane(s, i),
{
    reveal_with_fuel(shuf, 5);
    assert forall|j: int| 0 <= j < 128 implies shuf(s, 4)[j] == s[8 * (j % 16) + j / 16] by {
        lemma_rot4(j);
        lemma_rot4(rot7(j));
        lemma_rot4(rot7(rot7(j)));
        lemma_rot4(rot7(rot7(rot7(j))));
    }
    assert forall|i: int| 0 <= i < 16 implies #[trigger] blk_lane(shuf(s, 4), i) == lm_lane(s, i) by {
        let t = shuf(s, 4);
        assert(t[i] == s[8 * i]);
        assert(t[16 + i] == s[8 * i + 1]);
        assert(t[32 + i] == s[8 * i + 2]);
        assert(t[48 + i] == s[8 * i + 3]);
        assert(t[64 + i] == s[8 * i + 4]);
        assert(t[80 + i] == s[8 * i + 5]);
        assert(t[96 + i] == s[8 * i + 6]);
        assert(t[112 + i] == s[8 * i + 7]);
    }
}

/// Three more turn rows back into a lane-major block.
proof fn lemma_shuf3(s: Seq<u8>)
    requires
        s.len() == 128,
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] lm_lane(shuf(s, 3), i) == blk_lane(s, i),
{
    reveal_with_fuel(shuf, 4);
    assert forall|j: int| 0 <= j < 128 implies shuf(s, 3)[j] == s[16 * (j % 8) + j / 8] by {
        lemma_rot3(j);
        lemma_rot3(rot7(j));
        lemma_rot3(rot7(rot7(j)));
    }
    assert forall|i: int| 0 <= i < 16 implies #[trigger] lm_lane(shuf(s, 3), i) == blk_lane(s, i) by {
        let t = shuf(s, 3);
        assert(t[8 * i] == s[i]);
        assert(t[8 * i + 1] == s[16 + i]);
        assert(t[8 * i + 2] == s[32 + i]);
        assert(t[8 * i + 3] == s[48 + i]);
        assert(t[8 * i + 4] == s[64 + i]);
        assert(t[8 * i + 5] == s[80 + i]);
        assert(t[8 * i + 6] == s[96 + i]);
        assert(t[8 * i + 7] == s[112 + i]);
    }
}

/// The rows of eight SSE2 vectors.
pub open spec fn rows_sse(x: [__m128i; 8]) -> Seq<Seq<u8>> {
    Seq::new(8, |k: int| b128(x[k]))
}

/// The rows of eight NEON vectors.
pub open spec fn rows_neon(x: [uint8x16_t; 8]) -> Seq<Seq<u8>> {
    Seq::new(8, |k: int| n8(x[k]))
}

/// Eight rows loaded from a block are the block.
proof fn lemma_flat_load(m: Seq<Seq<u8>>, s: Seq<u8>)
    requires
        s.len() == 128,
        m.len() == 8,
        forall|k: int| 0 <= k < 8 ==> #[trigger] m[k] == s.subrange(16 * k, 16 * k + 16),
    ensures
        flat8(m) == s,
{
    assert forall|j: int| 0 <= j < 128 implies flat8(m)[j] == s[j] by {
        let k = j / 16;
        assert(m[k] == s.subrange(16 * k, 16 * k + 16));
    }
    assert(flat8(m) =~= s);
}

/// One perfect-shuffle round on eight 16-byte rows: row `2j` and `2j + 1`
/// are the low and high interleavings of rows `j` and `j + 4`.
fn shuffle_sse2(x: [__m128i; 8]) -> (r: [__m128i; 8])
    ensures
        flat8(rows_sse(r)) == shuf1(flat8(rows_sse(x))),
{
    let r = [
        _mm_unpacklo_epi8(x[0], x[4]), _mm_unpackhi_epi8(x[0], x[4]),
        _mm_unpacklo_epi8(x[1], x[5]), _mm_unpackhi_epi8(x[1], x[5]),
        _mm_unpacklo_epi8(x[2], x[6]), _mm_unpackhi_epi8(x[2], x[6]),
        _mm_unpacklo_epi8(x[3], x[7]), _mm_unpackhi_epi8(x[3], x[7]),
    ];
    proof {
        assert(zipped(rows_sse(x), rows_sse(r)));
        lemma_zip(rows_sse(x), rows_sse(r));
    }
    r
}

/// `shuffle_sse2` with NEON's `zip1`/`zip2`.
#[inline(always)]
fn shuffle_neon(x: [uint8x16_t; 8]) -> (r: [uint8x16_t; 8])
    requires
        neon(),
    ensures
        flat8(rows_neon(r)) == shuf1(flat8(rows_neon(x))),
{
    let r = [
        vzip1q_u8(x[0], x[4]), vzip2q_u8(x[0], x[4]),
        vzip1q_u8(x[1], x[5]), vzip2q_u8(x[1], x[5]),
        vzip1q_u8(x[2], x[6]), vzip2q_u8(x[2], x[6]),
        vzip1q_u8(x[3], x[7]), vzip2q_u8(x[3], x[7]),
    ];
    proof {
        assert(zipped(rows_neon(x), rows_neon(r)));
        lemma_zip(rows_neon(x), rows_neon(r));
    }
    r
}

/// Applies `rounds` perfect shuffles to the block, as eight 16-byte rows.
/// The shuffle permutes the 128 byte positions as a rotation of their 7
/// index bits, so 4 rounds turn the lane-major block (lane `i`'s byte `k`
/// at `8 * i + k`) into rows (`16 * k + i`), and 3 more turn it back.
#[inline(always)]
fn shuffle_block(r: &mut [u8; 128], rounds: usize)
    ensures
        final(r)@ == shuf(old(r)@, rounds as nat),
{
    let s: [u8; 128] = *r;
    let ss: &[u8] = &s;
    let rs: &mut [u8] = r;
    proof {
        assert(ss@.len() == 128);
        assert(rs@.len() == 128);
    }
    if has_neon() {
        let mut x = [
            vld1q_u8_at(ss, 0), vld1q_u8_at(ss, 16), vld1q_u8_at(ss, 32), vld1q_u8_at(ss, 48),
            vld1q_u8_at(ss, 64), vld1q_u8_at(ss, 80), vld1q_u8_at(ss, 96), vld1q_u8_at(ss, 112),
        ];
        proof {
            lemma_flat_load(rows_neon(x), ss@);
        }
        let mut n: usize = 0;
        while n < rounds
            invariant
                neon(),
                n <= rounds,
                flat8(rows_neon(x)) == shuf(ss@, n as nat),
            decreases rounds - n,
        {
            x = shuffle_neon(x);
            n = n + 1;
        }
        let ghost f = flat8(rows_neon(x));
        let mut k: usize = 0;
        while k < 8
            invariant
                neon(),
                k <= 8,
                rs@.len() == 128,
                f == flat8(rows_neon(x)),
                forall|j: int| 0 <= j < 16 * k ==> rs@[j] == f[j],
            decreases 8 - k,
        {
            vst1q_u8_at(rs, 16 * k, x[k]);
            k = k + 1;
        }
        proof {
            assert(rs@ =~= f);
        }
    } else {
        // SSE2 is part of x86-64 (and emulated elsewhere).
        shuffle_rows_sse2(ss, rs, rounds);
    }
}

/// `shuffle_block`'s SSE2 path, from `ss` into `rs`.
fn shuffle_rows_sse2(ss: &[u8], rs: &mut [u8], rounds: usize)
    requires
        ss@.len() == 128,
        old(rs)@.len() == 128,
    ensures
        final(rs)@.len() == 128,
        final(rs)@ == shuf(ss@, rounds as nat),
{
    let mut x = [
        load128_u8(ss, 0), load128_u8(ss, 16), load128_u8(ss, 32), load128_u8(ss, 48),
        load128_u8(ss, 64), load128_u8(ss, 80), load128_u8(ss, 96), load128_u8(ss, 112),
    ];
    proof {
        lemma_flat_load(rows_sse(x), ss@);
    }
    let mut n: usize = 0;
    while n < rounds
        invariant
            n <= rounds,
            flat8(rows_sse(x)) == shuf(ss@, n as nat),
        decreases rounds - n,
    {
        x = shuffle_sse2(x);
        n = n + 1;
    }
    let ghost f = flat8(rows_sse(x));
    let mut k: usize = 0;
    while k < 8
        invariant
            k <= 8,
            rs@.len() == 128,
            f == flat8(rows_sse(x)),
            forall|j: int| 0 <= j < 16 * k ==> rs@[j] == f[j],
        decreases 8 - k,
    {
        store128_u8(rs, 16 * k, x[k]);
        k = k + 1;
    }
    proof {
        assert(rs@ =~= f);
    }
}

/// `k * m`, as a term quantifiers can trigger on.
pub open spec fn kx(k: int, m: int) -> int {
    k * m
}

proof fn lemma_kx(m: int)
    requires
        m >= 0,
    ensures
        forall|a: int, b: int| #![trigger kx(a, m), kx(b, m)] 0 <= a < b ==> kx(a, m) + m <= kx(b, m),
        forall|a: int| 0 <= a ==> #[trigger] kx(a, m) >= 0,
        kx(0, m) == 0,
{
    assert forall|a: int, b: int| #![trigger kx(a, m), kx(b, m)] 0 <= a < b implies kx(a, m) + m <= kx(b, m) by {
        assert(a * m + m <= b * m) by (nonlinear_arith)
            requires
                0 <= a < b,
                m >= 0,
        ;
    }
    assert forall|a: int| 0 <= a implies #[trigger] kx(a, m) >= 0 by {
        assert(a * m >= 0) by (nonlinear_arith)
            requires
                0 <= a,
                m >= 0,
        ;
    }
}

/// `j` is one of the eight pixels across the edge at `q`.
pub open spec fn in_lane(j: int, q: int, hs: int) -> bool {
    j == q - 4 * hs || j == q - 3 * hs || j == q - 2 * hs || j == q - hs || j == q || j == q + hs || j == q + 2 * hs
        || j == q + 3 * hs
}

/// `j` is in lane `i` of the run from `p`.
pub open spec fn lane_has(j: int, p: int, hs: int, vs: int, i: int) -> bool {
    in_lane(j, p + kx(i, vs), hs)
}

/// `j` is one of the six pixels of lane `i` that the filters write.
pub open spec fn lane_has6(j: int, p: int, hs: int, vs: int, i: int) -> bool {
    lane_has(j, p, hs, vs, i) && j != p + kx(i, vs) - 4 * hs && j != p + kx(i, vs) + 3 * hs
}

/// `j` is in one of the first `n` lanes.
pub open spec fn lane_cov(j: int, p: int, hs: int, vs: int, n: int) -> bool {
    exists|i: int| 0 <= i < n && #[trigger] lane_has(j, p, hs, vs, i)
}

pub open spec fn lane_cov6(j: int, p: int, hs: int, vs: int, n: int) -> bool {
    exists|i: int| 0 <= i < n && #[trigger] lane_has6(j, p, hs, vs, i)
}

/// The lanes of a run do not overlap: along rows the edge pixels are at
/// least the run's length apart, or along columns at least eight. (The
/// decoder's strides always are; the lane-parallel filters need it, as
/// they read every lane before writing any.)
pub open spec fn lanes_apart(hs: int, vs: int, size: int) -> bool {
    (vs == 1 && hs >= size) || (hs == 1 && vs >= 8)
}

proof fn lemma_apart(p: int, hs: int, vs: int, size: int)
    requires
        lanes_apart(hs, vs, size),
        1 <= size <= 16,
        hs >= 1,
        vs >= 1,
    ensures
        forall|j: int, i1: int, i2: int|
            #![trigger lane_has(j, p, hs, vs, i1), lane_has(j, p, hs, vs, i2)]
            0 <= i1 < size && 0 <= i2 < size && lane_has(j, p, hs, vs, i1) && lane_has(j, p, hs, vs, i2) ==> i1
                == i2,
{
    lemma_kx(vs);
    assert forall|j: int, i1: int, i2: int|
        #![trigger lane_has(j, p, hs, vs, i1), lane_has(j, p, hs, vs, i2)]
        0 <= i1 < size && 0 <= i2 < size && lane_has(j, p, hs, vs, i1) && lane_has(j, p, hs, vs, i2) implies i1
        == i2 by {
        if i1 < i2 {
            assert(kx(i1, vs) + vs <= kx(i2, vs));
        } else if i2 < i1 {
            assert(kx(i2, vs) + vs <= kx(i1, vs));
        }
        if vs == 1 {
            assert(kx(i1, vs) == i1);
            assert(kx(i2, vs) == i2);
        }
    }
}

/// A lane with its outer pixels (which no filter writes) from `a`.
pub open spec fn mix(a: Edge8, r: Edge8) -> Edge8 {
    Edge8 { p3: a.p3, q3: a.q3, ..r }
}

/// The filters give pixels, and leave `p3` and `q3`.
proof fn lemma_kernel_px(x: Edge8, simple: bool, inner: bool, e: int, i: int, h: int)
    requires
        px8(x),
    ensures
        px8(lf_kernel(x, simple, inner, e, i, h)),
        lf_kernel(x, simple, inner, e, i, h).p3 == x.p3,
        lf_kernel(x, simple, inner, e, i, h).q3 == x.q3,
{
}

/// `b1` is `b0` with the first `n` lanes of a run each filtered, from the
/// pixels it had in `b0`.
pub open spec fn lanes_done(
    b0: Seq<u8>,
    b1: Seq<u8>,
    p: int,
    hs: int,
    vs: int,
    n: int,
    simple: bool,
    inner: bool,
    e: int,
    i: int,
    h: int,
) -> bool {
    &&& b1.len() == b0.len()
    &&& forall|l: int|
        0 <= l < n ==> lf_lane(b1, p + #[trigger] kx(l, vs), hs) == lf_kernel(
            lf_lane(b0, p + kx(l, vs), hs),
            simple,
            inner,
            e,
            i,
            h,
        )
    &&& forall|j: int| 0 <= j < b0.len() && !lane_cov(j, p, hs, vs, n) ==> b1[j] == b0[j]
}

proof fn lemma_put_get(c: Seq<u8>, q: int, hs: int, y: Edge8)
    requires
        edge_ok(c.len(), q, hs),
        px8(y),
        y.p3 == c[q - 4 * hs],
        y.q3 == c[q + 3 * hs],
    ensures
        lf_lane(lf_put(c, q, hs, y), q, hs) == y,
        lf_put(c, q, hs, y).len() == c.len(),
{
}

proof fn lemma_put_other(c: Seq<u8>, q: int, hs: int, y: Edge8, j: int)
    requires
        edge_ok(c.len(), q, hs),
        0 <= j < c.len(),
        !in_lane(j, q, hs),
    ensures
        lf_put(c, q, hs, y)[j] == c[j],
{
}

proof fn lemma_lane_eq(a: Seq<u8>, b: Seq<u8>, q: int, hs: int)
    requires
        forall|j: int| #[trigger] in_lane(j, q, hs) ==> a[j] == b[j],
    ensures
        lf_lane(a, q, hs) == lf_lane(b, q, hs),
{
    assert(in_lane(q - 4 * hs, q, hs));
    assert(in_lane(q - 3 * hs, q, hs));
    assert(in_lane(q - 2 * hs, q, hs));
    assert(in_lane(q - hs, q, hs));
    assert(in_lane(q, q, hs));
    assert(in_lane(q + hs, q, hs));
    assert(in_lane(q + 2 * hs, q, hs));
    assert(in_lane(q + 3 * hs, q, hs));
}

/// The lanes of a run are inside the plane.
proof fn lemma_lane_in(blen: nat, p: int, hs: int, vs: int, size: int, l: int)
    requires
        run_ok(blen, p, hs, vs, size),
        0 <= l < size,
    ensures
        edge_ok(blen, p + kx(l, vs), hs),
        forall|j: int| #[trigger] in_lane(j, p + kx(l, vs), hs) ==> 0 <= j < blen,
{
    lemma_kx(vs);
    assert(l == size - 1 || kx(l, vs) + vs <= kx(size - 1, vs));
}

/// Filtering lanes that do not overlap one after another filters each
/// from its original pixels.
proof fn lemma_run_lanes(
    b0: Seq<u8>,
    p: int,
    hs: int,
    vs: int,
    size: int,
    n: nat,
    simple: bool,
    inner: bool,
    e: int,
    i: int,
    h: int,
)
    requires
        run_ok(b0.len(), p, hs, vs, size),
        n <= size,
        lanes_apart(hs, vs, size),
    ensures
        lanes_done(b0, lf_run(b0, p, hs, vs, n, simple, inner, e, i, h), p, hs, vs, n as int, simple, inner, e, i, h),
    decreases n,
{
    hide(lf_kernel);
    hide(lf_put);
    hide(lf_lane);
    hide(in_lane);
    lemma_apart(p, hs, vs, size);
    if n == 0 {
    } else {
        let m = (n - 1) as nat;
        lemma_run_lanes(b0, p, hs, vs, size, m, simple, inner, e, i, h);
        let c = lf_run(b0, p, hs, vs, m, simple, inner, e, i, h);
        let q = p + kx(m as int, vs);
        assert(q == p + (n - 1) * vs);
        lemma_lane_in(b0.len(), p, hs, vs, size, m as int);
        let x0 = lf_lane(b0, q, hs);
        assert forall|j: int| #[trigger] in_lane(j, q, hs) implies c[j] == b0[j] by {
            assert(lane_has(j, p, hs, vs, m as int));
            assert(!lane_cov(j, p, hs, vs, m as int));
        }
        lemma_lane_eq(c, b0, q, hs);
        let y = lf_kernel(x0, simple, inner, e, i, h);
        assert(px8(x0) && c[q - 4 * hs] == x0.p3 && c[q + 3 * hs] == x0.q3) by {
            reveal(lf_lane);
        }
        lemma_kernel_px(x0, simple, inner, e, i, h);
        let d = lf_put(c, q, hs, y);
        assert(d == lf_run(b0, p, hs, vs, n, simple, inner, e, i, h));
        lemma_put_get(c, q, hs, y);
        assert forall|l: int| 0 <= l < n implies lf_lane(d, p + #[trigger] kx(l, vs), hs) == lf_kernel(
            lf_lane(b0, p + kx(l, vs), hs),
            simple,
            inner,
            e,
            i,
            h,
        ) by {
            let ql = p + kx(l, vs);
            if l < m {
                lemma_lane_in(b0.len(), p, hs, vs, size, l);
                assert forall|j: int| #[trigger] in_lane(j, ql, hs) implies d[j] == c[j] by {
                    assert(lane_has(j, p, hs, vs, l));
                    assert(!lane_has(j, p, hs, vs, m as int));
                    lemma_put_other(c, q, hs, y, j);
                }
                lemma_lane_eq(d, c, ql, hs);
            } else {
                assert(l == m);
            }
        }
        assert forall|j: int| 0 <= j < b0.len() && !lane_cov(j, p, hs, vs, n as int) implies d[j] == b0[j] by {
            assert(!lane_has(j, p, hs, vs, m as int));
            assert(!lane_cov(j, p, hs, vs, m as int));
            lemma_put_other(c, q, hs, y, j);
        }
    }
}

/// The block before and after the lanes are filtered, whichever way it
/// was gathered: `r1` as gathered, `ra` in rows, `rb` filtered, `r2` as
/// scattered.
proof fn lemma_block_ends(
    b0: Seq<u8>,
    b1: Seq<u8>,
    p: int,
    hs: int,
    vs: int,
    size: int,
    l0: int,
    r1: Seq<u8>,
    ra: Seq<u8>,
    rb: Seq<u8>,
    r2: Seq<u8>,
)
    requires
        lanes_apart(hs, vs, size),
        hs >= 1,
        vs >= 1,
        0 <= l0,
        l0 + size <= 16,
        vs == 1 ==> ra == r1 && r2 == rb,
        vs != 1 ==> forall|j: int| 0 <= j < 16 ==> #[trigger] blk_lane(ra, j) == lm_lane(r1, j),
        vs != 1 ==> forall|j: int| 0 <= j < 16 ==> #[trigger] lm_lane(r2, j) == blk_lane(rb, j),
        vs == 1 ==> forall|l: int| 0 <= l < size ==> blk_lane(r1, l0 + l) == lf_lane(b0, p + #[trigger] kx(l, vs), hs),
        vs != 1 ==> forall|l: int| 0 <= l < size ==> lm_lane(r1, l0 + l) == lf_lane(b0, p + #[trigger] kx(l, vs), hs),
        vs == 1 ==> forall|l: int|
            0 <= l < size ==> lf_lane(b1, p + #[trigger] kx(l, vs), hs) == mix(
                lf_lane(b0, p + kx(l, vs), hs),
                blk_lane(r2, l0 + l),
            ),
        vs != 1 ==> forall|l: int| 0 <= l < size ==> lf_lane(b1, p + #[trigger] kx(l, vs), hs) == lm_lane(r2, l0 + l),
    ensures
        forall|l: int| 0 <= l < size ==> blk_lane(ra, l0 + l) == lf_lane(b0, p + #[trigger] kx(l, vs), hs),
        forall|l: int|
            0 <= l < size ==> {
                let x = lf_lane(b1, p + #[trigger] kx(l, vs), hs);
                x == blk_lane(rb, l0 + l) || x == mix(lf_lane(b0, p + kx(l, vs), hs), blk_lane(rb, l0 + l))
            },
{
    hide(lf_lane);
    hide(blk_lane);
    hide(lm_lane);
    assert forall|l: int| 0 <= l < size implies blk_lane(ra, l0 + l) == lf_lane(b0, p + #[trigger] kx(l, vs), hs) by {
        if vs != 1 {
            assert(blk_lane(ra, l0 + l) == lm_lane(r1, l0 + l));
        }
    }
    assert forall|l: int| 0 <= l < size implies {
        let x = lf_lane(b1, p + #[trigger] kx(l, vs), hs);
        x == blk_lane(rb, l0 + l) || x == mix(lf_lane(b0, p + kx(l, vs), hs), blk_lane(rb, l0 + l))
    } by {
        if vs != 1 {
            assert(lm_lane(r2, l0 + l) == blk_lane(rb, l0 + l));
        }
    }
}

/// What a lane-parallel filter does (gathering lanes into a block,
/// filtering each, writing them back) is the run.
proof fn lemma_block_done(
    b0: Seq<u8>,
    b1: Seq<u8>,
    p: int,
    hs: int,
    vs: int,
    size: int,
    l0: int,
    ra: Seq<u8>,
    rb: Seq<u8>,
    simple: bool,
    inner: bool,
    e: int,
    i: int,
    h: int,
)
    requires
        run_ok(b0.len(), p, hs, vs, size),
        lanes_apart(hs, vs, size),
        forall|l: int| 0 <= l < size ==> blk_lane(ra, l0 + l) == lf_lane(b0, p + #[trigger] kx(l, vs), hs),
        forall|j: int| 0 <= j < 16 ==> #[trigger] blk_lane(rb, j) == lf_kernel(blk_lane(ra, j), simple, inner, e, i, h),
        0 <= l0,
        l0 + size <= 16,
        b1.len() == b0.len(),
        forall|l: int|
            0 <= l < size ==> {
                let x = lf_lane(b1, p + #[trigger] kx(l, vs), hs);
                x == blk_lane(rb, l0 + l) || x == mix(lf_lane(b0, p + kx(l, vs), hs), blk_lane(rb, l0 + l))
            },
        forall|j: int| 0 <= j < b0.len() && !lane_cov(j, p, hs, vs, size) ==> b1[j] == b0[j],
    ensures
        b1 == lf_run(b0, p, hs, vs, size as nat, simple, inner, e, i, h),
{
    let c = lf_run(b0, p, hs, vs, size as nat, simple, inner, e, i, h);
    lemma_run_lanes(b0, p, hs, vs, size, size as nat, simple, inner, e, i, h);
    assert forall|j: int| 0 <= j < b0.len() implies b1[j] == c[j] by {
        if lane_cov(j, p, hs, vs, size) {
            let l = choose|l: int| 0 <= l < size && #[trigger] lane_has(j, p, hs, vs, l);
            let q = p + kx(l, vs);
            let x0 = lf_lane(b0, q, hs);
            lemma_kernel_px(x0, simple, inner, e, i, h);
            assert(blk_lane(rb, l0 + l) == lf_kernel(x0, simple, inner, e, i, h));
            assert(lf_lane(b1, q, hs) == lf_lane(c, q, hs));
        }
    }
    assert(b1 =~= c);
}

/// `gather`'s rows are the lanes.
proof fn lemma_gather_rows(b: Seq<u8>, r: Seq<u8>, r0: Seq<u8>, p: int, hs: int, size: int, l0: int)
    requires
        r.len() == 128,
        r0.len() == 128,
        0 <= l0,
        l0 + size <= 16,
        forall|kk: int, i: int|
            #[trigger] gat(kk, i) && 0 <= kk < 8 && 0 <= i < size ==> r[16 * kk + l0 + i] == b[p - 4 * hs + kx(kk, hs)
                + i],
        forall|kk: int, c: int|
            #[trigger] gat(kk, c) && 0 <= kk < 8 && 0 <= c < 16 && !(l0 <= c < l0 + size) ==> r[16 * kk + c]
                == r0[16 * kk + c],
    ensures
        forall|l: int| 0 <= l < size ==> blk_lane(r, l0 + l) == lf_lane(b, p + #[trigger] kx(l, 1), hs),
        forall|c: int| 0 <= c < 16 && !(l0 <= c < l0 + size) ==> #[trigger] blk_lane(r, c) == blk_lane(r0, c),
{
    assert(kx(0, hs) == 0 && kx(1, hs) == hs && kx(2, hs) == 2 * hs && kx(3, hs) == 3 * hs && kx(4, hs) == 4 * hs && kx(
        5,
        hs,
    ) == 5 * hs && kx(6, hs) == 6 * hs && kx(7, hs) == 7 * hs);
    assert forall|l: int| 0 <= l < size implies blk_lane(r, l0 + l) == lf_lane(b, p + #[trigger] kx(l, 1), hs) by {
        assert(kx(l, 1) == l);
        assert(gat(0, l) && gat(1, l) && gat(2, l) && gat(3, l) && gat(4, l) && gat(5, l) && gat(6, l) && gat(7, l));
    }
    assert forall|c: int| 0 <= c < 16 && !(l0 <= c < l0 + size) implies #[trigger] blk_lane(r, c) == blk_lane(
        r0,
        c,
    ) by {
        assert(gat(0, c) && gat(1, c) && gat(2, c) && gat(3, c) && gat(4, c) && gat(5, c) && gat(6, c) && gat(7, c));
    }
}

/// `scatter`'s rows are the lanes, and nothing else changes.
proof fn lemma_scatter_rows(b0: Seq<u8>, b1: Seq<u8>, r: Seq<u8>, p: int, hs: int, size: int, l0: int)
    requires
        run_ok(b0.len(), p, hs, 1, size),
        b1.len() == b0.len(),
        0 <= l0,
        hs >= size ==> forall|kk: int, i: int|
            #[trigger] gat(kk, i) && 1 <= kk < 7 && 0 <= i < size ==> b1[p - 4 * hs + kx(kk, hs) + i] == r[16 * kk + l0
                + i],
        forall|j: int| 0 <= j < b0.len() ==> b1[j] == b0[j] || lane_cov6(j, p, hs, 1, size),
    ensures
        hs >= size ==> forall|l: int|
            0 <= l < size ==> lf_lane(b1, p + #[trigger] kx(l, 1), hs) == mix(
                lf_lane(b0, p + kx(l, 1), hs),
                blk_lane(r, l0 + l),
            ),
        forall|j: int| 0 <= j < b0.len() && !lane_cov(j, p, hs, 1, size) ==> b1[j] == b0[j],
{
    assert forall|j: int| 0 <= j < b0.len() && !lane_cov(j, p, hs, 1, size) implies b1[j] == b0[j] by {
        if lane_cov6(j, p, hs, 1, size) {
            let l = choose|l: int| 0 <= l < size && #[trigger] lane_has6(j, p, hs, 1, l);
            assert(lane_has(j, p, hs, 1, l));
        }
    }
    if hs >= size {
        lemma_apart(p, hs, 1, size);
        assert(kx(1, hs) == hs && kx(2, hs) == 2 * hs && kx(3, hs) == 3 * hs && kx(4, hs) == 4 * hs && kx(5, hs) == 5
            * hs && kx(6, hs) == 6 * hs);
        assert forall|l: int| 0 <= l < size implies lf_lane(b1, p + #[trigger] kx(l, 1), hs) == mix(
            lf_lane(b0, p + kx(l, 1), hs),
            blk_lane(r, l0 + l),
        ) by {
            let q = p + kx(l, 1);
            assert(kx(l, 1) == l);
            lemma_lane_in(b0.len(), p, hs, 1, size, l);
            assert(gat(1, l) && gat(2, l) && gat(3, l) && gat(4, l) && gat(5, l) && gat(6, l));
            assert(lane_has(q - 4 * hs, p, hs, 1, l));
            assert(lane_has(q + 3 * hs, p, hs, 1, l));
            assert(in_lane(q - 4 * hs, q, hs) && in_lane(q + 3 * hs, q, hs));
            assert(!lane_cov6(q - 4 * hs, p, hs, 1, size));
            assert(!lane_cov6(q + 3 * hs, p, hs, 1, size));
        }
    }
}

/// A trigger for facts about row `k` of lane `i`.
pub open spec fn gat(k: int, i: int) -> bool {
    true
}

/// Gathers `size` lanes from `p`, `vstride` apart, eight pixels each across
/// the edge (`hstride` apart, the edge between the fourth and fifth).
#[inline(always)]
fn gather(b: &[u8], p: usize, hstride: usize, vstride: usize, size: usize, r: &mut [u8; 128], l0: usize)
    requires
        run_ok(b@.len(), p as int, hstride as int, vstride as int, size as int),
        l0 + size <= 16,
    ensures
        vstride == 1 ==> forall|l: int|
            0 <= l < size ==> blk_lane(final(r)@, l0 + l) == lf_lane(
                b@,
                p + #[trigger] kx(l, vstride as int),
                hstride as int,
            ),
        vstride == 1 ==> forall|c: int|
            0 <= c < 16 && !(l0 <= c < l0 + size) ==> #[trigger] blk_lane(final(r)@, c) == blk_lane(old(r)@, c),
        lane_major(hstride, vstride) ==> forall|l: int|
            0 <= l < size ==> lm_lane(final(r)@, l0 + l) == lf_lane(
                b@,
                p + #[trigger] kx(l, vstride as int),
                hstride as int,
            ),
        lane_major(hstride, vstride) ==> forall|c: int|
            0 <= c < 16 && !(l0 <= c < l0 + size) ==> #[trigger] lm_lane(final(r)@, c) == lm_lane(old(r)@, c),
{
    proof {assert(b@.len() == b.len());}
    let ghost r0 = r@;
    let ghost hs = hstride as int;
    let ghost vs = vstride as int;
    proof {
        lemma_kx(hs);
        lemma_kx(vs);
    }
    let base = p - 4 * hstride;
    if vstride == 1 {
        proof {
            assert((size - 1) * vstride == size - 1) by (nonlinear_arith)
                requires
                    vstride == 1,
            ;
        }
        // A horizontal edge: each row is contiguous.
        let mut k: usize = 0;
        while k < 8
            invariant
                l0 + size <= 16,
                b@.len() <= usize::MAX,
                k <= 8,
                run_ok(b@.len(), p as int, hstride as int, vstride as int, size as int),
                vstride == 1,
                base == p - 4 * hstride,
                hs == hstride as int,
                r0.len() == 128,
                forall|kk: int, i: int|
                    #[trigger] gat(kk, i) && 0 <= kk < k && 0 <= i < size ==> r@[16 * kk + l0 + i] == b@[base + kx(kk, hs) + i],
                forall|kk: int, c: int|
                    #[trigger] gat(kk, c) && 0 <= kk < 8 && 0 <= c < 16 && !(l0 <= c < l0 + size) ==> r@[16 * kk + c] == r0[16 * kk + c],
            decreases 8 - k,
        {
            proof {
                assert(k * hstride <= 7 * hstride) by (nonlinear_arith)
                    requires k < 8, hstride >= 1;
            }
            let s = base + k * hstride;
            let mut i: usize = 0;
            while i < size
                invariant
                    l0 + size <= 16,
                    b@.len() <= usize::MAX,
                    i <= size,
                    k < 8,
                    s + size <= b@.len(),
                    s == base + kx(k as int, hs),
                    r0.len() == 128,
                    forall|kk: int, i: int|
                        #[trigger] gat(kk, i) && 0 <= kk < k && 0 <= i < size ==> r@[16 * kk + l0 + i] == b@[base + kx(kk, hs) + i],
                    forall|kk: int, c: int|
                        #[trigger] gat(kk, c) && 0 <= kk < 8 && 0 <= c < 16 && !(l0 <= c < l0 + size) ==> r@[16 * kk + c] == r0[16 * kk + c],
                    forall|ii: int| #[trigger] gat(k as int, ii) && 0 <= ii < i ==> r@[16 * k + l0 + ii] == b@[s + ii],
                decreases size - i,
            {
                r[16 * k + l0 + i] = get(b, s + i);
                i = i + 1;
            }
            k = k + 1;
        }
        proof {
            lemma_gather_rows(b@, r@, r0, p as int, hs, size as int, l0 as int);
        }
    } else if hstride == 1 {
        // A vertical edge: each lane's 8 bytes are contiguous; copied as
        // they are (lane `i` at `r[8 * i..]`), and `to_rows` transposes.
        let rs: &mut [u8] = r;
        let mut i: usize = 0;
        while i < size
            invariant
                b@.len() <= usize::MAX,
                l0 + size <= 16,
                i <= size,
                run_ok(b@.len(), p as int, hstride as int, vstride as int, size as int),
                hstride == 1,
                base == p - 4,
                rs@.len() == 128,
                r0.len() == 128,
                vs == vstride as int,
                forall|a: int, b: int| #![trigger kx(a, vs), kx(b, vs)] 0 <= a < b ==> kx(a, vs) + vs <= kx(b, vs),
                forall|a: int| 0 <= a ==> #[trigger] kx(a, vs) >= 0,
                forall|ii: int| 0 <= ii < i ==> lm_lane(rs@, l0 + ii) == lf_lane(b@, p + #[trigger] kx(ii, vs), 1),
                forall|j: int| 0 <= j < 128 && !(8 * l0 <= j < 8 * (l0 + i)) ==> rs@[j] == r0[j],
            decreases size - i,
        {
            proof {
                assert(i * vstride <= (size - 1) * vstride) by (nonlinear_arith)
                    requires i < size, vstride >= 1;
                assert(i * vstride == kx(i as int, vs));
            }
            copy_in(rs, 8 * (l0 + i), b, base + i * vstride, 8);
            i = i + 1;
        }
        proof {
            assert forall|c: int| 0 <= c < 16 && !(l0 <= c < l0 + size) implies #[trigger] lm_lane(rs@, c) == lm_lane(
                r0,
                c,
            ) by {}
        }
    } else {
        let mut i: usize = 0;
        while i < size
            invariant
                l0 + size <= 16,
                b@.len() <= usize::MAX,
                i <= size,
                run_ok(b@.len(), p as int, hstride as int, vstride as int, size as int),
                base == p - 4 * hstride,
            decreases size - i,
        {
            proof {
                assert(i * vstride <= (size - 1) * vstride) by (nonlinear_arith)
                    requires i < size, vstride >= 1;
            }
            let q = base + i * vstride;
            let mut k: usize = 0;
            while k < 8
                invariant
                    l0 + size <= 16,
                    b@.len() <= usize::MAX,
                    k <= 8,
                    i < size,
                    hstride >= 1,
                    q + 7 * hstride < b@.len(),
                decreases 8 - k,
            {
                proof {
                    assert(k * hstride <= 7 * hstride) by (nonlinear_arith)
                        requires k < 8, hstride >= 1;
                }
                r[16 * k + l0 + i] = get(b, q + k * hstride);
                k = k + 1;
            }
            i = i + 1;
        }
    }
}

/// Writes rows `p2..q2` of `size` lanes back (`gather`'s inverse).
#[inline(always)]
fn scatter(b: &mut [u8], p: usize, hstride: usize, vstride: usize, size: usize, r: &[u8; 128], l0: usize)
    requires
        run_ok(old(b)@.len(), p as int, hstride as int, vstride as int, size as int),
        l0 + size <= 16,
    ensures
        final(b)@.len() == old(b)@.len(),
        vstride == 1 && hstride >= size ==> forall|l: int|
            0 <= l < size ==> lf_lane(final(b)@, p + #[trigger] kx(l, vstride as int), hstride as int) == mix(
                lf_lane(old(b)@, p + kx(l, vstride as int), hstride as int),
                blk_lane(r@, l0 + l),
            ),
        lane_major(hstride, vstride) && vstride >= 8 ==> forall|l: int|
            0 <= l < size ==> lf_lane(final(b)@, p + #[trigger] kx(l, vstride as int), hstride as int) == lm_lane(
                r@,
                l0 + l,
            ),
        lanes_apart(hstride as int, vstride as int, size as int) ==> forall|j: int|
            0 <= j < old(b)@.len() && !lane_cov(j, p as int, hstride as int, vstride as int, size as int) ==> final(b)@[j]
                == old(b)@[j],
{
    proof {assert(b@.len() == b.len());}
    let ghost b0 = b@;
    let ghost hs = hstride as int;
    let ghost vs = vstride as int;
    proof {
        lemma_kx(hs);
        lemma_kx(vs);
    }
    let base = p - 4 * hstride;
    if vstride == 1 {
        proof {
            assert((size - 1) * vstride == size - 1) by (nonlinear_arith)
                requires
                    vstride == 1,
            ;
        }
        let mut k: usize = 1;
        while k < 7
            invariant
                l0 + size <= 16,
                b@.len() <= usize::MAX,
                1 <= k <= 7,
                run_ok(b@.len(), p as int, hstride as int, vstride as int, size as int),
                vstride == 1,
                base == p - 4 * hstride,
                b@.len() == old(b)@.len(),
                b0.len() == b@.len(),
                hs == hstride as int,
                vs == 1,
                hstride >= size ==> forall|kk: int, i: int|
                    #[trigger] gat(kk, i) && 1 <= kk < k && 0 <= i < size ==> b@[base + kx(kk, hs) + i] == r@[16 * kk + l0 + i],
                forall|j: int| 0 <= j < b0.len() ==> b@[j] == b0[j] || lane_cov6(j, p as int, hs, vs, size as int),
            decreases 7 - k,
        {
            proof {
                assert(k * hstride <= 7 * hstride) by (nonlinear_arith)
                    requires k < 8, hstride >= 1;
            }
            let s = base + k * hstride;
            let mut i: usize = 0;
            while i < size
                invariant
                    l0 + size <= 16,
                    b@.len() <= usize::MAX,
                    i <= size,
                    k < 7,
                    s + size <= b@.len(),
                    b@.len() == old(b)@.len(),
                    s == base + kx(k as int, hs),
                    b0.len() == b@.len(),
                    hs == hstride as int,
                    hs >= 1,
                    vs == 1,
                    1 <= k,
                    base == p - 4 * hstride,
                    hstride >= size ==> forall|kk: int, i: int|
                        #[trigger] gat(kk, i) && 1 <= kk < k && 0 <= i < size ==> b@[base + kx(kk, hs) + i] == r@[16 * kk + l0 + i],
                    hstride >= size ==> forall|ii: int|
                        #[trigger] gat(k as int, ii) && 0 <= ii < i ==> b@[s + ii] == r@[16 * k + l0 + ii],
                    forall|j: int| 0 <= j < b0.len() ==> b@[j] == b0[j] || lane_cov6(j, p as int, hs, vs, size as int),
                decreases size - i,
            {
                let ghost b1 = b@;
                set(b, s + i, r[16 * k + l0 + i]);
                proof {
                    lemma_kx(hs);
                    assert(kx(i as int, vs) == i);
                    assert(kx(1, hs) == hs && kx(2, hs) == 2 * hs && kx(3, hs) == 3 * hs && kx(4, hs) == 4 * hs && kx(
                        5,
                        hs,
                    ) == 5 * hs && kx(6, hs) == 6 * hs);
                    assert(lane_has6(s + i, p as int, hs, vs, i as int));
                    assert(lane_cov6(s + i, p as int, hs, vs, size as int));
                    assert forall|j: int| 0 <= j < b0.len() implies b@[j] == b0[j] || lane_cov6(
                        j,
                        p as int,
                        hs,
                        vs,
                        size as int,
                    ) by {
                        if j != s + i {
                            assert(b@[j] == b1[j]);
                        }
                    }
                    if hstride >= size {
                        assert forall|kk: int, i2: int|
                            #[trigger] gat(kk, i2) && 1 <= kk < k && 0 <= i2 < size implies b@[base + kx(kk, hs) + i2] == r@[16 * kk + l0 + i2] by {
                            assert(kx(kk, hs) + hs <= kx(k as int, hs));
                            assert(b1[base + kx(kk, hs) + i2] == r@[16 * kk + l0 + i2]);
                        }
                    }
                }
                i = i + 1;
            }
            k = k + 1;
        }
        proof {
            lemma_scatter_rows(b0, b@, r@, p as int, hs, size as int, l0 as int);
        }
    } else if hstride == 1 {
        // Lane-major (`to_lanes` has transposed back): bytes 1..7 of each.
        let rs: &[u8] = r;
        let mut i: usize = 0;
        while i < size
            invariant
                l0 + size <= 16,
                b@.len() <= usize::MAX,
                i <= size,
                run_ok(b@.len(), p as int, hstride as int, vstride as int, size as int),
                hstride == 1,
                base == p - 4,
                b@.len() == old(b)@.len(),
                rs@.len() == 128,
                b0.len() == b@.len(),
                vs == vstride as int,
                hs == 1,
                forall|a: int, b: int| #![trigger kx(a, vs), kx(b, vs)] 0 <= a < b ==> kx(a, vs) + vs <= kx(b, vs),
                forall|a: int| 0 <= a ==> #[trigger] kx(a, vs) >= 0,
                vstride >= 8 ==> forall|ii: int|
                    0 <= ii < i ==> lf_lane(b@, p + #[trigger] kx(ii, vs), 1) == lm_lane(rs@, l0 + ii),
                forall|j: int| 0 <= j < b0.len() ==> b@[j] == b0[j] || lane_cov(j, p as int, hs, vs, size as int),
            decreases size - i,
        {
            proof {
                assert(i * vstride <= (size - 1) * vstride) by (nonlinear_arith)
                    requires i < size, vstride >= 1;
                assert(i * vstride == kx(i as int, vs));
            }
            let ghost b1 = b@;
            let ghost d = base + i * vstride;
            copy_in(b, base + i * vstride, rs, 8 * (l0 + i), 8);
            proof {
                assert forall|j: int| 0 <= j < b0.len() implies b@[j] == b0[j] || lane_cov(
                    j,
                    p as int,
                    hs,
                    vs,
                    size as int,
                ) by {
                    if d <= j < d + 8 {
                        assert(lane_has(j, p as int, hs, vs, i as int));
                    } else {
                        assert(b@[j] == b1[j]);
                    }
                }
                if vstride >= 8 {
                    assert forall|ii: int| 0 <= ii < i implies lf_lane(b@, p + #[trigger] kx(ii, vs), 1) == lm_lane(
                        rs@,
                        l0 + ii,
                    ) by {
                        assert(kx(ii, vs) + vs <= kx(i as int, vs));
                        assert(lf_lane(b@, p + kx(ii, vs), 1) == lf_lane(b1, p + kx(ii, vs), 1));
                    }
                }
            }
            i = i + 1;
        }
    } else {
        let mut i: usize = 0;
        while i < size
            invariant
                l0 + size <= 16,
                b@.len() <= usize::MAX,
                i <= size,
                run_ok(b@.len(), p as int, hstride as int, vstride as int, size as int),
                base == p - 4 * hstride,
                b@.len() == old(b)@.len(),
            decreases size - i,

        {
            proof {
                assert(i * vstride <= (size - 1) * vstride) by (nonlinear_arith)
                    requires i < size, vstride >= 1;
            }
            let q = base + i * vstride;
            let mut k: usize = 1;
            while k < 7
                invariant
                    l0 + size <= 16,
                    b@.len() <= usize::MAX,
                    1 <= k <= 7,
                    i < size,
                    hstride >= 1,
                    q + 7 * hstride < b@.len(),
                    b@.len() == old(b)@.len(),
                decreases 7 - k,
            {
                proof {
                    assert(k * hstride <= 7 * hstride) by (nonlinear_arith)
                        requires k < 8, hstride >= 1;
                }
                set(b, q + k * hstride, r[16 * k + l0 + i]);
                k = k + 1;
            }
            i = i + 1;
        }
    }
}

/// The simple filter along `size` pixels (`SimpleVFilter16`,
/// `SimpleHFilter16`), all lanes at once.
pub fn simple_filter(b: &mut [u8], p: usize, hstride: usize, vstride: usize, size: usize, thresh: i32)
    requires
        run_ok(old(b)@.len(), p as int, hstride as int, vstride as int, size as int),
        0 <= thresh <= 0x1000,
    ensures
        final(b)@.len() == old(b)@.len(),
        lanes_apart(hstride as int, vstride as int, size as int) ==> final(b)@ == lf_run(
            old(b)@,
            p as int,
            hstride as int,
            vstride as int,
            size as nat,
            true,
            false,
            thresh as int,
            0,
            0,
        ),
{
    if thresh > 254 {
        simple_filter_ref(b, p, hstride, vstride, size, thresh);
        return;
    }
    let th = thresh as u8;
    if size == 16 {
        simple_block(b, p, hstride, vstride, 16, th);
    } else {
        simple_block(b, p, hstride, vstride, size, th);
    }
}

/// `simple_filter`'s body, inlined with `size` a constant.
#[inline(always)]
fn simple_block(b: &mut [u8], p: usize, hstride: usize, vstride: usize, size: usize, th: u8)
    requires
        run_ok(old(b)@.len(), p as int, hstride as int, vstride as int, size as int),
    ensures
        final(b)@.len() == old(b)@.len(),
        th <= 254 && lanes_apart(hstride as int, vstride as int, size as int) ==> final(b)@ == lf_run(
            old(b)@,
            p as int,
            hstride as int,
            vstride as int,
            size as nat,
            true,
            false,
            th as int,
            0,
            0,
        ),
{
    let ghost b0 = b@;
    let mut r: [u8; 128] = [0; 128];
    gather(b, p, hstride, vstride, size, &mut r, 0);
    let ghost r1 = r@;
    let lm = vstride != 1 && hstride == 1;
    if lm {
        shuffle_block(&mut r, 4);
        proof {
            lemma_shuf4(r1);
        }
    }
    let ghost ra = r@;
    simple_lanes(&mut r, th);
    let ghost rb = r@;
    if lm {
        shuffle_block(&mut r, 3);
        proof {
            lemma_shuf3(rb);
        }
    }
    scatter(b, p, hstride, vstride, size, &r, 0);
    proof {
        if th <= 254 && lanes_apart(hstride as int, vstride as int, size as int) {
            lemma_block_ends(b0, b@, p as int, hstride as int, vstride as int, size as int, 0, r1, ra, rb, r@);
            lemma_block_done(
                b0,
                b@,
                p as int,
                hstride as int,
                vstride as int,
                size as int,
                0,
                ra,
                rb,
                true,
                false,
                th as int,
                0,
                0,
            );
        }
    }
}

/// `DoFilter2_SSE2` on every lane of a block.
#[inline(always)]
fn simple_lanes(r: &mut [u8; 128], th: u8)
    ensures
        th <= 254 ==> forall|j: int| 0 <= j < 16 ==> #[trigger] blk_lane(final(r)@, j) == lf_simple(blk_lane(old(r)@, j), th as int),
{
    let ghost r0 = r@;
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            th <= 254 ==> forall|j: int| 0 <= j < i ==> #[trigger] blk_lane(r@, j) == lf_simple(blk_lane(r0, j), th as int),
            forall|j: int| i <= j < 16 ==> #[trigger] blk_lane(r@, j) == blk_lane(r0, j),
        decreases 16 - i,
    {
        let ghost x = blk_lane(r@, i as int);
        let ghost r1 = r@;
        assert(x == blk_lane(r0, i as int));
        let p1 = r[32 + i];
        let p0 = r[48 + i];
        let q0 = r[64 + i];
        let q1 = r[80 + i];
        let m = bmask(needs_filter8(p1, p0, q0, q1, th));
        let a = and8(base_delta(sb(p1), sb(p0), sb(q0), sb(q1)), m);
        let v3 = sshr3(addc(a, 3));
        let v4 = sshr3(addc(a, 4));
        r[48 + i] = ub(adds(sb(p0), v3));
        r[64 + i] = ub(subs(sb(q0), v4));
        proof {
            if th <= 254 {
                assert(blk_lane(r@, i as int) == lf_simple(x, th as int));
            }
            assert forall|j: int| 0 <= j < 16 && j != i implies #[trigger] blk_lane(r@, j) == blk_lane(r1, j) by {}
        }
        i = i + 1;
    }
}



/// `ComplexMask_SSE2` and `GetNotHEV_SSE2` for lane `i`: whether to filter,
/// and whether the edge variance is low.
#[inline(always)]
fn mask_hev(r: &[u8; 128], i: usize, th: u8, it: u8, ht: u8) -> (m: (u8, u8))
    requires
        i < 16,
    ensures
        th <= 254 ==> m.0 == (if lf_normal_yes(blk_lane(r@, i as int), th as int, it as int) { 0xffu8 } else { 0u8 }),
        m.1 == (if lf_hev(blk_lane(r@, i as int), ht as int) { 0u8 } else { 0xffu8 }),
{
    let p3 = r[i];
    let p2 = r[16 + i];
    let p1 = r[32 + i];
    let p0 = r[48 + i];
    let q0 = r[64 + i];
    let q1 = r[80 + i];
    let q2 = r[96 + i];
    let q3 = r[112 + i];
    let d10 = absd8(p1, p0);
    let e10 = absd8(q1, q0);
    let m1 = if d10 > e10 { d10 } else { e10 };
    let d32 = absd8(p3, p2);
    let d21 = absd8(p2, p1);
    let e32 = absd8(q3, q2);
    let e21 = absd8(q2, q1);
    let m2 = if d32 > d21 { d32 } else { d21 };
    let m3 = if e32 > e21 { e32 } else { e21 };
    let m4 = if m2 > m3 { m2 } else { m3 };
    let mx = if m1 > m4 { m1 } else { m4 };
    let ma = bmask(mx <= it);
    let mb = bmask(needs_filter8(p1, p0, q0, q1, th));
    proof {
        assert((ma == 0 || ma == 0xff) && (mb == 0 || mb == 0xff) ==> (ma & mb) == (if ma == 0xff && mb == 0xff {
            0xffu8
        } else {
            0u8
        })) by (bit_vector);
    }
    let mask = ma & mb;
    (mask, bmask(m1 <= ht))
}

/// `lanes4`'s arithmetic on one lane is the subblock filter.
proof fn lemma_lane4(
    x: Edge8,
    e: int,
    i: int,
    h: int,
    yes: bool,
    hv: bool,
    o1: int,
    d: int,
    t1: int,
    t2: int,
    t3: int,
    t3d: int,
    o: Edge8,
)
    requires
        px8(x),
        yes == lf_normal_yes(x, e, i),
        hv == lf_hev(x, h),
        o1 == (if hv { lf_c(x.p1 - x.q1) } else { 0 }),
        d == lf_c(x.q0 - x.p0),
        t1 == (if yes { lf_c(lf_c(lf_c(o1 + d) + d) + d) } else { 0 }),
        t2 == (if t1 + 3 > 127 { 127 } else { t1 + 3 }) / 8,
        t3 == (if t1 + 4 > 127 { 127 } else { t1 + 4 }) / 8,
        t3d == (if hv { 0 } else { (t3 + 129) / 2 - 64 }),
        o == (Edge8 {
            p3: x.p3,
            p2: x.p2,
            p1: lf_c(x.p1 - 128 + t3d) + 128,
            p0: lf_c(x.p0 - 128 + t2) + 128,
            q0: lf_c(x.q0 - 128 - t3) + 128,
            q1: lf_c(x.q1 - 128 - t3d) + 128,
            q2: x.q2,
            q3: x.q3,
        }),
    ensures
        o == lf_subblock(x, e, i, h),
{
    if yes {
        assert(t1 == lf_w(hv, x));
    }
}

/// `lanes6`'s arithmetic on one lane is the macroblock-edge filter.
proof fn lemma_lane6(
    x: Edge8,
    e: int,
    i: int,
    h: int,
    yes: bool,
    hv: bool,
    w: int,
    f1: int,
    v3: int,
    v4: int,
    p0a: int,
    q0a: int,
    f2: int,
    d2: int,
    d1: int,
    d0: int,
    o: Edge8,
)
    requires
        px8(x),
        yes == lf_normal_yes(x, e, i),
        hv == lf_hev(x, h),
        w == lf_c(lf_c(x.p1 - x.q1) + 3 * (x.q0 - x.p0)),
        f1 == (if yes && hv { w } else { 0 }),
        v3 == (if f1 + 3 > 127 { 127 } else { f1 + 3 }) / 8,
        v4 == (if f1 + 4 > 127 { 127 } else { f1 + 4 }) / 8,
        p0a == lf_c(x.p0 - 128 + v3),
        q0a == lf_c(x.q0 - 128 - v4),
        f2 == (if yes && !hv { w } else { 0 }),
        d2 == lf_c((9 * f2 + 63) / 128),
        d1 == lf_c((18 * f2 + 63) / 128),
        d0 == lf_c((27 * f2 + 63) / 128),
        o == (Edge8 {
            p3: x.p3,
            p2: lf_c(x.p2 - 128 + d2) + 128,
            p1: lf_c(x.p1 - 128 + d1) + 128,
            p0: lf_c(p0a + d0) + 128,
            q0: lf_c(q0a - d0) + 128,
            q1: lf_c(x.q1 - 128 - d1) + 128,
            q2: lf_c(x.q2 - 128 - d2) + 128,
            q3: x.q3,
        }),
    ensures
        o == lf_mbedge(x, e, i, h),
{
}

/// `FilterLoop24`'s lanes (`DoFilter4_SSE2`).
#[inline(never)]
fn lanes4(r: &mut [u8; 128], th: u8, it: u8, ht: u8)
    ensures
        th <= 254 ==> forall|j: int| 0 <= j < 16 ==> #[trigger] blk_lane(final(r)@, j) == lf_subblock(
            blk_lane(old(r)@, j),
            th as int,
            it as int,
            ht as int,
        ),
{
    let ghost r0 = r@;
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            th <= 254 ==> forall|j: int| 0 <= j < i ==> #[trigger] blk_lane(r@, j) == lf_subblock(
                blk_lane(r0, j),
                th as int,
                it as int,
                ht as int,
            ),
            forall|j: int| i <= j < 16 ==> #[trigger] blk_lane(r@, j) == blk_lane(r0, j),
        decreases 16 - i,
    {
        let ghost x = blk_lane(r@, i as int);
        let ghost r1 = r@;
        assert(x == blk_lane(r0, i as int));
        let (mask, not_hev) = mask_hev(r, i, th, it, ht);
        proof {
            assert(not_hev == 0xffu8 ==> !not_hev == 0u8) by (bit_vector);
            assert(not_hev == 0u8 ==> !not_hev == 0xffu8) by (bit_vector);
        }
        let p1 = sb(r[32 + i]);
        let p0 = sb(r[48 + i]);
        let q0 = sb(r[64 + i]);
        let q1 = sb(r[80 + i]);
        let t1 = and8(subs(p1, q1), !not_hev);
        let t2 = subs(q0, p0);
        let ghost o1 = t1 as int;
        let ghost d = t2 as int;
        let t1 = and8(adds(adds(adds(t1, t2), t2), t2), mask);
        let ghost g1 = t1 as int;
        let t2 = sshr3(addc(t1, 3));
        let t3 = sshr3(addc(t1, 4));
        let np0 = adds(p0, t2);
        let nq0 = subs(q0, t3);
        // `(t3 + 1) >> 1`, signed, as `_mm_avg_epu8` computes it.
        proof {
            assert((((t3 as u8) ^ 0x80u8) as i32) == (t3 as i32) + 128) by (bit_vector);
        }
        let t3b = ((((t3 as u8) ^ 0x80u8) as u16 + 1) / 2) as u8;
        let t3d = and8((t3b as i16 - 64) as i8, not_hev);
        r[32 + i] = ub(adds(p1, t3d));
        r[48 + i] = ub(np0);
        r[64 + i] = ub(nq0);
        r[80 + i] = ub(subs(q1, t3d));
        proof {
            if th <= 254 {
                lemma_lane4(
                    x,
                    th as int,
                    it as int,
                    ht as int,
                    mask == 0xff,
                    not_hev == 0,
                    o1,
                    d,
                    g1,
                    t2 as int,
                    t3 as int,
                    t3d as int,
                    blk_lane(r@, i as int),
                );
            }
            assert forall|j: int| 0 <= j < 16 && j != i implies #[trigger] blk_lane(r@, j) == blk_lane(r1, j) by {}
        }
        i = i + 1;
    }
}

/// `FilterLoop26`'s lanes (`DoFilter6_SSE2`).
#[inline(never)]
fn lanes6(r: &mut [u8; 128], th: u8, it: u8, ht: u8)
    ensures
        th <= 254 ==> forall|j: int| 0 <= j < 16 ==> #[trigger] blk_lane(final(r)@, j) == lf_mbedge(
            blk_lane(old(r)@, j),
            th as int,
            it as int,
            ht as int,
        ),
{
    let ghost r0 = r@;
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            th <= 254 ==> forall|j: int| 0 <= j < i ==> #[trigger] blk_lane(r@, j) == lf_mbedge(
                blk_lane(r0, j),
                th as int,
                it as int,
                ht as int,
            ),
            forall|j: int| i <= j < 16 ==> #[trigger] blk_lane(r@, j) == blk_lane(r0, j),
        decreases 16 - i,
    {
        let ghost x = blk_lane(r@, i as int);
        let ghost r1 = r@;
        assert(x == blk_lane(r0, i as int));
        let (mask, not_hev) = mask_hev(r, i, th, it, ht);
        proof {
            assert((mask == 0 || mask == 0xff) && (not_hev == 0 || not_hev == 0xff) ==> (mask & !not_hev) == (if mask
                == 0xff && not_hev == 0 {
                0xffu8
            } else {
                0u8
            }) && (mask & not_hev) == (if mask == 0xff && not_hev == 0xff {
                0xffu8
            } else {
                0u8
            })) by (bit_vector);
        }
        let p2 = sb(r[16 + i]);
        let p1 = sb(r[32 + i]);
        let p0 = sb(r[48 + i]);
        let q0 = sb(r[64 + i]);
        let q1 = sb(r[80 + i]);
        let q2 = sb(r[96 + i]);
        let a = base_delta(p1, p0, q0, q1);
        // The simple filter where the variance is high.
        let f = and8(a, mask & !not_hev);
        let ghost f1 = f as int;
        let v3 = sshr3(addc(f, 3));
        let v4 = sshr3(addc(f, 4));
        let p0 = adds(p0, v3);
        let q0 = subs(q0, v4);
        // The strong filter where it is low.
        let f = and8(a, mask & not_hev) as i16;
        let ghost f2 = f as int;
        let f9 = 9 * f;
        let a2 = f9 + 63;
        let a1 = a2 + f9;
        let a0 = a1 + f9;
        let d2 = shr7(a2);
        let d1 = shr7(a1);
        let d0 = shr7(a0);
        r[16 + i] = ub(adds(p2, d2));
        r[32 + i] = ub(adds(p1, d1));
        r[48 + i] = ub(adds(p0, d0));
        r[64 + i] = ub(subs(q0, d0));
        r[80 + i] = ub(subs(q1, d1));
        r[96 + i] = ub(subs(q2, d2));
        proof {
            if th <= 254 {
                lemma_lane6(
                    x,
                    th as int,
                    it as int,
                    ht as int,
                    mask == 0xff,
                    not_hev == 0,
                    a as int,
                    f1,
                    v3 as int,
                    v4 as int,
                    p0 as int,
                    q0 as int,
                    f2,
                    d2 as int,
                    d1 as int,
                    d0 as int,
                    blk_lane(r@, i as int),
                );
            }
            assert forall|j: int| 0 <= j < 16 && j != i implies #[trigger] blk_lane(r@, j) == blk_lane(r1, j) by {}
        }
        i = i + 1;
    }
}

// ---------------------------------------------------------------------------
// The loop filter in SSE2 registers
// ---------------------------------------------------------------------------
//
// On x86-64 the normal filters work on the sixteen lanes of an edge as
// eight SSE2 vectors, one per row across the edge (`p3 .. q3`), with
// libwebp's SSE2 arithmetic (`src/dsp/dec_sse2.c`) written as intrinsics,
// for SSE2 and for NEON (the kernels are generic over the vector type):
// no block in memory, and no shuffles for a horizontal edge. A vertical
// edge is loaded as sixteen 8-byte rows and transposed with interleaves.
// Each vector operation below states what it does to every byte, as the
// scalar helpers above do for one lane, so the kernels are proven lane by
// lane against the same `lemma_lane4` and `lemma_lane6`, and the loads and
// stores against the same `lemma_block_done`.

/// Byte `i` of a vector's bytes.
pub open spec fn ub_at(s: Seq<u8>, i: int) -> int {
    s[i] as int
}

/// Byte `i`, signed.
pub open spec fn sb_at(s: Seq<u8>, i: int) -> int {
    s8(s[i])
}

/// 16-bit lane `k` of a vector's bytes, signed.
pub open spec fn sw_at(s: Seq<u8>, k: int) -> int {
    s16(u16s(s)[k])
}

/// A 16-byte vector type the loop filter can run on: SSE2's `__m128i` and
/// NEON's `uint8x16_t`. Each operation states what it does to every byte
/// (or 16-bit lane), the same for both, so the kernels and the loads and
/// stores below are written and proven once, and each architecture gives
/// only these small bodies, each proven from its own intrinsics' specs.
pub trait Lfv: Copy + Sized {
    /// The vector's sixteen bytes in memory order.
    spec fn by(self) -> Seq<u8>;

    /// What the operations need of the CPU.
    spec fn ok() -> bool;

    proof fn lemma_len(self)
        ensures
            self.by().len() == 16,
    ;

    fn vzero() -> (r: Self)
        requires
            Self::ok(),
    ;

    /// A byte in every lane.
    fn vsplat(x: u8) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int| 0 <= i < 16 ==> #[trigger] ub_at(r.by(), i) == x,
    ;

    /// The sign bits.
    fn vsign() -> (r: Self)
        requires
            Self::ok(),
        ensures
            r.by() == splat8(0x80u8, 16),
    ;

    /// Pixels to signed bytes and back: the sign bits flipped.
    fn vflip(a: Self, s: Self) -> (r: Self)
        requires
            Self::ok(),
            s.by() == splat8(0x80u8, 16),
        ensures
            forall|i: int| 0 <= i < 16 ==> #[trigger] sb_at(r.by(), i) == ub_at(a.by(), i) - 128,
            forall|i: int| 0 <= i < 16 ==> #[trigger] ub_at(r.by(), i) == sb_at(a.by(), i) + 128,
    ;

    /// `|a - b|` on unsigned bytes.
    fn vabsd(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int| 0 <= i < 16 ==> #[trigger] ub_at(r.by(), i) == lf_abs(ub_at(a.by(), i) - ub_at(b.by(), i)),
    ;

    /// The larger of each pair of unsigned bytes.
    fn vmax(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int|
                0 <= i < 16 ==> #[trigger] ub_at(r.by(), i) == (if ub_at(a.by(), i) > ub_at(b.by(), i) {
                    ub_at(a.by(), i)
                } else {
                    ub_at(b.by(), i)
                }),
    ;

    /// `a <= t` on unsigned bytes, as a mask.
    fn vle(a: Self, t: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int| 0 <= i < 16 ==> #[trigger] ub_at(r.by(), i) == (if ub_at(a.by(), i) <= ub_at(t.by(), i) { 255int } else { 0 }),
    ;

    /// Unsigned saturating addition.
    fn vaddus(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int|
                0 <= i < 16 ==> #[trigger] ub_at(r.by(), i) == (if ub_at(a.by(), i) + ub_at(b.by(), i) > 255 {
                    255
                } else {
                    ub_at(a.by(), i) + ub_at(b.by(), i)
                }),
    ;

    /// Each byte halved.
    fn vhalf(d: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int| 0 <= i < 16 ==> #[trigger] ub_at(r.by(), i) == ub_at(d.by(), i) / 2,
    ;

    /// `a & m`, where `m` is a byte mask.
    fn vand(a: Self, m: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int|
                0 <= i < 16 ==> (ub_at(m.by(), i) == 255 ==> #[trigger] ub_at(r.by(), i) == ub_at(a.by(), i)) && (ub_at(m.by(), i) == 0
                    ==> ub_at(r.by(), i) == 0),
            forall|i: int|
                0 <= i < 16 ==> (ub_at(m.by(), i) == 255 ==> #[trigger] sb_at(r.by(), i) == sb_at(a.by(), i)) && (ub_at(m.by(), i) == 0
                    ==> sb_at(r.by(), i) == 0),
    ;

    /// `a & !m`, where `m` is a byte mask.
    fn vandnot(m: Self, a: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int|
                0 <= i < 16 ==> (ub_at(m.by(), i) == 0 ==> #[trigger] ub_at(r.by(), i) == ub_at(a.by(), i)) && (ub_at(m.by(), i) == 255
                    ==> ub_at(r.by(), i) == 0),
            forall|i: int|
                0 <= i < 16 ==> (ub_at(m.by(), i) == 0 ==> #[trigger] sb_at(r.by(), i) == sb_at(a.by(), i)) && (ub_at(m.by(), i) == 255
                    ==> sb_at(r.by(), i) == 0),
    ;

    /// Signed saturating addition.
    fn vadds(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int| 0 <= i < 16 ==> #[trigger] sb_at(r.by(), i) == lf_c(sb_at(a.by(), i) + sb_at(b.by(), i)),
    ;

    /// Signed saturating subtraction.
    fn vsubs(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int| 0 <= i < 16 ==> #[trigger] sb_at(r.by(), i) == lf_c(sb_at(a.by(), i) - sb_at(b.by(), i)),
    ;

    /// Signed saturating addition of a constant.
    fn vaddc(a: Self, c: i8) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int| 0 <= i < 16 ==> #[trigger] sb_at(r.by(), i) == lf_c(sb_at(a.by(), i) + c),
    ;

    /// `x >> 3` on signed bytes.
    fn vsshr3(x: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int| 0 <= i < 16 ==> #[trigger] sb_at(r.by(), i) == sb_at(x.by(), i) / 8,
    ;

    /// `(t + 1) >> 1` on signed bytes.
    fn vavg1(t: Self, s: Self) -> (r: Self)
        requires
            Self::ok(),
            s.by() == splat8(0x80u8, 16),
        ensures
            forall|i: int| 0 <= i < 16 ==> #[trigger] sb_at(r.by(), i) == (sb_at(t.by(), i) + 129) / 2 - 64,
    ;

    /// Nine times each signed byte of the low half, in 16-bit lanes.
    fn vnine_lo(f: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(r.by(), k) == 9 * sb_at(f.by(), k),
    ;

    /// `vnine_lo` for the high half.
    fn vnine_hi(f: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(r.by(), k) == 9 * sb_at(f.by(), 8 + k),
    ;

    /// 63 in every 16-bit lane.
    fn vk63() -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(r.by(), k) == 63,
    ;

    /// 16-bit addition where no lane overflows.
    fn vadd16(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
            forall|k: int| 0 <= k < 8 ==> -0x4000 <= #[trigger] sw_at(a.by(), k) < 0x4000,
            forall|k: int| 0 <= k < 8 ==> -0x4000 <= #[trigger] sw_at(b.by(), k) < 0x4000,
        ensures
            forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(r.by(), k) == sw_at(a.by(), k) + sw_at(b.by(), k),
    ;

    /// `(x >> 7)` of sixteen 16-bit lanes, saturated to signed bytes.
    fn vshr7(lo: Self, hi: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            forall|i: int|
                0 <= i < 16 ==> #[trigger] sb_at(r.by(), i) == lf_c(
                    (if i < 8 {
                        sw_at(lo.by(), i)
                    } else {
                        sw_at(hi.by(), i - 8)
                    }) / 128,
                ),
    ;

    /// The interleaves of bytes and of 16-, 32- and 64-bit lanes, of the
    /// low halves and of the high halves.
    fn unpacklo8(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            r.by() == unpacklo8_lanes(a.by(), b.by()),
    ;

    fn unpackhi8(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            r.by() == unpackhi8_lanes(a.by(), b.by()),
    ;

    fn unpacklo16(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            u16s(r.by()) == unpacklo16_lanes(u16s(a.by()), u16s(b.by())),
    ;

    fn unpackhi16(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            u16s(r.by()) == unpackhi16_lanes(u16s(a.by()), u16s(b.by())),
    ;

    fn unpacklo32(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            u32s(r.by()) == unpacklo32_lanes(u32s(a.by()), u32s(b.by())),
    ;

    fn unpackhi32(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            u32s(r.by()) == unpackhi32_lanes(u32s(a.by()), u32s(b.by())),
    ;

    fn unpacklo64(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            u64s(r.by()) == unpacklo64_lanes(u64s(a.by()), u64s(b.by())),
    ;

    fn unpackhi64(a: Self, b: Self) -> (r: Self)
        requires
            Self::ok(),
        ensures
            u64s(r.by()) == unpackhi64_lanes(u64s(a.by()), u64s(b.by())),
    ;

    /// The 16 bytes at `s[i..i + 16]`.
    fn load16(s: &[u8], i: usize) -> (r: Self)
        requires
            Self::ok(),
            i + 16 <= s@.len(),
        ensures
            r.by() == s@.subrange(i as int, i + 16),
    ;

    /// The 8 bytes at `s[i..i + 8]` in the low half, zeros above.
    fn loadl8(s: &[u8], i: usize) -> (r: Self)
        requires
            Self::ok(),
            i + 8 <= s@.len(),
        ensures
            r.by() == s@.subrange(i as int, i + 8) + splat8(0u8, 8),
    ;

    /// Stores `v` at `s[i..i + 16]`.
    fn store16(s: &mut [u8], i: usize, v: Self)
        requires
            Self::ok(),
            i + 16 <= old(s)@.len(),
        ensures
            final(s)@ == old(s)@.subrange(0, i as int) + v.by() + old(s)@.subrange(i + 16, old(s)@.len() as int),
    ;

    /// Stores the low 8 bytes of `v` at `s[i..i + 8]`.
    fn storel8(s: &mut [u8], i: usize, v: Self)
        requires
            Self::ok(),
            i + 8 <= old(s)@.len(),
        ensures
            final(s)@ == old(s)@.subrange(0, i as int) + v.by().subrange(0, 8) + old(s)@.subrange(
                i + 8,
                old(s)@.len() as int,
            ),
    ;
}

/// The bytes of a vector.
pub open spec fn vb<V: Lfv>(v: V) -> Seq<u8> {
    v.by()
}

pub broadcast proof fn lemma_vb_len<V: Lfv>(v: V)
    ensures
        #[trigger] v.by().len() == 16,
{
    v.lemma_len();
}

/// Byte `i` of a vector.
pub open spec fn ubyte<V: Lfv>(v: V, i: int) -> int {
    ub_at(v.by(), i)
}

/// Byte `i` of a vector, signed.
pub open spec fn sbyte<V: Lfv>(v: V, i: int) -> int {
    sb_at(v.by(), i)
}

/// 16-bit lane `k` of a vector, signed.
pub open spec fn sword<V: Lfv>(v: V, k: int) -> int {
    sw_at(v.by(), k)
}

/// The rows of eight vectors.
pub open spec fn vrows<V: Lfv>(x: [V; 8]) -> Seq<Seq<u8>> {
    Seq::new(8, |k: int| vb(x[k]))
}

// SSE2's operations, each from its `_mm_*` intrinsics; `impl Lfv for
// __m128i` below hands them to the trait.

/// A signed byte in two's complement is its value.
proof fn lemma_s8_byte(v: int)
    requires
        -128 <= v <= 127,
    ensures
        s8((v % 256) as u8) == v,
{
}

/// `_mm_set1_epi8` of a byte.
#[inline(always)]
fn vsplat(x: u8) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] ub_at(b128(r), i) == x,
{
    proof {
        assert(x >= 128 ==> (x as i8) as i32 == (x as i32) - 256) by (bit_vector);
        assert(x < 128 ==> (x as i8) as i32 == (x as i32)) by (bit_vector);
    }
    _mm_set1_epi8(x as i8)
}

/// The sign bits (`_mm_set1_epi8(-128)`).
#[inline(always)]
fn vsign() -> (r: __m128i)
    ensures
        b128(r) == splat8(0x80u8, 16),
{
    let r = _mm_set1_epi8(-128);
    proof {
        assert(u8_of_i8(-128i8) == 0x80u8);
    }
    r
}

/// Pixels to signed bytes and back: the sign bits flipped.
#[inline(always)]
fn vflip(a: __m128i, s: __m128i) -> (r: __m128i)
    requires
        b128(s) == splat8(0x80u8, 16),
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] sb_at(b128(r), i) == ub_at(b128(a), i) - 128,
        forall|i: int| 0 <= i < 16 ==> #[trigger] ub_at(b128(r), i) == sb_at(b128(a), i) + 128,
{
    let r = _mm_xor_si128(a, s);
    proof {
        assert forall|i: int| 0 <= i < 16 implies sb_at(b128(r), i) == ub_at(b128(a), i) - 128 && ub_at(b128(r), i) == sb_at(b128(a), i)
            + 128 by {
            let x = b128(a)[i];
            assert(b128(r)[i] == x ^ 0x80u8);
            assert(((x ^ 0x80u8) as i32) == (if x >= 128 { (x as i32) - 128 } else { (x as i32) + 128 }))
                by (bit_vector);
        }
    }
    r
}

/// `MM_ABS`: `|a - b|` on unsigned bytes.
#[inline(always)]
fn vabsd(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] ub_at(b128(r), i) == lf_abs(ub_at(b128(a), i) - ub_at(b128(b), i)),
{
    let x = _mm_subs_epu8(a, b);
    let y = _mm_subs_epu8(b, a);
    let r = _mm_or_si128(x, y);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] ub_at(b128(r), i) == lf_abs(ub_at(b128(a), i) - ub_at(b128(b), i)) by {
            let u = b128(x)[i];
            let v = b128(y)[i];
            assert(b128(r)[i] == u | v);
            assert(u == 0 ==> (u | v) == v) by (bit_vector);
            assert(v == 0 ==> (u | v) == u) by (bit_vector);
        }
    }
    r
}

/// `_mm_max_epu8`.
#[inline(always)]
fn vmax(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        forall|i: int|
            0 <= i < 16 ==> #[trigger] ub_at(b128(r), i) == (if ub_at(b128(a), i) > ub_at(b128(b), i) {
                ub_at(b128(a), i)
            } else {
                ub_at(b128(b), i)
            }),
{
    let r = _mm_max_epu8(a, b);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] ub_at(b128(r), i) == (if ub_at(b128(a), i) > ub_at(b128(b), i) {
            ub_at(b128(a), i)
        } else {
            ub_at(b128(b), i)
        }) by {
            assert(b128(r)[i] == max_u8(b128(a), b128(b))[i]);
        }
    }
    r
}

/// `a <= t` on unsigned bytes, as a mask (`_mm_subs_epu8` and a compare
/// with zero).
#[inline(always)]
fn vle(a: __m128i, t: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] ub_at(b128(r), i) == (if ub_at(b128(a), i) <= ub_at(b128(t), i) { 255int } else { 0 }),
{
    let d = _mm_subs_epu8(a, t);
    let z = _mm_setzero_si128();
    let r = _mm_cmpeq_epi8(d, z);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] ub_at(b128(r), i) == (if ub_at(b128(a), i) <= ub_at(b128(t), i) {
            255int
        } else {
            0
        }) by {
            assert(b128(d)[i] == subs_u8(b128(a), b128(t))[i]);
            assert(b128(z)[i] == 0u8);
            assert(b128(r)[i] == cmpeq8(b128(d), b128(z))[i]);
        }
    }
    r
}

/// `_mm_adds_epu8`.
#[inline(always)]
fn vaddus(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        forall|i: int|
            0 <= i < 16 ==> #[trigger] ub_at(b128(r), i) == (if ub_at(b128(a), i) + ub_at(b128(b), i) > 255 {
                255
            } else {
                ub_at(b128(a), i) + ub_at(b128(b), i)
            }),
{
    let r = _mm_adds_epu8(a, b);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] ub_at(b128(r), i) == (if ub_at(b128(a), i) + ub_at(b128(b), i) > 255 {
            255
        } else {
            ub_at(b128(a), i) + ub_at(b128(b), i)
        }) by {
            assert(b128(r)[i] == adds_u8(b128(a), b128(b))[i]);
        }
    }
    r
}

/// Each byte halved (`_mm_srli_epi16` by one, and the bit shifted in from
/// the byte above masked off).
#[inline(always)]
fn vhalf(d: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] ub_at(b128(r), i) == ub_at(b128(d), i) / 2,
{
    let s = _mm_srli_epi16::<1>(d);
    let m = _mm_set1_epi8(0x7f);
    let r = _mm_and_si128(s, m);
    proof {
        reveal_with_fuel(pow2_spec, 2);
        assert(pow2_spec(1) == 2);
        lemma_u16s_len(b128(d));
        lemma_u16s_len(b128(s));
        assert forall|i: int| 0 <= i < 16 implies #[trigger] ub_at(b128(r), i) == ub_at(b128(d), i) / 2 by {
            let k = i / 2;
            let x = b128(d)[2 * k];
            let y = b128(d)[2 * k + 1];
            let l = u16s(b128(d))[k];
            let sh = u16s(b128(s))[k];
            assert(l == le16(x, y));
            assert(sh == srli16(u16s(b128(d)), 1)[k]);
            assert(sh == l / 2);
            lemma_u16_lane_bytes(b128(s), k);
            let s0 = b128(s)[2 * k];
            let s1 = b128(s)[2 * k + 1];
            assert(sh == l / 2 && l == (x as u16) | ((y as u16) << 8u16) && s0 == (sh & 0xff) as u8 && s1 == ((sh
                >> 8u16) & 0xff) as u8 ==> (s0 & 0x7fu8) == x / 2 && (s1 & 0x7fu8) == y / 2) by (bit_vector);
            assert(b128(m)[i] == 0x7fu8);
            assert(b128(r)[i] == b128(s)[i] & b128(m)[i]);
            assert(i == 2 * k || i == 2 * k + 1);
        }
    }
    r
}

/// `a & m`, where `m` is a byte mask.
#[inline(always)]
fn vand(a: __m128i, m: __m128i) -> (r: __m128i)
    ensures
        forall|i: int|
            0 <= i < 16 ==> (ub_at(b128(m), i) == 255 ==> #[trigger] ub_at(b128(r), i) == ub_at(b128(a), i)) && (ub_at(b128(m), i) == 0
                ==> ub_at(b128(r), i) == 0),
        forall|i: int|
            0 <= i < 16 ==> (ub_at(b128(m), i) == 255 ==> #[trigger] sb_at(b128(r), i) == sb_at(b128(a), i)) && (ub_at(b128(m), i) == 0
                ==> sb_at(b128(r), i) == 0),
{
    let r = _mm_and_si128(a, m);
    proof {
        assert forall|i: int| 0 <= i < 16 implies (ub_at(b128(m), i) == 255 ==> b128(r)[i] == b128(a)[i]) && (ub_at(b128(m), i)
            == 0 ==> b128(r)[i] == 0u8) by {
            let x = b128(a)[i];
            let y = b128(m)[i];
            assert(b128(r)[i] == x & y);
            assert(y == 0xffu8 ==> (x & y) == x) by (bit_vector);
            assert(y == 0u8 ==> (x & y) == 0u8) by (bit_vector);
        }
    }
    r
}

/// `a & !m`, where `m` is a byte mask (`_mm_andnot_si128(m, a)`).
#[inline(always)]
fn vandnot(m: __m128i, a: __m128i) -> (r: __m128i)
    ensures
        forall|i: int|
            0 <= i < 16 ==> (ub_at(b128(m), i) == 0 ==> #[trigger] ub_at(b128(r), i) == ub_at(b128(a), i)) && (ub_at(b128(m), i) == 255
                ==> ub_at(b128(r), i) == 0),
        forall|i: int|
            0 <= i < 16 ==> (ub_at(b128(m), i) == 0 ==> #[trigger] sb_at(b128(r), i) == sb_at(b128(a), i)) && (ub_at(b128(m), i) == 255
                ==> sb_at(b128(r), i) == 0),
{
    let r = _mm_andnot_si128(m, a);
    proof {
        assert forall|i: int| 0 <= i < 16 implies (ub_at(b128(m), i) == 0 ==> b128(r)[i] == b128(a)[i]) && (ub_at(b128(m), i)
            == 255 ==> b128(r)[i] == 0u8) by {
            let x = b128(a)[i];
            let y = b128(m)[i];
            assert(b128(r)[i] == !y & x);
            assert(y == 0u8 ==> (!y & x) == x) by (bit_vector);
            assert(y == 0xffu8 ==> (!y & x) == 0u8) by (bit_vector);
        }
    }
    r
}

/// `_mm_adds_epi8`.
#[inline(always)]
fn vadds(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] sb_at(b128(r), i) == lf_c(sb_at(b128(a), i) + sb_at(b128(b), i)),
{
    let r = _mm_adds_epi8(a, b);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(b128(r), i) == lf_c(sb_at(b128(a), i) + sb_at(b128(b), i)) by {
            let v = sat_s8(sb_at(b128(a), i) + sb_at(b128(b), i));
            assert(b128(r)[i] == adds_s8(b128(a), b128(b))[i]);
            lemma_s8_byte(v);
        }
    }
    r
}

/// `_mm_subs_epi8`.
#[inline(always)]
fn vsubs(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] sb_at(b128(r), i) == lf_c(sb_at(b128(a), i) - sb_at(b128(b), i)),
{
    let r = _mm_subs_epi8(a, b);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(b128(r), i) == lf_c(sb_at(b128(a), i) - sb_at(b128(b), i)) by {
            let v = sat_s8(sb_at(b128(a), i) - sb_at(b128(b), i));
            assert(b128(r)[i] == subs_s8(b128(a), b128(b))[i]);
            lemma_s8_byte(v);
        }
    }
    r
}

/// `_mm_adds_epi8` with a constant.
#[inline(always)]
fn vaddc(a: __m128i, c: i8) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] sb_at(b128(r), i) == lf_c(sb_at(b128(a), i) + c),
{
    let k = _mm_set1_epi8(c);
    let r = vadds(a, k);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(b128(r), i) == lf_c(sb_at(b128(a), i) + c) by {
            assert(b128(k)[i] == u8_of_i8(c));
            assert(sb_at(b128(k), i) == c);
        }
    }
    r
}

/// The bytes of the low half as the high bytes of 16-bit lanes
/// (`_mm_unpacklo_epi8` with zero below): each lane is its byte times 256.
#[inline(always)]
fn vhigh_lo(x: __m128i) -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(b128(r), k) == 256 * sb_at(b128(x), k),
{
    let z = _mm_setzero_si128();
    let r = _mm_unpacklo_epi8(z, x);
    proof {
        lemma_u16s_len(b128(r));
        assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(b128(r), k) == 256 * sb_at(b128(x), k) by {
            lemma_le16_value(b128(r)[2 * k], b128(r)[2 * k + 1]);
            assert(b128(r)[2 * k] == b128(z)[k]);
            assert(b128(r)[2 * k + 1] == b128(x)[k]);
        }
    }
    r
}

/// `vhigh_lo` for the high half.
#[inline(always)]
fn vhigh_hi(x: __m128i) -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(b128(r), k) == 256 * sb_at(b128(x), 8 + k),
{
    let z = _mm_setzero_si128();
    let r = _mm_unpackhi_epi8(z, x);
    proof {
        lemma_u16s_len(b128(r));
        assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(b128(r), k) == 256 * sb_at(b128(x), 8 + k) by {
            lemma_le16_value(b128(r)[2 * k], b128(r)[2 * k + 1]);
            assert(b128(r)[2 * k] == b128(z)[8 + k]);
            assert(b128(r)[2 * k + 1] == b128(x)[8 + k]);
        }
    }
    r
}

/// An arithmetic right shift of 16-bit lanes divides, rounding down.
proof fn lemma_srai_lanes(u: __m128i, r: __m128i, n: int, d: int)
    requires
        u16x8(r) == srai16(u16x8(u), n),
        (n == 7 && d == 128) || (n == 8 && d == 256) || (n == 11 && d == 2048),
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(b128(r), k) == sw_at(b128(u), k) / d,
{
    reveal_with_fuel(pow2_spec, 12);
    assert(pow2_spec(7) == 128 && pow2_spec(8) == 256 && pow2_spec(11) == 2048);
    lemma_u16s_len(b128(u));
    assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(b128(r), k) == sw_at(b128(u), k) / d by {
        let a = u16x8(u)[k];
        let q = s16(a) / d;
        assert(-256 <= q <= 255);
        assert(u16x8(r)[k] == (q % 0x10000) as u16);
    }
}

/// `_mm_packs_epi16`: sixteen 16-bit lanes to signed bytes, saturating.
#[inline(always)]
fn vpack(lo: __m128i, hi: __m128i) -> (r: __m128i)
    ensures
        forall|i: int|
            0 <= i < 16 ==> #[trigger] sb_at(b128(r), i) == lf_c(
                if i < 8 {
                    sw_at(b128(lo), i)
                } else {
                    sw_at(b128(hi), i - 8)
                },
            ),
{
    let r = _mm_packs_epi16(lo, hi);
    proof {
        lemma_u16s_len(b128(lo));
        lemma_u16s_len(b128(hi));
        assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(b128(r), i) == lf_c(
            if i < 8 {
                sw_at(b128(lo), i)
            } else {
                sw_at(b128(hi), i - 8)
            },
        ) by {
            assert(b128(r)[i] == packs16_lanes(u16x8(lo), u16x8(hi))[i]);
            assert(i / 16 == 0 && i % 16 == i);
            if i < 8 {
                lemma_s8_byte(sat_s8(sw_at(b128(lo), i)));
            } else {
                lemma_s8_byte(sat_s8(sw_at(b128(hi), i - 8)));
            }
        }
    }
    r
}

/// `SignedShift8b_SSE2`: `x >> 3` on signed bytes, through 16-bit lanes.
#[inline(always)]
fn vsshr3(x: __m128i) -> (r: __m128i)
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] sb_at(b128(r), i) == sb_at(b128(x), i) / 8,
{
    let ul = vhigh_lo(x);
    let uh = vhigh_hi(x);
    let lo = _mm_srai_epi16::<11>(ul);
    let hi = _mm_srai_epi16::<11>(uh);
    let r = vpack(lo, hi);
    proof {
        lemma_srai_lanes(ul, lo, 11, 2048);
        lemma_srai_lanes(uh, hi, 11, 2048);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(b128(r), i) == sb_at(b128(x), i) / 8 by {
            let s = sb_at(b128(x), i);
            assert((256 * s) / 2048 == s / 8);
            if i < 8 {
                assert(sw_at(b128(lo), i) == sw_at(b128(ul), i) / 2048);
            } else {
                assert(sw_at(b128(hi), i - 8) == sw_at(b128(uh), i - 8) / 2048);
            }
        }
    }
    r
}

/// `(t + 1) >> 1` on signed bytes, as `_mm_avg_epu8` computes it on the
/// bytes with their sign bits flipped.
#[inline(always)]
fn vavg1(t: __m128i, s: __m128i) -> (r: __m128i)
    requires
        b128(s) == splat8(0x80u8, 16),
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] sb_at(b128(r), i) == (sb_at(b128(t), i) + 129) / 2 - 64,
{
    let u = vflip(t, s);
    let z = _mm_setzero_si128();
    let a = _mm_avg_epu8(u, z);
    let k = _mm_set1_epi8(64);
    let r = _mm_sub_epi8(a, k);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(b128(r), i) == (sb_at(b128(t), i) + 129) / 2 - 64 by {
            assert(ub_at(b128(u), i) == sb_at(b128(t), i) + 128);
            assert(b128(z)[i] == 0u8);
            assert(b128(a)[i] == avg_u8(b128(u), b128(z))[i]);
            assert(b128(k)[i] == 64u8);
            assert(b128(r)[i] == sub8(b128(a), b128(k))[i]);
        }
    }
    r
}

/// The bytes of the low half, sign-extended to 16-bit lanes.
#[inline(always)]
fn vwiden_lo(f: __m128i) -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(b128(r), k) == sb_at(b128(f), k),
{
    let u = vhigh_lo(f);
    let r = _mm_srai_epi16::<8>(u);
    proof {
        lemma_srai_lanes(u, r, 8, 256);
        assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(b128(r), k) == sb_at(b128(f), k) by {
            assert(sw_at(b128(u), k) == 256 * sb_at(b128(f), k));
        }
    }
    r
}

/// The bytes of the high half, sign-extended to 16-bit lanes.
#[inline(always)]
fn vwiden_hi(f: __m128i) -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(b128(r), k) == sb_at(b128(f), 8 + k),
{
    let u = vhigh_hi(f);
    let r = _mm_srai_epi16::<8>(u);
    proof {
        lemma_srai_lanes(u, r, 8, 256);
        assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(b128(r), k) == sb_at(b128(f), 8 + k) by {
            assert(sw_at(b128(u), k) == 256 * sb_at(b128(f), 8 + k));
        }
    }
    r
}

/// `_mm_add_epi16` where no lane overflows.
#[inline(always)]
fn vadd16(a: __m128i, b: __m128i) -> (r: __m128i)
    requires
        forall|k: int| 0 <= k < 8 ==> -0x4000 <= #[trigger] sw_at(b128(a), k) < 0x4000,
        forall|k: int| 0 <= k < 8 ==> -0x4000 <= #[trigger] sw_at(b128(b), k) < 0x4000,
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(b128(r), k) == sw_at(b128(a), k) + sw_at(b128(b), k),
{
    let r = _mm_add_epi16(a, b);
    proof {
        lemma_u16s_len(b128(a));
        lemma_u16s_len(b128(b));
        assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(b128(r), k) == sw_at(b128(a), k) + sw_at(b128(b), k) by {
            assert(-0x4000 <= sw_at(b128(a), k) < 0x4000);
            assert(-0x4000 <= sw_at(b128(b), k) < 0x4000);
            assert(u16x8(r)[k] == verilith_simd::ops::add16(u16x8(a), u16x8(b))[k]);
        }
    }
    r
}

/// Nine times each 16-bit lane (`(x << 3) + x`), for lanes that hold bytes.
#[inline(always)]
fn vmul9(x: __m128i) -> (r: __m128i)
    requires
        forall|k: int| 0 <= k < 8 ==> -128 <= #[trigger] sw_at(b128(x), k) <= 127,
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(b128(r), k) == 9 * sw_at(b128(x), k),
{
    let s = _mm_slli_epi16::<3>(x);
    proof {
        reveal_with_fuel(pow2_spec, 4);
        assert(pow2_spec(3) == 8);
        lemma_u16s_len(b128(x));
        assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(b128(s), k) == 8 * sw_at(b128(x), k) by {
            assert(-128 <= sw_at(b128(x), k) <= 127);
            let a = u16x8(x)[k];
            assert(u16x8(s)[k] == slli16(u16x8(x), 3)[k]);
            assert(u16x8(s)[k] == ((a as nat * 8) % 0x10000) as u16);
        }
        assert forall|k: int| 0 <= k < 8 implies -0x4000 <= #[trigger] sw_at(b128(x), k) < 0x4000 by {
            assert(-128 <= sw_at(b128(x), k) <= 127);
        }
    }
    vadd16(s, x)
}

/// `(x >> 7)` of sixteen 16-bit lanes, packed to signed bytes.
#[inline(always)]
fn vshr7(lo: __m128i, hi: __m128i) -> (r: __m128i)
    ensures
        forall|i: int|
            0 <= i < 16 ==> #[trigger] sb_at(b128(r), i) == lf_c(
                (if i < 8 {
                    sw_at(b128(lo), i)
                } else {
                    sw_at(b128(hi), i - 8)
                }) / 128,
            ),
{
    let sl = _mm_srai_epi16::<7>(lo);
    let sh = _mm_srai_epi16::<7>(hi);
    let r = vpack(sl, sh);
    proof {
        lemma_srai_lanes(lo, sl, 7, 128);
        lemma_srai_lanes(hi, sh, 7, 128);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(b128(r), i) == lf_c(
            (if i < 8 {
                sw_at(b128(lo), i)
            } else {
                sw_at(b128(hi), i - 8)
            }) / 128,
        ) by {
            if i < 8 {
                assert(sw_at(b128(sl), i) == sw_at(b128(lo), i) / 128);
            } else {
                assert(sw_at(b128(sh), i - 8) == sw_at(b128(hi), i - 8) / 128);
            }
        }
    }
    r
}

/// The strong filter's `9 f` from the low half's bytes.
#[inline(always)]
fn vnine_lo(f: __m128i) -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(b128(r), k) == 9 * sb_at(b128(f), k),
{
    let w = vwiden_lo(f);
    proof {
        assert forall|k: int| 0 <= k < 8 implies -128 <= #[trigger] sw_at(b128(w), k) <= 127 by {
            assert(sw_at(b128(w), k) == sb_at(b128(f), k));
        }
    }
    let r = vmul9(w);
    proof {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(b128(r), k) == 9 * sb_at(b128(f), k) by {
            assert(sw_at(b128(w), k) == sb_at(b128(f), k));
        }
    }
    r
}

/// `vnine_lo` for the high half.
#[inline(always)]
fn vnine_hi(f: __m128i) -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(b128(r), k) == 9 * sb_at(b128(f), 8 + k),
{
    let w = vwiden_hi(f);
    proof {
        assert forall|k: int| 0 <= k < 8 implies -128 <= #[trigger] sw_at(b128(w), k) <= 127 by {
            assert(sw_at(b128(w), k) == sb_at(b128(f), 8 + k));
        }
    }
    let r = vmul9(w);
    proof {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(b128(r), k) == 9 * sb_at(b128(f), 8 + k) by {
            assert(sw_at(b128(w), k) == sb_at(b128(f), 8 + k));
        }
    }
    r
}

/// `_mm_set1_epi16(63)`.
#[inline(always)]
fn vk63() -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] sw_at(b128(r), k) == 63,
{
    let r = _mm_set1_epi16(63);
    proof {
        lemma_u16s_len(b128(r));
        assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(b128(r), k) == 63 by {
            assert(u16x8(r)[k] == u16_of_i16(63i16));
        }
    }
    r
}

/// SSE2 (the x86-64 baseline): the helpers above.
impl Lfv for __m128i {
    open spec fn by(self) -> Seq<u8> {
        b128(self)
    }

    open spec fn ok() -> bool {
        true
    }

    proof fn lemma_len(self) {
    }

    #[inline(always)]
    fn vzero() -> (r: Self) {
        _mm_setzero_si128()
    }

    #[inline(always)]
    fn vsplat(x: u8) -> (r: Self) {
        vsplat(x)
    }

    #[inline(always)]
    fn vsign() -> (r: Self) {
        vsign()
    }

    #[inline(always)]
    fn vflip(a: Self, s: Self) -> (r: Self) {
        vflip(a, s)
    }

    #[inline(always)]
    fn vabsd(a: Self, b: Self) -> (r: Self) {
        vabsd(a, b)
    }

    #[inline(always)]
    fn vmax(a: Self, b: Self) -> (r: Self) {
        vmax(a, b)
    }

    #[inline(always)]
    fn vle(a: Self, t: Self) -> (r: Self) {
        vle(a, t)
    }

    #[inline(always)]
    fn vaddus(a: Self, b: Self) -> (r: Self) {
        vaddus(a, b)
    }

    #[inline(always)]
    fn vhalf(d: Self) -> (r: Self) {
        vhalf(d)
    }

    #[inline(always)]
    fn vand(a: Self, m: Self) -> (r: Self) {
        vand(a, m)
    }

    #[inline(always)]
    fn vandnot(m: Self, a: Self) -> (r: Self) {
        vandnot(m, a)
    }

    #[inline(always)]
    fn vadds(a: Self, b: Self) -> (r: Self) {
        vadds(a, b)
    }

    #[inline(always)]
    fn vsubs(a: Self, b: Self) -> (r: Self) {
        vsubs(a, b)
    }

    #[inline(always)]
    fn vaddc(a: Self, c: i8) -> (r: Self) {
        vaddc(a, c)
    }

    #[inline(always)]
    fn vsshr3(x: Self) -> (r: Self) {
        vsshr3(x)
    }

    #[inline(always)]
    fn vavg1(t: Self, s: Self) -> (r: Self) {
        vavg1(t, s)
    }

    #[inline(always)]
    fn vnine_lo(f: Self) -> (r: Self) {
        vnine_lo(f)
    }

    #[inline(always)]
    fn vnine_hi(f: Self) -> (r: Self) {
        vnine_hi(f)
    }

    #[inline(always)]
    fn vk63() -> (r: Self) {
        vk63()
    }

    #[inline(always)]
    fn vadd16(a: Self, b: Self) -> (r: Self) {
        vadd16(a, b)
    }

    #[inline(always)]
    fn vshr7(lo: Self, hi: Self) -> (r: Self) {
        vshr7(lo, hi)
    }

    #[inline(always)]
    fn unpacklo8(a: Self, b: Self) -> (r: Self) {
        _mm_unpacklo_epi8(a, b)
    }

    #[inline(always)]
    fn unpackhi8(a: Self, b: Self) -> (r: Self) {
        _mm_unpackhi_epi8(a, b)
    }

    #[inline(always)]
    fn unpacklo16(a: Self, b: Self) -> (r: Self) {
        _mm_unpacklo_epi16(a, b)
    }

    #[inline(always)]
    fn unpackhi16(a: Self, b: Self) -> (r: Self) {
        _mm_unpackhi_epi16(a, b)
    }

    #[inline(always)]
    fn unpacklo32(a: Self, b: Self) -> (r: Self) {
        _mm_unpacklo_epi32(a, b)
    }

    #[inline(always)]
    fn unpackhi32(a: Self, b: Self) -> (r: Self) {
        _mm_unpackhi_epi32(a, b)
    }

    #[inline(always)]
    fn unpacklo64(a: Self, b: Self) -> (r: Self) {
        _mm_unpacklo_epi64(a, b)
    }

    #[inline(always)]
    fn unpackhi64(a: Self, b: Self) -> (r: Self) {
        _mm_unpackhi_epi64(a, b)
    }

    #[inline(always)]
    fn load16(s: &[u8], i: usize) -> (r: Self) {
        load128_u8(s, i)
    }

    #[inline(always)]
    fn loadl8(s: &[u8], i: usize) -> (r: Self) {
        loadl64_u8(s, i)
    }

    #[inline(always)]
    fn store16(s: &mut [u8], i: usize, v: Self) {
        store128_u8(s, i, v)
    }

    #[inline(always)]
    fn storel8(s: &mut [u8], i: usize, v: Self) {
        storel64_u8(s, i, v)
    }
}

/// An arithmetic right shift of eight 16-bit lanes divides, rounding down.
proof fn lemma_srai_seq(u: Seq<u16>, r: Seq<u16>, n: int, d: int)
    requires
        u.len() == 8,
        r == srai16(u, n),
        (n == 5 && d == 32) || (n == 7 && d == 128) || (n == 8 && d == 256),
    ensures
        forall|k: int| 0 <= k < 8 ==> s16(#[trigger] r[k]) == s16(u[k]) / d,
{
    reveal_with_fuel(pow2_spec, 9);
    assert(pow2_spec(5) == 32 && pow2_spec(7) == 128 && pow2_spec(8) == 256);
    assert forall|k: int| 0 <= k < 8 implies s16(#[trigger] r[k]) == s16(u[k]) / d by {
        let q = s16(u[k]) / d;
        assert(-1024 <= q <= 1023);
        assert(r[k] == (q % 0x10000) as u16);
    }
}

/// NEON (the AArch64 baseline). Where NEON has the operation as one
/// instruction (`uabd`, `cmhs`, `ushr` and `sshr` on bytes, the narrowing
/// `sqshrn`), that is used in place of SSE2's sequence.
impl Lfv for uint8x16_t {
    open spec fn by(self) -> Seq<u8> {
        n8(self)
    }

    open spec fn ok() -> bool {
        neon()
    }

    proof fn lemma_len(self) {
    }

    #[inline(always)]
    fn vzero() -> (r: Self) {
        vdupq_n_u8(0)
    }

    #[inline(always)]
    fn vsplat(x: u8) -> (r: Self) {
        vdupq_n_u8(x)
    }

    #[inline(always)]
    fn vsign() -> (r: Self) {
        vdupq_n_u8(0x80)
    }

    #[inline(always)]
    fn vflip(a: Self, s: Self) -> (r: Self) {
        let r = veorq_u8(a, s);
        proof {
            assert forall|i: int| 0 <= i < 16 implies sb_at(n8(r), i) == ub_at(n8(a), i) - 128 && ub_at(n8(r), i) == sb_at(n8(a), i)
                + 128 by {
                let x = n8(a)[i];
                assert(n8(r)[i] == x ^ 0x80u8);
                assert(((x ^ 0x80u8) as i32) == (if x >= 128 { (x as i32) - 128 } else { (x as i32) + 128 }))
                    by (bit_vector);
            }
        }
        r
    }

    #[inline(always)]
    fn vabsd(a: Self, b: Self) -> (r: Self) {
        let r = vabdq_u8(a, b);
        proof {
            assert forall|i: int| 0 <= i < 16 implies #[trigger] ub_at(n8(r), i) == lf_abs(ub_at(n8(a), i) - ub_at(n8(b), i)) by {
                assert(n8(r)[i] == abd_u8(n8(a), n8(b))[i]);
            }
        }
        r
    }

    #[inline(always)]
    fn vmax(a: Self, b: Self) -> (r: Self) {
        let r = vmaxq_u8(a, b);
        proof {
            assert forall|i: int| 0 <= i < 16 implies #[trigger] ub_at(n8(r), i) == (if ub_at(n8(a), i) > ub_at(n8(b), i) {
                ub_at(n8(a), i)
            } else {
                ub_at(n8(b), i)
            }) by {
                assert(n8(r)[i] == max_u8(n8(a), n8(b))[i]);
            }
        }
        r
    }

    #[inline(always)]
    fn vle(a: Self, t: Self) -> (r: Self) {
        let r = vcleq_u8(a, t);
        proof {
            assert forall|i: int| 0 <= i < 16 implies #[trigger] ub_at(n8(r), i) == (if ub_at(n8(a), i) <= ub_at(n8(t), i) {
                255int
            } else {
                0
            }) by {
                assert(n8(r)[i] == cmple_u8(n8(a), n8(t))[i]);
            }
        }
        r
    }

    #[inline(always)]
    fn vaddus(a: Self, b: Self) -> (r: Self) {
        let r = vqaddq_u8(a, b);
        proof {
            assert forall|i: int| 0 <= i < 16 implies #[trigger] ub_at(n8(r), i) == (if ub_at(n8(a), i) + ub_at(n8(b), i) > 255 {
                255
            } else {
                ub_at(n8(a), i) + ub_at(n8(b), i)
            }) by {
                assert(n8(r)[i] == adds_u8(n8(a), n8(b))[i]);
            }
        }
        r
    }

    #[inline(always)]
    fn vhalf(d: Self) -> (r: Self) {
        let r = vshrq_n_u8::<1>(d);
        proof {
            reveal_with_fuel(pow2_spec, 2);
            assert(pow2_spec(1) == 2);
            assert forall|i: int| 0 <= i < 16 implies #[trigger] ub_at(n8(r), i) == ub_at(n8(d), i) / 2 by {
                assert(n8(r)[i] == shr8(n8(d), 1)[i]);
            }
        }
        r
    }

    #[inline(always)]
    fn vand(a: Self, m: Self) -> (r: Self) {
        let r = vandq_u8(a, m);
        proof {
            assert forall|i: int| 0 <= i < 16 implies (ub_at(n8(m), i) == 255 ==> n8(r)[i] == n8(a)[i]) && (ub_at(n8(m), i)
                == 0 ==> n8(r)[i] == 0u8) by {
                let x = n8(a)[i];
                let y = n8(m)[i];
                assert(n8(r)[i] == x & y);
                assert(y == 0xffu8 ==> (x & y) == x) by (bit_vector);
                assert(y == 0u8 ==> (x & y) == 0u8) by (bit_vector);
            }
        }
        r
    }

    #[inline(always)]
    fn vandnot(m: Self, a: Self) -> (r: Self) {
        let r = vbicq_u8(a, m);
        proof {
            assert forall|i: int| 0 <= i < 16 implies (ub_at(n8(m), i) == 0 ==> n8(r)[i] == n8(a)[i]) && (ub_at(n8(m), i)
                == 255 ==> n8(r)[i] == 0u8) by {
                let x = n8(a)[i];
                let y = n8(m)[i];
                assert(n8(r)[i] == !y & x);
                assert(y == 0u8 ==> (!y & x) == x) by (bit_vector);
                assert(y == 0xffu8 ==> (!y & x) == 0u8) by (bit_vector);
            }
        }
        r
    }

    #[inline(always)]
    fn vadds(a: Self, b: Self) -> (r: Self) {
        let r = vqaddq_s8(a, b);
        proof {
            assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(n8(r), i) == lf_c(sb_at(n8(a), i) + sb_at(n8(b), i)) by {
                let v = sat_s8(sb_at(n8(a), i) + sb_at(n8(b), i));
                assert(n8(r)[i] == adds_s8(n8(a), n8(b))[i]);
                lemma_s8_byte(v);
            }
        }
        r
    }

    #[inline(always)]
    fn vsubs(a: Self, b: Self) -> (r: Self) {
        let r = vqsubq_s8(a, b);
        proof {
            assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(n8(r), i) == lf_c(sb_at(n8(a), i) - sb_at(n8(b), i)) by {
                let v = sat_s8(sb_at(n8(a), i) - sb_at(n8(b), i));
                assert(n8(r)[i] == subs_s8(n8(a), n8(b))[i]);
                lemma_s8_byte(v);
            }
        }
        r
    }

    #[inline(always)]
    fn vaddc(a: Self, c: i8) -> (r: Self) {
        let k = vdupq_n_u8(c as u8);
        let r = vqaddq_s8(a, k);
        proof {
            assert(c >= 0 ==> (c as u8) as i32 == c as i32) by (bit_vector);
            assert(c < 0 ==> (c as u8) as i32 == (c as i32) + 256) by (bit_vector);
            assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(n8(r), i) == lf_c(sb_at(n8(a), i) + c) by {
                assert(n8(k)[i] == c as u8);
                assert(sb_at(n8(k), i) == c);
                let v = sat_s8(sb_at(n8(a), i) + sb_at(n8(k), i));
                assert(n8(r)[i] == adds_s8(n8(a), n8(k))[i]);
                lemma_s8_byte(v);
            }
        }
        r
    }

    #[inline(always)]
    fn vsshr3(x: Self) -> (r: Self) {
        let r = vshrq_n_s8::<3>(x);
        proof {
            reveal_with_fuel(pow2_spec, 4);
            assert(pow2_spec(3) == 8);
            assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(n8(r), i) == sb_at(n8(x), i) / 8 by {
                let q = sb_at(n8(x), i) / 8;
                assert(n8(r)[i] == sra8(n8(x), 3)[i]);
                lemma_s8_byte(q);
            }
        }
        r
    }

    #[inline(always)]
    fn vavg1(t: Self, s: Self) -> (r: Self) {
        let u = Self::vflip(t, s);
        let z = vdupq_n_u8(0);
        let a = vrhaddq_u8(u, z);
        let k = vdupq_n_u8(64);
        let r = vsubq_u8(a, k);
        proof {
            assert(u.by() == n8(u) && t.by() == n8(t));
            assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(n8(r), i) == (sb_at(n8(t), i) + 129) / 2 - 64 by {
                assert(ub_at(n8(u), i) == sb_at(n8(t), i) + 128);
                assert(n8(z)[i] == 0u8);
                assert(n8(a)[i] == avg_u8(n8(u), n8(z))[i]);
                assert(n8(k)[i] == 64u8);
                assert(n8(r)[i] == sub8(n8(a), n8(k))[i]);
            }
        }
        r
    }

    // `f << 8` in 16-bit lanes (the byte above a zero), and from it `f`
    // and `8 f` by arithmetic shifts.
    #[inline(always)]
    fn vnine_lo(f: Self) -> (r: Self) {
        let z = vdupq_n_u8(0);
        let u = vzip1q_u8(z, f);
        let a = vshrq_n_s16::<8>(u);
        let b = vshrq_n_s16::<5>(u);
        let r = vaddq_s16(a, b);
        proof {
            lemma_u16s_len(n8(u));
            lemma_u16s_len(n8(a));
            lemma_u16s_len(n8(b));
            lemma_srai_seq(u16s(n8(u)), u16s(n8(a)), 8, 256);
            lemma_srai_seq(u16s(n8(u)), u16s(n8(b)), 5, 32);
            assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(n8(r), k) == 9 * sb_at(n8(f), k) by {
                lemma_le16_value(n8(u)[2 * k], n8(u)[2 * k + 1]);
                assert(n8(u)[2 * k] == n8(z)[k]);
                assert(n8(u)[2 * k + 1] == n8(f)[k]);
                assert(sw_at(n8(u), k) == 256 * sb_at(n8(f), k));
                assert(s16(u16s(n8(a))[k]) == sb_at(n8(f), k));
                assert(s16(u16s(n8(b))[k]) == 8 * sb_at(n8(f), k));
                assert(u16s(n8(r))[k] == verilith_simd::ops::add16(u16s(n8(a)), u16s(n8(b)))[k]);
            }
        }
        r
    }

    #[inline(always)]
    fn vnine_hi(f: Self) -> (r: Self) {
        let z = vdupq_n_u8(0);
        let u = vzip2q_u8(z, f);
        let a = vshrq_n_s16::<8>(u);
        let b = vshrq_n_s16::<5>(u);
        let r = vaddq_s16(a, b);
        proof {
            lemma_u16s_len(n8(u));
            lemma_u16s_len(n8(a));
            lemma_u16s_len(n8(b));
            lemma_srai_seq(u16s(n8(u)), u16s(n8(a)), 8, 256);
            lemma_srai_seq(u16s(n8(u)), u16s(n8(b)), 5, 32);
            assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(n8(r), k) == 9 * sb_at(n8(f), 8 + k) by {
                lemma_le16_value(n8(u)[2 * k], n8(u)[2 * k + 1]);
                assert(n8(u)[2 * k] == n8(z)[8 + k]);
                assert(n8(u)[2 * k + 1] == n8(f)[8 + k]);
                assert(sw_at(n8(u), k) == 256 * sb_at(n8(f), 8 + k));
                assert(s16(u16s(n8(a))[k]) == sb_at(n8(f), 8 + k));
                assert(s16(u16s(n8(b))[k]) == 8 * sb_at(n8(f), 8 + k));
                assert(u16s(n8(r))[k] == verilith_simd::ops::add16(u16s(n8(a)), u16s(n8(b)))[k]);
            }
        }
        r
    }

    #[inline(always)]
    fn vk63() -> (r: Self) {
        let r = vdupq_n_s16(63);
        proof {
            lemma_u16s_len(n8(r));
            assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(n8(r), k) == 63 by {
                assert(u16s(n8(r))[k] == u16_of_i16(63i16));
            }
        }
        r
    }

    #[inline(always)]
    fn vadd16(a: Self, b: Self) -> (r: Self) {
        let r = vaddq_s16(a, b);
        proof {
            assert(a.by() == n8(a) && b.by() == n8(b));
            lemma_u16s_len(n8(a));
            lemma_u16s_len(n8(b));
            assert forall|k: int| 0 <= k < 8 implies #[trigger] sw_at(n8(r), k) == sw_at(n8(a), k) + sw_at(n8(b), k) by {
                assert(-0x4000 <= sw_at(n8(a), k) < 0x4000);
                assert(-0x4000 <= sw_at(n8(b), k) < 0x4000);
                assert(u16s(n8(r))[k] == verilith_simd::ops::add16(u16s(n8(a)), u16s(n8(b)))[k]);
            }
        }
        r
    }

    #[inline(always)]
    fn vshr7(lo: Self, hi: Self) -> (r: Self) {
        let r = vqshrn2_n_s16::<7>(lo, hi);
        proof {
            lemma_u16s_len(n8(lo));
            lemma_u16s_len(n8(hi));
            let sl = srai16(u16s(n8(lo)), 7);
            let sh = srai16(u16s(n8(hi)), 7);
            lemma_srai_seq(u16s(n8(lo)), sl, 7, 128);
            lemma_srai_seq(u16s(n8(hi)), sh, 7, 128);
            assert forall|i: int| 0 <= i < 16 implies #[trigger] sb_at(n8(r), i) == lf_c(
                (if i < 8 {
                    sw_at(n8(lo), i)
                } else {
                    sw_at(n8(hi), i - 8)
                }) / 128,
            ) by {
                assert(n8(r)[i] == packs16_lanes(sl, sh)[i]);
                assert(i / 16 == 0 && i % 16 == i);
                if i < 8 {
                    assert(s16(sl[i]) == sw_at(n8(lo), i) / 128);
                    lemma_s8_byte(sat_s8(s16(sl[i])));
                } else {
                    assert(s16(sh[i - 8]) == sw_at(n8(hi), i - 8) / 128);
                    lemma_s8_byte(sat_s8(s16(sh[i - 8])));
                }
            }
        }
        r
    }

    #[inline(always)]
    fn unpacklo8(a: Self, b: Self) -> (r: Self) {
        vzip1q_u8(a, b)
    }

    #[inline(always)]
    fn unpackhi8(a: Self, b: Self) -> (r: Self) {
        vzip2q_u8(a, b)
    }

    #[inline(always)]
    fn unpacklo16(a: Self, b: Self) -> (r: Self) {
        vzip1q_u16(a, b)
    }

    #[inline(always)]
    fn unpackhi16(a: Self, b: Self) -> (r: Self) {
        vzip2q_u16(a, b)
    }

    #[inline(always)]
    fn unpacklo32(a: Self, b: Self) -> (r: Self) {
        vzip1q_u32(a, b)
    }

    #[inline(always)]
    fn unpackhi32(a: Self, b: Self) -> (r: Self) {
        vzip2q_u32(a, b)
    }

    #[inline(always)]
    fn unpacklo64(a: Self, b: Self) -> (r: Self) {
        vzip1q_u64(a, b)
    }

    #[inline(always)]
    fn unpackhi64(a: Self, b: Self) -> (r: Self) {
        vzip2q_u64(a, b)
    }

    #[inline(always)]
    fn load16(s: &[u8], i: usize) -> (r: Self) {
        vld1q_u8_at(s, i)
    }

    #[inline(always)]
    fn loadl8(s: &[u8], i: usize) -> (r: Self) {
        vld1q_u8_low_at(s, i)
    }

    #[inline(always)]
    fn store16(s: &mut [u8], i: usize, v: Self) {
        vst1q_u8_at(s, i, v)
    }

    #[inline(always)]
    fn storel8(s: &mut [u8], i: usize, v: Self) {
        vst1q_u8_low_at(s, i, v)
    }
}

/// The strong filter's three adjustments, `(9 f + 63) >> 7`,
/// `(18 f + 63) >> 7` and `(27 f + 63) >> 7`, in 16-bit lanes.
#[inline(always)]
fn vstrong<V: Lfv>(f: V) -> (d: (V, V, V))
    requires
        V::ok(),
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] sbyte(d.0, i) == lf_c((9 * sbyte(f, i) + 63) / 128),
        forall|i: int| 0 <= i < 16 ==> #[trigger] sbyte(d.1, i) == lf_c((18 * sbyte(f, i) + 63) / 128),
        forall|i: int| 0 <= i < 16 ==> #[trigger] sbyte(d.2, i) == lf_c((27 * sbyte(f, i) + 63) / 128),
{
    broadcast use lemma_vb_len;
    let f9lo = V::vnine_lo(f);
    let f9hi = V::vnine_hi(f);
    let k63 = V::vk63();
    proof {
        assert forall|k: int| 0 <= k < 8 implies -0x4000 <= #[trigger] sword(f9lo, k) < 0x4000 by {
            assert(sword(f9lo, k) == 9 * sbyte(f, k));
        }
        assert forall|k: int| 0 <= k < 8 implies -0x4000 <= #[trigger] sword(f9hi, k) < 0x4000 by {
            assert(sword(f9hi, k) == 9 * sbyte(f, 8 + k));
        }
        assert forall|k: int| 0 <= k < 8 implies -0x4000 <= #[trigger] sword(k63, k) < 0x4000 by {
            assert(sword(k63, k) == 63);
        }
    }
    let a2lo = V::vadd16(f9lo, k63);
    let a2hi = V::vadd16(f9hi, k63);
    proof {
        assert forall|k: int| 0 <= k < 8 implies -0x4000 <= #[trigger] sword(a2lo, k) < 0x4000 by {
            assert(sword(a2lo, k) == sword(f9lo, k) + sword(k63, k));
            assert(sword(f9lo, k) == 9 * sbyte(f, k));
            assert(sword(k63, k) == 63);
        }
        assert forall|k: int| 0 <= k < 8 implies -0x4000 <= #[trigger] sword(a2hi, k) < 0x4000 by {
            assert(sword(a2hi, k) == sword(f9hi, k) + sword(k63, k));
            assert(sword(f9hi, k) == 9 * sbyte(f, 8 + k));
            assert(sword(k63, k) == 63);
        }
    }
    let a1lo = V::vadd16(a2lo, f9lo);
    let a1hi = V::vadd16(a2hi, f9hi);
    proof {
        assert forall|k: int| 0 <= k < 8 implies -0x4000 <= #[trigger] sword(a1lo, k) < 0x4000 by {
            assert(sword(a1lo, k) == sword(a2lo, k) + sword(f9lo, k));
            assert(sword(a2lo, k) == sword(f9lo, k) + sword(k63, k));
            assert(sword(f9lo, k) == 9 * sbyte(f, k));
            assert(sword(k63, k) == 63);
        }
        assert forall|k: int| 0 <= k < 8 implies -0x4000 <= #[trigger] sword(a1hi, k) < 0x4000 by {
            assert(sword(a1hi, k) == sword(a2hi, k) + sword(f9hi, k));
            assert(sword(a2hi, k) == sword(f9hi, k) + sword(k63, k));
            assert(sword(f9hi, k) == 9 * sbyte(f, 8 + k));
            assert(sword(k63, k) == 63);
        }
    }
    let a0lo = V::vadd16(a1lo, f9lo);
    let a0hi = V::vadd16(a1hi, f9hi);
    let d2 = V::vshr7(a2lo, a2hi);
    let d1 = V::vshr7(a1lo, a1hi);
    let d0 = V::vshr7(a0lo, a0hi);
    proof {
        assert forall|i: int| 0 <= i < 16 implies sbyte(d2, i) == lf_c((9 * sbyte(f, i) + 63) / 128) && sbyte(d1, i)
            == lf_c((18 * sbyte(f, i) + 63) / 128) && sbyte(d0, i) == lf_c((27 * sbyte(f, i) + 63) / 128) by {
            let s = sbyte(f, i);
            if i < 8 {
                let k = i;
                assert(sword(f9lo, k) == 9 * s);
                assert(sword(k63, k) == 63);
                assert(sword(a2lo, k) == 9 * s + 63);
                assert(sword(a1lo, k) == 18 * s + 63);
                assert(sword(a0lo, k) == 27 * s + 63);
            } else {
                let k = i - 8;
                assert(sword(f9hi, k) == 9 * s);
                assert(sword(k63, k) == 63);
                assert(sword(a2hi, k) == 9 * s + 63);
                assert(sword(a1hi, k) == 18 * s + 63);
                assert(sword(a0hi, k) == 27 * s + 63);
            }
        }
    }
    (d2, d1, d0)
}
/// `GetBaseDelta_SSE2`: `p1 - q1 + 3 * (q0 - p0)`, saturating in this order.
#[inline(always)]
fn vbase_delta<V: Lfv>(p1: V, p0: V, q0: V, q1: V) -> (r: V)
    requires
        V::ok(),
    ensures
        forall|i: int|
            0 <= i < 16 ==> #[trigger] sbyte(r, i) == lf_c(
                lf_c(sbyte(p1, i) - sbyte(q1, i)) + 3 * (sbyte(q0, i) - sbyte(p0, i)),
            ),
{
    broadcast use lemma_vb_len;
    let p1_q1 = V::vsubs(p1, q1);
    let q0_p0 = V::vsubs(q0, p0);
    let s1 = V::vadds(p1_q1, q0_p0);
    let s2 = V::vadds(q0_p0, s1);
    let r = V::vadds(q0_p0, s2);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] sbyte(r, i) == lf_c(
            lf_c(sbyte(p1, i) - sbyte(q1, i)) + 3 * (sbyte(q0, i) - sbyte(p0, i)),
        ) by {
            let o = sbyte(p1_q1, i);
            let d = sbyte(q0_p0, i);
            assert(sbyte(s1, i) == lf_c(o + d));
            assert(sbyte(s2, i) == lf_c(d + sbyte(s1, i)));
            assert(sbyte(r, i) == lf_c(d + sbyte(s2, i)));
        }
    }
    r
}

/// The eight rows as one block, row `k` at `16 * k` (what `gather` builds
/// in memory).
pub open spec fn vblk<V: Lfv>(r: [V; 8]) -> Seq<u8> {
    flat8(vrows(r))
}

/// Lane `j` of eight rows.
pub open spec fn vedge<V: Lfv>(r: [V; 8], j: int) -> Edge8 {
    Edge8 {
        p3: ubyte(r[0], j),
        p2: ubyte(r[1], j),
        p1: ubyte(r[2], j),
        p0: ubyte(r[3], j),
        q0: ubyte(r[4], j),
        q1: ubyte(r[5], j),
        q2: ubyte(r[6], j),
        q3: ubyte(r[7], j),
    }
}

proof fn lemma_vblk<V: Lfv>(r: [V; 8])
    ensures
        vblk(r).len() == 128,
        forall|k: int, i: int| #[trigger] gat(k, i) && 0 <= k < 8 && 0 <= i < 16 ==> vblk(r)[16 * k + i] == vb(r[k])[i],
        forall|j: int| 0 <= j < 16 ==> #[trigger] blk_lane(vblk(r), j) == vedge(r, j),
{
    broadcast use lemma_vb_len;
    assert forall|k: int, i: int| #[trigger] gat(k, i) && 0 <= k < 8 && 0 <= i < 16 implies vblk(r)[16 * k + i]
        == vb(r[k])[i] by {
        assert((16 * k + i) / 16 == k && (16 * k + i) % 16 == i);
    }
    assert forall|j: int| 0 <= j < 16 implies #[trigger] blk_lane(vblk(r), j) == vedge(r, j) by {
        assert(gat(0, j) && gat(1, j) && gat(2, j) && gat(3, j) && gat(4, j) && gat(5, j) && gat(6, j) && gat(7, j));
    }
}

/// `ComplexMask_SSE2` and `GetNotHEV_SSE2`: per lane, whether to filter,
/// and whether the edge variance is low (`mask_hev` on sixteen lanes).
#[inline(always)]
fn mask_hev_vec<V: Lfv>(r: [V; 8], th: u8, it: u8, ht: u8) -> (m: (V, V))
    requires
        V::ok(),
    ensures
        th <= 254 ==> forall|j: int|
            0 <= j < 16 ==> #[trigger] ubyte(m.0, j) == (if lf_normal_yes(vedge(r, j), th as int, it as int) {
                255int
            } else {
                0
            }),
        forall|j: int| 0 <= j < 16 ==> #[trigger] ubyte(m.1, j) == (if lf_hev(vedge(r, j), ht as int) { 0int } else { 255 }),
{
    broadcast use lemma_vb_len;
    let p3 = r[0];
    let p2 = r[1];
    let p1 = r[2];
    let p0 = r[3];
    let q0 = r[4];
    let q1 = r[5];
    let q2 = r[6];
    let q3 = r[7];
    let d10 = V::vabsd(p1, p0);
    let e10 = V::vabsd(q1, q0);
    let m1 = V::vmax(d10, e10);
    let d32 = V::vabsd(p3, p2);
    let d21 = V::vabsd(p2, p1);
    let m2 = V::vmax(d32, d21);
    let e32 = V::vabsd(q3, q2);
    let e21 = V::vabsd(q2, q1);
    let m3 = V::vmax(e32, e21);
    let m4 = V::vmax(m2, m3);
    let mx = V::vmax(m1, m4);
    let itv = V::vsplat(it);
    let ma = V::vle(mx, itv);
    let d11 = V::vabsd(p1, q1);
    let t3 = V::vhalf(d11);
    let t4 = V::vabsd(p0, q0);
    let t5 = V::vaddus(t4, t4);
    let t6 = V::vaddus(t5, t3);
    let thv = V::vsplat(th);
    let mb = V::vle(t6, thv);
    let mask = V::vand(ma, mb);
    let htv = V::vsplat(ht);
    let nh = V::vle(m1, htv);
    proof {
        assert forall|j: int| 0 <= j < 16 implies #[trigger] ubyte(nh, j) == (if lf_hev(vedge(r, j), ht as int) {
            0int
        } else {
            255
        }) by {
            assert(ubyte(m1, j) == (if ubyte(d10, j) > ubyte(e10, j) { ubyte(d10, j) } else { ubyte(e10, j) }));
            assert(ubyte(htv, j) == ht);
        }
        if th <= 254 {
            assert forall|j: int| 0 <= j < 16 implies #[trigger] ubyte(mask, j) == (if lf_normal_yes(
                vedge(r, j),
                th as int,
                it as int,
            ) {
                255int
            } else {
                0
            }) by {
                assert(ubyte(m1, j) == (if ubyte(d10, j) > ubyte(e10, j) { ubyte(d10, j) } else { ubyte(e10, j) }));
                assert(ubyte(m2, j) == (if ubyte(d32, j) > ubyte(d21, j) { ubyte(d32, j) } else { ubyte(d21, j) }));
                assert(ubyte(m3, j) == (if ubyte(e32, j) > ubyte(e21, j) { ubyte(e32, j) } else { ubyte(e21, j) }));
                assert(ubyte(m4, j) == (if ubyte(m2, j) > ubyte(m3, j) { ubyte(m2, j) } else { ubyte(m3, j) }));
                assert(ubyte(mx, j) == (if ubyte(m1, j) > ubyte(m4, j) { ubyte(m1, j) } else { ubyte(m4, j) }));
                assert(ubyte(itv, j) == it);
                assert(ubyte(thv, j) == th);
                assert(ubyte(ma, j) == (if ubyte(mx, j) <= it { 255int } else { 0 }));
                assert(ubyte(t3, j) == ubyte(d11, j) / 2);
                assert(ubyte(t5, j) == (if 2 * ubyte(t4, j) > 255 { 255 } else { 2 * ubyte(t4, j) }));
                assert(ubyte(t6, j) == (if ubyte(t5, j) + ubyte(t3, j) > 255 { 255 } else { ubyte(t5, j) + ubyte(t3, j) }));
                assert(ubyte(mb, j) == (if ubyte(t6, j) <= th { 255int } else { 0 }));
            }
        }
    }
    (mask, nh)
}

/// `FilterLoop24`'s lanes (`DoFilter4_SSE2`), in registers: `lanes4` on
/// eight row vectors.
#[inline(always)]
fn lanes4_vec<V: Lfv>(r: [V; 8], th: u8, it: u8, ht: u8) -> (o: [V; 8])
    requires
        V::ok(),
    ensures
        th <= 254 ==> forall|j: int|
            0 <= j < 16 ==> #[trigger] blk_lane(vblk(o), j) == lf_subblock(
                blk_lane(vblk(r), j),
                th as int,
                it as int,
                ht as int,
            ),
        o[0] == r[0],
        o[1] == r[1],
        o[6] == r[6],
        o[7] == r[7],
{
    broadcast use lemma_vb_len;
    let (mask, not_hev) = mask_hev_vec(r, th, it, ht);
    let s = V::vsign();
    let p1 = V::vflip(r[2], s);
    let p0 = V::vflip(r[3], s);
    let q0 = V::vflip(r[4], s);
    let q1 = V::vflip(r[5], s);
    let t0 = V::vsubs(p1, q1);
    let t1a = V::vandnot(not_hev, t0);
    let t2a = V::vsubs(q0, p0);
    let u1 = V::vadds(t1a, t2a);
    let u2 = V::vadds(u1, t2a);
    let u3 = V::vadds(u2, t2a);
    let t1 = V::vand(u3, mask);
    let w3 = V::vaddc(t1, 3);
    let t2 = V::vsshr3(w3);
    let w4 = V::vaddc(t1, 4);
    let t3 = V::vsshr3(w4);
    let np0 = V::vadds(p0, t2);
    let nq0 = V::vsubs(q0, t3);
    let t3b = V::vavg1(t3, s);
    let t3d = V::vand(t3b, not_hev);
    let np1 = V::vadds(p1, t3d);
    let nq1 = V::vsubs(q1, t3d);
    let o = [r[0], r[1], V::vflip(np1, s), V::vflip(np0, s), V::vflip(nq0, s), V::vflip(nq1, s), r[6], r[7]];
    proof {
        lemma_vblk(r);
        lemma_vblk(o);
        if th <= 254 {
            assert forall|j: int| 0 <= j < 16 implies #[trigger] vedge(o, j) == lf_subblock(
                vedge(r, j),
                th as int,
                it as int,
                ht as int,
            ) by {
                let x = vedge(r, j);
                let yes = ubyte(mask, j) == 255;
                let hv = ubyte(not_hev, j) == 0;
                assert(yes == lf_normal_yes(x, th as int, it as int));
                assert(hv == lf_hev(x, ht as int));
                assert(sbyte(p1, j) == x.p1 - 128 && sbyte(p0, j) == x.p0 - 128 && sbyte(q0, j) == x.q0 - 128
                    && sbyte(q1, j) == x.q1 - 128);
                assert(sbyte(t0, j) == lf_c(x.p1 - x.q1));
                assert(sbyte(t1a, j) == (if hv { lf_c(x.p1 - x.q1) } else { 0 }));
                assert(sbyte(t2a, j) == lf_c(x.q0 - x.p0));
                assert(sbyte(u1, j) == lf_c(sbyte(t1a, j) + sbyte(t2a, j)));
                assert(sbyte(u2, j) == lf_c(sbyte(u1, j) + sbyte(t2a, j)));
                assert(sbyte(u3, j) == lf_c(sbyte(u2, j) + sbyte(t2a, j)));
                assert(sbyte(t1, j) == (if yes { sbyte(u3, j) } else { 0 }));
                assert(sbyte(w3, j) == lf_c(sbyte(t1, j) + 3));
                assert(sbyte(w4, j) == lf_c(sbyte(t1, j) + 4));
                assert(sbyte(t2, j) == sbyte(w3, j) / 8);
                assert(sbyte(t3, j) == sbyte(w4, j) / 8);
                assert(sbyte(t3b, j) == (sbyte(t3, j) + 129) / 2 - 64);
                assert(sbyte(t3d, j) == (if hv { 0 } else { sbyte(t3b, j) }));
                assert(sbyte(np0, j) == lf_c(sbyte(p0, j) + sbyte(t2, j)));
                assert(sbyte(nq0, j) == lf_c(sbyte(q0, j) - sbyte(t3, j)));
                assert(sbyte(np1, j) == lf_c(sbyte(p1, j) + sbyte(t3d, j)));
                assert(sbyte(nq1, j) == lf_c(sbyte(q1, j) - sbyte(t3d, j)));
                assert(ubyte(o[2], j) == sbyte(np1, j) + 128);
                assert(ubyte(o[3], j) == sbyte(np0, j) + 128);
                assert(ubyte(o[4], j) == sbyte(nq0, j) + 128);
                assert(ubyte(o[5], j) == sbyte(nq1, j) + 128);
                lemma_lane4(
                    x,
                    th as int,
                    it as int,
                    ht as int,
                    yes,
                    hv,
                    sbyte(t1a, j),
                    sbyte(t2a, j),
                    sbyte(t1, j),
                    sbyte(t2, j),
                    sbyte(t3, j),
                    sbyte(t3d, j),
                    vedge(o, j),
                );
            }
        }
    }
    o
}

/// `FilterLoop26`'s lanes (`DoFilter6_SSE2`), in registers: `lanes6` on
/// eight row vectors.
#[inline(always)]
fn lanes6_vec<V: Lfv>(r: [V; 8], th: u8, it: u8, ht: u8) -> (o: [V; 8])
    requires
        V::ok(),
    ensures
        th <= 254 ==> forall|j: int|
            0 <= j < 16 ==> #[trigger] blk_lane(vblk(o), j) == lf_mbedge(
                blk_lane(vblk(r), j),
                th as int,
                it as int,
                ht as int,
            ),
        o[0] == r[0],
        o[7] == r[7],
{
    broadcast use lemma_vb_len;
    let (mask, not_hev) = mask_hev_vec(r, th, it, ht);
    let s = V::vsign();
    let p2 = V::vflip(r[1], s);
    let p1 = V::vflip(r[2], s);
    let p0 = V::vflip(r[3], s);
    let q0 = V::vflip(r[4], s);
    let q1 = V::vflip(r[5], s);
    let q2 = V::vflip(r[6], s);
    let a = vbase_delta(p1, p0, q0, q1);
    // The simple filter where the variance is high.
    let m1 = V::vandnot(not_hev, mask);
    let f = V::vand(a, m1);
    let w3 = V::vaddc(f, 3);
    let v3 = V::vsshr3(w3);
    let w4 = V::vaddc(f, 4);
    let v4 = V::vsshr3(w4);
    let p0a = V::vadds(p0, v3);
    let q0a = V::vsubs(q0, v4);
    // The strong filter where it is low.
    let m2 = V::vand(mask, not_hev);
    let g = V::vand(a, m2);
    let (d2, d1, d0) = vstrong(g);
    let np2 = V::vadds(p2, d2);
    let np1 = V::vadds(p1, d1);
    let np0 = V::vadds(p0a, d0);
    let nq0 = V::vsubs(q0a, d0);
    let nq1 = V::vsubs(q1, d1);
    let nq2 = V::vsubs(q2, d2);
    let o = [
        r[0], V::vflip(np2, s), V::vflip(np1, s), V::vflip(np0, s),
        V::vflip(nq0, s), V::vflip(nq1, s), V::vflip(nq2, s), r[7],
    ];
    proof {
        lemma_vblk(r);
        lemma_vblk(o);
        if th <= 254 {
            assert forall|j: int| 0 <= j < 16 implies #[trigger] vedge(o, j) == lf_mbedge(
                vedge(r, j),
                th as int,
                it as int,
                ht as int,
            ) by {
                let x = vedge(r, j);
                let yes = ubyte(mask, j) == 255;
                let hv = ubyte(not_hev, j) == 0;
                assert(yes == lf_normal_yes(x, th as int, it as int));
                assert(hv == lf_hev(x, ht as int));
                assert(sbyte(p2, j) == x.p2 - 128 && sbyte(p1, j) == x.p1 - 128 && sbyte(p0, j) == x.p0 - 128
                    && sbyte(q0, j) == x.q0 - 128 && sbyte(q1, j) == x.q1 - 128 && sbyte(q2, j) == x.q2 - 128);
                let w = sbyte(a, j);
                assert(w == lf_c(lf_c(x.p1 - x.q1) + 3 * (x.q0 - x.p0)));
                assert(ubyte(m1, j) == (if yes && hv { 255int } else { 0 }));
                assert(ubyte(m2, j) == (if yes && !hv { 255int } else { 0 }));
                assert(sbyte(f, j) == (if yes && hv { w } else { 0 }));
                assert(sbyte(g, j) == (if yes && !hv { w } else { 0 }));
                assert(sbyte(w3, j) == lf_c(sbyte(f, j) + 3));
                assert(sbyte(w4, j) == lf_c(sbyte(f, j) + 4));
                assert(sbyte(v3, j) == sbyte(w3, j) / 8);
                assert(sbyte(v4, j) == sbyte(w4, j) / 8);
                assert(sbyte(p0a, j) == lf_c(sbyte(p0, j) + sbyte(v3, j)));
                assert(sbyte(q0a, j) == lf_c(sbyte(q0, j) - sbyte(v4, j)));
                assert(sbyte(d2, j) == lf_c((9 * sbyte(g, j) + 63) / 128));
                assert(sbyte(d1, j) == lf_c((18 * sbyte(g, j) + 63) / 128));
                assert(sbyte(d0, j) == lf_c((27 * sbyte(g, j) + 63) / 128));
                assert(sbyte(np2, j) == lf_c(sbyte(p2, j) + sbyte(d2, j)));
                assert(sbyte(np1, j) == lf_c(sbyte(p1, j) + sbyte(d1, j)));
                assert(sbyte(np0, j) == lf_c(sbyte(p0a, j) + sbyte(d0, j)));
                assert(sbyte(nq0, j) == lf_c(sbyte(q0a, j) - sbyte(d0, j)));
                assert(sbyte(nq1, j) == lf_c(sbyte(q1, j) - sbyte(d1, j)));
                assert(sbyte(nq2, j) == lf_c(sbyte(q2, j) - sbyte(d2, j)));
                assert(ubyte(o[1], j) == sbyte(np2, j) + 128);
                assert(ubyte(o[2], j) == sbyte(np1, j) + 128);
                assert(ubyte(o[3], j) == sbyte(np0, j) + 128);
                assert(ubyte(o[4], j) == sbyte(nq0, j) + 128);
                assert(ubyte(o[5], j) == sbyte(nq1, j) + 128);
                assert(ubyte(o[6], j) == sbyte(nq2, j) + 128);
                lemma_lane6(
                    x,
                    th as int,
                    it as int,
                    ht as int,
                    yes,
                    hv,
                    w,
                    sbyte(f, j),
                    sbyte(v3, j),
                    sbyte(v4, j),
                    sbyte(p0a, j),
                    sbyte(q0a, j),
                    sbyte(g, j),
                    sbyte(d2, j),
                    sbyte(d1, j),
                    sbyte(d0, j),
                    vedge(o, j),
                );
            }
        }
    }
    o
}

/// The normal filter on the sixteen lanes of eight row vectors: the inner
/// or the macroblock-edge form.
#[inline(always)]
fn kernel_vec<V: Lfv>(r: [V; 8], th: u8, it: u8, ht: u8, inner: bool) -> (o: [V; 8])
    requires
        V::ok(),
    ensures
        th <= 254 ==> forall|j: int|
            0 <= j < 16 ==> #[trigger] blk_lane(vblk(o), j) == lf_kernel(
                blk_lane(vblk(r), j),
                false,
                inner,
                th as int,
                it as int,
                ht as int,
            ),
        o[0] == r[0],
        o[7] == r[7],
        inner ==> o[1] == r[1] && o[6] == r[6],
{
    broadcast use lemma_vb_len;
    if inner {
        lanes4_vec(r, th, it, ht)
    } else {
        lanes6_vec(r, th, it, ht)
    }
}

/// Which bytes an interleave of `w`-byte lanes takes: byte `m` of the
/// result is byte `unpack_at(m, w, hi)` of the first operand (`m / w` even)
/// or of the second.
pub open spec fn unpack_at(m: int, w: int, hi: bool) -> int {
    (if hi { 8int } else { 0 }) + (m / (2 * w)) * w + m % w
}

/// `_mm_unpacklo_epi8` and `_mm_unpackhi_epi8`, byte by byte.
proof fn lemma_unpack8_bytes(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>, hi: bool)
    requires
        a.len() == 16,
        b.len() == 16,
        r == (if hi { unpackhi8_lanes(a, b) } else { unpacklo8_lanes(a, b) }),
    ensures
        r.len() == 16,
        forall|m: int|
            0 <= m < 16 ==> #[trigger] r[m] == (if m % 2 == 0 { a } else { b })[unpack_at(m, 1, hi)],
{
}

/// The 16-bit interleaves, byte by byte.
proof fn lemma_unpack16_bytes(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>, hi: bool)
    requires
        a.len() == 16,
        b.len() == 16,
        r.len() == 16,
        u16s(r) == (if hi { unpackhi16_lanes(u16s(a), u16s(b)) } else { unpacklo16_lanes(u16s(a), u16s(b)) }),
    ensures
        forall|m: int|
            0 <= m < 16 ==> #[trigger] r[m] == (if (m / 2) % 2 == 0 { a } else { b })[unpack_at(m, 2, hi)],
{
    lemma_unpack16(a, b, r, hi);
    let o: int = if hi { 4 } else { 0 };
    assert forall|m: int| 0 <= m < 16 implies #[trigger] r[m] == (if (m / 2) % 2 == 0 { a } else { b })[unpack_at(
        m,
        2,
        hi,
    )] by {
        let n = m / 2;
        let sn = o + n / 2;
        lemma_u16_lane_bytes(r, n);
        lemma_u16_lane_bytes(a, sn);
        lemma_u16_lane_bytes(b, sn);
        assert(n == 0 || n == 1 || n == 2 || n == 3 || n == 4 || n == 5 || n == 6 || n == 7);
        assert(m == 2 * n || m == 2 * n + 1);
    }
}

/// The 32-bit interleaves, byte by byte.
proof fn lemma_unpack32_bytes(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>, hi: bool)
    requires
        a.len() == 16,
        b.len() == 16,
        r.len() == 16,
        u32s(r) == (if hi { unpackhi32_lanes(u32s(a), u32s(b)) } else { unpacklo32_lanes(u32s(a), u32s(b)) }),
    ensures
        forall|m: int|
            0 <= m < 16 ==> #[trigger] r[m] == (if (m / 4) % 2 == 0 { a } else { b })[unpack_at(m, 4, hi)],
{
    lemma_u32s_bytes(a);
    lemma_u32s_bytes(b);
    lemma_u32s_bytes(r);
    let o: int = if hi { 2 } else { 0 };
    assert forall|m: int| 0 <= m < 16 implies #[trigger] r[m] == (if (m / 4) % 2 == 0 { a } else { b })[unpack_at(
        m,
        4,
        hi,
    )] by {
        let n = m / 4;
        let k = m % 4;
        let sn = o + n / 2;
        assert(byte32(u32s(r)[n], k) == r[4 * n + k]);
        assert(byte32(u32s(a)[sn], k) == a[4 * sn + k]);
        assert(byte32(u32s(b)[sn], k) == b[4 * sn + k]);
        assert(n == 0 || n == 1 || n == 2 || n == 3);
    }
}

/// The 64-bit interleaves, byte by byte.
proof fn lemma_unpack64_bytes(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>, hi: bool)
    requires
        a.len() == 16,
        b.len() == 16,
        r.len() == 16,
        u64s(r) == (if hi { unpackhi64_lanes(u64s(a), u64s(b)) } else { unpacklo64_lanes(u64s(a), u64s(b)) }),
    ensures
        forall|m: int| 0 <= m < 16 ==> #[trigger] r[m] == (if m / 8 == 0 { a } else { b })[unpack_at(m, 8, hi)],
{
    let k: int = if hi { 1 } else { 0 };
    assert(u64s(r)[0] == u64s(a)[k]);
    assert(u64s(r)[1] == u64s(b)[k]);
    lemma_le64_inj(u32s(r)[2 * 0int], u32s(r)[2 * 0int + 1], u32s(a)[2 * k], u32s(a)[2 * k + 1]);
    lemma_le64_inj(u32s(r)[2 * 1int], u32s(r)[2 * 1int + 1], u32s(b)[2 * k], u32s(b)[2 * k + 1]);
    lemma_u32s_bytes(a);
    lemma_u32s_bytes(b);
    lemma_u32s_bytes(r);
    assert forall|m: int| 0 <= m < 16 implies #[trigger] r[m] == (if m / 8 == 0 { a } else { b })[unpack_at(m, 8, hi)] by {
        let n = m / 4;
        let e = m % 4;
        let sn = 2 * k + n % 2;
        assert(byte32(u32s(r)[n], e) == r[4 * n + e]);
        assert(byte32(u32s(a)[sn], e) == a[4 * sn + e]);
        assert(byte32(u32s(b)[sn], e) == b[4 * sn + e]);
        assert(n == 0 || n == 1 || n == 2 || n == 3);
        assert(m == 4 * n + e);
        assert(0 <= e < 4);
        assert(m / 16 == 0);
        // `unpack_at(m, 8, hi)` is `8 * k + (m / 16) * 8 + m % 8`: lane by lane.
        if n == 0 {
            assert(m == e);
            assert(m % 8 == e);
            assert(sn == 2 * k);
            assert(u32s(r)[0] == u32s(a)[2 * k]);
        } else if n == 1 {
            assert(m == 4 + e);
            assert(m % 8 == 4 + e);
            assert(sn == 2 * k + 1);
            assert(u32s(r)[1] == u32s(a)[2 * k + 1]);
        } else if n == 2 {
            assert(m == 8 + e);
            assert(m % 8 == e);
            assert(sn == 2 * k);
            assert(u32s(r)[2] == u32s(b)[2 * k]);
        } else {
            assert(m == 12 + e);
            assert(m % 8 == 4 + e);
            assert(sn == 2 * k + 1);
            assert(u32s(r)[3] == u32s(b)[2 * k + 1]);
        }
        assert(4 * sn + e == 8 * k + m % 8);
        assert(unpack_at(m, 8, hi) == 8 * k + (m / 16) * 8 + m % 8);
        assert(4 * sn + e == unpack_at(m, 8, hi));
    }
}

/// The three interleave rounds of `tr8`, byte by byte: output `n` holds
/// columns `2n` and `2n + 1` of the eight input rows.
proof fn lemma_tr8(
    x: Seq<Seq<u8>>,
    a0: Seq<u8>,
    a1: Seq<u8>,
    a2: Seq<u8>,
    a3: Seq<u8>,
    b0: Seq<u8>,
    b1: Seq<u8>,
    b2: Seq<u8>,
    b3: Seq<u8>,
    c0: Seq<u8>,
    c1: Seq<u8>,
    c2: Seq<u8>,
    c3: Seq<u8>,
    hi: bool,
)
    requires
        x.len() == 8,
        forall|k: int| 0 <= k < 8 ==> (#[trigger] x[k]).len() == 16,
        b0.len() == 16 && b1.len() == 16 && b2.len() == 16 && b3.len() == 16,
        c0.len() == 16 && c1.len() == 16 && c2.len() == 16 && c3.len() == 16,
        a0 == (if hi { unpackhi8_lanes(x[0], x[1]) } else { unpacklo8_lanes(x[0], x[1]) }),
        a1 == (if hi { unpackhi8_lanes(x[2], x[3]) } else { unpacklo8_lanes(x[2], x[3]) }),
        a2 == (if hi { unpackhi8_lanes(x[4], x[5]) } else { unpacklo8_lanes(x[4], x[5]) }),
        a3 == (if hi { unpackhi8_lanes(x[6], x[7]) } else { unpacklo8_lanes(x[6], x[7]) }),
        u16s(b0) == unpacklo16_lanes(u16s(a0), u16s(a1)),
        u16s(b1) == unpackhi16_lanes(u16s(a0), u16s(a1)),
        u16s(b2) == unpacklo16_lanes(u16s(a2), u16s(a3)),
        u16s(b3) == unpackhi16_lanes(u16s(a2), u16s(a3)),
        u32s(c0) == unpacklo32_lanes(u32s(b0), u32s(b2)),
        u32s(c1) == unpackhi32_lanes(u32s(b0), u32s(b2)),
        u32s(c2) == unpacklo32_lanes(u32s(b1), u32s(b3)),
        u32s(c3) == unpackhi32_lanes(u32s(b1), u32s(b3)),
    ensures
        forall|m: int| 0 <= m < 16 ==> #[trigger] c0[m] == x[m % 8][(if hi { 8int } else { 0 }) + m / 8],
        forall|m: int| 0 <= m < 16 ==> #[trigger] c1[m] == x[m % 8][(if hi { 8int } else { 0 }) + 2 + m / 8],
        forall|m: int| 0 <= m < 16 ==> #[trigger] c2[m] == x[m % 8][(if hi { 8int } else { 0 }) + 4 + m / 8],
        forall|m: int| 0 <= m < 16 ==> #[trigger] c3[m] == x[m % 8][(if hi { 8int } else { 0 }) + 6 + m / 8],
{
    lemma_tr8_quarter(x, a0, a1, a2, a3, b0, b2, c0, false, false, hi);
    lemma_tr8_quarter(x, a0, a1, a2, a3, b0, b2, c1, false, true, hi);
    lemma_tr8_quarter(x, a0, a1, a2, a3, b1, b3, c2, true, false, hi);
    lemma_tr8_quarter(x, a0, a1, a2, a3, b1, b3, c3, true, true, hi);
}

/// One of `lemma_tr8`'s four outputs: `c` is the 32-bit interleave (high
/// when `h32`) of `p` and `q`, the 16-bit interleaves (high when `h16`) of
/// `a0, a1` and of `a2, a3`, so it holds columns `4 h16 + 2 h32` and one
/// more. Proved apart so each proof sees only the facts it needs.
proof fn lemma_tr8_quarter(
    x: Seq<Seq<u8>>,
    a0: Seq<u8>,
    a1: Seq<u8>,
    a2: Seq<u8>,
    a3: Seq<u8>,
    p: Seq<u8>,
    q: Seq<u8>,
    c: Seq<u8>,
    h16: bool,
    h32: bool,
    hi: bool,
)
    requires
        x.len() == 8,
        forall|k: int| 0 <= k < 8 ==> (#[trigger] x[k]).len() == 16,
        p.len() == 16 && q.len() == 16 && c.len() == 16,
        a0 == (if hi { unpackhi8_lanes(x[0], x[1]) } else { unpacklo8_lanes(x[0], x[1]) }),
        a1 == (if hi { unpackhi8_lanes(x[2], x[3]) } else { unpacklo8_lanes(x[2], x[3]) }),
        a2 == (if hi { unpackhi8_lanes(x[4], x[5]) } else { unpacklo8_lanes(x[4], x[5]) }),
        a3 == (if hi { unpackhi8_lanes(x[6], x[7]) } else { unpacklo8_lanes(x[6], x[7]) }),
        u16s(p) == (if h16 { unpackhi16_lanes(u16s(a0), u16s(a1)) } else { unpacklo16_lanes(u16s(a0), u16s(a1)) }),
        u16s(q) == (if h16 { unpackhi16_lanes(u16s(a2), u16s(a3)) } else { unpacklo16_lanes(u16s(a2), u16s(a3)) }),
        u32s(c) == (if h32 { unpackhi32_lanes(u32s(p), u32s(q)) } else { unpacklo32_lanes(u32s(p), u32s(q)) }),
    ensures
        forall|m: int|
            0 <= m < 16 ==> #[trigger] c[m] == x[m % 8][(if hi { 8int } else { 0 }) + (if h16 { 4int } else { 0 }) + (
            if h32 { 2int } else { 0 }) + m / 8],
{
    hide(u16s);
    hide(u32s);
    hide(unpacklo8_lanes);
    hide(unpackhi8_lanes);
    hide(unpacklo16_lanes);
    hide(unpackhi16_lanes);
    hide(unpacklo32_lanes);
    hide(unpackhi32_lanes);
    lemma_unpack8_bytes(x[0], x[1], a0, hi);
    lemma_unpack8_bytes(x[2], x[3], a1, hi);
    lemma_unpack8_bytes(x[4], x[5], a2, hi);
    lemma_unpack8_bytes(x[6], x[7], a3, hi);
    lemma_unpack16_bytes(a0, a1, p, h16);
    lemma_unpack16_bytes(a2, a3, q, h16);
    lemma_unpack32_bytes(p, q, c, h32);
    let o: int = (if hi { 8int } else { 0 }) + (if h16 { 4int } else { 0 }) + (if h32 { 2int } else { 0 });
    assert forall|m: int| 0 <= m < 16 implies #[trigger] c[m] == x[m % 8][o + m / 8] by {
        lemma_tr8_at(m);
    }
}

/// The byte indices `lemma_tr8` meets are a case split on `m`.
proof fn lemma_tr8_at(m: int)
    requires
        0 <= m < 16,
    ensures
        m == 0 || m == 1 || m == 2 || m == 3 || m == 4 || m == 5 || m == 6 || m == 7 || m == 8 || m == 9 || m == 10
            || m == 11 || m == 12 || m == 13 || m == 14 || m == 15,
{
}

/// Eight 16-byte rows to four vectors of two columns each, by three
/// rounds of interleaves (of bytes, 16-bit and 32-bit lanes): vector `n`
/// has column `2n` of the rows in its low half and column `2n + 1` in its
/// high half, the columns counted from 8 when `hi`.
#[inline(always)]
fn tr8<V: Lfv>(x: [V; 8], hi: bool) -> (c: [V; 4])
    requires
        V::ok(),
    ensures
        forall|n: int, m: int|
            #[trigger] gat(n, m) && 0 <= n < 4 && 0 <= m < 16 ==> vb(c[n])[m] == vb(x[m % 8])[(if hi {
                8int
            } else {
                0
            }) + 2 * n + m / 8],
{
    broadcast use lemma_vb_len;
    let a0 = if hi { V::unpackhi8(x[0], x[1]) } else { V::unpacklo8(x[0], x[1]) };
    let a1 = if hi { V::unpackhi8(x[2], x[3]) } else { V::unpacklo8(x[2], x[3]) };
    let a2 = if hi { V::unpackhi8(x[4], x[5]) } else { V::unpacklo8(x[4], x[5]) };
    let a3 = if hi { V::unpackhi8(x[6], x[7]) } else { V::unpacklo8(x[6], x[7]) };
    let b0 = V::unpacklo16(a0, a1);
    let b1 = V::unpackhi16(a0, a1);
    let b2 = V::unpacklo16(a2, a3);
    let b3 = V::unpackhi16(a2, a3);
    let c = [
        V::unpacklo32(b0, b2), V::unpackhi32(b0, b2),
        V::unpacklo32(b1, b3), V::unpackhi32(b1, b3),
    ];
    proof {
        lemma_tr8(
            vrows(x),
            vb(a0),
            vb(a1),
            vb(a2),
            vb(a3),
            vb(b0),
            vb(b1),
            vb(b2),
            vb(b3),
            vb(c[0]),
            vb(c[1]),
            vb(c[2]),
            vb(c[3]),
            hi,
        );
        assert forall|n: int, m: int| #[trigger] gat(n, m) && 0 <= n < 4 && 0 <= m < 16 implies vb(c[n])[m] == vb(
            x[m % 8],
        )[(if hi { 8int } else { 0 }) + 2 * n + m / 8] by {
            assert(vrows(x)[m % 8] == vb(x[m % 8]));
            assert(n == 0 || n == 1 || n == 2 || n == 3);
        }
    }
    c
}

/// Sixteen rows of eight bytes (in the low halves) to eight columns of
/// sixteen: byte `m` of column `k` is byte `k` of row `m`.
#[inline(always)]
fn to_cols<V: Lfv>(x: [V; 16]) -> (r: [V; 8])
    requires
        V::ok(),
    ensures
        forall|k: int, m: int| #[trigger] gat(k, m) && 0 <= k < 8 && 0 <= m < 16 ==> vb(r[k])[m] == vb(x[m])[k],
{
    broadcast use lemma_vb_len;
    let xa = [x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]];
    let xb = [x[8], x[9], x[10], x[11], x[12], x[13], x[14], x[15]];
    let c = tr8(xa, false);
    let e = tr8(xb, false);
    let r = [
        V::unpacklo64(c[0], e[0]), V::unpackhi64(c[0], e[0]),
        V::unpacklo64(c[1], e[1]), V::unpackhi64(c[1], e[1]),
        V::unpacklo64(c[2], e[2]), V::unpackhi64(c[2], e[2]),
        V::unpacklo64(c[3], e[3]), V::unpackhi64(c[3], e[3]),
    ];
    proof {
        lemma_unpack64_bytes(vb(c[0]), vb(e[0]), vb(r[0]), false);
        lemma_unpack64_bytes(vb(c[0]), vb(e[0]), vb(r[1]), true);
        lemma_unpack64_bytes(vb(c[1]), vb(e[1]), vb(r[2]), false);
        lemma_unpack64_bytes(vb(c[1]), vb(e[1]), vb(r[3]), true);
        lemma_unpack64_bytes(vb(c[2]), vb(e[2]), vb(r[4]), false);
        lemma_unpack64_bytes(vb(c[2]), vb(e[2]), vb(r[5]), true);
        lemma_unpack64_bytes(vb(c[3]), vb(e[3]), vb(r[6]), false);
        lemma_unpack64_bytes(vb(c[3]), vb(e[3]), vb(r[7]), true);
        assert forall|m: int| 0 <= m < 16 implies #[trigger] vb(r[0])[m] == vb(x[m])[0] by {
            let mm = 0 + m % 8;
            assert(gat(0, mm));
            assert(mm % 8 == m % 8 && mm / 8 == 0);
            lemma_tr8_at(m);
            if m < 8 {
                assert(m / 8 == 0 && m % 8 == m && m / 16 == 0);
                assert(unpack_at(m, 8, false) == mm);
                assert(vb(r[0])[m] == vb(c[0])[mm]);
                assert(vb(c[0])[mm] == vb(xa[mm % 8])[2 * 0 + mm / 8]);
                assert(xa[m] == x[m]);
            } else {
                assert(m / 8 == 1 && m % 8 == m - 8 && m / 16 == 0);
                assert(unpack_at(m, 8, false) == mm);
                assert(vb(r[0])[m] == vb(e[0])[mm]);
                assert(vb(e[0])[mm] == vb(xb[mm % 8])[2 * 0 + mm / 8]);
                assert(xb[m - 8] == x[m]);
            }
        }
        assert forall|m: int| 0 <= m < 16 implies #[trigger] vb(r[1])[m] == vb(x[m])[1] by {
            let mm = 8 + m % 8;
            assert(gat(0, mm));
            assert(mm % 8 == m % 8 && mm / 8 == 1);
            lemma_tr8_at(m);
            if m < 8 {
                assert(m / 8 == 0 && m % 8 == m && m / 16 == 0);
                assert(unpack_at(m, 8, true) == mm);
                assert(vb(r[1])[m] == vb(c[0])[mm]);
                assert(vb(c[0])[mm] == vb(xa[mm % 8])[2 * 0 + mm / 8]);
                assert(xa[m] == x[m]);
            } else {
                assert(m / 8 == 1 && m % 8 == m - 8 && m / 16 == 0);
                assert(unpack_at(m, 8, true) == mm);
                assert(vb(r[1])[m] == vb(e[0])[mm]);
                assert(vb(e[0])[mm] == vb(xb[mm % 8])[2 * 0 + mm / 8]);
                assert(xb[m - 8] == x[m]);
            }
        }
        assert forall|m: int| 0 <= m < 16 implies #[trigger] vb(r[2])[m] == vb(x[m])[2] by {
            let mm = 0 + m % 8;
            assert(gat(1, mm));
            assert(mm % 8 == m % 8 && mm / 8 == 0);
            lemma_tr8_at(m);
            if m < 8 {
                assert(m / 8 == 0 && m % 8 == m && m / 16 == 0);
                assert(unpack_at(m, 8, false) == mm);
                assert(vb(r[2])[m] == vb(c[1])[mm]);
                assert(vb(c[1])[mm] == vb(xa[mm % 8])[2 * 1 + mm / 8]);
                assert(xa[m] == x[m]);
            } else {
                assert(m / 8 == 1 && m % 8 == m - 8 && m / 16 == 0);
                assert(unpack_at(m, 8, false) == mm);
                assert(vb(r[2])[m] == vb(e[1])[mm]);
                assert(vb(e[1])[mm] == vb(xb[mm % 8])[2 * 1 + mm / 8]);
                assert(xb[m - 8] == x[m]);
            }
        }
        assert forall|m: int| 0 <= m < 16 implies #[trigger] vb(r[3])[m] == vb(x[m])[3] by {
            let mm = 8 + m % 8;
            assert(gat(1, mm));
            assert(mm % 8 == m % 8 && mm / 8 == 1);
            lemma_tr8_at(m);
            if m < 8 {
                assert(m / 8 == 0 && m % 8 == m && m / 16 == 0);
                assert(unpack_at(m, 8, true) == mm);
                assert(vb(r[3])[m] == vb(c[1])[mm]);
                assert(vb(c[1])[mm] == vb(xa[mm % 8])[2 * 1 + mm / 8]);
                assert(xa[m] == x[m]);
            } else {
                assert(m / 8 == 1 && m % 8 == m - 8 && m / 16 == 0);
                assert(unpack_at(m, 8, true) == mm);
                assert(vb(r[3])[m] == vb(e[1])[mm]);
                assert(vb(e[1])[mm] == vb(xb[mm % 8])[2 * 1 + mm / 8]);
                assert(xb[m - 8] == x[m]);
            }
        }
        assert forall|m: int| 0 <= m < 16 implies #[trigger] vb(r[4])[m] == vb(x[m])[4] by {
            let mm = 0 + m % 8;
            assert(gat(2, mm));
            assert(mm % 8 == m % 8 && mm / 8 == 0);
            lemma_tr8_at(m);
            if m < 8 {
                assert(m / 8 == 0 && m % 8 == m && m / 16 == 0);
                assert(unpack_at(m, 8, false) == mm);
                assert(vb(r[4])[m] == vb(c[2])[mm]);
                assert(vb(c[2])[mm] == vb(xa[mm % 8])[2 * 2 + mm / 8]);
                assert(xa[m] == x[m]);
            } else {
                assert(m / 8 == 1 && m % 8 == m - 8 && m / 16 == 0);
                assert(unpack_at(m, 8, false) == mm);
                assert(vb(r[4])[m] == vb(e[2])[mm]);
                assert(vb(e[2])[mm] == vb(xb[mm % 8])[2 * 2 + mm / 8]);
                assert(xb[m - 8] == x[m]);
            }
        }
        assert forall|m: int| 0 <= m < 16 implies #[trigger] vb(r[5])[m] == vb(x[m])[5] by {
            let mm = 8 + m % 8;
            assert(gat(2, mm));
            assert(mm % 8 == m % 8 && mm / 8 == 1);
            lemma_tr8_at(m);
            if m < 8 {
                assert(m / 8 == 0 && m % 8 == m && m / 16 == 0);
                assert(unpack_at(m, 8, true) == mm);
                assert(vb(r[5])[m] == vb(c[2])[mm]);
                assert(vb(c[2])[mm] == vb(xa[mm % 8])[2 * 2 + mm / 8]);
                assert(xa[m] == x[m]);
            } else {
                assert(m / 8 == 1 && m % 8 == m - 8 && m / 16 == 0);
                assert(unpack_at(m, 8, true) == mm);
                assert(vb(r[5])[m] == vb(e[2])[mm]);
                assert(vb(e[2])[mm] == vb(xb[mm % 8])[2 * 2 + mm / 8]);
                assert(xb[m - 8] == x[m]);
            }
        }
        assert forall|m: int| 0 <= m < 16 implies #[trigger] vb(r[6])[m] == vb(x[m])[6] by {
            let mm = 0 + m % 8;
            assert(gat(3, mm));
            assert(mm % 8 == m % 8 && mm / 8 == 0);
            lemma_tr8_at(m);
            if m < 8 {
                assert(m / 8 == 0 && m % 8 == m && m / 16 == 0);
                assert(unpack_at(m, 8, false) == mm);
                assert(vb(r[6])[m] == vb(c[3])[mm]);
                assert(vb(c[3])[mm] == vb(xa[mm % 8])[2 * 3 + mm / 8]);
                assert(xa[m] == x[m]);
            } else {
                assert(m / 8 == 1 && m % 8 == m - 8 && m / 16 == 0);
                assert(unpack_at(m, 8, false) == mm);
                assert(vb(r[6])[m] == vb(e[3])[mm]);
                assert(vb(e[3])[mm] == vb(xb[mm % 8])[2 * 3 + mm / 8]);
                assert(xb[m - 8] == x[m]);
            }
        }
        assert forall|m: int| 0 <= m < 16 implies #[trigger] vb(r[7])[m] == vb(x[m])[7] by {
            let mm = 8 + m % 8;
            assert(gat(3, mm));
            assert(mm % 8 == m % 8 && mm / 8 == 1);
            lemma_tr8_at(m);
            if m < 8 {
                assert(m / 8 == 0 && m % 8 == m && m / 16 == 0);
                assert(unpack_at(m, 8, true) == mm);
                assert(vb(r[7])[m] == vb(c[3])[mm]);
                assert(vb(c[3])[mm] == vb(xa[mm % 8])[2 * 3 + mm / 8]);
                assert(xa[m] == x[m]);
            } else {
                assert(m / 8 == 1 && m % 8 == m - 8 && m / 16 == 0);
                assert(unpack_at(m, 8, true) == mm);
                assert(vb(r[7])[m] == vb(e[3])[mm]);
                assert(vb(e[3])[mm] == vb(xb[mm % 8])[2 * 3 + mm / 8]);
                assert(xb[m - 8] == x[m]);
            }
        }
        assert forall|k: int, m: int| #[trigger] gat(k, m) && 0 <= k < 8 && 0 <= m < 16 implies vb(r[k])[m] == vb(
            x[m],
        )[k] by {
            if k == 0 {
            } else if k == 1 {
            } else if k == 2 {
            } else if k == 3 {
            } else if k == 4 {
            } else if k == 5 {
            } else if k == 6 {
            } else {
            }
        }
    }
    r
}

/// Eight columns of sixteen bytes to sixteen rows of eight, two rows per
/// vector: vector `q` has row `2q` in its low half and row `2q + 1` in its
/// high half.
#[inline(always)]
fn to_rows<V: Lfv>(c: [V; 8]) -> (t: [V; 8])
    requires
        V::ok(),
    ensures
        forall|q: int, m: int|
            #[trigger] gat(q, m) && 0 <= q < 8 && 0 <= m < 16 ==> vb(t[q])[m] == vb(c[m % 8])[2 * q + m / 8],
{
    broadcast use lemma_vb_len;
    let l = tr8(c, false);
    let h = tr8(c, true);
    let t = [l[0], l[1], l[2], l[3], h[0], h[1], h[2], h[3]];
    proof {
        assert forall|q: int, m: int| #[trigger] gat(q, m) && 0 <= q < 8 && 0 <= m < 16 implies vb(t[q])[m] == vb(
            c[m % 8],
        )[2 * q + m / 8] by {
            if q < 4 {
                assert(gat(q, m));
                assert(t[q] == l[q]);
            } else {
                assert(gat(q - 4, m));
                assert(t[q] == h[q - 4]);
            }
        }
    }
    t
}

/// `j` is in row `k` of the `w`-byte rows that start `m` apart from `base`.
pub open spec fn row_at(j: int, base: int, m: int, k: int, w: int) -> bool {
    base + kx(k, m) <= j < base + kx(k, m) + w
}

/// `j` is in one of the rows `lo..hi`.
pub open spec fn rows_cov(j: int, base: int, m: int, lo: int, hi: int, w: int) -> bool {
    exists|k: int| lo <= k < hi && #[trigger] row_at(j, base, m, k, w)
}

/// Loads eight 16-byte rows, `hstride` apart: the rows across a
/// horizontal sixteen-pixel edge.
#[inline(always)]
fn hload16<V: Lfv>(b: &[u8], base: usize, hstride: usize) -> (r: [V; 8])
    requires
        V::ok(),
        hstride >= 1,
        base + 7 * hstride + 16 <= b@.len(),
    ensures
        forall|k: int, i: int|
            #[trigger] gat(k, i) && 0 <= k < 8 && 0 <= i < 16 ==> vb(r[k])[i] == b@[base + kx(k, hstride as int) + i],
{
    broadcast use lemma_vb_len;
    proof {
        assert(b@.len() == b.len());
    }
    let mut r = [V::vzero();8];
    let mut k: usize = 0;
    while k < 8
        invariant
            V::ok(),
            k <= 8,
            hstride >= 1,
            b@.len() <= usize::MAX,
            base + 7 * hstride + 16 <= b@.len(),
            forall|kk: int, i: int|
                #[trigger] gat(kk, i) && 0 <= kk < k && 0 <= i < 16 ==> vb(r[kk])[i] == b@[base + kx(
                    kk,
                    hstride as int,
                ) + i],
        decreases 8 - k,
    {
        proof {
            broadcast use lemma_vb_len;

        }
        proof {
            assert(k * hstride <= 7 * hstride) by (nonlinear_arith)
                requires
                    k < 8,
                    hstride >= 1,
            ;
            assert(k * hstride == kx(k as int, hstride as int));
        }
        let v = V::load16(b, base + k * hstride);
        r[k] = v;
        k = k + 1;
    }
    r
}

/// Loads eight rows of two chroma planes side by side: `bu`'s eight bytes
/// in the low half of each vector, `bv`'s in the high half.
#[inline(always)]
fn hload8x2<V: Lfv>(bu: &[u8], bv: &[u8], base: usize, hstride: usize) -> (r: [V; 8])
    requires
        V::ok(),
        hstride >= 1,
        base + 7 * hstride + 8 <= bu@.len(),
        base + 7 * hstride + 8 <= bv@.len(),
    ensures
        forall|k: int, i: int|
            #[trigger] gat(k, i) && 0 <= k < 8 && 0 <= i < 8 ==> vb(r[k])[i] == bu@[base + kx(k, hstride as int) + i],
        forall|k: int, i: int|
            #[trigger] gat(k, i) && 0 <= k < 8 && 0 <= i < 8 ==> vb(r[k])[8 + i] == bv@[base + kx(k, hstride as int)
                + i],
{
    broadcast use lemma_vb_len;
    proof {
        assert(bu@.len() == bu.len());
        assert(bv@.len() == bv.len());
    }
    let mut r = [V::vzero();8];
    let mut k: usize = 0;
    while k < 8
        invariant
            V::ok(),
            k <= 8,
            hstride >= 1,
            bu@.len() <= usize::MAX,
            bv@.len() <= usize::MAX,
            base + 7 * hstride + 8 <= bu@.len(),
            base + 7 * hstride + 8 <= bv@.len(),
            forall|kk: int, i: int|
                #[trigger] gat(kk, i) && 0 <= kk < k && 0 <= i < 8 ==> vb(r[kk])[i] == bu@[base + kx(
                    kk,
                    hstride as int,
                ) + i],
            forall|kk: int, i: int|
                #[trigger] gat(kk, i) && 0 <= kk < k && 0 <= i < 8 ==> vb(r[kk])[8 + i] == bv@[base + kx(
                    kk,
                    hstride as int,
                ) + i],
        decreases 8 - k,
    {
        proof {
            broadcast use lemma_vb_len;

        }
        proof {
            assert(k * hstride <= 7 * hstride) by (nonlinear_arith)
                requires
                    k < 8,
                    hstride >= 1,
            ;
            assert(k * hstride == kx(k as int, hstride as int));
        }
        let lu = V::loadl8(bu, base + k * hstride);
        let lv = V::loadl8(bv, base + k * hstride);
        let v = V::unpacklo64(lu, lv);
        proof {
            lemma_unpack64_bytes(vb(lu), vb(lv), vb(v), false);
            assert forall|i: int| #[trigger] gat(k as int, i) && 0 <= i < 8 implies vb(v)[i] == bu@[base + k * hstride + i] && vb(v)[8 + i]
                == bv@[base + k * hstride + i] by {
                assert(i / 8 == 0 && i % 8 == i && (8 + i) / 8 == 1 && (8 + i) % 8 == i);
                assert(i / 16 == 0 && (8 + i) / 16 == 0);
                assert(unpack_at(i, 8, false) == i && unpack_at(8 + i, 8, false) == i);
                assert(vb(v)[i] == vb(lu)[i]);
                assert(vb(v)[8 + i] == vb(lv)[i]);
            }
        }
        r[k] = v;
        k = k + 1;
    }
    r
}

/// Stores rows `lo..hi` of eight row vectors, `hstride` apart: all sixteen
/// bytes of each (`half == 0`), its low eight (`1`) or its high eight (`2`).
#[inline(always)]
fn hstore<V: Lfv>(b: &mut [u8], base: usize, hstride: usize, o: [V; 8], lo: usize, hi: usize, half: u8)
    requires
        V::ok(),
        hstride >= 1,
        1 <= lo <= hi <= 7,
        half <= 2,
        base + 6 * hstride + (if half == 0 { 16int } else { 8 }) <= old(b)@.len(),
    ensures
        final(b)@.len() == old(b)@.len(),
        hstride >= (if half == 0 { 16int } else { 8 }) ==> forall|k: int, i: int|
            #[trigger] gat(k, i) && lo <= k < hi && 0 <= i < (if half == 0 { 16int } else { 8 }) ==> final(b)@[base + kx(
                k,
                hstride as int,
            ) + i] == vb(o[k])[(if half == 2 { 8int } else { 0 }) + i],
        forall|j: int|
            0 <= j < old(b)@.len() ==> final(b)@[j] == old(b)@[j] || rows_cov(
                j,
                base as int,
                hstride as int,
                lo as int,
                hi as int,
                if half == 0 { 16int } else { 8 },
            ),
{
    broadcast use lemma_vb_len;
    let ghost b0 = b@;
    let ghost hs = hstride as int;
    let ghost w: int = if half == 0 { 16 } else { 8 };
    let ghost off: int = if half == 2 { 8 } else { 0 };
    proof {
        assert(b@.len() == b.len());
        lemma_kx(hs);
    }
    let mut k: usize = lo;
    while k < hi
        invariant
            V::ok(),
            lo <= k <= hi,
            hi <= 7,
            1 <= lo,
            half <= 2,
            hstride >= 1,
            hs == hstride as int,
            w == (if half == 0 { 16int } else { 8 }),
            off == (if half == 2 { 8int } else { 0 }),
            b@.len() <= usize::MAX,
            b@.len() == b0.len(),
            base + 6 * hstride + w <= b@.len(),
            forall|a: int, b: int| #![trigger kx(a, hs), kx(b, hs)] 0 <= a < b ==> kx(a, hs) + hs <= kx(b, hs),
            hstride >= w ==> forall|kk: int, i: int|
                #[trigger] gat(kk, i) && lo <= kk < k && 0 <= i < w ==> b@[base + kx(kk, hs) + i] == vb(o[kk])[off
                    + i],
            forall|j: int| 0 <= j < b0.len() ==> b@[j] == b0[j] || rows_cov(j, base as int, hs, lo as int, k as int, w),
        decreases hi - k,
    {
        proof {
            broadcast use lemma_vb_len;

        }
        proof {
            assert(k * hstride <= 6 * hstride) by (nonlinear_arith)
                requires
                    k < 7,
                    hstride >= 1,
            ;
            assert(k * hstride == kx(k as int, hs));
        }
        let ghost b1 = b@;
        let s = base + k * hstride;
        let v = o[k];
        if half == 0 {
            V::store16(b, s, v);
        } else if half == 1 {
            V::storel8(b, s, v);
        } else {
            let h = V::unpackhi64(v, v);
            proof {
                lemma_unpack64_bytes(vb(v), vb(v), vb(h), true);
                assert forall|i: int| 0 <= i < 8 implies vb(h)[i] == vb(v)[8 + i] by {
                    assert(i / 8 == 0 && i % 8 == i && i / 16 == 0);
                    assert(unpack_at(i, 8, true) == 8 + i);
                }
            }
            V::storel8(b, s, h);
        }
        proof {
            assert forall|i: int| #[trigger] gat(k as int, i) && 0 <= i < w implies b@[s + i] == vb(v)[off + i] by {}
            assert forall|j: int| 0 <= j < b0.len() && !(s <= j < s + w) implies b@[j] == b1[j] by {}
            assert forall|j: int| 0 <= j < b0.len() implies b@[j] == b0[j] || rows_cov(
                j,
                base as int,
                hs,
                lo as int,
                k + 1,
                w,
            ) by {
                if s <= j < s + w {
                    assert(row_at(j, base as int, hs, k as int, w));
                } else if b1[j] != b0[j] {
                    let kk = choose|kk: int| lo <= kk < k && #[trigger] row_at(j, base as int, hs, kk, w);
                    assert(row_at(j, base as int, hs, kk, w));
                }
            }
            if hstride >= w {
                assert forall|kk: int, i: int| #[trigger] gat(kk, i) && lo <= kk < k + 1 && 0 <= i < w implies b@[base
                    + kx(kk, hs) + i] == vb(o[kk])[off + i] by {
                    if kk < k {
                        assert(kx(kk, hs) + hs <= kx(k as int, hs));
                        assert(b1[base + kx(kk, hs) + i] == vb(o[kk])[off + i]);
                    }
                }
            }
        }
        k = k + 1;
    }
}

/// Loads `n` rows of eight bytes, `vstride` apart, into the low halves of
/// `x[first..]`: the lanes of a vertical edge, one per row.
#[inline(always)]
fn vload<V: Lfv>(b: &[u8], base: usize, vstride: usize, x: [V; 16], first: usize, n: usize) -> (r: [V; 16])
    requires
        V::ok(),
        vstride >= 1,
        n >= 1,
        first + n <= 16,
        base + (n - 1) * vstride + 8 <= b@.len(),
    ensures
        forall|c: int, i: int|
            #[trigger] gat(c, i) && 0 <= c < 8 && 0 <= i < n ==> vb(r[first + i])[c] == b@[base + kx(
                i,
                vstride as int,
            ) + c],
        forall|m: int| 0 <= m < 16 && !(first <= m < first + n) ==> r[m] == x[m],
{
    broadcast use lemma_vb_len;
    proof {
        assert(b@.len() == b.len());
    }
    let mut r = x;
    let mut i: usize = 0;
    while i < n
        invariant
            V::ok(),
            i <= n,
            vstride >= 1,
            first + n <= 16,
            b@.len() <= usize::MAX,
            base + (n - 1) * vstride + 8 <= b@.len(),
            forall|c: int, ii: int|
                #[trigger] gat(c, ii) && 0 <= c < 8 && 0 <= ii < i ==> vb(r[first + ii])[c] == b@[base + kx(
                    ii,
                    vstride as int,
                ) + c],
            forall|m: int| 0 <= m < 16 && !(first <= m < first + i) ==> r[m] == x[m],
        decreases n - i,
    {
        proof {
            broadcast use lemma_vb_len;

        }
        proof {
            assert(i * vstride <= (n - 1) * vstride) by (nonlinear_arith)
                requires
                    i < n,
                    vstride >= 1,
            ;
            assert(i * vstride == kx(i as int, vstride as int));
        }
        let v = V::loadl8(b, base + i * vstride);
        proof {
            assert forall|c: int| 0 <= c < 8 implies vb(v)[c] == b@[base + i * vstride + c] by {}
        }
        r[first + i] = v;
        i = i + 1;
    }
    r
}

/// Stores `2 * n` rows of eight bytes, `vstride` apart: rows `2m` and
/// `2m + 1` are the low and high halves of `t[first + m]`.
#[inline(always)]
fn vstore<V: Lfv>(b: &mut [u8], base: usize, vstride: usize, t: [V; 8], first: usize, n: usize)
    requires
        V::ok(),
        vstride >= 1,
        n >= 1,
        first + n <= 8,
        base + (2 * n - 1) * vstride + 8 <= old(b)@.len(),
    ensures
        final(b)@.len() == old(b)@.len(),
        vstride >= 8 ==> forall|c: int, i: int|
            #[trigger] gat(c, i) && 0 <= c < 8 && 0 <= i < 2 * n ==> final(b)@[base + kx(i, vstride as int) + c] == vb(
                t[first + i / 2],
            )[8 * (i % 2) + c],
        forall|j: int|
            0 <= j < old(b)@.len() ==> final(b)@[j] == old(b)@[j] || rows_cov(j, base as int, vstride as int, 0, 2 * n, 8),
{
    broadcast use lemma_vb_len;
    let ghost b0 = b@;
    let ghost vs = vstride as int;
    proof {
        assert(b@.len() == b.len());
        lemma_kx(vs);
    }
    let mut m: usize = 0;
    while m < n
        invariant
            V::ok(),
            m <= n,
            first + n <= 8,
            vstride >= 1,
            vs == vstride as int,
            b@.len() <= usize::MAX,
            b@.len() == b0.len(),
            base + (2 * n - 1) * vstride + 8 <= b@.len(),
            forall|a: int, b: int| #![trigger kx(a, vs), kx(b, vs)] 0 <= a < b ==> kx(a, vs) + vs <= kx(b, vs),
            vstride >= 8 ==> forall|c: int, i: int|
                #[trigger] gat(c, i) && 0 <= c < 8 && 0 <= i < 2 * m ==> b@[base + kx(i, vs) + c] == vb(
                    t[first + i / 2],
                )[8 * (i % 2) + c],
            forall|j: int| 0 <= j < b0.len() ==> b@[j] == b0[j] || rows_cov(j, base as int, vs, 0, 2 * m, 8),
        decreases n - m,
    {
        proof {
            broadcast use lemma_vb_len;

        }
        proof {
            assert((2 * m + 1) * vstride <= (2 * n - 1) * vstride) by (nonlinear_arith)
                requires
                    m < n,
                    vstride >= 1,
            ;
            assert(2 * m * vstride == kx(2 * m, vs));
            assert((2 * m + 1) * vstride == kx(2 * m + 1, vs));
            assert(kx(2 * m, vs) + vs <= kx(2 * m + 1, vs));
        }
        let ghost b1 = b@;
        let v = t[first + m];
        let s1 = base + 2 * m * vstride;
        let s2 = base + (2 * m + 1) * vstride;
        V::storel8(b, s1, v);
        let ghost b2 = b@;
        let h = V::unpackhi64(v, v);
        V::storel8(b, s2, h);
        proof {
            lemma_unpack64_bytes(vb(v), vb(v), vb(h), true);
            assert forall|c: int| 0 <= c < 8 implies vb(h)[c] == vb(v)[8 + c] by {
                assert(c / 8 == 0 && c % 8 == c && c / 16 == 0);
                assert(unpack_at(c, 8, true) == 8 + c);
            }
            assert forall|j: int| 0 <= j < b0.len() && !(s1 <= j < s1 + 8) implies b2[j] == b1[j] by {}
            assert forall|j: int| 0 <= j < b0.len() && !(s2 <= j < s2 + 8) implies b@[j] == b2[j] by {}
            assert forall|c: int| #[trigger] gat(c, 2 * m as int) && 0 <= c < 8 implies b2[s1 + c] == vb(v)[c] by {}
            assert forall|c: int| #[trigger] gat(c, 2 * m + 1) && 0 <= c < 8 implies b@[s2 + c] == vb(v)[8 + c] by {}
            assert forall|j: int| 0 <= j < b0.len() implies b@[j] == b0[j] || rows_cov(
                j,
                base as int,
                vs,
                0,
                2 * m + 2,
                8,
            ) by {
                if s1 <= j < s1 + 8 {
                    assert(row_at(j, base as int, vs, 2 * m, 8));
                } else if s2 <= j < s2 + 8 {
                    assert(row_at(j, base as int, vs, 2 * m + 1, 8));
                } else if b1[j] != b0[j] {
                    let kk = choose|kk: int| 0 <= kk < 2 * m && #[trigger] row_at(j, base as int, vs, kk, 8);
                    assert(row_at(j, base as int, vs, kk, 8));
                }
            }
            if vstride >= 8 {
                assert forall|c: int, i: int| #[trigger] gat(c, i) && 0 <= c < 8 && 0 <= i < 2 * m + 2 implies b@[base
                    + kx(i, vs) + c] == vb(t[first + i / 2])[8 * (i % 2) + c] by {
                    if i < 2 * m {
                        assert(kx(i, vs) + vs <= kx(2 * m, vs));
                        assert(b1[base + kx(i, vs) + c] == vb(t[first + i / 2])[8 * (i % 2) + c]);
                    } else if i == 2 * m {
                        assert(i / 2 == m && i % 2 == 0);
                    } else {
                        assert(i == 2 * m + 1);
                        assert(i / 2 == m && i % 2 == 1);
                    }
                }
            }
        }
        m = m + 1;
    }
}

/// A horizontal edge filtered in registers is the run: rows loaded from
/// `b0` into `r`, filtered into `o`, and rows `p2..q2` (or `p1..q1` for the
/// inner filter, which leaves `p2` and `q2`) stored into `b1`.
proof fn lemma_h_done<V: Lfv>(
    b0: Seq<u8>,
    b1: Seq<u8>,
    p: int,
    hs: int,
    size: int,
    l0: int,
    r: [V; 8],
    o: [V; 8],
    inner: bool,
    th: int,
    it: int,
    ht: int,
)
    requires
        run_ok(b0.len(), p, hs, 1, size),
        hs >= size,
        0 <= l0,
        l0 + size <= 16,
        b1.len() == b0.len(),
        forall|k: int, i: int|
            #[trigger] gat(k, i) && 0 <= k < 8 && 0 <= i < size ==> vb(r[k])[l0 + i] == b0[p - 4 * hs + kx(k, hs) + i],
        forall|j: int|
            0 <= j < 16 ==> #[trigger] blk_lane(vblk(o), j) == lf_kernel(blk_lane(vblk(r), j), false, inner, th, it, ht),
        inner ==> o[1] == r[1] && o[6] == r[6],
        forall|k: int, i: int|
            #[trigger] gat(k, i) && (if inner { 2int } else { 1 }) <= k < (if inner { 6int } else { 7 }) && 0 <= i < size
                ==> b1[p - 4 * hs + kx(k, hs) + i] == vb(o[k])[l0 + i],
        forall|j: int|
            0 <= j < b0.len() ==> b1[j] == b0[j] || rows_cov(
                j,
                p - 4 * hs,
                hs,
                if inner { 2int } else { 1 },
                if inner { 6int } else { 7 },
                size,
            ),
    ensures
        b1 == lf_run(b0, p, hs, 1, size as nat, false, inner, th, it, ht),
{
    broadcast use lemma_vb_len;
    let ra = vblk(r);
    let rb = vblk(o);
    let lo: int = if inner { 2 } else { 1 };
    let hi: int = if inner { 6 } else { 7 };
    let base = p - 4 * hs;
    lemma_vblk(r);
    lemma_vblk(o);
    lemma_kx(hs);
    assert(kx(1, hs) == hs && kx(2, hs) == 2 * hs && kx(3, hs) == 3 * hs && kx(4, hs) == 4 * hs && kx(5, hs) == 5 * hs
        && kx(6, hs) == 6 * hs);
    assert forall|kk: int, i: int| #[trigger] gat(kk, i) && 0 <= kk < 8 && 0 <= i < size implies ra[16 * kk + l0 + i]
        == b0[p - 4 * hs + kx(kk, hs) + i] by {
        assert(gat(kk, l0 + i));
    }
    lemma_gather_rows(b0, ra, ra, p, hs, size, l0);
    assert forall|kk: int, i: int| #[trigger] gat(kk, i) && 1 <= kk < 7 && 0 <= i < size implies b1[p - 4 * hs + kx(
        kk,
        hs,
    ) + i] == rb[16 * kk + l0 + i] by {
        assert(gat(kk, l0 + i));
        assert(kk == 1 || kk == 2 || kk == 3 || kk == 4 || kk == 5 || kk == 6);
        if !(lo <= kk < hi) {
            let j = base + kx(kk, hs) + i;
            if b1[j] != b0[j] {
                let k2 = choose|k2: int| lo <= k2 < hi && #[trigger] row_at(j, base, hs, k2, size);
                if k2 < kk {
                    assert(kx(k2, hs) + hs <= kx(kk, hs));
                } else {
                    assert(kx(kk, hs) + hs <= kx(k2, hs));
                }
            }
            assert(o[kk] == r[kk]);
        }
    }
    assert forall|j: int| 0 <= j < b0.len() implies b1[j] == b0[j] || lane_cov6(j, p, hs, 1, size) by {
        if b1[j] != b0[j] {
            let k = choose|k: int| lo <= k < hi && #[trigger] row_at(j, base, hs, k, size);
            let i = j - base - kx(k, hs);
            assert(k == 1 || k == 2 || k == 3 || k == 4 || k == 5 || k == 6);
            assert(kx(i, 1) == i);
            assert(lane_has6(j, p, hs, 1, i));
        }
    }
    lemma_scatter_rows(b0, b1, rb, p, hs, size, l0);
    lemma_block_done(b0, b1, p, hs, 1, size, l0, ra, rb, false, inner, th, it, ht);
}

/// A vertical edge filtered in registers is the run: each lane's eight
/// bytes loaded from `b0`, transposed into `r`, filtered into `o`, and
/// transposed back and stored into `b1`.
proof fn lemma_v_done<V: Lfv>(
    b0: Seq<u8>,
    b1: Seq<u8>,
    p: int,
    vs: int,
    size: int,
    l0: int,
    r: [V; 8],
    o: [V; 8],
    inner: bool,
    th: int,
    it: int,
    ht: int,
)
    requires
        run_ok(b0.len(), p, 1, vs, size),
        vs >= 8,
        0 <= l0,
        l0 + size <= 16,
        b1.len() == b0.len(),
        forall|c: int, i: int|
            #[trigger] gat(c, i) && 0 <= c < 8 && 0 <= i < size ==> vb(r[c])[l0 + i] == b0[p - 4 + kx(i, vs) + c],
        forall|j: int|
            0 <= j < 16 ==> #[trigger] blk_lane(vblk(o), j) == lf_kernel(blk_lane(vblk(r), j), false, inner, th, it, ht),
        forall|c: int, i: int|
            #[trigger] gat(c, i) && 0 <= c < 8 && 0 <= i < size ==> b1[p - 4 + kx(i, vs) + c] == vb(o[c])[l0 + i],
        forall|j: int| 0 <= j < b0.len() ==> b1[j] == b0[j] || rows_cov(j, p - 4, vs, 0, size, 8),
    ensures
        b1 == lf_run(b0, p, 1, vs, size as nat, false, inner, th, it, ht),
{
    broadcast use lemma_vb_len;
    let ra = vblk(r);
    let rb = vblk(o);
    lemma_vblk(r);
    lemma_vblk(o);
    assert forall|l: int| 0 <= l < size implies blk_lane(ra, l0 + l) == lf_lane(b0, p + #[trigger] kx(l, vs), 1) by {
        assert(gat(0, l) && gat(1, l) && gat(2, l) && gat(3, l) && gat(4, l) && gat(5, l) && gat(6, l) && gat(7, l));
        assert(blk_lane(ra, l0 + l) == vedge(r, l0 + l));
    }
    assert forall|l: int| 0 <= l < size implies lf_lane(b1, p + #[trigger] kx(l, vs), 1) == blk_lane(rb, l0 + l) by {
        assert(gat(0, l) && gat(1, l) && gat(2, l) && gat(3, l) && gat(4, l) && gat(5, l) && gat(6, l) && gat(7, l));
        assert(blk_lane(rb, l0 + l) == vedge(o, l0 + l));
    }
    assert forall|j: int| 0 <= j < b0.len() && !lane_cov(j, p, 1, vs, size) implies b1[j] == b0[j] by {
        if b1[j] != b0[j] {
            let i = choose|i: int| 0 <= i < size && #[trigger] row_at(j, p - 4, vs, i, 8);
            assert(lane_has(j, p, 1, vs, i));
        }
    }
    lemma_block_done(b0, b1, p, 1, vs, size, l0, ra, rb, false, inner, th, it, ht);
}

/// `filter_block` for a sixteen-pixel edge, in registers: a
/// horizontal edge's eight rows are loaded as they are and rows `p2..q2`
/// (`p1..q1` for the inner filter) stored back; a vertical edge's sixteen
/// 8-byte lanes are loaded, transposed, filtered, transposed back and
/// stored whole.
#[inline(always)]
fn filter16_vec<V: Lfv>(b: &mut [u8], p: usize, hstride: usize, vstride: usize, th: u8, it: u8, ht: u8, inner: bool)
    requires
        V::ok(),
        run_ok(old(b)@.len(), p as int, hstride as int, vstride as int, 16),
    ensures
        final(b)@.len() == old(b)@.len(),
        th <= 254 && lanes_apart(hstride as int, vstride as int, 16) ==> final(b)@ == lf_run(
            old(b)@,
            p as int,
            hstride as int,
            vstride as int,
            16,
            false,
            inner,
            th as int,
            it as int,
            ht as int,
        ),
{
    broadcast use lemma_vb_len;
    let ghost b0 = b@;
    proof {
        assert(b@.len() == b.len());
    }
    let base = p - 4 * hstride;
    if vstride == 1 {
        let r = hload16::<V>(b, base, hstride);
        let o = kernel_vec(r, th, it, ht, inner);
        let lo: usize = if inner { 2 } else { 1 };
        let hi: usize = if inner { 6 } else { 7 };
        hstore(b, base, hstride, o, lo, hi, 0);
        proof {
            if th <= 254 && hstride >= 16 {
                lemma_h_done(b0, b@, p as int, hstride as int, 16, 0, r, o, inner, th as int, it as int, ht as int);
            }
        }
    } else {
        let z = [V::vzero();16];
        let x = vload(b, base, vstride, z, 0, 16);
        let r = to_cols(x);
        let o = kernel_vec(r, th, it, ht, inner);
        let t = to_rows(o);
        vstore(b, base, vstride, t, 0, 8);
        proof {
            if th <= 254 && hstride == 1 && vstride >= 8 {
                let vs = vstride as int;
                assert forall|c: int, i: int| #[trigger] gat(c, i) && 0 <= c < 8 && 0 <= i < 16 implies vb(r[c])[0 + i]
                    == b0[p - 4 + kx(i, vs) + c] by {
                    assert(vb(r[c])[i] == vb(x[i])[c]);
                    assert(vb(x[0 + i])[c] == b0[base + kx(i, vs) + c]);
                }
                assert forall|c: int, i: int| #[trigger] gat(c, i) && 0 <= c < 8 && 0 <= i < 16 implies b@[p - 4 + kx(
                    i,
                    vs,
                ) + c] == vb(o[c])[0 + i] by {
                    let q = i / 2;
                    let m = 8 * (i % 2) + c;
                    assert(gat(q, m));
                    assert(m % 8 == c && m / 8 == i % 2);
                    assert(b@[base + kx(i, vs) + c] == vb(t[0 + q])[m]);
                }
                lemma_v_done(b0, b@, p as int, vs, 16, 0, r, o, inner, th as int, it as int, ht as int);
            }
        }
    }
}

/// `filter16_vec` for the same eight-pixel edge of both chroma planes:
/// `bu`'s lanes are the low eight of the sixteen, `bv`'s the high eight.
#[inline(always)]
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn filter8uv_vec<V: Lfv>(
    bu: &mut [u8],
    bv: &mut [u8],
    p: usize,
    hstride: usize,
    vstride: usize,
    th: u8,
    it: u8,
    ht: u8,
    inner: bool,
)
    requires
        V::ok(),
        run_ok(old(bu)@.len(), p as int, hstride as int, vstride as int, 8),
        run_ok(old(bv)@.len(), p as int, hstride as int, vstride as int, 8),
    ensures
        final(bu)@.len() == old(bu)@.len(),
        final(bv)@.len() == old(bv)@.len(),
        th <= 254 && lanes_apart(hstride as int, vstride as int, 8) ==> final(bu)@ == lf_run(
            old(bu)@,
            p as int,
            hstride as int,
            vstride as int,
            8,
            false,
            inner,
            th as int,
            it as int,
            ht as int,
        ),
        th <= 254 && lanes_apart(hstride as int, vstride as int, 8) ==> final(bv)@ == lf_run(
            old(bv)@,
            p as int,
            hstride as int,
            vstride as int,
            8,
            false,
            inner,
            th as int,
            it as int,
            ht as int,
        ),
{
    broadcast use lemma_vb_len;
    let ghost bu0 = bu@;
    let ghost bv0 = bv@;
    proof {
        assert(bu@.len() == bu.len());
        assert(bv@.len() == bv.len());
    }
    let base = p - 4 * hstride;
    if vstride == 1 {
        let r = hload8x2::<V>(bu, bv, base, hstride);
        let o = kernel_vec(r, th, it, ht, inner);
        let lo: usize = if inner { 2 } else { 1 };
        let hi: usize = if inner { 6 } else { 7 };
        hstore(bu, base, hstride, o, lo, hi, 1);
        hstore(bv, base, hstride, o, lo, hi, 2);
        proof {
            if th <= 254 && hstride >= 8 {
                lemma_h_done(bu0, bu@, p as int, hstride as int, 8, 0, r, o, inner, th as int, it as int, ht as int);
                lemma_h_done(bv0, bv@, p as int, hstride as int, 8, 8, r, o, inner, th as int, it as int, ht as int);
            }
        }
    } else {
        let z = [V::vzero();16];
        let x1 = vload(bu, base, vstride, z, 0, 8);
        let x = vload(bv, base, vstride, x1, 8, 8);
        let r = to_cols(x);
        let o = kernel_vec(r, th, it, ht, inner);
        let t = to_rows(o);
        vstore(bu, base, vstride, t, 0, 4);
        vstore(bv, base, vstride, t, 4, 4);
        proof {
            if th <= 254 && hstride == 1 && vstride >= 8 {
                let vs = vstride as int;
                assert forall|c: int, i: int| #[trigger] gat(c, i) && 0 <= c < 8 && 0 <= i < 8 implies vb(r[c])[0 + i]
                    == bu0[p - 4 + kx(i, vs) + c] by {
                    assert(vb(r[c])[i] == vb(x[i])[c]);
                    assert(x[i] == x1[i]);
                    assert(vb(x1[0 + i])[c] == bu0[base + kx(i, vs) + c]);
                }
                assert forall|c: int, i: int| #[trigger] gat(c, i) && 0 <= c < 8 && 0 <= i < 8 implies vb(r[c])[8 + i]
                    == bv0[p - 4 + kx(i, vs) + c] by {
                    assert(gat(c, 8 + i));
                    assert(vb(r[c])[8 + i] == vb(x[8 + i])[c]);
                    assert(vb(x[8 + i])[c] == bv0[base + kx(i, vs) + c]);
                }
                assert forall|c: int, i: int| #[trigger] gat(c, i) && 0 <= c < 8 && 0 <= i < 8 implies bu@[p - 4 + kx(
                    i,
                    vs,
                ) + c] == vb(o[c])[0 + i] by {
                    let q = i / 2;
                    let m = 8 * (i % 2) + c;
                    assert(gat(q, m));
                    assert(m % 8 == c && m / 8 == i % 2);
                    assert(bu@[base + kx(i, vs) + c] == vb(t[0 + q])[m]);
                }
                assert forall|c: int, i: int| #[trigger] gat(c, i) && 0 <= c < 8 && 0 <= i < 8 implies bv@[p - 4 + kx(
                    i,
                    vs,
                ) + c] == vb(o[c])[8 + i] by {
                    let q = 4 + i / 2;
                    let m = 8 * (i % 2) + c;
                    assert(gat(q, m));
                    assert(m % 8 == c && m / 8 == i % 2);
                    assert(bv@[base + kx(i, vs) + c] == vb(t[4 + i / 2])[m]);
                }
                lemma_v_done(bu0, bu@, p as int, vs, 8, 0, r, o, inner, th as int, it as int, ht as int);
                lemma_v_done(bv0, bv@, p as int, vs, 8, 8, r, o, inner, th as int, it as int, ht as int);
            }
        }
    }
}

/// `filter_loop`'s body, inlined with `size` a constant.
#[inline(always)]
fn filter_block(
    b: &mut [u8],
    p: usize,
    hstride: usize,
    vstride: usize,
    size: usize,
    th: u8,
    it: u8,
    ht: u8,
    inner: bool,
)
    requires
        run_ok(old(b)@.len(), p as int, hstride as int, vstride as int, size as int),
    ensures
        final(b)@.len() == old(b)@.len(),
        th <= 254 && lanes_apart(hstride as int, vstride as int, size as int) ==> final(b)@ == lf_run(
            old(b)@,
            p as int,
            hstride as int,
            vstride as int,
            size as nat,
            false,
            inner,
            th as int,
            it as int,
            ht as int,
        ),
{
    let ghost b0 = b@;
    let mut r: [u8; 128] = [0; 128];
    gather(b, p, hstride, vstride, size, &mut r, 0);
    let ghost r1 = r@;
    let lm = vstride != 1 && hstride == 1;
    if lm {
        shuffle_block(&mut r, 4);
        proof {
            lemma_shuf4(r1);
        }
    }
    let ghost ra = r@;
    if inner {
        lanes4(&mut r, th, it, ht);
    } else {
        lanes6(&mut r, th, it, ht);
    }
    let ghost rb = r@;
    if lm {
        shuffle_block(&mut r, 3);
        proof {
            lemma_shuf3(rb);
        }
    }
    scatter(b, p, hstride, vstride, size, &r, 0);
    proof {
        if th <= 254 && lanes_apart(hstride as int, vstride as int, size as int) {
            lemma_block_ends(b0, b@, p as int, hstride as int, vstride as int, size as int, 0, r1, ra, rb, r@);
            lemma_block_done(
                b0,
                b@,
                p as int,
                hstride as int,
                vstride as int,
                size as int,
                0,
                ra,
                rb,
                false,
                inner,
                th as int,
                it as int,
                ht as int,
            );
        }
    }
}

/// `FilterLoop26` (`inner == false`) and `FilterLoop24` (`inner`), all
/// lanes at once.
pub fn filter_loop(
    b: &mut [u8],
    p: usize,
    hstride: usize,
    vstride: usize,
    size: usize,
    thresh: i32,
    ithresh: i32,
    hev_thresh: i32,
    inner: bool,
)
    requires
        run_ok(old(b)@.len(), p as int, hstride as int, vstride as int, size as int),
        0 <= thresh <= 0x1000,
    ensures
        final(b)@.len() == old(b)@.len(),
        lanes_apart(hstride as int, vstride as int, size as int) ==> final(b)@ == lf_run(
            old(b)@,
            p as int,
            hstride as int,
            vstride as int,
            size as nat,
            false,
            inner,
            thresh as int,
            ithresh as int,
            hev_thresh as int,
        ),
{
    // The byte arithmetic needs byte thresholds; the decoder's always are
    // (`thresh` at most 193), and anything else takes the reference path
    // (at 255, `NeedsFilter_SSE2`'s saturated sum would pass everything).
    if thresh > 254 || ithresh < 0 || ithresh > 255 || hev_thresh < 0 || hev_thresh > 255 {
        filter_loop_ref(b, p, hstride, vstride, size, thresh, ithresh, hev_thresh, inner);
        return;
    }
    let th = thresh as u8;
    let it = ithresh as u8;
    let ht = hev_thresh as u8;
    // A sixteen-pixel edge is filtered in registers: NEON's on AArch64,
    // SSE2's elsewhere (x86-64, where SSE2 is the baseline).
    if size == 16 {
        if has_neon() {
            filter16_vec::<uint8x16_t>(b, p, hstride, vstride, th, it, ht, inner);
        } else {
            filter16_vec::<__m128i>(b, p, hstride, vstride, th, it, ht, inner);
        }
        return;
    }
    // Other sizes go through a block in memory; a constant size, so the
    // gathers and scatters unroll.
    if size == 8 {
        filter_block(b, p, hstride, vstride, 8, th, it, ht, inner);
    } else {
        filter_block(b, p, hstride, vstride, size, th, it, ht, inner);
    }
}

/// `filter_loop` on the same eight-pixel edge of both chroma planes, as
/// one sixteen-lane block (`VFilter8`, `HFilter8` and their inner forms).
pub fn filter_loop_uv(
    bu: &mut [u8],
    bv: &mut [u8],
    p: usize,
    hstride: usize,
    vstride: usize,
    thresh: i32,
    ithresh: i32,
    hev_thresh: i32,
    inner: bool,
)
    requires
        run_ok(old(bu)@.len(), p as int, hstride as int, vstride as int, 8),
        run_ok(old(bv)@.len(), p as int, hstride as int, vstride as int, 8),
        0 <= thresh <= 0x1000,
    ensures
        final(bu)@.len() == old(bu)@.len(),
        final(bv)@.len() == old(bv)@.len(),
        lanes_apart(hstride as int, vstride as int, 8) ==> final(bu)@ == lf_run(
            old(bu)@,
            p as int,
            hstride as int,
            vstride as int,
            8,
            false,
            inner,
            thresh as int,
            ithresh as int,
            hev_thresh as int,
        ),
        lanes_apart(hstride as int, vstride as int, 8) ==> final(bv)@ == lf_run(
            old(bv)@,
            p as int,
            hstride as int,
            vstride as int,
            8,
            false,
            inner,
            thresh as int,
            ithresh as int,
            hev_thresh as int,
        ),
{
    if thresh > 254 || ithresh < 0 || ithresh > 255 || hev_thresh < 0 || hev_thresh > 255 {
        filter_loop_ref(bu, p, hstride, vstride, 8, thresh, ithresh, hev_thresh, inner);
        filter_loop_ref(bv, p, hstride, vstride, 8, thresh, ithresh, hev_thresh, inner);
        return;
    }
    let th = thresh as u8;
    let it = ithresh as u8;
    let ht = hev_thresh as u8;
    // Both planes' eight lanes as one sixteen-lane block in registers.
    if has_neon() {
        filter8uv_vec::<uint8x16_t>(bu, bv, p, hstride, vstride, th, it, ht, inner);
    } else {
        filter8uv_vec::<__m128i>(bu, bv, p, hstride, vstride, th, it, ht, inner);
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    /// The lane-parallel filters equal the one-pixel-at-a-time reference on
    /// random blocks, smooth and rough, for every kind and direction.
    #[test]
    fn filters_match_reference() {
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for iter in 0..400000 {
            let stride = 24;
            let mut buf = vec![0u8; stride * 24];
            let base = (rnd() % 256) as i32;
            let spread = [2u64, 8, 32, 256][iter % 4];
            for v in buf.iter_mut() {
                *v = (base + (rnd() % spread) as i32 - (spread / 2) as i32).clamp(0, 255) as u8;
            }
            let size = if iter % 3 == 0 { 8 } else { 16 };
            let (p, hs, vs) = if iter % 2 == 0 { (4 * stride + 4, 1, stride) } else { (4 * stride + 4, stride, 1) };
            // Mostly the decoder's ranges, sometimes past a byte.
            let wide = iter % 7 == 0;
            let thresh = (rnd() % if wide { 400 } else { 200 }) as i32;
            let it = (rnd() % if wide { 400 } else { 64 }) as i32 - wide as i32;
            let ht = (rnd() % if wide { 400 } else { 3 }) as i32 - wide as i32;
            let inner = rnd() % 2 == 0;
            let mut a = buf.clone();
            let mut b = buf.clone();
            if iter % 5 == 0 {
                simple_filter(&mut a, p, hs, vs, size, thresh);
                simple_filter_ref(&mut b, p, hs, vs, size, thresh);
            } else {
                filter_loop(&mut a, p, hs, vs, size, thresh, it, ht, inner);
                filter_loop_ref(&mut b, p, hs, vs, size, thresh, it, ht, inner);
            }
            assert!(a == b, "iteration {iter}: thresh {thresh} it {it} ht {ht} inner {inner} size {size} hs {hs} simple {}", iter % 5 == 0);
        }
    }

    /// `transform_two` is `transform_one` twice, on any coefficients.
    #[test]
    fn transform_two_matches_one() {
        let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for iter in 0..200000 {
            let range = [16u64, 256, 2048, 65536][iter % 4];
            let inp: Vec<i16> = (0..32).map(|_| ((rnd() % range) as i64 - (range / 2) as i64) as i16).collect();
            let dst0: Vec<u8> = (0..4 * BPS).map(|_| rnd() as u8).collect();
            let mut a = dst0.clone();
            let mut b = dst0.clone();
            transform_two(&inp, 0, &mut a, 0);
            transform_one(&inp, 0, &mut b, 0);
            transform_one(&inp, 16, &mut b, 4);
            assert_eq!(a, b, "iteration {iter}");
        }
    }

    /// The two-plane chroma filter is the reference filter on each plane.
    #[test]
    fn filter_uv_matches_reference() {
        let mut seed: u64 = 0x1234_5678_9abc_def1;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for iter in 0..100000 {
            let stride = 16;
            let spread = [2u64, 8, 32, 256][iter % 4];
            let mut planes: Vec<Vec<u8>> = (0..2).map(|_| {
                let base = (rnd() % 256) as i32;
                (0..stride * 16).map(|_| (base + (rnd() % spread) as i32 - (spread / 2) as i32).clamp(0, 255) as u8).collect()
            }).collect();
            let (p, hs, vs) = if iter % 2 == 0 { (4 * stride + 4, 1, stride) } else { (4 * stride + 4, stride, 1) };
            let wide = iter % 7 == 0;
            let thresh = (rnd() % if wide { 400 } else { 200 }) as i32;
            let it = (rnd() % if wide { 400 } else { 64 }) as i32 - wide as i32;
            let ht = (rnd() % if wide { 400 } else { 3 }) as i32 - wide as i32;
            let inner = rnd() % 2 == 0;
            let mut want = planes.clone();
            for w in want.iter_mut() {
                filter_loop_ref(w, p, hs, vs, 8, thresh, it, ht, inner);
            }
            let (a, b) = planes.split_at_mut(1);
            filter_loop_uv(&mut a[0], &mut b[0], p, hs, vs, thresh, it, ht, inner);
            assert!(planes == want, "iteration {iter}");
        }
    }
}

//! YCbCr to RGB on NEON, sixteen pixels at a time, through `vsimd`'s
//! specified intrinsics. The arithmetic is 16-bit where libjpeg's 16.16
//! fixed-point constants allow it. Each channel is built doubled, as
//! `2 * y + 1 + t`, and the last shift, a saturating narrow by one bit,
//! halves and clamps it, so `t` is the chroma term to one more bit and the
//! `+ 1` is the rounding. For red and blue `t` is one `sqdmulh` of the
//! chroma sample times 4 by a 15-bit constant that gives libjpeg's result
//! on every byte; for green it is the high half of a 32-bit sum.
#[cfg(verus_only)]
use crate::idct_neon::{l16, l32};
#[cfg(verus_only)]
use crate::render::chan;
use crate::spec::*;
use crate::types::*;
#[cfg(verus_only)]
use verilith_simd::lanes::*;
use verilith_simd::neon::*;
#[cfg(verus_only)]
use verilith_simd::ops::*;
use vstd::prelude::*;

verus! {

broadcast use verilith_simd::neon::group_neon;

/// A 16-bit lane read as signed.
pub open spec fn s16i(x: int) -> int {
    if x < 0x8000 {
        x
    } else {
        x - 0x10000
    }
}

/// The bytes of `v` as two vectors of 16-bit lanes.
#[inline(always)]
fn widen1(v: uint8x16_t) -> (r: (uint8x16_t, uint8x16_t))
    requires
        neon(),
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(r.0, i) == n8(v)[i],
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(r.1, i) == n8(v)[8 + i],
{
    let lo = vshll_low_n_u8::<0>(v);
    let hi = vshll_high_n_u8::<0>(v);
    proof {
        reveal_with_fuel(pow2_spec, 3);
        let zl = unpacklo8_lanes(n8(v), splat8(0, 16));
        let zh = unpackhi8_lanes(n8(v), splat8(0, 16));
        assert forall|i: int| 0 <= i < 8 implies #[trigger] l16(lo, i) == n8(v)[i] by {
            assert(zl[2 * i] == n8(v)[i] && zl[2 * i + 1] == 0);
            lemma_le16_value(zl[2 * i], zl[2 * i + 1]);
            assert(u16s(zl)[i] == n8(v)[i]);
        }
        assert forall|i: int| 0 <= i < 8 implies #[trigger] l16(hi, i) == n8(v)[8 + i] by {
            assert(zh[2 * i] == n8(v)[8 + i] && zh[2 * i + 1] == 0);
            lemma_le16_value(zh[2 * i], zh[2 * i + 1]);
            assert(u16s(zh)[i] == n8(v)[8 + i]);
        }
    }
    (lo, hi)
}

/// The bytes of `v`, doubled, as two vectors of 16-bit lanes.
#[inline(always)]
fn widen2(v: uint8x16_t) -> (r: (uint8x16_t, uint8x16_t))
    requires
        neon(),
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(r.0, i) == 2 * n8(v)[i],
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(r.1, i) == 2 * n8(v)[8 + i],
{
    let lo = vshll_low_n_u8::<1>(v);
    let hi = vshll_high_n_u8::<1>(v);
    proof {
        reveal_with_fuel(pow2_spec, 3);
        let zl = unpacklo8_lanes(n8(v), splat8(0, 16));
        let zh = unpackhi8_lanes(n8(v), splat8(0, 16));
        assert forall|i: int| 0 <= i < 8 implies #[trigger] l16(lo, i) == 2 * n8(v)[i] by {
            assert(zl[2 * i] == n8(v)[i] && zl[2 * i + 1] == 0);
            lemma_le16_value(zl[2 * i], zl[2 * i + 1]);
            assert(u16s(zl)[i] == n8(v)[i]);
            assert(pow2_spec(1) == 2);
            assert(u16s(zl)[i] as nat * pow2_spec(1) == 2 * n8(v)[i]);
        }
        assert forall|i: int| 0 <= i < 8 implies #[trigger] l16(hi, i) == 2 * n8(v)[8 + i] by {
            assert(zh[2 * i] == n8(v)[8 + i] && zh[2 * i + 1] == 0);
            lemma_le16_value(zh[2 * i], zh[2 * i + 1]);
            assert(u16s(zh)[i] == n8(v)[8 + i]);
            assert(pow2_spec(1) == 2);
            assert(u16s(zh)[i] as nat * pow2_spec(1) == 2 * n8(v)[8 + i]);
        }
    }
    (lo, hi)
}

#[inline(always)]
fn addk(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(r, i) == (l16(a, i) + l16(b, i)) % 0x10000,
{
    vaddq_s16(a, b)
}

#[inline(always)]
fn subk(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(r, i) == (l16(a, i) - l16(b, i) + 0x10000) % 0x10000,
{
    vsubq_s16(a, b)
}

#[inline(always)]
fn dupk(c: i16) -> (r: uint8x16_t)
    requires
        neon(),
        c >= 0,
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(r, i) == c,
{
    vdupq_n_s16(c)
}

/// `sqdmulh` by a constant.
#[inline(always)]
fn qdc(a: uint8x16_t, c: i16) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(r, i) == sat_s16((2 * s16i(l16(a, i)) * c) / 0x10000) % 0x10000,
{
    let k = vdupq_n_s16(c);
    let r = vqdmulhq_s16(a, k);
    proof {
        assert forall|i: int| 0 <= i < 8 implies #[trigger] l16(r, i) == sat_s16((2 * s16i(l16(a, i)) * c) / 0x10000)
            % 0x10000 by {
            assert(s16(u16s(n8(k))[i]) == c);
            assert(s16(u16s(n8(a))[i]) == s16i(l16(a, i)));
        }
    }
    r
}

/// The 32-bit products of the 16-bit lanes with a constant.
#[inline(always)]
fn mullc(a: uint8x16_t, c: i16) -> (r: (uint8x16_t, uint8x16_t))
    requires
        neon(),
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] l32(r.0, i) == (s16i(l16(a, i)) * c) % 0x1_0000_0000,
        forall|i: int| 0 <= i < 4 ==> #[trigger] l32(r.1, i) == (s16i(l16(a, 4 + i)) * c) % 0x1_0000_0000,
{
    let k = vdupq_n_s16(c);
    let lo = vmull_lo_s16(a, k);
    let hi = vmull_hi_s16(a, k);
    proof {
        assert forall|i: int| 0 <= i < 4 implies #[trigger] l32(lo, i) == (s16i(l16(a, i)) * c) % 0x1_0000_0000 by {
            assert(s16(u16s(n8(k))[i]) == c);
            assert(s16(u16s(n8(a))[i]) == s16i(l16(a, i)));
        }
        assert forall|i: int| 0 <= i < 4 implies #[trigger] l32(hi, i) == (s16i(l16(a, 4 + i)) * c) % 0x1_0000_0000 by {
            assert(s16(u16s(n8(k))[4 + i]) == c);
            assert(s16(u16s(n8(a))[4 + i]) == s16i(l16(a, 4 + i)));
        }
    }
    (lo, hi)
}

#[inline(always)]
fn add32k(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] l32(r, i) == (l32(a, i) + l32(b, i)) % 0x1_0000_0000,
{
    vaddq_u32(a, b)
}

/// The high halves of the 32-bit lanes of `lo`, then of `hi`.
#[inline(always)]
fn hi16(lo: uint8x16_t, hi: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        forall|j: int|
            0 <= j < 8 ==> #[trigger] l16(r, j) == (if j < 4 {
                l32(lo, j)
            } else {
                l32(hi, j - 4)
            }) / 0x10000,
{
    let r = vuzp2q_u16(lo, hi);
    proof {
        lemma_u16s_of_u32s(n8(lo));
        lemma_u16s_of_u32s(n8(hi));
        assert forall|j: int| 0 <= j < 8 implies #[trigger] l16(r, j) == (if j < 4 {
            l32(lo, j)
        } else {
            l32(hi, j - 4)
        }) / 0x10000 by {
            let (src, k) = if j < 4 {
                (n8(lo), j)
            } else {
                (n8(hi), j - 4)
            };
            let x = u32s(src)[k];
            assert(u16s(src)[2 * k] == (x & 0xffff) as u16);
            assert(u16s(src)[2 * k + 1] == (x >> 16u32) as u16);
            assert((x >> 16u32) == x / 0x10000u32) by (bit_vector);
        }
    }
    r
}

/// Each signed 16-bit lane halved, rounding down, and clamped to a byte.
#[inline(always)]
fn narrow1(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        forall|j: int|
            0 <= j < 16 ==> #[trigger] n8(r)[j] == sat_u8(
                s16i(
                    if j < 8 {
                        l16(a, j)
                    } else {
                        l16(b, j - 8)
                    },
                ) / 2,
            ),
{
    let r = vqshrun2_n_s16::<1>(a, b);
    proof {
        reveal_with_fuel(pow2_spec, 2);
        assert forall|j: int| 0 <= j < 16 implies #[trigger] n8(r)[j] == sat_u8(
            s16i(
                if j < 8 {
                    l16(a, j)
                } else {
                    l16(b, j - 8)
                },
            ) / 2,
        ) by {
            let (src, k) = if j < 8 {
                (u16s(n8(a)), j)
            } else {
                (u16s(n8(b)), j - 8)
            };
            let g = srai16(src, 1)[k];
            assert(g as int == (s16(src[k]) / 2) % 0x10000);
            assert(s16(g) == s16(src[k]) / 2);
        }
    }
    r
}

/// Red, doubled plus one: `2y + 1 + t` halves to the specification's
/// value, where `t` is `sqdmulh(4 * (cr - 128), 22971)`. That constant is
/// exact for every `cr` a byte holds.
proof fn lemma_red(y: int, cr: int, y1: int, d: int, d2: int, d4: int, t: int, s: int)
    requires
        0 <= y <= 255,
        0 <= cr <= 255,
        y1 == (2 * y + 1) % 0x10000,
        d == (cr - 128 + 0x10000) % 0x10000,
        d2 == (d + d) % 0x10000,
        d4 == (d2 + d2) % 0x10000,
        t == sat_s16((2 * s16i(d4) * 22971) / 0x10000) % 0x10000,
        s == (y1 + t) % 0x10000,
    ensures
        sat_u8(s16i(s) / 2) as int == ycc_r(y, cr),
{
    // Step by step, each with only the facts it needs: in one piece the
    // nonlinear terms are past the solver's budget with some z3 builds.
    let dd = cr - 128;
    assert(s16i(d) == dd);
    assert(s16i(d2) == 2 * dd);
    assert(s16i(d4) == 4 * dd);
    let q = (183768 * dd) / 0x10000;
    assert(2 * s16i(d4) * 22971 == 183768 * dd) by (nonlinear_arith)
        requires
            s16i(d4) == 4 * dd;
    assert(-360 <= q <= 357) by (nonlinear_arith)
        requires
            -128 <= dd <= 127,
            q == (183768 * dd) / 0x10000;
    assert(t == q % 0x10000);
    assert(s16i(t) == q);
    assert(y1 == 2 * y + 1);
    assert(s16i(s) == 2 * y + 1 + q);
    assert(s16i(s) / 2 == y + (q + 1) / 2);
    lemma_round_r(dd);
}

/// `22971 / 8192` stands for `91881 / 65536` on the range of a chroma
/// sample.
proof fn lemma_round_r(dd: int)
    requires
        -128 <= dd <= 127,
    ensures
        ((183768 * dd) / 0x10000 + 1) / 2 == (91881 * dd + 32768) / 65536,
{
    assert(((183768 * dd) / 0x10000 + 1) / 2 == (22971 * dd + 8192) / 16384);
    let u = (dd + 128) as u32;
    assert((22971 * u + 16384 * 180 + 8192 - 22971 * 128) / 16384 == (91881 * u + 65536 * 180 + 32768 - 91881 * 128) / 65536)
        by (bit_vector)
        requires
            u <= 255,
    ;
    assert((22971 * dd + 8192) / 16384 == (22971 * dd + 8192 + 16384 * 180) / 16384 - 180);
    assert((91881 * dd + 32768) / 65536 == (91881 * dd + 32768 + 65536 * 180) / 65536 - 180);
}

/// Blue, doubled plus one: `2y + 1 + t`, where `t` is
/// `sqdmulh(4 * (cb - 128), 29033)`.
proof fn lemma_blue(y: int, cb: int, y1: int, c: int, c2: int, c4: int, t: int, s: int)
    requires
        0 <= y <= 255,
        0 <= cb <= 255,
        y1 == (2 * y + 1) % 0x10000,
        c == (cb - 128 + 0x10000) % 0x10000,
        c2 == (c + c) % 0x10000,
        c4 == (c2 + c2) % 0x10000,
        t == sat_s16((2 * s16i(c4) * 29033) / 0x10000) % 0x10000,
        s == (y1 + t) % 0x10000,
    ensures
        sat_u8(s16i(s) / 2) as int == ycc_b(y, cb),
{
    let cc = cb - 128;
    assert(s16i(c) == cc);
    assert(s16i(c2) == 2 * cc);
    assert(s16i(c4) == 4 * cc);
    let q = (232264 * cc) / 0x10000;
    assert(2 * (4 * cc) * 29033 == 232264 * cc);
    assert(s16i(t) == q);
    assert(s16i(s) == 2 * y + 1 + q);
    lemma_round_b(cc);
}

/// `29033 / 8192` stands for `116130 / 65536` on the range of a chroma
/// sample.
proof fn lemma_round_b(cc: int)
    requires
        -128 <= cc <= 127,
    ensures
        ((232264 * cc) / 0x10000 + 1) / 2 == (116130 * cc + 32768) / 65536,
{
    assert(((232264 * cc) / 0x10000 + 1) / 2 == (29033 * cc + 8192) / 16384);
    let u = (cc + 128) as u32;
    assert((29033 * u + 16384 * 227 + 8192 - 29033 * 128) / 16384 == (116130 * u + 65536 * 227 + 32768 - 116130 * 128) / 65536)
        by (bit_vector)
        requires
            u <= 255,
    ;
    assert((29033 * cc + 8192) / 16384 == (29033 * cc + 8192 + 16384 * 227) / 16384 - 227);
    assert((116130 * cc + 32768) / 65536 == (116130 * cc + 32768 + 65536 * 227) / 65536 - 227);
}

/// The high half of `-45108 * c - 93604 * d` in wrapping 32-bit lanes is
/// the exact quotient by 65536.
proof fn lemma_g32(cc: int, dd: int, m1: int, m2: int, a: int, g: int)
    requires
        -128 <= cc <= 127,
        -128 <= dd <= 127,
        m1 == ((4 * cc) * (-11277)) % 0x1_0000_0000,
        m2 == ((4 * dd) * (-23401)) % 0x1_0000_0000,
        a == (m1 + m2) % 0x1_0000_0000,
        g == a / 0x10000,
    ensures
        0 <= g < 0x10000,
        s16i(g) == (-45108 * cc - 93604 * dd) / 65536,
        -272 <= s16i(g) <= 272,
{
    let p1 = (4 * cc) * (-11277);
    let p2 = (4 * dd) * (-23401);
    let e = p1 + p2;
    vstd::arithmetic::div_mod::lemma_add_mod_noop(p1, p2, 0x1_0000_0000);
    assert(a == e % 0x1_0000_0000);
    assert(-0x200_0000 < e < 0x200_0000);
    let q = e / 65536;
    if e < 0 {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(e, 0x1_0000_0000, -1, e + 0x1_0000_0000);
        assert(a == e + 0x1_0000_0000);
        assert(g == q + 65536);
    } else {
        vstd::arithmetic::div_mod::lemma_small_mod(e as nat, 0x1_0000_0000);
        assert(g == q);
    }
}

/// Green, doubled plus one: `2y + 1 + g`, where `g` is the high half of
/// `4 * (cb - 128) * -11277 + 4 * (cr - 128) * -23401`, twice the
/// specification's sum.
proof fn lemma_green(y: int, cb: int, cr: int, y1: int, c: int, c2: int, c4: int, d: int, d2: int, d4: int, m1: int, m2: int, a: int, g: int, s: int)
    requires
        0 <= y <= 255,
        0 <= cb <= 255,
        0 <= cr <= 255,
        y1 == (2 * y + 1) % 0x10000,
        c == (cb - 128 + 0x10000) % 0x10000,
        c2 == (c + c) % 0x10000,
        c4 == (c2 + c2) % 0x10000,
        d == (cr - 128 + 0x10000) % 0x10000,
        d2 == (d + d) % 0x10000,
        d4 == (d2 + d2) % 0x10000,
        m1 == (s16i(c4) * (-11277)) % 0x1_0000_0000,
        m2 == (s16i(d4) * (-23401)) % 0x1_0000_0000,
        a == (m1 + m2) % 0x1_0000_0000,
        g == a / 0x10000,
        s == (y1 + g) % 0x10000,
    ensures
        sat_u8(s16i(s) / 2) as int == ycc_g(y, cb, cr),
{
    let cc = cb - 128;
    let dd = cr - 128;
    lemma_x4(cb, c, c2, c4);
    lemma_x4(cr, d, d2, d4);
    lemma_g32(cc, dd, m1, m2, a, g);
    let aa = -22554 * cc - 46802 * dd;
    let q = (2 * aa) / 65536;
    assert(-45108 * cc - 93604 * dd == 2 * aa);
    lemma_sum16(y, q, y1, g, s);
    assert((q + 1) / 2 == (aa + 32768) / 65536);
    assert((2 * y + 1 + q) / 2 == y + (q + 1) / 2);
}

/// A chroma sample less 128, times 4, in a 16-bit lane.
proof fn lemma_x4(cb: int, c: int, c2: int, c4: int)
    requires
        0 <= cb <= 255,
        c == (cb - 128 + 0x10000) % 0x10000,
        c2 == (c + c) % 0x10000,
        c4 == (c2 + c2) % 0x10000,
    ensures
        s16i(c4) == 4 * (cb - 128),
{
    assert(s16i(c) == cb - 128);
    assert(s16i(c2) == 2 * (cb - 128));
}

/// The 16-bit sum of the doubled luma and a small chroma term.
proof fn lemma_sum16(y: int, q: int, y1: int, g: int, s: int)
    requires
        0 <= y <= 255,
        -272 <= q <= 272,
        0 <= g < 0x10000,
        s16i(g) == q,
        y1 == (2 * y + 1) % 0x10000,
        s == (y1 + g) % 0x10000,
    ensures
        s16i(s) == 2 * y + 1 + q,
{
}

/// Eight pixels: the three channels as 16-bit lanes, doubled plus one.
#[inline(always)]
fn half(y1: uint8x16_t, c: uint8x16_t, d: uint8x16_t, Ghost(ys): Ghost<Seq<int>>, Ghost(cbs): Ghost<Seq<int>>, Ghost(crs): Ghost<Seq<int>>) -> (r: (uint8x16_t, uint8x16_t, uint8x16_t))
    requires
        neon(),
        forall|i: int| 0 <= i < 8 ==> 0 <= #[trigger] ys[i] <= 255 && 0 <= cbs[i] <= 255 && 0 <= crs[i] <= 255,
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(y1, i) == (2 * ys[i] + 1) % 0x10000,
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(c, i) == (cbs[i] - 128 + 0x10000) % 0x10000,
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(d, i) == (crs[i] - 128 + 0x10000) % 0x10000,
    ensures
        forall|i: int| 0 <= i < 8 ==> sat_u8(s16i(#[trigger] l16(r.0, i)) / 2) as int == ycc_r(ys[i], crs[i]),
        forall|i: int| 0 <= i < 8 ==> sat_u8(s16i(#[trigger] l16(r.1, i)) / 2) as int == ycc_g(ys[i], cbs[i], crs[i]),
        forall|i: int| 0 <= i < 8 ==> sat_u8(s16i(#[trigger] l16(r.2, i)) / 2) as int == ycc_b(ys[i], cbs[i]),
{
    hide(s16i);
    let c2 = addk(c, c);
    let c4 = addk(c2, c2);
    let d2 = addk(d, d);
    let d4 = addk(d2, d2);
    let tr = qdc(d4, 22971);
    let r1 = addk(y1, tr);
    let tb = qdc(c4, 29033);
    let b1 = addk(y1, tb);
    let m1 = mullc(c4, -11277);
    let m2 = mullc(d4, -23401);
    let al = add32k(m1.0, m2.0);
    let ah = add32k(m1.1, m2.1);
    let g = hi16(al, ah);
    let g1 = addk(y1, g);
    proof {
        assert forall|i: int| 0 <= i < 8 implies sat_u8(s16i(#[trigger] l16(r1, i)) / 2) as int == ycc_r(ys[i], crs[i]) by {
            assert(0 <= ys[i] <= 255);
            lemma_red(ys[i], crs[i], l16(y1, i), l16(d, i), l16(d2, i), l16(d4, i), l16(tr, i), l16(r1, i));
        }
        assert forall|i: int| 0 <= i < 8 implies sat_u8(s16i(#[trigger] l16(b1, i)) / 2) as int == ycc_b(ys[i], cbs[i]) by {
            assert(0 <= ys[i] <= 255);
            lemma_blue(ys[i], cbs[i], l16(y1, i), l16(c, i), l16(c2, i), l16(c4, i), l16(tb, i), l16(b1, i));
        }
        assert forall|i: int| 0 <= i < 8 implies sat_u8(s16i(#[trigger] l16(g1, i)) / 2) as int == ycc_g(
            ys[i],
            cbs[i],
            crs[i],
        ) by {
            assert(0 <= ys[i] <= 255);
            let (ml1, ml2, a) = if i < 4 {
                (l32(m1.0, i), l32(m2.0, i), l32(al, i))
            } else {
                (l32(m1.1, i - 4), l32(m2.1, i - 4), l32(ah, i - 4))
            };
            if i >= 4 {
                assert(l16(c4, 4 + (i - 4)) == l16(c4, i));
                assert(l16(d4, 4 + (i - 4)) == l16(d4, i));
            }
            lemma_green(ys[i], cbs[i], crs[i], l16(y1, i), l16(c, i), l16(c2, i), l16(c4, i), l16(d, i), l16(d2, i), l16(d4, i), ml1, ml2, a, l16(g, i), l16(g1, i));
        }
    }
    (r1, g1, b1)
}

/// Sixteen pixels from `x` of the three rows, to red, green, blue at
/// `out[p..p + 48]`.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
#[inline(always)]
pub fn ycc16(yr: &[u8], cbr: &[u8], crr: &[u8], x: usize, out: &mut [u8], p: usize)
    requires
        neon(),
        x + 16 <= yr@.len(),
        x + 16 <= cbr@.len(),
        x + 16 <= crr@.len(),
        p + 48 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|j: int|
            p <= j < p + 48 ==> (#[trigger] final(out)@[j]) as int == chan(
                Color::YCbCr,
                yr@[x + (j - p) / 3] as int,
                cbr@[x + (j - p) / 3] as int,
                crr@[x + (j - p) / 3] as int,
                (j - p) % 3,
            ),
        forall|j: int| 0 <= j < p || p + 48 <= j < final(out)@.len() ==> (#[trigger] final(out)@[j]) == old(out)@[j],
{
    hide(s16i);
    let yv = vld1q_u8_at(yr, x);
    let cbv = vld1q_u8_at(cbr, x);
    let crv = vld1q_u8_at(crr, x);
    let one = dupk(1);
    let k128 = dupk(128);
    let yw = widen2(yv);
    let cbw = widen1(cbv);
    let crw = widen1(crv);
    let yl = addk(yw.0, one);
    let yh = addk(yw.1, one);
    let cl = subk(cbw.0, k128);
    let ch = subk(cbw.1, k128);
    let dl = subk(crw.0, k128);
    let dh = subk(crw.1, k128);
    let ghost ysl = Seq::new(8, |i: int| yr@[x + i] as int);
    let ghost ysh = Seq::new(8, |i: int| yr@[x + 8 + i] as int);
    let ghost cbl = Seq::new(8, |i: int| cbr@[x + i] as int);
    let ghost cbh = Seq::new(8, |i: int| cbr@[x + 8 + i] as int);
    let ghost crl = Seq::new(8, |i: int| crr@[x + i] as int);
    let ghost crh = Seq::new(8, |i: int| crr@[x + 8 + i] as int);
    proof {
        assert forall|i: int| 0 <= i < 8 implies #[trigger] l16(yl, i) == (2 * ysl[i] + 1) % 0x10000 by {
            assert(l16(yw.0, i) == 2 * n8(yv)[i]);
        }
        assert forall|i: int| 0 <= i < 8 implies #[trigger] l16(yh, i) == (2 * ysh[i] + 1) % 0x10000 by {
            assert(l16(yw.1, i) == 2 * n8(yv)[8 + i]);
        }
        assert forall|i: int| 0 <= i < 8 implies #[trigger] l16(cl, i) == (cbl[i] - 128 + 0x10000) % 0x10000 by {
            assert(l16(cbw.0, i) == n8(cbv)[i]);
        }
        assert forall|i: int| 0 <= i < 8 implies #[trigger] l16(ch, i) == (cbh[i] - 128 + 0x10000) % 0x10000 by {
            assert(l16(cbw.1, i) == n8(cbv)[8 + i]);
        }
        assert forall|i: int| 0 <= i < 8 implies #[trigger] l16(dl, i) == (crl[i] - 128 + 0x10000) % 0x10000 by {
            assert(l16(crw.0, i) == n8(crv)[i]);
        }
        assert forall|i: int| 0 <= i < 8 implies #[trigger] l16(dh, i) == (crh[i] - 128 + 0x10000) % 0x10000 by {
            assert(l16(crw.1, i) == n8(crv)[8 + i]);
        }
    }
    let lo = half(yl, cl, dl, Ghost(ysl), Ghost(cbl), Ghost(crl));
    let hi = half(yh, ch, dh, Ghost(ysh), Ghost(cbh), Ghost(crh));
    let rv = narrow1(lo.0, hi.0);
    let gv = narrow1(lo.1, hi.1);
    let bv = narrow1(lo.2, hi.2);
    let ghost old_out = out@;
    vst3q_u8_at(out, p, rv, gv, bv);
    proof {
        assert forall|j: int| p <= j < p + 48 implies (#[trigger] out@[j]) as int == chan(
            Color::YCbCr,
            yr@[x + (j - p) / 3] as int,
            cbr@[x + (j - p) / 3] as int,
            crr@[x + (j - p) / 3] as int,
            (j - p) % 3,
        ) by {
            let m = (j - p) / 3;
            let il = interleave3(n8(rv), n8(gv), n8(bv));
            assert(out@[j] == il[j - p]);
            assert(0 <= m < 16);
            if m < 8 {
                assert(ysl[m] == yr@[x + m] && cbl[m] == cbr@[x + m] && crl[m] == crr@[x + m]);
                assert(sat_u8(s16i(l16(lo.0, m)) / 2) as int == ycc_r(ysl[m], crl[m]));
                assert(sat_u8(s16i(l16(lo.1, m)) / 2) as int == ycc_g(ysl[m], cbl[m], crl[m]));
                assert(sat_u8(s16i(l16(lo.2, m)) / 2) as int == ycc_b(ysl[m], cbl[m]));
            } else {
                assert(ysh[m - 8] == yr@[x + 8 + (m - 8)] && cbh[m - 8] == cbr@[x + 8 + (m - 8)] && crh[m - 8] == crr@[x + 8 + (m - 8)]);
                assert(sat_u8(s16i(l16(hi.0, m - 8)) / 2) as int == ycc_r(ysh[m - 8], crh[m - 8]));
                assert(sat_u8(s16i(l16(hi.1, m - 8)) / 2) as int == ycc_g(ysh[m - 8], cbh[m - 8], crh[m - 8]));
                assert(sat_u8(s16i(l16(hi.2, m - 8)) / 2) as int == ycc_b(ysh[m - 8], cbh[m - 8]));
            }
            assert(n8(rv)[m] as int == ycc_r(yr@[x + m] as int, crr@[x + m] as int));
            assert(n8(gv)[m] as int == ycc_g(yr@[x + m] as int, cbr@[x + m] as int, crr@[x + m] as int));
            assert(n8(bv)[m] as int == ycc_b(yr@[x + m] as int, cbr@[x + m] as int));
        }
    }
}

} // verus!

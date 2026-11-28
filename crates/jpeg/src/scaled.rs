//! Decoding at a reduced size: `decode_scaled` gives the image at 1/2,
//! 1/4 or 1/8 of the file's width and height, as `spec_scaled` says (and
//! as libjpeg-turbo gives it with the same scaling factor). Each block of
//! coefficients goes straight to a 4x4, 2x2 or 1x1 block of samples; the
//! full-size image is never built, so a thumbnail of a large photograph
//! costs little more than entropy decoding.
use crate::decode::*;
use crate::idct::{plane_x, range_limit_x};
#[cfg(verus_only)]
use crate::idct::{pat, psample};
use crate::bits::rd;
use crate::num::*;
use crate::parse::*;
use crate::prims::*;
use crate::render::clamp8;
use crate::scan::*;
use crate::spec::*;
use crate::spec_scaled::*;
use crate::types::*;
use crate::work::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Shifts
// ---------------------------------------------------------------------------
proof fn lemma_sar(v: i64, k: u64)
    requires
        k == 3 || k == 12 || k == 13 || k == 19 || k == 20,
    ensures
        (v >> k) as int == (v as int) / pow2(k as nat) as int,
{
    lemma2_to64();
    if k == 3 {
        let m = v & 7;
        let q = v >> 3;
        assert(0 <= m < 8 && v == q * 8 + m) by (bit_vector)
            requires
                m == v & 7,
                q == v >> 3,
        ;
        lemma_fundamental_div_mod_converse(v as int, 8, q as int, m as int);
    } else if k == 12 {
        let m = v & 4095;
        let q = v >> 12;
        assert(0 <= m < 4096 && v == q * 4096 + m) by (bit_vector)
            requires
                m == v & 4095,
                q == v >> 12,
        ;
        lemma_fundamental_div_mod_converse(v as int, 4096, q as int, m as int);
    } else if k == 13 {
        let m = v & 8191;
        let q = v >> 13;
        assert(0 <= m < 8192 && v == q * 8192 + m) by (bit_vector)
            requires
                m == v & 8191,
                q == v >> 13,
        ;
        lemma_fundamental_div_mod_converse(v as int, 8192, q as int, m as int);
    } else if k == 19 {
        let m = v & 0x7_ffff;
        let q = v >> 19;
        assert(0 <= m < 0x8_0000 && v == q * 0x8_0000 + m) by (bit_vector)
            requires
                m == v & 0x7_ffff,
                q == v >> 19,
        ;
        lemma_fundamental_div_mod_converse(v as int, 0x8_0000, q as int, m as int);
    } else {
        let m = v & 0xf_ffff;
        let q = v >> 20;
        assert(0 <= m < 0x10_0000 && v == q * 0x10_0000 + m) by (bit_vector)
            requires
                m == v & 0xf_ffff,
                q == v >> 20,
        ;
        lemma_fundamental_div_mod_converse(v as int, 0x10_0000, q as int, m as int);
    }
}

/// `descale(v, k)` in 64 bits, for the values the reduced inverse DCTs
/// shift.
#[inline(always)]
fn ds(v: i64, k: u64) -> (r: i64)
    requires
        k == 3 || k == 12 || k == 13 || k == 19 || k == 20,
        -0x1_0000_0000_0000 <= v <= 0x1_0000_0000_0000,
    ensures
        r as int == descale(v as int, k as nat),
{
    proof {
        lemma2_to64();
    }
    let b: i64 = if k == 3 {
        4
    } else if k == 12 {
        2048
    } else if k == 13 {
        4096
    } else if k == 19 {
        0x4_0000
    } else {
        0x8_0000
    };
    assert(b as int == pow2((k - 1) as nat));
    proof {
        lemma_sar((v + b) as i64, k);
    }
    (v + b) >> k
}

/// The low 32 bits of `v`, signed: libjpeg's `int` workspace.
#[inline(always)]
fn w32(v: i64) -> (r: i32)
    ensures
        r as int == wrap32(v as int),
{
    proof {
        lemma_wrap32(v);
    }
    v as i32
}

// ---------------------------------------------------------------------------
// The reduced inverse DCTs
// ---------------------------------------------------------------------------
/// A dequantized coefficient.
#[inline(always)]
fn dq(a: &Vec<i16>, o: usize, q: &[u16; 64], k: usize) -> (r: i64)
    requires
        o + 64 <= a.len(),
        k < 64,
    ensures
        r == dequant(a@, o as int, q@)[k as int],
        -0x4000_0000 <= r <= 0x4000_0000,
{
    proof {
        lemma_sx16(q[k as int]);
    }
    let x = vget(a, o + k) as i64;
    let y = (q[k] as i16) as i64;
    assert(-0x4000_0000 <= x * y <= 0x4000_0000) by (nonlinear_arith)
        requires
            -0x8000 <= x <= 0x7fff,
            -0x8000 <= y <= 0x7fff,
    ;
    x * y
}

/// `jpeg_idct_1x1`.
fn blk1(a: &Vec<i16>, o: usize, q: &[u16; 64]) -> (r: u8)
    requires
        o + 64 <= a.len(),
    ensures
        r == idct1(dequant(a@, o as int, q@)),
{
    range_limit_x(ds(dq(a, o, q, 0), 3))
}

/// The odd part of `jpeg_idct_2x2`.
#[inline(always)]
fn odd2(x1: i64, x3: i64, x5: i64, x7: i64) -> (r: i64)
    requires
        -0x8000_0000 <= x1 <= 0x8000_0000,
        -0x8000_0000 <= x3 <= 0x8000_0000,
        -0x8000_0000 <= x5 <= 0x8000_0000,
        -0x8000_0000 <= x7 <= 0x8000_0000,
    ensures
        r == x7 * (-5906) + x5 * 6967 + x3 * (-10426) + x1 * 29692,
        -0x8000_0000_0000 <= r <= 0x8000_0000_0000,
{
    x7 * (-5906) + x5 * 6967 + x3 * (-10426) + x1 * 29692
}

/// The first pass of `jpeg_idct_2x2` down column `x`.
fn col2(a: &Vec<i16>, o: usize, q: &[u16; 64], x: usize) -> (r: (i32, i32))
    requires
        o + 64 <= a.len(),
        x < 8,
    ensures
        r.0 as int == idct2_col(dequant(a@, o as int, q@), x as int, 0),
        r.1 as int == idct2_col(dequant(a@, o as int, q@), x as int, 1),
{
    let t10 = dq(a, o, q, x) * 32768;
    let t0 = odd2(dq(a, o, q, 8 + x), dq(a, o, q, 24 + x), dq(a, o, q, 40 + x), dq(a, o, q, 56 + x));
    (w32(ds(t10 + t0, 13)), w32(ds(t10 - t0, 13)))
}

/// `jpeg_idct_2x2`: sample (`y`, `x`) at `r[2 * y + x]`.
fn blk2(a: &Vec<i16>, o: usize, q: &[u16; 64]) -> (r: [u8; 4])
    requires
        o + 64 <= a.len(),
    ensures
        forall|t: int| 0 <= t < 4 ==> #[trigger] r[t] == idct2(dequant(a@, o as int, q@), t / 2, t % 2),
{
    let ghost c = dequant(a@, o as int, q@);
    let c0 = col2(a, o, q, 0);
    let c1 = col2(a, o, q, 1);
    let c3 = col2(a, o, q, 3);
    let c5 = col2(a, o, q, 5);
    let c7 = col2(a, o, q, 7);
    let t10a = c0.0 as i64 * 32768;
    let t0a = odd2(c1.0 as i64, c3.0 as i64, c5.0 as i64, c7.0 as i64);
    let t10b = c0.1 as i64 * 32768;
    let t0b = odd2(c1.1 as i64, c3.1 as i64, c5.1 as i64, c7.1 as i64);
    let r = [
        range_limit_x(ds(t10a + t0a, 20)),
        range_limit_x(ds(t10a - t0a, 20)),
        range_limit_x(ds(t10b + t0b, 20)),
        range_limit_x(ds(t10b - t0b, 20)),
    ];
    assert forall|t: int| 0 <= t < 4 implies #[trigger] r[t] == idct2(c, t / 2, t % 2) by {
        assert(t == 0 || t == 1 || t == 2 || t == 3);
    }
    r
}

/// `jpeg_idct_4x4`'s one-dimensional transform, before the final shift.
#[inline(always)]
fn t4(v0: i64, v1: i64, v2: i64, v3: i64, v5: i64, v6: i64, v7: i64, Ghost(s): Ghost<Seq<int>>) -> (r: [i64; 4])
    requires
        s.len() == 8,
        s[0] == v0 && s[1] == v1 && s[2] == v2 && s[3] == v3 && s[5] == v5 && s[6] == v6 && s[7] == v7,
        -0x8000_0000 <= v0 <= 0x8000_0000,
        -0x8000_0000 <= v1 <= 0x8000_0000,
        -0x8000_0000 <= v2 <= 0x8000_0000,
        -0x8000_0000 <= v3 <= 0x8000_0000,
        -0x8000_0000 <= v5 <= 0x8000_0000,
        -0x8000_0000 <= v6 <= 0x8000_0000,
        -0x8000_0000 <= v7 <= 0x8000_0000,
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] r[i] as int == idct4_1d(s)[i],
        forall|i: int| 0 <= i < 4 ==> -0x1_0000_0000_0000 <= #[trigger] r[i] <= 0x1_0000_0000_0000,
{
    let t0 = v0 * 16384;
    let t2 = v2 * 15137 + v6 * (-6270);
    let t10 = t0 + t2;
    let t12 = t0 - t2;
    let o0 = v7 * (-1730) + v5 * 11893 + v3 * (-17799) + v1 * 8697;
    let o2 = v7 * (-4176) + v5 * (-4926) + v3 * 7373 + v1 * 20995;
    let r = [t10 + o2, t12 + o0, t12 - o0, t10 - o2];
    assert forall|i: int| 0 <= i < 4 implies #[trigger] r[i] as int == idct4_1d(s)[i] by {
        assert(i == 0 || i == 1 || i == 2 || i == 3);
    }
    r
}

/// The first pass of `jpeg_idct_4x4` down column `x`.
fn col4(a: &Vec<i16>, o: usize, q: &[u16; 64], x: usize) -> (r: [i32; 4])
    requires
        o + 64 <= a.len(),
        x < 8,
    ensures
        forall|y: int| 0 <= y < 4 ==> (#[trigger] r[y]) as int == idct4_col(dequant(a@, o as int, q@), x as int, y),
{
    let ghost c = dequant(a@, o as int, q@);
    let ghost s = Seq::new(8, |i: int| c[8 * i + x]);
    let v = t4(
        dq(a, o, q, x),
        dq(a, o, q, 8 + x),
        dq(a, o, q, 16 + x),
        dq(a, o, q, 24 + x),
        dq(a, o, q, 40 + x),
        dq(a, o, q, 48 + x),
        dq(a, o, q, 56 + x),
        Ghost(s),
    );
    [w32(ds(v[0], 12)), w32(ds(v[1], 12)), w32(ds(v[2], 12)), w32(ds(v[3], 12))]
}

/// `jpeg_idct_4x4`: sample (`y`, `x`) at `r[4 * y + x]`.
fn blk4(a: &Vec<i16>, o: usize, q: &[u16; 64]) -> (r: [u8; 16])
    requires
        o + 64 <= a.len(),
    ensures
        forall|t: int| 0 <= t < 16 ==> #[trigger] r[t] == idct4(dequant(a@, o as int, q@), t / 4, t % 4),
{
    let ghost c = dequant(a@, o as int, q@);
    let k0 = col4(a, o, q, 0);
    let k1 = col4(a, o, q, 1);
    let k2 = col4(a, o, q, 2);
    let k3 = col4(a, o, q, 3);
    let k5 = col4(a, o, q, 5);
    let k6 = col4(a, o, q, 6);
    let k7 = col4(a, o, q, 7);
    let mut r = [0u8; 16];
    let mut y: usize = 0;
    while y < 4
        invariant
            y <= 4,
            forall|j: int| 0 <= j < 4 ==> (#[trigger] k0[j]) as int == idct4_col(c, 0, j),
            forall|j: int| 0 <= j < 4 ==> (#[trigger] k1[j]) as int == idct4_col(c, 1, j),
            forall|j: int| 0 <= j < 4 ==> (#[trigger] k2[j]) as int == idct4_col(c, 2, j),
            forall|j: int| 0 <= j < 4 ==> (#[trigger] k3[j]) as int == idct4_col(c, 3, j),
            forall|j: int| 0 <= j < 4 ==> (#[trigger] k5[j]) as int == idct4_col(c, 5, j),
            forall|j: int| 0 <= j < 4 ==> (#[trigger] k6[j]) as int == idct4_col(c, 6, j),
            forall|j: int| 0 <= j < 4 ==> (#[trigger] k7[j]) as int == idct4_col(c, 7, j),
            forall|t: int| 0 <= t < 4 * y ==> #[trigger] r[t] == idct4(c, t / 4, t % 4),
        decreases 4 - y,
    {
        let ghost s = Seq::new(8, |j: int| if j == 4 { 0 } else { idct4_col(c, j, y as int) });
        let v = t4(
            k0[y] as i64,
            k1[y] as i64,
            k2[y] as i64,
            k3[y] as i64,
            k5[y] as i64,
            k6[y] as i64,
            k7[y] as i64,
            Ghost(s),
        );
        let ghost r0 = r;
        r[4 * y] = range_limit_x(ds(v[0], 19));
        r[4 * y + 1] = range_limit_x(ds(v[1], 19));
        r[4 * y + 2] = range_limit_x(ds(v[2], 19));
        r[4 * y + 3] = range_limit_x(ds(v[3], 19));
        assert forall|t: int| 0 <= t < 4 * (y + 1) implies #[trigger] r[t] == idct4(c, t / 4, t % 4) by {
            if t >= 4 * y {
                assert(t / 4 == y && t % 4 == t - 4 * y);
            } else {
                assert(r[t] == r0[t]);
            }
        }
        y += 1;
    }
    r
}

/// An `n` by `n` block (`n` 1, 2 or 4), sample (`y`, `x`) at `r[n * y + x]`.
fn sblock(a: &Vec<i16>, o: usize, q: &[u16; 64], n: usize) -> (r: [u8; 16])
    requires
        o + 64 <= a.len(),
        n == 1 || n == 2 || n == 4,
    ensures
        forall|t: int| 0 <= t < n * n ==> #[trigger] r[t] == idct_n(dequant(a@, o as int, q@), n as int, t / n as int, t % n as int),
{
    if n == 1 {
        let mut r = [0u8; 16];
        r[0] = blk1(a, o, q);
        assert forall|t: int| 0 <= t < n * n implies #[trigger] r[t] == idct_n(dequant(a@, o as int, q@), n as int, t / n as int, t % n as int) by {
            assert(t == 0);
        }
        r
    } else if n == 2 {
        let b = blk2(a, o, q);
        let mut r = [0u8; 16];
        r[0] = b[0];
        r[1] = b[1];
        r[2] = b[2];
        r[3] = b[3];
        assert forall|t: int| 0 <= t < n * n implies #[trigger] r[t] == idct_n(dequant(a@, o as int, q@), n as int, t / n as int, t % n as int) by {
            assert(t == 0 || t == 1 || t == 2 || t == 3);
            assert(r[t] == b[t]);
        }
        r
    } else {
        blk4(a, o, q)
    }
}

// ---------------------------------------------------------------------------
// Component planes
// ---------------------------------------------------------------------------
/// Where sample (`r`, `x`) of a plane of `n` by `n` blocks, `wb` blocks
/// wide, is kept: block by block, each block row by row.
pub open spec fn sidx(n: int, wb: int, r: int, x: int) -> int {
    ((r / n) * wb + x / n) * (n * n) + (r % n) * n + x % n
}

/// What `splane` stores at `j`.
pub open spec fn bval(a: Seq<i16>, q: Seq<u16>, cw: int, wb: int, n: int, j: int) -> u8 {
    let b = j / (n * n);
    let t = j % (n * n);
    idct_n(dequant(a, 64 * ((b / wb) * cw + b % wb), q), n, t / n, t % n)
}

proof fn lemma_sidx(n: int, wb: int, hb: int, r: int, x: int)
    requires
        n >= 1,
        wb >= 1,
        0 <= r < n * hb,
        0 <= x < n * wb,
    ensures
        0 <= sidx(n, wb, r, x) < (n * n) * (wb * hb),
        sidx(n, wb, r, x) / (n * n) == (r / n) * wb + x / n,
        ((r / n) * wb + x / n) / wb == r / n,
        ((r / n) * wb + x / n) % wb == x / n,
        sidx(n, wb, r, x) % (n * n) == (r % n) * n + x % n,
        ((r % n) * n + x % n) / n == r % n,
        ((r % n) * n + x % n) % n == x % n,
{
    let (br, bx, yr, xr) = (r / n, x / n, r % n, x % n);
    lemma_fundamental_div_mod(r, n);
    lemma_fundamental_div_mod(x, n);
    lemma_mod_bound(r, n);
    lemma_mod_bound(x, n);
    assert(0 <= br < hb && 0 <= bx < wb) by {
        lemma_div_pos_is_pos(r, n);
        lemma_div_pos_is_pos(x, n);
        assert(r < hb * n && x < wb * n) by (nonlinear_arith)
            requires
                r < n * hb,
                x < n * wb,
        ;
        crate::render::lemma_div_lt(r, n, hb);
        crate::render::lemma_div_lt(x, n, wb);
    }
    let t = yr * n + xr;
    assert(0 <= t < n * n) by (nonlinear_arith)
        requires
            0 <= yr < n,
            0 <= xr < n,
            t == yr * n + xr,
    ;
    let b = br * wb + bx;
    assert(0 <= b < wb * hb) by (nonlinear_arith)
        requires
            0 <= br < hb,
            0 <= bx < wb,
            b == br * wb + bx,
    ;
    assert(0 <= b * (n * n) + t < (n * n) * (wb * hb)) by (nonlinear_arith)
        requires
            0 <= b < wb * hb,
            0 <= t < n * n,
    ;
    lemma_fundamental_div_mod_converse(b * (n * n) + t, n * n, b, t);
    lemma_fundamental_div_mod_converse(b, wb, br, bx);
    lemma_fundamental_div_mod_converse(t, n, yr, xr);
}

/// `splane`'s planes hold `ssample`.
proof fn lemma_bval(a: Seq<i16>, q: Seq<u16>, cw: int, wb: int, hb: int, n: int, r: int, x: int)
    requires
        n >= 1,
        wb >= 1,
        0 <= r < n * hb,
        0 <= x < n * wb,
    ensures
        bval(a, q, cw, wb, n, sidx(n, wb, r, x)) == idct_n(dequant(a, 64 * ((r / n) * cw + x / n), q), n, r % n, x % n),
{
    lemma_sidx(n, wb, hb, r, x);
}

/// The samples of a component's blocks of image data at inverse DCT size
/// `n` (1, 2 or 4), block by block.
fn splane(a: &Vec<i16>, q: &[u16; 64], cw: u32, wb: u32, hb: u32, n: usize, Ghost(chh): Ghost<int>) -> (r: Option<Vec<u8>>)
    requires
        1 <= wb <= cw <= 0x4_0080,
        1 <= hb <= chh <= 0x4_0080,
        a.len() == 64 * (cw * chh),
        n == 1 || n == 2 || n == 4,
    ensures
        r matches Some(pl) ==> {
            &&& pl.len() == (n * n) * (wb * hb)
            &&& forall|j: int| 0 <= j < pl.len() ==> #[trigger] pl@[j] == bval(a@, q@, cw as int, wb as int, n as int, j)
        },
{
    let nn = n * n;
    assert(nn <= 16);
    assert((wb as u64) * (hb as u64) <= 0x4_0080 * 0x4_0080) by (nonlinear_arith)
        requires
            wb <= 0x4_0080,
            hb <= 0x4_0080,
    ;
    let nb64 = wb as u64 * hb as u64;
    assert(nb64 * (nn as u64) <= 16 * (0x4_0080 * 0x4_0080)) by (nonlinear_arith)
        requires
            nb64 <= 0x4_0080 * 0x4_0080,
            nn <= 16,
    ;
    let total64 = nb64 * nn as u64;
    if total64 > usize::MAX as u64 {
        return None;
    }
    assert(nb64 <= total64) by (nonlinear_arith)
        requires
            total64 == nb64 * nn,
            nn >= 1,
            nb64 >= 0,
    ;
    let nb = nb64 as usize;
    let total = total64 as usize;
    let mut pl = match alloc_u8(total) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    let mut b: usize = 0;
    while b < nb
        invariant
            b <= nb,
            nb == wb * hb,
            nn == n * n,
            nn <= 16,
            n == 1 || n == 2 || n == 4,
            1 <= wb <= cw <= 0x4_0080,
            1 <= hb <= chh <= 0x4_0080,
            a.len() == 64 * (cw * chh),
            nb <= 0x4_0080 * 0x4_0080,
            nb * nn <= usize::MAX,
            pl.len() == nb * nn,
            forall|j: int| 0 <= j < b * nn ==> #[trigger] pl@[j] == bval(a@, q@, cw as int, wb as int, n as int, j),
        decreases nb - b,
    {
        let by = b / wb as usize;
        let bx = b % wb as usize;
        proof {
            lemma_fundamental_div_mod(b as int, wb as int);
            lemma_mod_bound(b as int, wb as int);
            lemma_div_pos_is_pos(b as int, wb as int);
            assert(b < hb * wb) by (nonlinear_arith)
                requires
                    b < nb,
                    nb == wb * hb,
            ;
            crate::render::lemma_div_lt(b as int, wb as int, hb as int);
            assert(by * cw + bx < cw * chh && 64 * (by * cw + bx) + 64 <= a.len()) by (nonlinear_arith)
                requires
                    by < hb <= chh,
                    bx < wb <= cw,
                    a.len() == 64 * (cw * chh),
            ;
            assert((b + 1) * nn <= nb * nn && b * nn + nn == (b + 1) * nn) by (nonlinear_arith)
                requires
                    b < nb,
            ;
        }
        let o = 64 * (by * cw as usize + bx);
        let blk = sblock(a, o, q, n);
        let base = b * nn;
        let mut t: usize = 0;
        while t < nn
            invariant
                t <= nn,
                nn == n * n,
                nn <= 16,
                base == b * nn,
                base + nn <= pl.len(),
                pl.len() == nb * nn,
                b < nb,
                by == b as int / wb as int,
                bx == b as int % wb as int,
                o == 64 * (by * cw + bx),
                forall|t2: int| 0 <= t2 < nn ==> #[trigger] blk[t2] == idct_n(dequant(a@, o as int, q@), n as int, t2 / n as int, t2 % n as int),
                forall|j: int| 0 <= j < base + t ==> #[trigger] pl@[j] == bval(a@, q@, cw as int, wb as int, n as int, j),
            decreases nn - t,
        {
            proof {
                lemma_fundamental_div_mod_converse((base + t) as int, nn as int, b as int, t as int);
            }
            vset(&mut pl, base + t, blk[t]);
            t += 1;
        }
        b += 1;
        proof {
            assert((b - 1) * nn + nn == b * nn) by (nonlinear_arith);
        }
    }
    proof {
        assert(pl.len() == (n * n) * (wb * hb)) by (nonlinear_arith)
            requires
                pl.len() == nb * nn,
                nb == wb * hb,
                nn == n * n,
        ;
    }
    Some(pl)
}

// ---------------------------------------------------------------------------
// Sizes
// ---------------------------------------------------------------------------
proof fn lemma_step(aa: int, b: int, m: int, s: int)
    requires
        m == 1 || m == 2 || m == 4,
        s == m || s == 2 * m || s == 4 * m,
        b >= 1,
        aa >= 1,
        (aa * m) % (b * s * 2) == 0,
    ensures
        aa % (b * ((2 * s) / m)) == 0,
{
    let d = b * s * 2;
    assert(d > 0) by (nonlinear_arith)
        requires
            d == b * s * 2,
            b >= 1,
            s >= 1,
    ;
    lemma_fundamental_div_mod(aa * m, d);
    let qq = (aa * m) / d;
    let t = s / m;
    assert(s == m * t && (2 * s) / m == 2 * t) by {
        if s == m {
            assert(t == 1);
        } else if s == 2 * m {
            assert(t == 2);
        } else {
            assert(t == 4);
        }
    }
    assert(aa == (b * (2 * t)) * qq) by (nonlinear_arith)
        requires
            aa * m == d * qq,
            d == b * s * 2,
            s == m * t,
            m > 0,
    ;
    assert(b * (2 * t) > 0) by (nonlinear_arith)
        requires
            b >= 1,
            t >= 1,
    ;
    lemma_mod_multiples_basic(qq, b * (2 * t));
    assert(qq * (b * (2 * t)) == (b * (2 * t)) * qq) by (nonlinear_arith);
}

/// What `ssize_from` gives from `s` on.
proof fn lemma_ss(f: Frame, c: int, m: int, s: int)
    requires
        0 <= c < f.comps.len(),
        m == 1 || m == 2 || m == 4,
        s == m || s == 2 * m || s == 4 * m || s == 8 * m,
        1 <= s <= 8,
        1 <= f.comps[c].h <= 4,
        1 <= f.comps[c].v <= 4,
        1 <= maxh(f) <= 4,
        1 <= maxv(f) <= 4,
        maxh(f) % (f.comps[c].h as int * (s / m)) == 0,
        maxv(f) % (f.comps[c].v as int * (s / m)) == 0,
    ensures
        ({
            let n = ssize_from(f, c, m, s);
            &&& n == m || n == 2 * m || n == 4 * m || n == 8 * m
            &&& s <= n <= 8
            &&& maxh(f) % (f.comps[c].h as int * (n / m)) == 0
            &&& maxv(f) % (f.comps[c].v as int * (n / m)) == 0
        }),
    decreases 8 - s,
{
    let b = f.comps[c].h as int;
    let v = f.comps[c].v as int;
    if 0 < s < 8 && (maxh(f) * m) % (b * s * 2) == 0 && (maxv(f) * m) % (v * s * 2) == 0 {
        assert(s != 8 * m);
        lemma_step(maxh(f), b, m, s);
        lemma_step(maxv(f), v, m, s);
        lemma_ss(f, c, m, 2 * s);
    }
}

/// The sizes of component `c` at scale `m / 8`, and what reading its
/// samples for the output needs.
proof fn lemma_sizes(f: Frame, c: int, m: int)
    requires
        frame_ok(f),
        frame_basic(f),
        0 <= c < f.nc,
        m == 1 || m == 2 || m == 4,
    ensures
        ({
            let n = ssize(f, c, m);
            let hi = hin(f, c, m);
            let vi = vin(f, c, m);
            &&& n == 1 || n == 2 || n == 4 || n == 8
            &&& m <= n
            &&& 1 <= hi <= maxh(f)
            &&& 1 <= vi <= maxv(f)
            &&& hi * (maxh(f) / hi) == maxh(f)
            &&& vi * (maxv(f) / vi) == maxv(f)
            &&& 1 <= sdw(f, c, m) <= n * wb(f, c)
            &&& 1 <= sdh(f, c, m) <= n * hb(f, c)
            &&& cdiv(f.w * m, 8) <= sdw(f, c, m) * (maxh(f) / hi)
            &&& cdiv(f.h * m, 8) <= sdh(f, c, m) * (maxv(f) / vi)
        }),
{
    assert(1 <= f.comps[c].h <= 4 && 1 <= f.comps[c].v <= 4);
    assert(maxh(f) % f.comps[c].h as int == 0 && maxv(f) % f.comps[c].v as int == 0);
    assert(1 <= maxh(f) <= 4 && 1 <= maxv(f) <= 4) by {
        assert(1 <= f.comps[0].h <= 4 && 1 <= f.comps[0].v <= 4);
        if f.nc == 3 {
            assert(1 <= f.comps[1].h <= 4 && 1 <= f.comps[1].v <= 4);
            assert(1 <= f.comps[2].h <= 4 && 1 <= f.comps[2].v <= 4);
        }
    }
    assert(m / m == 1);
    lemma_ss(f, c, m, m);
    let n = ssize(f, c, m);
    let t = n / m;
    assert(n == m * t && 1 <= t <= 8) by {
        if n == m {
            assert(t == 1);
        } else if n == 2 * m {
            assert(t == 2);
        } else if n == 4 * m {
            assert(t == 4);
        } else {
            assert(t == 8);
        }
    }
    lemma_dim1(f.w, f.comps[c].h as int, maxh(f), m, n, t, wb(f, c));
    lemma_dim1(f.h, f.comps[c].v as int, maxv(f), m, n, t, hb(f, c));
}

/// `cdiv(x, d) <= t` when `x <= d * t`.
proof fn lemma_cdiv_le(x: int, d: int, t: int)
    requires
        0 <= x <= d * t,
        d > 0,
    ensures
        cdiv(x, d) <= t,
{
    assert(x + d - 1 <= t * d + d - 1) by (nonlinear_arith)
        requires
            x <= d * t,
    ;
    lemma_div_is_ordered(x + d - 1, t * d + d - 1, d);
    lemma_fundamental_div_mod_converse(t * d + d - 1, d, t, d - 1);
}

/// One dimension of `lemma_sizes`.
proof fn lemma_dim1(w: int, b: int, aa: int, m: int, n: int, t: int, wbc: int)
    requires
        1 <= w <= 65535,
        1 <= b <= 4,
        1 <= aa <= 4,
        m == 1 || m == 2 || m == 4,
        n == m * t,
        1 <= t <= 8,
        aa % (b * t) == 0,
        wbc == cdiv(w * b, 8 * aa),
    ensures
        ({
            let hi = b * n / m;
            let sd = cdiv(w * b * n, 8 * aa);
            &&& hi == b * t
            &&& 1 <= hi <= aa
            &&& hi * (aa / hi) == aa
            &&& 1 <= sd <= n * wbc
            &&& cdiv(w * m, 8) <= sd * (aa / hi)
        }),
{
    let hi = b * t;
    assert(b * n == hi * m) by (nonlinear_arith)
        requires
            n == m * t,
            hi == b * t,
    ;
    lemma_div_by_multiple(hi, m);
    assert(hi >= 1) by (nonlinear_arith)
        requires
            b >= 1,
            t >= 1,
            hi == b * t,
    ;
    lemma_fundamental_div_mod(aa, hi);
    let he = aa / hi;
    assert(hi * he == aa);
    assert(he >= 1 && hi <= aa) by (nonlinear_arith)
        requires
            hi * he == aa,
            hi >= 1,
            aa >= 1,
    ;
    let x = w * b * n;
    let d = 8 * aa;
    assert(x >= 1) by (nonlinear_arith)
        requires
            x == w * b * n,
            w >= 1,
            b >= 1,
            n >= 1,
    ;
    let sd = cdiv(x, d);
    lemma_cdiv(x, d);
    assert(sd >= 1) by {
        lemma_div_is_ordered(d, x + d - 1, d);
        lemma_div_by_multiple(1, d);
    }
    // sd <= n * wbc
    lemma_cdiv(w * b, d);
    assert(x <= d * (n * wbc)) by (nonlinear_arith)
        requires
            w * b <= wbc * d,
            x == w * b * n,
            n >= 1,
    ;
    lemma_cdiv_le(x, d, n * wbc);
    // cdiv(w * m, 8) <= sd * he
    assert(w * m <= 8 * (sd * he)) by (nonlinear_arith)
        requires
            x <= sd * d,
            d == 8 * aa,
            aa == hi * he,
            x == w * b * n,
            b * n == hi * m,
            hi >= 1,
    ;
    assert(w * m >= 0) by (nonlinear_arith)
        requires
            w >= 1,
            m >= 1,
    ;
    lemma_cdiv_le(w * m, 8, sd * he);
}

/// `ssize`, computed.
fn ssize_x(f: &FrameX, maxh_: u32, maxv_: u32, c: usize, m: u32) -> (n: u32)
    requires
        frame_ok(f@),
        frame_basic(f@),
        c < f.nc,
        maxh_ == maxh(f@),
        maxv_ == maxv(f@),
        m == 1 || m == 2 || m == 4,
    ensures
        n == ssize(f@, c as int, m as int),
{
    let ghost fv = f@;
    let ghost ci = c as int;
    let h = f.comps[c].h as u32;
    let v = f.comps[c].v as u32;
    assert(fv.comps[ci] == f.comps[ci]);
    assert(1 <= h <= 4 && 1 <= v <= 4);
    proof {
        lemma_sizes(fv, ci, m as int);
    }
    let mut s = m;
    loop
        invariant
            s == 1 || s == 2 || s == 4 || s == 8,
            1 <= h <= 4,
            1 <= v <= 4,
            1 <= maxh_ <= 4,
            1 <= maxv_ <= 4,
            1 <= m <= 4,
            h == fv.comps[ci].h,
            v == fv.comps[ci].v,
            maxh_ == maxh(fv),
            maxv_ == maxv(fv),
            ssize_from(fv, ci, m as int, s as int) == ssize(fv, ci, m as int),
        ensures
            s as int == ssize(fv, ci, m as int),
        decreases 8 - s,
    {
        if s >= 8 {
            assert(ssize_from(fv, ci, m as int, s as int) == s as int);
            break;
        }
        assert(maxh_ * m <= 16 && maxv_ * m <= 16 && h * s * 2 <= 64 && v * s * 2 <= 64 && h * s * 2 >= 1 && v * s * 2 >= 1)
            by (nonlinear_arith)
            requires
                1 <= s <= 8,
                1 <= h <= 4,
                1 <= v <= 4,
                1 <= maxh_ <= 4,
                1 <= maxv_ <= 4,
                1 <= m <= 4,
        ;
        if (maxh_ * m) % (h * s * 2) != 0 || (maxv_ * m) % (v * s * 2) != 0 {
            assert(ssize_from(fv, ci, m as int, s as int) == s as int);
            break;
        }
        s = s * 2;
    }
    s
}

// ---------------------------------------------------------------------------
// A component at scale m / 8
// ---------------------------------------------------------------------------
/// A component's samples at the reduced size, and its upsampling ratios.
pub struct SComp {
    /// Block by block (`sidx`) when `n` is 1, 2 or 4; row by row when 8.
    pub pl: Vec<u8>,
    pub n: usize,
    pub wb: usize,
    pub stride: usize,
    pub rows: usize,
    /// `sdw` and `sdh`.
    pub sw: usize,
    pub sh: usize,
    pub hi: usize,
    pub vi: usize,
    pub ho: usize,
    pub vo: usize,
    /// `ho / hi` and `vo / vi`.
    pub he: usize,
    pub ve: usize,
}

impl SComp {
    /// Sample (`r`, `x`).
    pub open spec fn at(&self, r: int, x: int) -> u8 {
        if self.n == 8 {
            self.pl@[r * self.stride + x]
        } else {
            self.pl@[sidx(self.n as int, self.wb as int, r, x)]
        }
    }

    pub open spec fn ok(&self, k: Coded, c: int, m: int) -> bool {
        &&& self.n as int == ssize(k.f, c, m)
        &&& self.n == 1 || self.n == 2 || self.n == 4 || self.n == 8
        &&& 1 <= self.wb <= 0x4_0080
        &&& self.stride == self.n * self.wb
        &&& 1 <= self.rows <= 8 * 0x4_0080
        &&& self.pl@.len() == self.stride * self.rows
        &&& self.n != 8 ==> self.rows % self.n == 0
        &&& forall|r: int, x: int| 0 <= r < self.rows && 0 <= x < self.stride ==> #[trigger] self.at(r, x) as int == ssample(k, c, m, r, x)
        &&& self.sw == sdw(k.f, c, m)
        &&& self.sh == sdh(k.f, c, m)
        &&& 1 <= self.sw <= self.stride
        &&& 1 <= self.sh <= self.rows
        &&& self.hi == hin(k.f, c, m)
        &&& self.vi == vin(k.f, c, m)
        &&& self.ho == maxh(k.f)
        &&& self.vo == maxv(k.f)
        &&& 1 <= self.hi <= self.ho <= 4
        &&& 1 <= self.vi <= self.vo <= 4
        &&& self.he == self.ho / self.hi
        &&& self.ve == self.vo / self.vi
        &&& self.he * self.hi == self.ho
        &&& self.ve * self.vi == self.vo
        &&& cdiv(k.f.w * m, 8) <= self.sw * self.he
        &&& cdiv(k.f.h * m, 8) <= self.sh * self.ve
    }

    /// Sample (`r`, `x`).
    #[inline(always)]
    #[verifier::rlimit(40)]
    fn get(&self, r: usize, x: usize, Ghost(k): Ghost<Coded>, Ghost(c): Ghost<int>, Ghost(m): Ghost<int>) -> (v: u8)
        requires
            self.ok(k, c, m),
            r < self.rows,
            x < self.stride,
        ensures
            v as int == ssample(k, c, m, r as int, x as int),
            v == self.at(r as int, x as int),
    {
        hide(ssample);
        hide(sidx);
        assert(self.at(r as int, x as int) as int == ssample(k, c, m, r as int, x as int));
        if self.n == 8 {
            let len = self.pl.len();
            proof {
                lemma_rowbase(r as int, self.rows as int, self.stride as int);
            }
            vget(&self.pl, r * self.stride + x)
        } else {
            let n = self.n;
            let len = self.pl.len();
            proof {
                lemma_get_idx(n as int, self.wb as int, self.rows as int, self.stride as int, r as int, x as int);
            }
            let br = r / n;
            let bx = x / n;
            let bl = br * self.wb + bx;
            let i = bl * (n * n) + (r % n) * n + x % n;
            vget(&self.pl, i)
        }
    }
}

/// Reading sample (`r`, `x`) of a plane kept block by block.
proof fn lemma_get_idx(n: int, wb: int, rows: int, stride: int, r: int, x: int)
    requires
        n == 1 || n == 2 || n == 4,
        1 <= wb <= 0x4_0080,
        stride == n * wb,
        1 <= rows <= 8 * 0x4_0080,
        rows % n == 0,
        0 <= r < rows,
        0 <= x < stride,
    ensures
        0 <= (r / n) * wb <= (r / n) * wb + x / n <= sidx(n, wb, r, x),
        0 <= ((r / n) * wb + x / n) * (n * n) <= sidx(n, wb, r, x),
        0 <= (r % n) * n + x % n < n * n,
        ((r / n) * wb + x / n) * (n * n) + (r % n) * n + x % n == sidx(n, wb, r, x),
        0 <= sidx(n, wb, r, x) < stride * rows,
{
    let hb = rows / n;
    lemma_fundamental_div_mod(rows, n);
    assert(rows == n * hb);
    assert(hb <= 8 * 0x4_0080) by {
        lemma_div_is_ordered_by_denominator(rows, 1, n);
    }
    lemma_sidx(n, wb, hb, r, x);
    assert((n * n) * (wb * hb) == stride * rows) by (nonlinear_arith)
        requires
            stride == n * wb,
            rows == n * hb,
    ;
    let b = (r / n) * wb + x / n;
    let t = (r % n) * n + x % n;
    lemma_div_pos_is_pos(r, n);
    lemma_div_pos_is_pos(x, n);
    lemma_mod_bound(r, n);
    lemma_mod_bound(x, n);
    assert(0 <= t < n * n) by (nonlinear_arith)
        requires
            0 <= r % n < n,
            0 <= x % n < n,
            t == (r % n) * n + x % n,
    ;
    assert(b < wb * hb) by {
        assert(sidx(n, wb, r, x) < (wb * hb) * (n * n)) by (nonlinear_arith)
            requires
                sidx(n, wb, r, x) < (n * n) * (wb * hb),
        ;
        lemma_div_lt(sidx(n, wb, r, x), n * n, wb * hb);
    }
    assert(0 <= (r / n) * wb && 0 <= b * (n * n) && b <= b * (n * n)) by (nonlinear_arith)
        requires
            r / n >= 0,
            wb >= 0,
            b >= 0,
            n >= 1,
    ;
}

proof fn lemma_div_lt(x: int, d: int, n: int)
    requires
        0 <= x < n * d,
        d > 0,
    ensures
        0 <= x / d < n,
{
    crate::render::lemma_div_lt(x, d, n);
}

/// `lemma_rowbase` from render.rs, for `usize` rows.
proof fn lemma_rowbase(r: int, rows: int, stride: int)
    requires
        0 <= r < rows,
        stride >= 0,
    ensures
        0 <= r * stride,
        r * stride + stride <= stride * rows,
{
    crate::render::lemma_rowbase(r, rows, stride);
}


/// Component `c` of a decoded file at scale `m / 8`.
#[verifier::rlimit(100)]
fn scomp(st: &DecX, c: usize, m: u32, Ghost(k): Ghost<Coded>) -> (r: Option<SComp>)
    requires
        st.wf(),
        st.started,
        !st.co.stream,
        c < st.f.nc,
        m == 1 || m == 2 || m == 4,
        k == coded(*st),
    ensures
        r matches Some(s) ==> s.ok(k, c as int, m as int),
{
    hide(idct_n);
    hide(idct);
    hide(dequant);
    hide(range_limit);
    let ghost f = st.f@;
    let ghost ci = c as int;
    let g = st.g;
    proof {
        lemma_comp_geom(f, ci);
        lemma_sizes(f, ci, m as int);
        assert(g.cw[ci] == cw(f, ci));
        assert(g.ch[ci] == ch(f, ci) && g.wb[ci] == wb(f, ci) && g.hb[ci] == hb(f, ci));
        assert(g.wb[ci] <= g.cw[ci] && g.hb[ci] <= g.ch[ci] && g.cw[ci] <= 0x4_0080 && g.ch[ci] <= 0x4_0080);
        assert(f.comps[ci] == st.f.comps[ci]);
        assert(g.maxh == maxh(f) && g.maxv == maxv(f));
        reveal(csize);
    }
    let n = ssize_x(&st.f, g.maxh, g.maxv, c, m) as usize;
    let a: &Vec<i16> = if c == 0 {
        &st.co.a0
    } else if c == 1 {
        &st.co.a1
    } else {
        &st.co.a2
    };
    assert(a@ == k.a[ci]);
    assert(st.ql[ci]@ == k.ql[ci]);
    assert(a.len() == 64 * (g.cw[ci] * g.ch[ci]));
    let (cwc, wbc, hbc) = (g.cw[c], g.wb[c], g.hb[c]);
    let ghost chh = g.ch[ci] as int;
    let pl = if n == 8 {
        let kt = crate::idct16::idct_consts();
        let tracked mut mt = Meter { n: 0 };
        match plane_x(a, &st.ql[c], &kt, cwc, wbc, hbc, Ghost(chh), Tracked(&mut mt)) {
            Some(p) => p,
            None => {
                return None;
            },
        }
    } else {
        match splane(a, &st.ql[c], cwc, wbc, hbc, n, Ghost(chh)) {
            Some(p) => p,
            None => {
                return None;
            },
        }
    };
    let h = st.f.comps[c].h as u64;
    let v = st.f.comps[c].v as u64;
    let w = st.f.w as u64;
    let hh = st.f.h as u64;
    let (mh, mv) = (g.maxh as u64, g.maxv as u64);
    let nn = n as u64;
    assert(h <= 4 && v <= 4 && nn <= 8 && 1 <= h && 1 <= v);
    assert(w * h <= 65535 * 4 && hh * v <= 65535 * 4) by (nonlinear_arith)
        requires
            w <= 65535,
            hh <= 65535,
            h <= 4,
            v <= 4,
    ;
    assert(w * h * nn <= 65535 * 32 && hh * v * nn <= 65535 * 32) by (nonlinear_arith)
        requires
            w <= 65535,
            hh <= 65535,
            h <= 4,
            v <= 4,
            nn <= 8,
    ;
    let sw = ((w * h * nn + 8 * mh - 1) / (8 * mh)) as usize;
    let sh = ((hh * v * nn + 8 * mv - 1) / (8 * mv)) as usize;
    let hi = (h * nn / (m as u64)) as usize;
    let vi = (v * nn / (m as u64)) as usize;
    let he = g.maxh as usize / hi;
    let ve = g.maxv as usize / vi;
    assert(n * (wbc as usize) <= 8 * 0x4_0080 && n * (hbc as usize) <= 8 * 0x4_0080) by (nonlinear_arith)
        requires
            n <= 8,
            wbc <= 0x4_0080,
            hbc <= 0x4_0080,
    ;
    let s = SComp {
        pl,
        n,
        wb: wbc as usize,
        stride: n * wbc as usize,
        rows: n * hbc as usize,
        sw,
        sh,
        hi,
        vi,
        ho: g.maxh as usize,
        vo: g.maxv as usize,
        he,
        ve,
    };
    proof {
        let (wbi, hbi, cwi) = (wbc as int, hbc as int, cwc as int);
        assert(s.stride * s.rows == (n * n) * (wbi * hbi) && s.stride * s.rows == (n * wbi) * (n * hbi)) by (nonlinear_arith)
            requires
                s.stride == n * wbi,
                s.rows == n * hbi,
        ;
        assert(s.rows <= 8 * 0x4_0080) by (nonlinear_arith)
            requires
                s.rows == n * hbi,
                n <= 8,
                hbi <= 0x4_0080,
        ;
        if n != 8 {
            lemma_mod_multiples_basic(hbi, n as int);
            assert(hbi * n == n * hbi) by (nonlinear_arith);
        }
        assert(s.n as int == ssize(k.f, ci, m as int));
        assert(s.sw == sdw(k.f, ci, m as int));
        assert(s.sh == sdh(k.f, ci, m as int));
        assert(s.hi == hin(k.f, ci, m as int));
        assert(s.vi == vin(k.f, ci, m as int));
        assert(s.he == s.ho / s.hi);
        assert(s.pl@.len() == s.stride * s.rows);
        assert(s.n != 8 ==> s.rows % s.n == 0);
        assert(1 <= s.wb <= 0x4_0080);
        assert(1 <= s.rows <= 8 * 0x4_0080);
        assert(1 <= s.sw <= s.stride);
        assert(1 <= s.sh <= s.rows);
        assert(s.ho == maxh(k.f) && s.vo == maxv(k.f));
        assert(1 <= s.hi <= s.ho <= 4);
        assert(1 <= s.vi <= s.vo <= 4);
        assert(s.he * s.hi == s.ho) by (nonlinear_arith)
            requires
                s.hi * (s.ho / s.hi) == s.ho,
                s.he == s.ho / s.hi,
        ;
        assert(s.ve * s.vi == s.vo) by (nonlinear_arith)
            requires
                s.vi * (s.vo / s.vi) == s.vo,
                s.ve == s.vo / s.vi,
        ;
        assert(cdiv(k.f.w * m, 8) <= s.sw * s.he);
        assert(cdiv(k.f.h * m, 8) <= s.sh * s.ve);
        assert forall|r: int, x: int| 0 <= r < s.rows && 0 <= x < s.stride implies #[trigger] s.at(r, x) as int == ssample(k, ci, m as int, r, x) by {
            if n == 8 {
                reveal(idct_n);
                assert(pat(s.pl@, 8 * wbi, r, x) == psample(a@, st.ql[ci]@, cwi, r, x));
            } else {
                lemma_bval(a@, st.ql[ci]@, cwi, wbi, hbi, n as int, r, x);
                lemma_sidx(n as int, wbi, hbi, r, x);
            }
        }
    }
    Some(s)
}

/// `3 * near + far` of a component upsampled vertically 2:1.
#[inline(always)]
fn csum_x(s: &SComp, y: usize, x: usize, Ghost(k): Ghost<Coded>, Ghost(c): Ghost<int>, Ghost(m): Ghost<int>) -> (r: u32)
    requires
        s.ok(k, c, m),
        y / 2 < s.sh,
        x < s.stride,
    ensures
        r as int == scolsum(k, c, m, y as int, x as int),
        r <= 1020,
{
    hide(ssample);
    hide(idct_n);
    let y2 = y / 2;
    let far = if y % 2 == 0 {
        if y2 == 0 {
            0
        } else {
            y2 - 1
        }
    } else if y2 + 1 > s.sh - 1 {
        s.sh - 1
    } else {
        y2 + 1
    };
    assert(far as int == sfar_row(k, c, m, y as int));
    3 * s.get(y2, x, Ghost(k), Ghost(c), Ghost(m)) as u32 + s.get(far, x, Ghost(k), Ghost(c), Ghost(m)) as u32
}

/// Component `c` at output pixel (`y`, `x`).
#[verifier::rlimit(60)]
fn sup_x(s: &SComp, m: u32, y: usize, x: usize, Ghost(k): Ghost<Coded>, Ghost(c): Ghost<int>) -> (v: u8)
    requires
        s.ok(k, c, m as int),
        m == 1 || m == 2 || m == 4,
        y < cdiv(k.f.h * m, 8),
        x < cdiv(k.f.w * m, 8),
    ensures
        v as int == supsampled(k, c, m as int, y as int, x as int),
{
    hide(ssample);
    hide(sdw);
    hide(sdh);
    hide(idct_n);
    let ghost mi = m as int;
    let fancy = m > 1;
    let w = s.sw;
    if s.hi == s.ho && s.vi == s.vo {
        assert(s.he == 1 && s.ve == 1) by (nonlinear_arith)
            requires
                s.he * s.hi == s.ho,
                s.ve * s.vi == s.vo,
                s.hi == s.ho,
                s.vi == s.vo,
                s.hi >= 1,
                s.vi >= 1,
        ;
        assert(s.sw * s.he == s.sw && s.sh * s.ve == s.sh) by (nonlinear_arith)
            requires
                s.he == 1,
                s.ve == 1,
        ;
        s.get(y, x, Ghost(k), Ghost(c), Ghost(mi))
    } else if s.hi * 2 == s.ho && s.vi == s.vo && fancy && w > 2 {
        assert(s.he == 2 && s.ve == 1) by (nonlinear_arith)
            requires
                s.he * s.hi == s.ho,
                s.ve * s.vi == s.vo,
                s.hi * 2 == s.ho,
                s.vi == s.vo,
                s.hi >= 1,
                s.vi >= 1,
        ;
        assert(s.sw * s.he == 2 * s.sw && s.sh * s.ve == s.ve * s.sh) by (nonlinear_arith)
            requires
                s.he == 2 && s.ve == 1,
        ;
        let i = x / 2;
        let sv = s.get(y, i, Ghost(k), Ghost(c), Ghost(mi)) as u32;
        if x % 2 == 0 {
            if i == 0 {
                sv as u8
            } else {
                ((3 * sv + s.get(y, i - 1, Ghost(k), Ghost(c), Ghost(mi)) as u32 + 1) / 4) as u8
            }
        } else if i == w - 1 {
            sv as u8
        } else {
            ((3 * sv + s.get(y, i + 1, Ghost(k), Ghost(c), Ghost(mi)) as u32 + 2) / 4) as u8
        }
    } else if s.hi == s.ho && s.vi * 2 == s.vo && fancy {
        assert(s.he == 1 && s.ve == 2) by (nonlinear_arith)
            requires
                s.he * s.hi == s.ho,
                s.ve * s.vi == s.vo,
                s.hi == s.ho,
                s.vi * 2 == s.vo,
                s.hi >= 1,
                s.vi >= 1,
        ;
        assert(s.sw * s.he == s.sw && s.sh * s.ve == 2 * s.sh) by (nonlinear_arith)
            requires
                s.he == 1 && s.ve == 2,
        ;
        // Stated for the solver (z3's Arm build does not find it).
        assert(y < 2 * s.sh);
        assert(y / 2 < s.sh);
        ((csum_x(s, y, x, Ghost(k), Ghost(c), Ghost(mi)) + 1 + (y % 2) as u32) / 4) as u8
    } else if s.hi * 2 == s.ho && s.vi * 2 == s.vo && fancy && w > 2 {
        assert(s.he == 2 && s.ve == 2) by (nonlinear_arith)
            requires
                s.he * s.hi == s.ho,
                s.ve * s.vi == s.vo,
                s.hi * 2 == s.ho,
                s.vi * 2 == s.vo,
                s.hi >= 1,
                s.vi >= 1,
        ;
        assert(s.sw * s.he == 2 * s.sw && s.sh * s.ve == s.ve * s.sh) by (nonlinear_arith)
            requires
                s.he == 2 && s.ve == 2,
        ;
        let i = x / 2;
        let sv = csum_x(s, y, i, Ghost(k), Ghost(c), Ghost(mi));
        if x % 2 == 0 {
            if i == 0 {
                ((4 * sv + 8) / 16) as u8
            } else {
                ((3 * sv + csum_x(s, y, i - 1, Ghost(k), Ghost(c), Ghost(mi)) + 8) / 16) as u8
            }
        } else if i == w - 1 {
            ((4 * sv + 7) / 16) as u8
        } else {
            ((3 * sv + csum_x(s, y, i + 1, Ghost(k), Ghost(c), Ghost(mi)) + 7) / 16) as u8
        }
    } else {
        proof {
            assert(s.ve >= 1 && s.he >= 1) by (nonlinear_arith)
                requires
                    s.he * s.hi == s.ho,
                    s.ve * s.vi == s.vo,
                    s.ho >= 1,
                    s.vo >= 1,
                    s.hi >= 1,
                    s.vi >= 1,
            ;
            crate::render::lemma_div_lt(y as int, s.ve as int, s.sh as int);
            crate::render::lemma_div_lt(x as int, s.he as int, s.sw as int);
        }
        s.get(y / s.ve, x / s.he, Ghost(k), Ghost(c), Ghost(mi))
    }
}

/// libjpeg's YCbCr to RGB conversion of one pixel, channel `ch`.
#[inline(always)]
fn ycc_x(l: u8, cb: u8, cr: u8, ch: usize) -> (r: u8)
    requires
        ch < 3,
    ensures
        ch == 0 ==> r as int == ycc_r(l as int, cr as int),
        ch == 1 ==> r as int == ycc_g(l as int, cb as int, cr as int),
        ch == 2 ==> r as int == ycc_b(l as int, cb as int),
{
    let l = l as i32;
    let cb = cb as i32 - 128;
    let cr = cr as i32 - 128;
    if ch == 0 {
        proof {
            lemma_shr16((91881 * cr + 32768) as i32);
        }
        clamp8(l + ((91881 * cr + 32768) >> 16))
    } else if ch == 1 {
        proof {
            lemma_shr16((-22554 * cb - 46802 * cr + 32768) as i32);
        }
        clamp8(l + ((-22554 * cb - 46802 * cr + 32768) >> 16))
    } else {
        proof {
            lemma_shr16((116130 * cb + 32768) as i32);
        }
        clamp8(l + ((116130 * cb + 32768) >> 16))
    }
}

/// Pixel (`y`, `x`)'s channels (only the first for a grayscale file).
#[verifier::rlimit(40)]
fn px3(s0: &SComp, s1: &Option<SComp>, s2: &Option<SComp>, color: u8, m: u32, y: usize, x: usize, Ghost(k): Ghost<Coded>) -> (r: (u8, u8, u8))
    requires
        m == 1 || m == 2 || m == 4,
        y < cdiv(k.f.h * m, 8),
        x < cdiv(k.f.w * m, 8),
        k.color == color_v(color),
        color <= 2,
        s0.ok(k, 0, m as int),
        color != 0 ==> s1 is Some && s2 is Some && s1->0.ok(k, 1, m as int) && s2->0.ok(k, 2, m as int),
    ensures
        r.0 == spixel(k, m as int, y as int, x as int, 0) as u8,
        color != 0 ==> r.1 == spixel(k, m as int, y as int, x as int, 1) as u8,
        color != 0 ==> r.2 == spixel(k, m as int, y as int, x as int, 2) as u8,
{
    hide(supsampled);
    let l = sup_x(s0, m, y, x, Ghost(k), Ghost(0));
    if color == 0 {
        return (l, 0, 0);
    }
    let cb = match s1 {
        Some(s) => sup_x(s, m, y, x, Ghost(k), Ghost(1)),
        None => 0,
    };
    let cr = match s2 {
        Some(s) => sup_x(s, m, y, x, Ghost(k), Ghost(2)),
        None => 0,
    };
    if color == 1 {
        (ycc_x(l, cb, cr, 0), ycc_x(l, cb, cr, 1), ycc_x(l, cb, cr, 2))
    } else {
        (l, cb, cr)
    }
}

/// Where channel `ch` of pixel (`y`, `x`) goes.
proof fn lemma_pix(y: int, x: int, ch: int, w: int, nc: int)
    requires
        0 <= y,
        0 <= x < w,
        0 <= ch < nc,
        nc >= 1,
    ensures
        ((y * w + x) * nc + ch) / (w * nc) == y,
        (((y * w + x) * nc + ch) / nc) % w == x,
        ((y * w + x) * nc + ch) % nc == ch,
{
    let j = (y * w + x) * nc + ch;
    lemma_fundamental_div_mod_converse(j, nc, y * w + x, ch);
    lemma_fundamental_div_mod_converse(y * w + x, w, y, x);
    assert(j == y * (w * nc) + (x * nc + ch)) by (nonlinear_arith)
        requires
            j == (y * w + x) * nc + ch,
    ;
    assert(0 <= x * nc + ch < w * nc) by (nonlinear_arith)
        requires
            0 <= x < w,
            0 <= ch < nc,
    ;
    lemma_fundamental_div_mod_converse(j, w * nc, y, x * nc + ch);
}

/// The coefficients of a whole file, all kept (no scan is streamed).
pub fn decode_coefs_kept(data: &[u8]) -> (r: Result<DecX, Error>)
    ensures
        match r {
            Ok(st) => jpeg_coded(data@) == Some(coded(st)) && st.wf() && st.started && !st.co.stream,
            Err(Error::Invalid) => jpeg_coded(data@) is None,
            Err(Error::OutOfMemory) => true,
        },
{
    if data.len() >= usize::MAX - 0x2_0000 {
        return Err(Error::OutOfMemory);
    }
    if rd(data, 0) != 0xFF || rd(data, 1) != 0xD8 {
        return Err(Error::Invalid);
    }
    let mut st = dec_new();
    st.keep = true;
    let tracked mut mt = Meter { n: 0 };
    match crate::parse::run_x(data, &mut st, 2, Tracked(&mut mt)) {
        Ok(()) => {
            proof {
                assert(st.has_f);
                assert(st@.ql =~= qlv(st.ql));
            }
            Ok(st)
        },
        Err(e) => Err(e),
    }
}

/// Decodes a JPEG file at `m / 8` of its size (`m` 1, 2 or 4): the image
/// `spec_scaled::jpeg_decode_scaled` gives, which is libjpeg-turbo's with
/// that scaling factor; `Invalid` exactly when the file does not decode.
#[verifier::rlimit(80)]
pub fn decode_scaled(data: &[u8], m: u32) -> (r: Result<Picture, Error>)
    requires
        m == 1 || m == 2 || m == 4,
    ensures
        match r {
            Ok(pic) => jpeg_decode_scaled(data@, m as int) == Some(pic@),
            Err(Error::Invalid) => jpeg_decode_scaled(data@, m as int) is None,
            Err(Error::OutOfMemory) => true,
        },
{
    hide(spixel);
    hide(supsampled);
    let st = match decode_coefs_kept(data) {
        Ok(st) => st,
        Err(e) => {
            return Err(e);
        },
    };
    let ghost k = coded(st);
    let ghost mi = m as int;
    let nc = st.f.nc as usize;
    assert(1 <= st.f.w <= 65535 && 1 <= st.f.h <= 65535);
    assert((st.f.w as usize) * (m as usize) <= 65535 * 4 && (st.f.h as usize) * (m as usize) <= 65535 * 4 && (st.f.w as usize) * (m as usize) >= 1 && (st.f.h as usize) * (m as usize) >= 1) by (nonlinear_arith)
        requires
            1 <= st.f.w <= 65535,
            1 <= st.f.h <= 65535,
            1 <= m <= 4,
    ;
    let ow = ((st.f.w as usize) * (m as usize) + 7) / 8;
    let oh = ((st.f.h as usize) * (m as usize) + 7) / 8;
    assert(ow == cdiv(k.f.w * mi, 8) && oh == cdiv(k.f.h * mi, 8));
    assert(1 <= ow <= 32768 && 1 <= oh <= 32768);
    assert((ow as u64) * (oh as u64) <= 32768 * 32768 && (ow as u64) * (oh as u64) * (nc as u64) <= 32768 * 32768 * 3) by (nonlinear_arith)
        requires
            ow <= 32768,
            oh <= 32768,
            nc <= 3,
    ;
    let total64 = (ow as u64) * (oh as u64) * (nc as u64);
    if total64 > usize::MAX as u64 {
        return Err(Error::OutOfMemory);
    }
    let total = total64 as usize;
    let s0 = match scomp(&st, 0, m, Ghost(k)) {
        Some(s) => s,
        None => {
            return Err(Error::OutOfMemory);
        },
    };
    let (s1, s2) = if nc == 3 {
        let s1 = match scomp(&st, 1, m, Ghost(k)) {
            Some(s) => s,
            None => {
                return Err(Error::OutOfMemory);
            },
        };
        let s2 = match scomp(&st, 2, m, Ghost(k)) {
            Some(s) => s,
            None => {
                return Err(Error::OutOfMemory);
            },
        };
        (Some(s1), Some(s2))
    } else {
        (None, None)
    };
    let mut px = match alloc_u8(total) {
        Some(v) => v,
        None => {
            return Err(Error::OutOfMemory);
        },
    };
    let color = st.color;
    assert(k.color == color_v(color));
    let ghost img = render_scaled(k, mi);
    assert(img.w == ow && img.h == oh && img.nc == nc);
    let mut y: usize = 0;
    let mut p: usize = 0;
    while y < oh
        invariant
            y <= oh,
            p == y * ow * nc,
            1 <= ow <= 32768,
            1 <= oh <= 32768,
            nc == 1 || nc == 3,
            nc == k.f.nc,
            total == ow * oh * nc,
            px@.len() == total,
            ow == cdiv(k.f.w * mi, 8),
            oh == cdiv(k.f.h * mi, 8),
            m == 1 || m == 2 || m == 4,
            mi == m,
            img == render_scaled(k, mi),
            k.color == color_v(color),
            (color == 0) == (nc == 1),
            color <= 2,
            s0.ok(k, 0, mi),
            color != 0 ==> s1 is Some && s2 is Some && s1->0.ok(k, 1, mi) && s2->0.ok(k, 2, mi),
            forall|j: int| 0 <= j < p ==> #[trigger] px@[j] == img.px[j],
        decreases oh - y,
    {
        let mut x: usize = 0;
        while x < ow
            invariant
                y < oh,
                x <= ow,
                p == (y * ow + x) * nc,
                1 <= ow <= 32768,
                1 <= oh <= 32768,
                nc == 1 || nc == 3,
                nc == k.f.nc,
                total == ow * oh * nc,
                px@.len() == total,
                ow == cdiv(k.f.w * mi, 8),
                oh == cdiv(k.f.h * mi, 8),
                m == 1 || m == 2 || m == 4,
                mi == m,
                img == render_scaled(k, mi),
                k.color == color_v(color),
                (color == 0) == (nc == 1),
                color <= 2,
                s0.ok(k, 0, mi),
                color != 0 ==> s1 is Some && s2 is Some && s1->0.ok(k, 1, mi) && s2->0.ok(k, 2, mi),
                forall|j: int| 0 <= j < p ==> #[trigger] px@[j] == img.px[j],
            decreases ow - x,
        {
            proof {
                assert((y * ow + x) * nc + nc <= total) by (nonlinear_arith)
                    requires
                        y < oh,
                        x < ow,
                        total == ow * oh * nc,
                ;
                assert(img.px.len() == total);
            }
            let v = px3(&s0, &s1, &s2, color, m, y, x, Ghost(k));
            let ghost pi = p as int;
            if nc == 1 {
                proof {
                    lemma_pix(y as int, x as int, 0, ow as int, 1);
                }
                vset(&mut px, p, v.0);
                proof {
                    assert(px@[pi] == img.px[pi]);
                }
            } else {
                proof {
                    lemma_pix(y as int, x as int, 0, ow as int, 3);
                    lemma_pix(y as int, x as int, 1, ow as int, 3);
                    lemma_pix(y as int, x as int, 2, ow as int, 3);
                }
                vset(&mut px, p, v.0);
                vset(&mut px, p + 1, v.1);
                vset(&mut px, p + 2, v.2);
                proof {
                    assert(px@[pi] == img.px[pi]);
                    assert(px@[pi + 1] == img.px[pi + 1]);
                    assert(px@[pi + 2] == img.px[pi + 2]);
                }
            }
            p = p + nc;
            x += 1;
        }
        proof {
            assert((y * ow + ow) * nc == (y + 1) * ow * nc) by (nonlinear_arith);
        }
        y += 1;
    }
    proof {
        assert(p == total) by (nonlinear_arith)
            requires
                p == y * ow * nc,
                y == oh,
                total == ow * oh * nc,
        ;
        assert(px@ =~= img.px);
    }
    Ok(Picture { w: ow as u32, h: oh as u32, nc: nc as u8, px })
}

} // verus!

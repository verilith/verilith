//! Dequantization and the inverse DCT: coefficients to samples.
use crate::num::*;
use crate::parse::*;
use crate::prims::*;
use crate::render::clamp8;
use crate::scan::*;
use crate::spec::*;
use crate::types::*;
use crate::work::Meter;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// One pass over eight values, before the final shift.
#[inline(always)]
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn idct_1d_x(x0: i64, x1: i64, x2: i64, x3: i64, x4: i64, x5: i64, x6: i64, x7: i64) -> (r: [i64; 8])
    requires
        -0x8000_0000 <= x0 <= 0x8000_0000,
        -0x8000_0000 <= x1 <= 0x8000_0000,
        -0x8000_0000 <= x2 <= 0x8000_0000,
        -0x8000_0000 <= x3 <= 0x8000_0000,
        -0x8000_0000 <= x4 <= 0x8000_0000,
        -0x8000_0000 <= x5 <= 0x8000_0000,
        -0x8000_0000 <= x6 <= 0x8000_0000,
        -0x8000_0000 <= x7 <= 0x8000_0000,
    ensures
        forall|i: int|
            0 <= i < 8 ==> (#[trigger] r[i]) as int == idct_1d(
                seq![x0 as int, x1 as int, x2 as int, x3 as int, x4 as int, x5 as int, x6 as int, x7 as int],
            )[i],
        forall|i: int| 0 <= i < 8 ==> -0x1000_0000_0000_0000 <= (#[trigger] r[i]) <= 0x1000_0000_0000_0000,
{
    let z1 = (x2 + x6) * 4433;
    let t2 = z1 + x6 * (-15137);
    let t3 = z1 + x2 * 6270;
    let t0 = (x0 + x4) * 8192;
    let t1 = (x0 - x4) * 8192;
    let t10 = t0 + t3;
    let t13 = t0 - t3;
    let t11 = t1 + t2;
    let t12 = t1 - t2;
    let z1 = x7 + x1;
    let z2 = x5 + x3;
    let z3 = x7 + x3;
    let z4 = x5 + x1;
    let z5 = (z3 + z4) * 9633;
    let z1 = z1 * (-7373);
    let z2 = z2 * (-20995);
    let z3 = z3 * (-16069) + z5;
    let z4 = z4 * (-3196) + z5;
    let t0 = x7 * 2446 + z1 + z3;
    let t1 = x5 * 16819 + z2 + z4;
    let t2 = x3 * 25172 + z2 + z3;
    let t3 = x1 * 12299 + z1 + z4;
    [t10 + t3, t11 + t2, t12 + t1, t13 + t0, t13 - t0, t12 - t1, t11 - t2, t10 - t3]
}

#[inline(always)]
pub fn range_limit_x(x: i64) -> (r: u8)
    ensures
        r == range_limit(x as int),
{
    proof {
        lemma_shr(x, 10);
    }
    // The low ten bits as a signed number, shifted by 128 and clamped.
    let m = (x & 1023) as i32;
    let s = if m >= 512 {
        m - 1024
    } else {
        m
    };
    clamp8(s + 128)
}

/// `range_limit` of every ten-bit value, as libjpeg's table.
pub fn range_table() -> (t: [u8; 1024])
    ensures
        forall|m: int| 0 <= m < 1024 ==> (#[trigger] t[m]) == range_limit(m),
{
    let mut t = [0u8; 1024];
    let mut m: usize = 0;
    while m < 1024
        invariant
            m <= 1024,
            forall|j: int| 0 <= j < m ==> (#[trigger] t[j]) == range_limit(j),
        decreases 1024 - m,
    {
        t[m] = range_limit_x(m as i64);
        m += 1;
    }
    t
}

/// `range_limit` by table.
#[inline(always)]
pub fn range_limit_t(x: i64, t: &[u8; 1024]) -> (r: u8)
    requires
        forall|m: int| 0 <= m < 1024 ==> (#[trigger] t[m]) == range_limit(m),
    ensures
        r == range_limit(x as int),
{
    proof {
        lemma_shr(x, 10);
    }
    let m = (x & 1023) as usize;
    assert(range_limit(x as int) == range_limit(m as int));
    t[m]
}

/// A pass over a column or row that is zero but for its first value gives
/// that value, scaled, eight times.
pub proof fn lemma_idct_dc(s: Seq<int>)
    requires
        s.len() == 8,
        forall|i: int| 1 <= i < 8 ==> s[i] == 0,
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] idct_1d(s)[i] == s[0] * 8192,
{
    assert(s[1] == 0 && s[2] == 0 && s[3] == 0 && s[4] == 0 && s[5] == 0 && s[6] == 0 && s[7] == 0);
}

/// A dequantized coefficient.
#[inline(always)]
fn deq(a: &Vec<i16>, o: usize, q: &[u16; 64], k: usize) -> (r: i64)
    requires
        o + 64 <= a.len(),
        k < 64,
    ensures
        r == dequant(a@, o as int, q@)[k as int],
        -0x8000_0000 <= r <= 0x8000_0000,
{
    proof {
        lemma_sx16(q[k as int]);
    }
    let x = vget(a, o + k) as i64;
    let y = (q[k] as i16) as i64;
    assert(-0x8000_0000 <= x * y <= 0x8000_0000) by (nonlinear_arith)
        requires
            -0x8000 <= x <= 0x7fff,
            -0x8000 <= y <= 0x7fff,
    ;
    x * y
}

/// The first pass down column `x`.
fn col_x(a: &Vec<i16>, o: usize, q: &[u16; 64], x: usize) -> (r: [i32; 8])
    requires
        o + 64 <= a.len(),
        x < 8,
    ensures
        forall|y: int| 0 <= y < 8 ==> (#[trigger] r[y]) as int == idct_col(dequant(a@, o as int, q@), x as int, y),
{
    hide(idct_1d);
    let ghost c = dequant(a@, o as int, q@);
    let d0 = deq(a, o, q, x);
    let d1 = deq(a, o, q, 8 + x);
    let d2 = deq(a, o, q, 16 + x);
    let d3 = deq(a, o, q, 24 + x);
    let d4 = deq(a, o, q, 32 + x);
    let d5 = deq(a, o, q, 40 + x);
    let d6 = deq(a, o, q, 48 + x);
    let d7 = deq(a, o, q, 56 + x);
    let ghost col = Seq::new(8, |i: int| c[8 * i + x]);
    proof {
        assert(seq![c[x as int], c[8 + x], c[16 + x], c[24 + x], c[32 + x], c[40 + x], c[48 + x], c[56 + x]] =~= col);
        lemma2_to64();
    }
    if (d1 | d2 | d3 | d4 | d5 | d6 | d7) == 0 {
        // Only the first value is not zero: the pass is a scaling.
        assert(d1 == 0 && d2 == 0 && d3 == 0 && d4 == 0 && d5 == 0 && d6 == 0 && d7 == 0) by (bit_vector)
            requires
                (d1 | d2 | d3 | d4 | d5 | d6 | d7) == 0,
        ;
        let d4x = d0 * 4;
        let v = d4x as i32;
        proof {
            reveal(idct_1d);
            assert(col[0] == d0 && col[1] == d1 && col[2] == d2 && col[3] == d3 && col[4] == d4 && col[5] == d5 && col[6]
                == d6 && col[7] == d7);
            lemma_idct_dc(col);
            lemma_wrap32(d4x);
            assert forall|k: int| 0 <= k < 8 implies v as int == idct_col(c, x as int, k) by {
                assert(idct_1d(col)[k] == d0 * 8192);
                assert((d0 * 8192 + 1024) / 2048 == d0 * 4);
            }
        }
        return [v, v, v, v, v, v, v, v];
    }
    let r = idct_1d_x(d0, d1, d2, d3, d4, d5, d6, d7);
    let mut out = [0i32; 8];
    let mut y: usize = 0;
    while y < 8
        invariant
            y <= 8,
            x < 8,
            col == Seq::new(8, |i: int| c[8 * i + x]),
            forall|i: int| 0 <= i < 8 ==> (#[trigger] r[i]) as int == idct_1d(col)[i],
            forall|i: int| 0 <= i < 8 ==> -0x1000_0000_0000_0000 <= (#[trigger] r[i]) <= 0x1000_0000_0000_0000,
            forall|k: int| 0 <= k < y ==> (#[trigger] out[k]) as int == idct_col(c, x as int, k),
        decreases 8 - y,
    {
        let v = (r[y] + 1024) >> 11;
        proof {
            lemma_shr((r[y as int] + 1024) as i64, 11);
            lemma_wrap32(v);
            lemma2_to64();
            assert(descale(idct_1d(col)[y as int], 11) == v);
        }
        out[y] = v as i32;
        y += 1;
    }
    out
}

/// The second pass along row `y` of the workspace.
#[verifier::spinoff_prover]
fn row_x(ws: &[i32; 64], y: usize, rl: &[u8; 1024], Ghost(c): Ghost<Seq<int>>) -> (out: [u8; 8])
    requires
        forall|m: int| 0 <= m < 1024 ==> (#[trigger] rl[m]) == range_limit(m),
        y < 8,
        forall|j: int| 0 <= j < 8 ==> (#[trigger] ws[8 * y + j]) as int == idct_col(c, j, y as int),
    ensures
        forall|x: int| 0 <= x < 8 ==> (#[trigger] out[x]) == idct(c, y as int, x),
{
    hide(idct_1d);
    let ghost row = Seq::new(8, |j: int| idct_col(c, j, y as int));
    let w0 = ws[8 * y];
    let w1 = ws[8 * y + 1];
    let w2 = ws[8 * y + 2];
    let w3 = ws[8 * y + 3];
    let w4 = ws[8 * y + 4];
    let w5 = ws[8 * y + 5];
    let w6 = ws[8 * y + 6];
    let w7 = ws[8 * y + 7];
    if (w1 | w2 | w3 | w4 | w5 | w6 | w7) == 0 {
        assert(w1 == 0 && w2 == 0 && w3 == 0 && w4 == 0 && w5 == 0 && w6 == 0 && w7 == 0) by (bit_vector)
            requires
                (w1 | w2 | w3 | w4 | w5 | w6 | w7) == 0,
        ;
        let t0 = w0 as i64 + 16;
        let t = t0 >> 5;
        let v = range_limit_t(t, rl);
        proof {
            reveal(idct_1d);
            lemma_shr5(t0);
            lemma2_to64();
            assert(ws[8 * y + 0] as int == idct_col(c, 0, y as int));
            assert(row[0] == w0 && row[1] == w1 && row[2] == w2 && row[3] == w3 && row[4] == w4 && row[5] == w5 && row[6]
                == w6 && row[7] == w7);
            lemma_idct_dc(row);
            assert forall|k: int| 0 <= k < 8 implies v == idct(c, y as int, k) by {
                assert(idct_1d(row)[k] == w0 * 8192);
                assert((w0 * 8192 + 131072) / 262144 == (w0 + 16) / 32);
            }
        }
        return [v, v, v, v, v, v, v, v];
    }
    let r = idct_1d_x(w0 as i64, w1 as i64, w2 as i64, w3 as i64, w4 as i64, w5 as i64, w6 as i64, w7 as i64);
    proof {
        assert(ws[8 * y + 0] as int == idct_col(c, 0, y as int));
        assert(seq![
            ws[8 * y + 0] as int,
            ws[8 * y + 1] as int,
            ws[8 * y + 2] as int,
            ws[8 * y + 3] as int,
            ws[8 * y + 4] as int,
            ws[8 * y + 5] as int,
            ws[8 * y + 6] as int,
            ws[8 * y + 7] as int,
        ] =~= row);
    }
    let mut out = [0u8; 8];
    let mut x: usize = 0;
    while x < 8
        invariant
            x <= 8,
            y < 8,
            row == Seq::new(8, |j: int| idct_col(c, j, y as int)),
            forall|m: int| 0 <= m < 1024 ==> (#[trigger] rl[m]) == range_limit(m),
            forall|i: int| 0 <= i < 8 ==> (#[trigger] r[i]) as int == idct_1d(row)[i],
            forall|i: int| 0 <= i < 8 ==> -0x1000_0000_0000_0000 <= (#[trigger] r[i]) <= 0x1000_0000_0000_0000,
            forall|k: int| 0 <= k < x ==> (#[trigger] out[k]) == idct(c, y as int, k),
        decreases 8 - x,
    {
        let v = (r[x] + 131072) >> 18;
        proof {
            lemma_shr((r[x as int] + 131072) as i64, 18);
            lemma2_to64();
            assert(descale(idct_1d(row)[x as int], 18) == v);
        }
        out[x] = range_limit_t(v, rl);
        x += 1;
    }
    out
}

/// One pass in 32 bits over values small enough that nothing overflows.
#[inline(always)]
fn pass_b(x0: i32, x1: i32, x2: i32, x3: i32, x4: i32, x5: i32, x6: i32, x7: i32) -> (r: [i32; 8])
    requires
        -16384 <= x0 <= 16384,
        -16384 <= x1 <= 16384,
        -16384 <= x2 <= 16384,
        -16384 <= x3 <= 16384,
        -16384 <= x4 <= 16384,
        -16384 <= x5 <= 16384,
        -16384 <= x6 <= 16384,
        -16384 <= x7 <= 16384,
    ensures
        forall|i: int|
            0 <= i < 8 ==> (#[trigger] r[i]) as int == idct_1d(
                seq![x0 as int, x1 as int, x2 as int, x3 as int, x4 as int, x5 as int, x6 as int, x7 as int],
            )[i],
        forall|i: int| 0 <= i < 8 ==> -0x7000_0000 <= (#[trigger] r[i]) <= 0x7000_0000,
{
    hide(idct_1d);
    let g1 = x2 + x6;
    let g2 = g1 * 4433;
    let g3 = x6 * (-15137);
    let g4 = g2 + g3;
    let g5 = x2 * 6270;
    let g6 = g2 + g5;
    let g7 = x0 + x4;
    let g8 = g7 * 8192;
    let g9 = x0 - x4;
    let g10 = g9 * 8192;
    let g11 = g8 + g6;
    let g12 = g8 - g6;
    let g13 = g10 + g4;
    let g14 = g10 - g4;
    let g15 = x7 + x1;
    let g16 = x5 + x3;
    let g17 = x7 + x3;
    let g18 = x5 + x1;
    let g19 = g17 + g18;
    let g20 = g19 * 9633;
    let g21 = g15 * (-7373);
    let g22 = g16 * (-20995);
    let g23 = g17 * (-16069);
    let g24 = g23 + g20;
    let g25 = g18 * (-3196);
    let g26 = g25 + g20;
    let g27 = x7 * 2446;
    let g28 = g27 + g21;
    let g29 = g28 + g24;
    let g30 = x5 * 16819;
    let g31 = g30 + g22;
    let g32 = g31 + g26;
    let g33 = x3 * 25172;
    let g34 = g33 + g22;
    let g35 = g34 + g24;
    let g36 = x1 * 12299;
    let g37 = g36 + g21;
    let g38 = g37 + g26;
    let r = [g11 + g38, g13 + g35, g14 + g32, g12 + g29, g12 - g29, g14 - g32, g13 - g35, g11 - g38];
    proof {
        lemma_pass_link(x0 as int, x1 as int, x2 as int, x3 as int, x4 as int, x5 as int, x6 as int, x7 as int, g1 as int, g2 as int, g3 as int, g4 as int, g5 as int, g6 as int, g7 as int, g8 as int, g9 as int, g10 as int, g11 as int, g12 as int, g13 as int, g14 as int, g15 as int, g16 as int, g17 as int, g18 as int, g19 as int, g20 as int, g21 as int, g22 as int, g23 as int, g24 as int, g25 as int, g26 as int, g27 as int, g28 as int, g29 as int, g30 as int, g31 as int, g32 as int, g33 as int, g34 as int, g35 as int, g36 as int, g37 as int, g38 as int, r[0] as int, r[1] as int, r[2] as int, r[3] as int, r[4] as int, r[5] as int, r[6] as int, r[7] as int);
    }
    r
}

// BEGIN generated by scripts/gen_pass_w.py
/// The exact values of a pass, named one by one, are `idct_1d`'s.
pub proof fn lemma_pass_link(x0: int, x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, gv1: int, gv2: int, gv3: int, gv4: int, gv5: int, gv6: int, gv7: int, gv8: int, gv9: int, gv10: int, gv11: int, gv12: int, gv13: int, gv14: int, gv15: int, gv16: int, gv17: int, gv18: int, gv19: int, gv20: int, gv21: int, gv22: int, gv23: int, gv24: int, gv25: int, gv26: int, gv27: int, gv28: int, gv29: int, gv30: int, gv31: int, gv32: int, gv33: int, gv34: int, gv35: int, gv36: int, gv37: int, gv38: int, gv39: int, gv40: int, gv41: int, gv42: int, gv43: int, gv44: int, gv45: int, gv46: int)
    requires
        gv1 == x2 + x6,
        gv2 == gv1 * (4433),
        gv3 == x6 * (-15137),
        gv4 == gv2 + gv3,
        gv5 == x2 * (6270),
        gv6 == gv2 + gv5,
        gv7 == x0 + x4,
        gv8 == gv7 * (8192),
        gv9 == x0 - x4,
        gv10 == gv9 * (8192),
        gv11 == gv8 + gv6,
        gv12 == gv8 - gv6,
        gv13 == gv10 + gv4,
        gv14 == gv10 - gv4,
        gv15 == x7 + x1,
        gv16 == x5 + x3,
        gv17 == x7 + x3,
        gv18 == x5 + x1,
        gv19 == gv17 + gv18,
        gv20 == gv19 * (9633),
        gv21 == gv15 * (-7373),
        gv22 == gv16 * (-20995),
        gv23 == gv17 * (-16069),
        gv24 == gv23 + gv20,
        gv25 == gv18 * (-3196),
        gv26 == gv25 + gv20,
        gv27 == x7 * (2446),
        gv28 == gv27 + gv21,
        gv29 == gv28 + gv24,
        gv30 == x5 * (16819),
        gv31 == gv30 + gv22,
        gv32 == gv31 + gv26,
        gv33 == x3 * (25172),
        gv34 == gv33 + gv22,
        gv35 == gv34 + gv24,
        gv36 == x1 * (12299),
        gv37 == gv36 + gv21,
        gv38 == gv37 + gv26,
        gv39 == gv11 + gv38,
        gv40 == gv13 + gv35,
        gv41 == gv14 + gv32,
        gv42 == gv12 + gv29,
        gv43 == gv12 - gv29,
        gv44 == gv14 - gv32,
        gv45 == gv13 - gv35,
        gv46 == gv11 - gv38,
    ensures
        idct_1d(seq![x0, x1, x2, x3, x4, x5, x6, x7])[0] == gv39,
        idct_1d(seq![x0, x1, x2, x3, x4, x5, x6, x7])[1] == gv40,
        idct_1d(seq![x0, x1, x2, x3, x4, x5, x6, x7])[2] == gv41,
        idct_1d(seq![x0, x1, x2, x3, x4, x5, x6, x7])[3] == gv42,
        idct_1d(seq![x0, x1, x2, x3, x4, x5, x6, x7])[4] == gv43,
        idct_1d(seq![x0, x1, x2, x3, x4, x5, x6, x7])[5] == gv44,
        idct_1d(seq![x0, x1, x2, x3, x4, x5, x6, x7])[6] == gv45,
        idct_1d(seq![x0, x1, x2, x3, x4, x5, x6, x7])[7] == gv46,
{
}

/// One pass in wrapping 32-bit arithmetic: right modulo 2^32.
#[inline(always)]
fn pass_w(x0: i32, x1: i32, x2: i32, x3: i32, x4: i32, x5: i32, x6: i32, x7: i32) -> (r: (i32, i32, i32, i32, i32, i32, i32, i32))
    ensures
        cong(r.0 as int, idct_1d(seq![x0 as int, x1 as int, x2 as int, x3 as int, x4 as int, x5 as int, x6 as int, x7 as int])[0]),
        cong(r.1 as int, idct_1d(seq![x0 as int, x1 as int, x2 as int, x3 as int, x4 as int, x5 as int, x6 as int, x7 as int])[1]),
        cong(r.2 as int, idct_1d(seq![x0 as int, x1 as int, x2 as int, x3 as int, x4 as int, x5 as int, x6 as int, x7 as int])[2]),
        cong(r.3 as int, idct_1d(seq![x0 as int, x1 as int, x2 as int, x3 as int, x4 as int, x5 as int, x6 as int, x7 as int])[3]),
        cong(r.4 as int, idct_1d(seq![x0 as int, x1 as int, x2 as int, x3 as int, x4 as int, x5 as int, x6 as int, x7 as int])[4]),
        cong(r.5 as int, idct_1d(seq![x0 as int, x1 as int, x2 as int, x3 as int, x4 as int, x5 as int, x6 as int, x7 as int])[5]),
        cong(r.6 as int, idct_1d(seq![x0 as int, x1 as int, x2 as int, x3 as int, x4 as int, x5 as int, x6 as int, x7 as int])[6]),
        cong(r.7 as int, idct_1d(seq![x0 as int, x1 as int, x2 as int, x3 as int, x4 as int, x5 as int, x6 as int, x7 as int])[7]),
{
    hide(idct_1d);
    hide(cong);
    let v1 = wadd(x2, x6);
    let ghost gv1: int = (x2 as int) + (x6 as int);
    let ghost ev1: int = 0int + 0int - wq(x2 + x6);
    assert(v1 == gv1 + 0x1_0000_0000 * ev1);
    let v2 = wmul(v1, 4433);
    let ghost gv2: int = gv1 * (4433);
    let ghost ev2: int = ev1 * (4433) - wq(v1 * (4433));
    assert(v2 == gv2 + 0x1_0000_0000 * ev2);
    let v3 = wmul(x6, -15137);
    let ghost gv3: int = (x6 as int) * (-15137);
    let ghost ev3: int = 0int * (-15137) - wq(x6 * (-15137));
    assert(v3 == gv3 + 0x1_0000_0000 * ev3);
    let v4 = wadd(v2, v3);
    let ghost gv4: int = gv2 + gv3;
    let ghost ev4: int = ev2 + ev3 - wq(v2 + v3);
    assert(v4 == gv4 + 0x1_0000_0000 * ev4);
    let v5 = wmul(x2, 6270);
    let ghost gv5: int = (x2 as int) * (6270);
    let ghost ev5: int = 0int * (6270) - wq(x2 * (6270));
    assert(v5 == gv5 + 0x1_0000_0000 * ev5);
    let v6 = wadd(v2, v5);
    let ghost gv6: int = gv2 + gv5;
    let ghost ev6: int = ev2 + ev5 - wq(v2 + v5);
    assert(v6 == gv6 + 0x1_0000_0000 * ev6);
    let v7 = wadd(x0, x4);
    let ghost gv7: int = (x0 as int) + (x4 as int);
    let ghost ev7: int = 0int + 0int - wq(x0 + x4);
    assert(v7 == gv7 + 0x1_0000_0000 * ev7);
    let v8 = wmul(v7, 8192);
    let ghost gv8: int = gv7 * (8192);
    let ghost ev8: int = ev7 * (8192) - wq(v7 * (8192));
    assert(v8 == gv8 + 0x1_0000_0000 * ev8);
    let v9 = wsub(x0, x4);
    let ghost gv9: int = (x0 as int) - (x4 as int);
    let ghost ev9: int = 0int - 0int - wq(x0 - x4);
    assert(v9 == gv9 + 0x1_0000_0000 * ev9);
    let v10 = wmul(v9, 8192);
    let ghost gv10: int = gv9 * (8192);
    let ghost ev10: int = ev9 * (8192) - wq(v9 * (8192));
    assert(v10 == gv10 + 0x1_0000_0000 * ev10);
    let v11 = wadd(v8, v6);
    let ghost gv11: int = gv8 + gv6;
    let ghost ev11: int = ev8 + ev6 - wq(v8 + v6);
    assert(v11 == gv11 + 0x1_0000_0000 * ev11);
    let v12 = wsub(v8, v6);
    let ghost gv12: int = gv8 - gv6;
    let ghost ev12: int = ev8 - ev6 - wq(v8 - v6);
    assert(v12 == gv12 + 0x1_0000_0000 * ev12);
    let v13 = wadd(v10, v4);
    let ghost gv13: int = gv10 + gv4;
    let ghost ev13: int = ev10 + ev4 - wq(v10 + v4);
    assert(v13 == gv13 + 0x1_0000_0000 * ev13);
    let v14 = wsub(v10, v4);
    let ghost gv14: int = gv10 - gv4;
    let ghost ev14: int = ev10 - ev4 - wq(v10 - v4);
    assert(v14 == gv14 + 0x1_0000_0000 * ev14);
    let v15 = wadd(x7, x1);
    let ghost gv15: int = (x7 as int) + (x1 as int);
    let ghost ev15: int = 0int + 0int - wq(x7 + x1);
    assert(v15 == gv15 + 0x1_0000_0000 * ev15);
    let v16 = wadd(x5, x3);
    let ghost gv16: int = (x5 as int) + (x3 as int);
    let ghost ev16: int = 0int + 0int - wq(x5 + x3);
    assert(v16 == gv16 + 0x1_0000_0000 * ev16);
    let v17 = wadd(x7, x3);
    let ghost gv17: int = (x7 as int) + (x3 as int);
    let ghost ev17: int = 0int + 0int - wq(x7 + x3);
    assert(v17 == gv17 + 0x1_0000_0000 * ev17);
    let v18 = wadd(x5, x1);
    let ghost gv18: int = (x5 as int) + (x1 as int);
    let ghost ev18: int = 0int + 0int - wq(x5 + x1);
    assert(v18 == gv18 + 0x1_0000_0000 * ev18);
    let v19 = wadd(v17, v18);
    let ghost gv19: int = gv17 + gv18;
    let ghost ev19: int = ev17 + ev18 - wq(v17 + v18);
    assert(v19 == gv19 + 0x1_0000_0000 * ev19);
    let v20 = wmul(v19, 9633);
    let ghost gv20: int = gv19 * (9633);
    let ghost ev20: int = ev19 * (9633) - wq(v19 * (9633));
    assert(v20 == gv20 + 0x1_0000_0000 * ev20);
    let v21 = wmul(v15, -7373);
    let ghost gv21: int = gv15 * (-7373);
    let ghost ev21: int = ev15 * (-7373) - wq(v15 * (-7373));
    assert(v21 == gv21 + 0x1_0000_0000 * ev21);
    let v22 = wmul(v16, -20995);
    let ghost gv22: int = gv16 * (-20995);
    let ghost ev22: int = ev16 * (-20995) - wq(v16 * (-20995));
    assert(v22 == gv22 + 0x1_0000_0000 * ev22);
    let v23 = wmul(v17, -16069);
    let ghost gv23: int = gv17 * (-16069);
    let ghost ev23: int = ev17 * (-16069) - wq(v17 * (-16069));
    assert(v23 == gv23 + 0x1_0000_0000 * ev23);
    let v24 = wadd(v23, v20);
    let ghost gv24: int = gv23 + gv20;
    let ghost ev24: int = ev23 + ev20 - wq(v23 + v20);
    assert(v24 == gv24 + 0x1_0000_0000 * ev24);
    let v25 = wmul(v18, -3196);
    let ghost gv25: int = gv18 * (-3196);
    let ghost ev25: int = ev18 * (-3196) - wq(v18 * (-3196));
    assert(v25 == gv25 + 0x1_0000_0000 * ev25);
    let v26 = wadd(v25, v20);
    let ghost gv26: int = gv25 + gv20;
    let ghost ev26: int = ev25 + ev20 - wq(v25 + v20);
    assert(v26 == gv26 + 0x1_0000_0000 * ev26);
    let v27 = wmul(x7, 2446);
    let ghost gv27: int = (x7 as int) * (2446);
    let ghost ev27: int = 0int * (2446) - wq(x7 * (2446));
    assert(v27 == gv27 + 0x1_0000_0000 * ev27);
    let v28 = wadd(v27, v21);
    let ghost gv28: int = gv27 + gv21;
    let ghost ev28: int = ev27 + ev21 - wq(v27 + v21);
    assert(v28 == gv28 + 0x1_0000_0000 * ev28);
    let v29 = wadd(v28, v24);
    let ghost gv29: int = gv28 + gv24;
    let ghost ev29: int = ev28 + ev24 - wq(v28 + v24);
    assert(v29 == gv29 + 0x1_0000_0000 * ev29);
    let v30 = wmul(x5, 16819);
    let ghost gv30: int = (x5 as int) * (16819);
    let ghost ev30: int = 0int * (16819) - wq(x5 * (16819));
    assert(v30 == gv30 + 0x1_0000_0000 * ev30);
    let v31 = wadd(v30, v22);
    let ghost gv31: int = gv30 + gv22;
    let ghost ev31: int = ev30 + ev22 - wq(v30 + v22);
    assert(v31 == gv31 + 0x1_0000_0000 * ev31);
    let v32 = wadd(v31, v26);
    let ghost gv32: int = gv31 + gv26;
    let ghost ev32: int = ev31 + ev26 - wq(v31 + v26);
    assert(v32 == gv32 + 0x1_0000_0000 * ev32);
    let v33 = wmul(x3, 25172);
    let ghost gv33: int = (x3 as int) * (25172);
    let ghost ev33: int = 0int * (25172) - wq(x3 * (25172));
    assert(v33 == gv33 + 0x1_0000_0000 * ev33);
    let v34 = wadd(v33, v22);
    let ghost gv34: int = gv33 + gv22;
    let ghost ev34: int = ev33 + ev22 - wq(v33 + v22);
    assert(v34 == gv34 + 0x1_0000_0000 * ev34);
    let v35 = wadd(v34, v24);
    let ghost gv35: int = gv34 + gv24;
    let ghost ev35: int = ev34 + ev24 - wq(v34 + v24);
    assert(v35 == gv35 + 0x1_0000_0000 * ev35);
    let v36 = wmul(x1, 12299);
    let ghost gv36: int = (x1 as int) * (12299);
    let ghost ev36: int = 0int * (12299) - wq(x1 * (12299));
    assert(v36 == gv36 + 0x1_0000_0000 * ev36);
    let v37 = wadd(v36, v21);
    let ghost gv37: int = gv36 + gv21;
    let ghost ev37: int = ev36 + ev21 - wq(v36 + v21);
    assert(v37 == gv37 + 0x1_0000_0000 * ev37);
    let v38 = wadd(v37, v26);
    let ghost gv38: int = gv37 + gv26;
    let ghost ev38: int = ev37 + ev26 - wq(v37 + v26);
    assert(v38 == gv38 + 0x1_0000_0000 * ev38);
    let v39 = wadd(v11, v38);
    let ghost gv39: int = gv11 + gv38;
    let ghost ev39: int = ev11 + ev38 - wq(v11 + v38);
    assert(v39 == gv39 + 0x1_0000_0000 * ev39);
    let v40 = wadd(v13, v35);
    let ghost gv40: int = gv13 + gv35;
    let ghost ev40: int = ev13 + ev35 - wq(v13 + v35);
    assert(v40 == gv40 + 0x1_0000_0000 * ev40);
    let v41 = wadd(v14, v32);
    let ghost gv41: int = gv14 + gv32;
    let ghost ev41: int = ev14 + ev32 - wq(v14 + v32);
    assert(v41 == gv41 + 0x1_0000_0000 * ev41);
    let v42 = wadd(v12, v29);
    let ghost gv42: int = gv12 + gv29;
    let ghost ev42: int = ev12 + ev29 - wq(v12 + v29);
    assert(v42 == gv42 + 0x1_0000_0000 * ev42);
    let v43 = wsub(v12, v29);
    let ghost gv43: int = gv12 - gv29;
    let ghost ev43: int = ev12 - ev29 - wq(v12 - v29);
    assert(v43 == gv43 + 0x1_0000_0000 * ev43);
    let v44 = wsub(v14, v32);
    let ghost gv44: int = gv14 - gv32;
    let ghost ev44: int = ev14 - ev32 - wq(v14 - v32);
    assert(v44 == gv44 + 0x1_0000_0000 * ev44);
    let v45 = wsub(v13, v35);
    let ghost gv45: int = gv13 - gv35;
    let ghost ev45: int = ev13 - ev35 - wq(v13 - v35);
    assert(v45 == gv45 + 0x1_0000_0000 * ev45);
    let v46 = wsub(v11, v38);
    let ghost gv46: int = gv11 - gv38;
    let ghost ev46: int = ev11 - ev38 - wq(v11 - v38);
    assert(v46 == gv46 + 0x1_0000_0000 * ev46);
    proof {
        lemma_pass_link(x0 as int, x1 as int, x2 as int, x3 as int, x4 as int, x5 as int, x6 as int, x7 as int, gv1, gv2, gv3, gv4, gv5, gv6, gv7, gv8, gv9, gv10, gv11, gv12, gv13, gv14, gv15, gv16, gv17, gv18, gv19, gv20, gv21, gv22, gv23, gv24, gv25, gv26, gv27, gv28, gv29, gv30, gv31, gv32, gv33, gv34, gv35, gv36, gv37, gv38, gv39, gv40, gv41, gv42, gv43, gv44, gv45, gv46);
        lemma_cong_k(v39 as int, gv39, ev39);
        lemma_cong_k(v40 as int, gv40, ev40);
        lemma_cong_k(v41 as int, gv41, ev41);
        lemma_cong_k(v42 as int, gv42, ev42);
        lemma_cong_k(v43 as int, gv43, ev43);
        lemma_cong_k(v44 as int, gv44, ev44);
        lemma_cong_k(v45 as int, gv45, ev45);
        lemma_cong_k(v46 as int, gv46, ev46);
    }
    (v39, v40, v41, v42, v43, v44, v45, v46)
}
// END generated

/// The first pass's final shift, of a value the pass computed exactly.
#[inline(always)]
fn ds11(v: i32) -> (r: i32)
    requires
        -0x7000_0000 <= v <= 0x7000_0000,
    ensures
        r as int == wrap32(descale(v as int, 11)),
{
    proof {
        lemma_shr11((v + 1024) as i32);
        lemma2_to64();
    }
    (v + 1024) >> 11
}

/// The second pass's final shift and range limit. The limit looks at ten
/// bits only, and those are right even though `v` is only right modulo
/// 2^32.
#[inline(always)]
fn fin(v: i32, Ghost(t): Ghost<int>) -> (r: u8)
    requires
        cong(v as int, t),
    ensures
        r == range_limit(descale(t, 18)),
{
    let u = wadd(v, 131072);
    let m = (u >> 18) & 1023;
    proof {
        lemma_bits18(u);
        lemma2_to64();
        lemma_fundamental_div_mod(v - t, 0x1_0000_0000);
        let k = (v - t) / 0x1_0000_0000 - wq(v + 131072);
        lemma_cong_bits(u as int, t + 131072, k);
        assert(m as int == descale(t, 18) % 1024);
        lemma_mod_twice(descale(t, 18), 1024);
    }
    range_limit_x(m as i64)
}

/// Row `y` of the workspace after the first pass.
pub open spec fn rowv(c: Seq<int>, y: int) -> Seq<int> {
    Seq::new(8, |j: int| idct_col(c, j, y))
}

/// The second pass's result at (`y`, `x`).
pub open spec fn osp(c: Seq<int>, y: int, x: int) -> u8 {
    range_limit(descale(idct_1d(rowv(c, y))[x], 18))
}

/// The dequantized block at `o`, and whether every value in it is small
/// enough for the 32-bit transform.
#[inline(never)]
fn deq_all(a: &Vec<i16>, o: usize, q: &[u16; 64]) -> (r: ([i32; 64], bool))
    requires
        o + 64 <= a.len(),
    ensures
        forall|k: int| 0 <= k < 64 ==> (#[trigger] r.0[k]) as int == dequant(a@, o as int, q@)[k],
        r.1 ==> forall|k: int| 0 <= k < 64 ==> -16384 <= (#[trigger] r.0[k]) <= 16384,
{
    let mut d = [0i32; 64];
    let mut bad: i32 = 0;
    let mut k: usize = 0;
    while k < 64
        invariant
            k <= 64,
            o + 64 <= a.len(),
            forall|j: int| 0 <= j < k ==> (#[trigger] d[j]) as int == dequant(a@, o as int, q@)[j],
            bad == 0 ==> forall|j: int| 0 <= j < k ==> -16384 <= (#[trigger] d[j]) <= 16384,
        decreases 64 - k,
    {
        proof {
            lemma_sx16(q[k as int]);
        }
        let x = vget(a, o + k) as i32;
        let y = (q[k] as i16) as i32;
        assert(-0x4000_0000 <= x * y <= 0x4000_0000) by (nonlinear_arith)
            requires
                -0x8000 <= x <= 0x7fff,
                -0x8000 <= y <= 0x7fff,
        ;
        let v = x * y;
        d[k] = v;
        let w = v + 16384;
        let t = w & -32768;
        assert((t == 0) <==> (0 <= w < 32768)) by (bit_vector)
            requires
                t == w & -32768i32,
        ;
        let nb = bad | t;
        assert((nb == 0) <==> (bad == 0 && t == 0)) by (bit_vector)
            requires
                nb == bad | t,
        ;
        bad = nb;
        k += 1;
    }
    (d, bad == 0)
}

/// The transform of a block of small values, in 32-bit arithmetic with no
/// branches, a column (then a row) at a time across all eight, so that
/// compilers turn each pass into vector code.
#[inline(never)]
fn idct_fast(d: &[i32; 64], Ghost(c): Ghost<Seq<int>>) -> (out: [u8; 64])
    requires
        c.len() == 64,
        forall|k: int| 0 <= k < 64 ==> (#[trigger] d[k]) as int == c[k] && -16384 <= d[k] <= 16384,
    ensures
        forall|k: int| 0 <= k < 64 ==> (#[trigger] out[k]) == idct(c, k / 8, k % 8),
{
    hide(idct_1d);
    hide(range_limit);
    hide(descale);
    // First pass: column `x` of the block to column `x` of `ws`.
    let mut ws = [0i32; 64];
    let mut x: usize = 0;
    while x < 8
        invariant
            x <= 8,
            c.len() == 64,
            forall|k: int| 0 <= k < 64 ==> (#[trigger] d[k]) as int == c[k] && -16384 <= d[k] <= 16384,
            forall|k: int| 0 <= k < 64 && k % 8 < x ==> (#[trigger] ws[k]) as int == idct_col(c, k % 8, k / 8),
        decreases 8 - x,
    {
        let ghost col = Seq::new(8, |i: int| c[8 * i + x]);
        let ghost ws0 = ws;
        proof {
            assert(d[x as int] as int == c[8 * 0 + x]);
            assert(d[8 + x as int] as int == c[8 * 1 + x]);
            assert(d[16 + x as int] as int == c[8 * 2 + x]);
            assert(d[24 + x as int] as int == c[8 * 3 + x]);
            assert(d[32 + x as int] as int == c[8 * 4 + x]);
            assert(d[40 + x as int] as int == c[8 * 5 + x]);
            assert(d[48 + x as int] as int == c[8 * 6 + x]);
            assert(d[56 + x as int] as int == c[8 * 7 + x]);
        }
        let r = pass_b(d[x], d[8 + x], d[16 + x], d[24 + x], d[32 + x], d[40 + x], d[48 + x], d[56 + x]);
        proof {
            assert(seq![
                d[x as int] as int,
                d[8 + x as int] as int,
                d[16 + x as int] as int,
                d[24 + x as int] as int,
                d[32 + x as int] as int,
                d[40 + x as int] as int,
                d[48 + x as int] as int,
                d[56 + x as int] as int,
            ] =~= col);
        }
        ws[x] = ds11(r[0]);
        ws[8 + x] = ds11(r[1]);
        ws[16 + x] = ds11(r[2]);
        ws[24 + x] = ds11(r[3]);
        ws[32 + x] = ds11(r[4]);
        ws[40 + x] = ds11(r[5]);
        ws[48 + x] = ds11(r[6]);
        ws[56 + x] = ds11(r[7]);
        proof {
            assert forall|k: int| 0 <= k < 64 && k % 8 < x + 1 implies (#[trigger] ws[k]) as int == idct_col(
                c,
                k % 8,
                k / 8,
            ) by {
                if k % 8 == x {
                    let y = k / 8;
                    assert(k == 8 * y + x);
                    assert(ws[k] as int == wrap32(descale(idct_1d(col)[y], 11)));
                } else {
                    assert(ws[k] == ws0[k]);
                }
            }
        }
        x += 1;
    }
    // Transposed, so that the second pass too runs across eight at a time.
    let mut wt = [0i32; 64];
    let mut i: usize = 0;
    while i < 8
        invariant
            i <= 8,
            forall|j: int| 0 <= j < 64 && j / 8 < i ==> (#[trigger] wt[j]) == ws[8 * (j % 8) + j / 8],
        decreases 8 - i,
    {
        wt[8 * i] = ws[i];
        wt[8 * i + 1] = ws[8 + i];
        wt[8 * i + 2] = ws[16 + i];
        wt[8 * i + 3] = ws[24 + i];
        wt[8 * i + 4] = ws[32 + i];
        wt[8 * i + 5] = ws[40 + i];
        wt[8 * i + 6] = ws[48 + i];
        wt[8 * i + 7] = ws[56 + i];
        i += 1;
    }
    // Second pass: row `y` of the workspace to column `y` of `ot`.
    let mut ot = [0u8; 64];
    let mut y: usize = 0;
    while y < 8
        invariant
            y <= 8,
            forall|j: int| 0 <= j < 64 ==> (#[trigger] wt[j]) == ws[8 * (j % 8) + j / 8],
            forall|k: int| 0 <= k < 64 ==> (#[trigger] ws[k]) as int == idct_col(c, k % 8, k / 8),
            forall|k: int| 0 <= k < 64 && k % 8 < y ==> (#[trigger] ot[k]) == osp(c, k % 8, k / 8),
        decreases 8 - y,
    {
        let ghost row = rowv(c, y as int);
        let ghost ot0 = ot;
        proof {
            assert forall|j: int| 0 <= j < 8 implies (#[trigger] wt[8 * j + y]) as int == row[j] by {
                assert((8 * j + y) % 8 == y && (8 * j + y) / 8 == j);
                assert(wt[8 * j + y] == ws[8 * y + j]);
                assert((8 * y + j) % 8 == j && (8 * y + j) / 8 == y);
            }
            assert(wt[y as int] as int == row[0]) by {
                assert(wt[8 * 0 + y] as int == row[0]);
            }
            assert(wt[8 + y as int] as int == row[1]) by {
                assert(wt[8 * 1 + y] as int == row[1]);
            }
            assert(wt[16 + y as int] as int == row[2]) by {
                assert(wt[8 * 2 + y] as int == row[2]);
            }
            assert(wt[24 + y as int] as int == row[3]) by {
                assert(wt[8 * 3 + y] as int == row[3]);
            }
            assert(wt[32 + y as int] as int == row[4]) by {
                assert(wt[8 * 4 + y] as int == row[4]);
            }
            assert(wt[40 + y as int] as int == row[5]) by {
                assert(wt[8 * 5 + y] as int == row[5]);
            }
            assert(wt[48 + y as int] as int == row[6]) by {
                assert(wt[8 * 6 + y] as int == row[6]);
            }
            assert(wt[56 + y as int] as int == row[7]) by {
                assert(wt[8 * 7 + y] as int == row[7]);
            }
        }
        let r = pass_w(wt[y], wt[8 + y], wt[16 + y], wt[24 + y], wt[32 + y], wt[40 + y], wt[48 + y], wt[56 + y]);
        proof {
            assert(seq![
                wt[y as int] as int,
                wt[8 + y as int] as int,
                wt[16 + y as int] as int,
                wt[24 + y as int] as int,
                wt[32 + y as int] as int,
                wt[40 + y as int] as int,
                wt[48 + y as int] as int,
                wt[56 + y as int] as int,
            ] =~= row);
        }
        ot[y] = fin(r.0, Ghost(idct_1d(row)[0]));
        ot[8 + y] = fin(r.1, Ghost(idct_1d(row)[1]));
        ot[16 + y] = fin(r.2, Ghost(idct_1d(row)[2]));
        ot[24 + y] = fin(r.3, Ghost(idct_1d(row)[3]));
        ot[32 + y] = fin(r.4, Ghost(idct_1d(row)[4]));
        ot[40 + y] = fin(r.5, Ghost(idct_1d(row)[5]));
        ot[48 + y] = fin(r.6, Ghost(idct_1d(row)[6]));
        ot[56 + y] = fin(r.7, Ghost(idct_1d(row)[7]));
        proof {
            assert forall|k: int| 0 <= k < 64 && k % 8 < y + 1 implies (#[trigger] ot[k]) == osp(c, k % 8, k / 8) by {
                if k % 8 == y {
                    let xx = k / 8;
                    assert(k == 8 * xx + y);
                    assert(ot[k] == range_limit(descale(idct_1d(row)[xx], 18)));
                } else {
                    assert(ot[k] == ot0[k]);
                }
            }
        }
        y += 1;
    }
    // Transposed back.
    let mut out = [0u8; 64];
    let mut i: usize = 0;
    while i < 8
        invariant
            i <= 8,
            c.len() == 64,
            forall|j: int| 0 <= j < 64 ==> (#[trigger] ot[j]) == osp(c, j % 8, j / 8),
            forall|j: int| 0 <= j < 64 && j / 8 < i ==> (#[trigger] out[j]) == idct(c, j / 8, j % 8),
        decreases 8 - i,
    {
        let ghost out0 = out;
        out[8 * i] = ot[i];
        out[8 * i + 1] = ot[8 + i];
        out[8 * i + 2] = ot[16 + i];
        out[8 * i + 3] = ot[24 + i];
        out[8 * i + 4] = ot[32 + i];
        out[8 * i + 5] = ot[40 + i];
        out[8 * i + 6] = ot[48 + i];
        out[8 * i + 7] = ot[56 + i];
        proof {
            assert forall|j: int| 0 <= j < 64 && j / 8 < i + 1 implies (#[trigger] out[j]) == idct(c, j / 8, j % 8) by {
                if j / 8 == i {
                    let n = j % 8;
                    assert(j == 8 * i + n);
                    assert(out[j] == ot[8 * n + i]);
                    assert((8 * n + i) % 8 == i && (8 * n + i) / 8 == n);
                    assert(out[j] == osp(c, i as int, n));
                    reveal(idct_1d);
                    assert(idct(c, i as int, n) == osp(c, i as int, n));
                } else {
                    assert(out[j] == out0[j]);
                }
            }
        }
        i += 1;
    }
    out
}

/// Whether every coefficient of the block at `o` but the first is zero.
#[inline(never)]
fn ac_zero(a: &[i16], o: usize) -> (r: bool)
    requires
        o + 64 <= a@.len(),
    ensures
        r ==> forall|j: int| o + 1 <= j < o + 64 ==> a@[j] == 0,
{
    let n = a.len();
    let mut acc: i16 = 0;
    let mut k: usize = 1;
    while k < 64
        invariant
            1 <= k <= 64,
            n == a@.len(),
            o + 64 <= n,
            acc == 0 ==> forall|j: int| o + 1 <= j < o + k ==> a@[j] == 0,
        decreases 64 - k,
    {
        let x = sget(a, o + k);
        let na = acc | x;
        assert((na == 0) <==> (acc == 0 && x == 0)) by (bit_vector)
            requires
                na == acc | x,
        ;
        acc = na;
        k += 1;
    }
    acc == 0
}

/// A block that is zero but for a small first value: every sample is the
/// same.
proof fn lemma_dc_block(c: Seq<int>, y: int, x: int)
    requires
        c.len() == 64,
        forall|k: int| 1 <= k < 64 ==> c[k] == 0,
        0 <= y < 8,
        0 <= x < 8,
    ensures
        idct(c, y, x) == range_limit(descale(wrap32(descale(c[0] * 8192, 11)) * 8192, 18)),
{
    let w0 = wrap32(descale(c[0] * 8192, 11));
    let row = Seq::new(8, |j: int| idct_col(c, j, y));
    assert forall|j: int| 0 <= j < 8 implies #[trigger] row[j] == if j == 0 {
        w0
    } else {
        0
    } by {
        let col = Seq::new(8, |i: int| c[8 * i + j]);
        assert forall|i: int| 1 <= i < 8 implies col[i] == 0 by {
            assert(c[8 * i + j] == 0);
        }
        lemma_idct_dc(col);
        assert(idct_1d(col)[y] == col[0] * 8192);
        assert(col[0] == c[j]);
        if j != 0 {
            assert(c[j] == 0);
            lemma2_to64();
            assert(descale(0, 11) == 0) by {
                assert(pow2(10) == 1024 && pow2(11) == 2048);
            }
        }
    }
    lemma_idct_dc(row);
    assert(idct_1d(row)[x] == row[0] * 8192);
}

/// The transform of a block that is zero but for a small first value.
fn idct_dc(d0: i32, Ghost(c): Ghost<Seq<int>>) -> (out: [u8; 64])
    requires
        c.len() == 64,
        c[0] == d0,
        -16384 <= d0 <= 16384,
        forall|k: int| 1 <= k < 64 ==> c[k] == 0,
    ensures
        forall|k: int| 0 <= k < 64 ==> (#[trigger] out[k]) == idct(c, k / 8, k % 8),
{
    let w0 = ds11(d0 * 8192);
    proof {
        lemma2_to64();
        assert(-65537 <= w0 <= 65537) by {
            lemma_shr11((d0 * 8192 + 1024) as i32);
        }
    }
    let t = w0 * 8192;
    proof {
        assert(cong(t as int, t as int)) by {
            reveal(cong);
        }
    }
    let v = fin(t, Ghost(t as int));
    let mut out = [0u8; 64];
    let mut k: usize = 0;
    while k < 64
        invariant
            k <= 64,
            forall|j: int| 0 <= j < k ==> (#[trigger] out[j]) == v,
        decreases 64 - k,
    {
        out[k] = v;
        k += 1;
    }
    proof {
        assert forall|k: int| 0 <= k < 64 implies (#[trigger] out[k]) == idct(c, k / 8, k % 8) by {
            lemma_dc_block(c, k / 8, k % 8);
        }
    }
    out
}

/// The block of coefficients at `o`, dequantized by `q` and transformed,
/// written as the 8 by 8 block at row `row0`, column `col0` of the plane.
/// With NEON, a block that has AC coefficients goes straight to the NEON
/// transform, which stores into the plane; `idct_slow` has every other
/// case. The ghost result is the block that was written.
#[inline(always)]
pub fn idct_into(out: &mut Vec<u8>, a: &Vec<i16>, o: usize, q: &[u16; 64], rl: &[u8; 1024], kt: &[i16; 24], row0: usize, col0: usize, stride: usize) -> (blk: Ghost<Seq<u8>>)
    requires
        kt@ == crate::idct16::kt_spec(),
        forall|m: int| 0 <= m < 1024 ==> (#[trigger] rl[m]) == range_limit(m),
        o + 64 <= a.len(),
        col0 + 8 <= stride,
        (row0 + 8) * stride <= old(out).len(),
    ensures
        final(out).len() == old(out).len(),
        blk@.len() == 64,
        forall|k: int| 0 <= k < 64 ==> (#[trigger] blk@[k]) == idct(dequant(a@, o as int, q@), k / 8, k % 8),
        forall|j: int|
            0 <= j < final(out).len() ==> (#[trigger] final(out)[j]) == if row0 <= j / (stride as int) < row0 + 8 && col0
                <= j % (stride as int) < col0 + 8 {
                blk@[8 * (j / (stride as int) - row0) + (j % (stride as int) - col0)]
            } else {
                old(out)[j]
            },
{
    if verilith_simd::neon::has_neon() {
        let r = crate::idct16::idct16_neon(a.as_slice(), o, q, kt, out.as_mut_slice(), row0, col0, stride);
        if r.0 == 0 {
            return r.1;
        }
        if r.0 == 2 {
            let r = crate::idct_neon::idct_neon(a.as_slice(), o, q, out.as_mut_slice(), row0, col0, stride);
            if r.0 {
                return r.1;
            }
        }
    }
    let b = idct_slow(a, o, q, rl);
    store_block(out, &b, row0, col0, stride);
    Ghost(b@)
}

/// The block of coefficients at `o`, dequantized by `q` and transformed:
/// 8 rows of 8 samples.
#[cold]
#[inline(never)]
fn idct_slow(a: &Vec<i16>, o: usize, q: &[u16; 64], rl: &[u8; 1024]) -> (out: [u8; 64])
    requires
        forall|m: int| 0 <= m < 1024 ==> (#[trigger] rl[m]) == range_limit(m),
        o + 64 <= a.len(),
    ensures
        forall|k: int| 0 <= k < 64 ==> (#[trigger] out[k]) == idct(dequant(a@, o as int, q@), k / 8, k % 8),
{
    hide(idct_1d);
    hide(idct_col);
    hide(idct);
    let ghost c = dequant(a@, o as int, q@);
    if ac_zero(a.as_slice(), o) {
        proof {
            lemma_sx16(q[0]);
        }
        let x0 = vget(a, o) as i32;
        let y0 = (q[0] as i16) as i32;
        assert(-0x4000_0000 <= x0 * y0 <= 0x4000_0000) by (nonlinear_arith)
            requires
                -0x8000 <= x0 <= 0x7fff,
                -0x8000 <= y0 <= 0x7fff,
        ;
        let d0 = x0 * y0;
        if -16384 <= d0 && d0 <= 16384 {
            proof {
                reveal(dequant);
                assert forall|k: int| 1 <= k < 64 implies c[k] == 0 by {
                    assert(a@[o + k] == 0);
                }
                assert(c[0] == d0);
            }
            return idct_dc(d0, Ghost(c));
        }
    }
    let (d, small) = deq_all(a, o, q);
    if small {
        return idct_fast(&d, Ghost(c));
    }
    // A corrupt file can hold values too large for that: 64-bit arithmetic.
    let mut ws = [0i32; 64];
    let mut x: usize = 0;
    while x < 8
        invariant
            x <= 8,
            o + 64 <= a.len(),
            c == dequant(a@, o as int, q@),
            forall|k: int| 0 <= k < 64 && k % 8 < x ==> (#[trigger] ws[k]) as int == idct_col(c, k % 8, k / 8),
        decreases 8 - x,
    {
        let r = col_x(a, o, q, x);
        let mut y: usize = 0;
        while y < 8
            invariant
                y <= 8,
                x < 8,
                forall|i: int| 0 <= i < 8 ==> (#[trigger] r[i]) as int == idct_col(c, x as int, i),
                forall|k: int| 0 <= k < 64 && k % 8 < x ==> (#[trigger] ws[k]) as int == idct_col(c, k % 8, k / 8),
                forall|k: int|
                    0 <= k < 64 && k % 8 == x && k / 8 < y ==> (#[trigger] ws[k]) as int == idct_col(c, k % 8, k / 8),
            decreases 8 - y,
        {
            ws[8 * y + x] = r[y];
            y += 1;
        }
        x += 1;
    }
    let mut out = [0u8; 64];
    let mut y: usize = 0;
    while y < 8
        invariant
            y <= 8,
            forall|m: int| 0 <= m < 1024 ==> (#[trigger] rl[m]) == range_limit(m),
            forall|k: int| 0 <= k < 64 ==> (#[trigger] ws[k]) as int == idct_col(c, k % 8, k / 8),
            forall|k: int| 0 <= k < 64 && k / 8 < y ==> (#[trigger] out[k]) == idct(c, k / 8, k % 8),
        decreases 8 - y,
    {
        proof {
            assert forall|j: int| 0 <= j < 8 implies (#[trigger] ws[8 * y + j]) as int == idct_col(c, j, y as int) by {
                assert((8 * y + j) % 8 == j && (8 * y + j) / 8 == y);
            }
        }
        let r = row_x(&ws, y, rl, Ghost(c));
        let mut x: usize = 0;
        while x < 8
            invariant
                x <= 8,
                y < 8,
                forall|i: int| 0 <= i < 8 ==> (#[trigger] r[i]) == idct(c, y as int, i),
                forall|k: int| 0 <= k < 64 && k / 8 < y ==> (#[trigger] out[k]) == idct(c, k / 8, k % 8),
                forall|k: int| 0 <= k < 64 && k / 8 == y && k % 8 < x ==> (#[trigger] out[k]) == idct(c, k / 8, k % 8),
            decreases 8 - x,
        {
            out[8 * y + x] = r[x];
            x += 1;
        }
        y += 1;
    }
    out
}

/// Sample (`r`, `x`) of a component with coefficients `a`, `cw` blocks to
/// a row, and quantization table `q`.
pub open spec fn psample(a: Seq<i16>, q: Seq<u16>, cw: int, r: int, x: int) -> u8 {
    idct(dequant(a, 64 * ((r / 8) * cw + x / 8), q), r % 8, x % 8)
}

/// The value at row `r`, column `x` of a plane `stride` wide.
pub open spec fn pat(pl: Seq<u8>, stride: int, r: int, x: int) -> u8 {
    pl[r * stride + x]
}

/// Storing block (`by`, `bx`) extends the part of the plane that holds its
/// samples by that block.
pub proof fn lemma_block_stored(o0: Seq<u8>, o1: Seq<u8>, blk: Seq<u8>, a: Seq<i16>, q: Seq<u16>, cw: int, st: int, by: int, bx: int)
    requires
        0 <= by,
        0 <= bx,
        8 * bx + 8 <= st,
        o1.len() == o0.len(),
        blk.len() == 64,
        forall|j: int|
            0 <= j < o0.len() && (j / st < 8 * by || (j / st < 8 * by + 8 && j % st < 8 * bx)) ==> (#[trigger] o0[j])
                == psample(a, q, cw, j / st, j % st),
        forall|j: int|
            0 <= j < o1.len() ==> (#[trigger] o1[j]) == if 8 * by <= j / st < 8 * by + 8 && 8 * bx <= j % st < 8 * bx + 8 {
                blk[8 * (j / st - 8 * by) + (j % st - 8 * bx)]
            } else {
                o0[j]
            },
        forall|k: int| 0 <= k < 64 ==> (#[trigger] blk[k]) == idct(dequant(a, 64 * (by * cw + bx), q), k / 8, k % 8),
    ensures
        forall|j: int|
            0 <= j < o1.len() && (j / st < 8 * by || (j / st < 8 * by + 8 && j % st < 8 * (bx + 1))) ==> (#[trigger] o1[j])
                == psample(a, q, cw, j / st, j % st),
{
    hide(idct);
    hide(dequant);
    assert forall|j: int|
        0 <= j < o1.len() && (j / st < 8 * by || (j / st < 8 * by + 8 && j % st < 8 * (bx + 1))) implies (#[trigger] o1[j])
        == psample(a, q, cw, j / st, j % st) by {
        lemma_mod_bound(j, st);
        let rr = j / st;
        let x = j % st;
        if 8 * by <= rr < 8 * by + 8 && 8 * bx <= x < 8 * bx + 8 {
            let k = 8 * (rr - 8 * by) + (x - 8 * bx);
            assert(o1[j] == blk[k]);
            assert(k / 8 == rr - 8 * by && k % 8 == x - 8 * bx);
            assert(rr / 8 == by && x / 8 == bx && rr % 8 == rr - 8 * by && x % 8 == x - 8 * bx);
        } else {
            assert(o1[j] == o0[j]);
        }
    }
}

/// Writes the 8 by 8 block `blk` at row `row0`, column `col0` of the
/// plane.
pub fn store_block(out: &mut Vec<u8>, blk: &[u8; 64], row0: usize, col0: usize, stride: usize)
    requires
        col0 + 8 <= stride,
        (row0 + 8) * stride <= old(out).len(),
    ensures
        final(out).len() == old(out).len(),
        forall|j: int|
            0 <= j < final(out).len() ==> (#[trigger] final(out)[j]) == if row0 <= j / (stride as int) < row0 + 8 && col0
                <= j % (stride as int) < col0 + 8 {
                blk[8 * (j / (stride as int) - row0) + (j % (stride as int) - col0)]
            } else {
                old(out)[j]
            },
{
    let ghost st = stride as int;
    let mut y: usize = 0;
    while y < 8
        invariant
            y <= 8,
            st == stride,
            col0 + 8 <= stride,
            (row0 + 8) * stride <= out.len(),
            out.len() == old(out).len(),
            forall|j: int|
                0 <= j < out.len() ==> (#[trigger] out[j]) == if row0 <= j / st < row0 + y && col0 <= j % st < col0 + 8 {
                    blk[8 * (j / st - row0) + (j % st - col0)]
                } else {
                    old(out)[j]
                },
        decreases 8 - y,
    {
        assert(0 <= (row0 + y) * stride && (row0 + y) * stride + stride <= (row0 + 8) * stride) by (nonlinear_arith)
            requires
                y < 8,
                stride >= 0,
        ;
        assert(row0 + 8 <= (row0 + 8) * stride) by (nonlinear_arith)
            requires
                stride >= 1,
        ;
        let base = (row0 + y) * stride + col0;
        let mut x: usize = 0;
        while x < 8
            invariant
                x <= 8,
                y < 8,
                st == stride,
                col0 + 8 <= stride,
                base == (row0 + y) * stride + col0,
                base + 8 <= out.len(),
                out.len() == old(out).len(),
                forall|j: int|
                    0 <= j < out.len() ==> (#[trigger] out[j]) == if (row0 <= j / st < row0 + y && col0 <= j % st < col0
                        + 8) || (j / st == row0 + y && col0 <= j % st < col0 + x) {
                        blk[8 * (j / st - row0) + (j % st - col0)]
                    } else {
                        old(out)[j]
                    },
            decreases 8 - x,
        {
            let ghost prev = out@;
            vset(out, base + x, blk[8 * y + x]);
            proof {
                lemma_fundamental_div_mod_converse(base + x, st, row0 + y, col0 + x);
                assert((row0 + y) * st == st * (row0 + y)) by (nonlinear_arith);
                assert forall|j: int| 0 <= j < out.len() implies (#[trigger] out[j]) == if (row0 <= j / st < row0 + y && col0
                    <= j % st < col0 + 8) || (j / st == row0 + y && col0 <= j % st < col0 + (x + 1)) {
                    blk[8 * (j / st - row0) + (j % st - col0)]
                } else {
                    old(out)[j]
                } by {
                    lemma_fundamental_div_mod(j, st);
                    if j != base + x {
                        assert(out[j] == prev[j]);
                    }
                }
            }
            x += 1;
        }
        y += 1;
    }
}

/// The samples of a component: `8 * wb` by `8 * hb`, from its `wb` by `hb`
/// blocks that hold image data.
#[inline(never)]
pub fn plane_x(a: &Vec<i16>, q: &[u16; 64], kt: &[i16; 24], cw: u32, wb: u32, hb: u32, Ghost(chh): Ghost<int>, Tracked(mt): Tracked<&mut Meter>) -> (r: Option<Vec<u8>>)
    requires
        1 <= wb <= cw <= 0x4_0080,
        1 <= hb <= chh <= 0x4_0080,
        a.len() == 64 * (cw * chh),
        kt@ == crate::idct16::kt_spec(),
    ensures
        final(mt).n <= old(mt).n + 66 * (cw * chh),
        r matches Some(pl) ==> {
            &&& pl.len() == (8 * wb) * (8 * hb)
            &&& forall|rr: int, x: int|
                0 <= rr < 8 * hb && 0 <= x < 8 * wb ==> #[trigger] pat(pl@, 8 * wb, rr, x) == psample(a@, q@, cw as int, rr, x)
        },
{
    hide(idct);
    hide(dequant);
    hide(range_limit);
    let stride = 8 * wb as usize;
    let ghost st = stride as int;
    assert((stride as u64) * 8 * (hb as u64) <= 0x20_0400 * 0x20_0400 && (stride as u64) * 8 * (hb as u64) == (8 * wb) * (8
        * hb)) by (nonlinear_arith)
        requires
            stride == 8 * wb,
            wb <= 0x4_0080,
            hb <= 0x4_0080,
    ;
    let n = (stride as u64) * 8 * (hb as u64);
    if n > usize::MAX as u64 {
        return None;
    }
    assert(n + hb * (wb + 1) <= 66 * (cw * chh)) by (nonlinear_arith)
        requires
            n == stride * 8 * hb,
            stride == 8 * wb,
            1 <= wb <= cw,
            1 <= hb <= chh,
    ;
    proof {
        mt.n = mt.n + n as nat;
    }
    let ghost m1 = mt.n;
    let mut out = match alloc_u8(n as usize) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    let rl = range_table();
    let mut by: usize = 0;
    while by < hb as usize
        invariant
            forall|m: int| 0 <= m < 1024 ==> (#[trigger] rl[m]) == range_limit(m),
            kt@ == crate::idct16::kt_spec(),
            by <= hb,
            mt.n <= m1 + by * (wb + 1),
            st == stride == 8 * wb,
            1 <= wb <= cw <= 0x4_0080,
            1 <= hb <= chh <= 0x4_0080,
            a.len() == 64 * (cw * chh),
            out.len() == st * (8 * hb),
            forall|j: int|
                0 <= j < out.len() && j / st < 8 * by ==> (#[trigger] out[j]) == psample(a@, q@, cw as int, j / st, j % st),
        decreases hb - by,
    {
        let ghost m2 = mt.n;
        let mut bx: usize = 0;
        while bx < wb as usize
            invariant
                mt.n <= m2 + bx,
                forall|m: int| 0 <= m < 1024 ==> (#[trigger] rl[m]) == range_limit(m),
                kt@ == crate::idct16::kt_spec(),
                bx <= wb,
                by < hb,
                st == stride == 8 * wb,
                1 <= wb <= cw <= 0x4_0080,
                1 <= hb <= chh <= 0x4_0080,
                a.len() == 64 * (cw * chh),
                out.len() == st * (8 * hb),
                forall|j: int|
                    0 <= j < out.len() && (j / st < 8 * by || (j / st < 8 * by + 8 && j % st < 8 * bx)) ==> (
                    #[trigger] out[j]) == psample(a@, q@, cw as int, j / st, j % st),
            decreases wb - bx,
        {
            proof {
                lemma_grid(by as int, bx as int, chh, cw as int);
                assert((8 * by + 8) * st <= st * (8 * hb)) by (nonlinear_arith)
                    requires
                        by < hb,
                        st >= 0,
                ;
            }
            let o = 64 * (by * cw as usize + bx);
            let ghost out0 = out;
            let blk = idct_into(&mut out, a, o, q, &rl, kt, 8 * by, 8 * bx, stride);
            proof {
                lemma_block_stored(out0@, out@, blk@, a@, q@, cw as int, st, by as int, bx as int);
            }
            bx += 1;
            proof {
                mt.n = mt.n + 1;
            }
        }
        proof {
            assert forall|j: int| 0 <= j < out.len() && j / st < 8 * (by + 1) implies (#[trigger] out[j]) == psample(
                a@,
                q@,
                cw as int,
                j / st,
                j % st,
            ) by {
                lemma_mod_bound(j, st);
            }
        }
        by += 1;
        proof {
            mt.n = mt.n + 1;
            assert(by * (wb + 1) == (by - 1) * (wb + 1) + wb + 1) by (nonlinear_arith);
        }
    }

    proof {
        assert forall|rr: int, x: int| 0 <= rr < 8 * hb && 0 <= x < 8 * wb implies #[trigger] pat(out@, 8 * wb, rr, x)
            == psample(a@, q@, cw as int, rr, x) by {
            lemma_grid(rr, x, 8 * hb, st);
            lemma_fundamental_div_mod_converse(rr * st + x, st, rr, x);
        }
    }
    Some(out)
}

} // verus!

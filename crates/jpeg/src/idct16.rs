//! The inverse DCT on NEON over 16-bit rows, as libjpeg-turbo's NEON code
//! does it: for the blocks an encoder makes, whose values are small enough
//! that the first pass's results fit 16 bits. Each pass multiplies 16-bit
//! lanes by constants held in the lanes of a table (`smull`, `smlal`), the
//! first narrows back to 16 bits, and the second saturates straight to
//! samples. A guard on the sum of the dequantized magnitudes proves both;
//! a block that fails it goes to `idct_neon`'s 32-bit transform.
use crate::idct::*;
use crate::idct_neon::*;
use crate::num::*;
use crate::spec::*;
#[cfg(verus_only)]
use verilith_simd::lanes::*;
use verilith_simd::neon::*;
#[cfg(verus_only)]
use verilith_simd::ops::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

broadcast use verilith_simd::neon::group_neon;

/// 16-bit lane `i` of a vector, read as signed.
pub open spec fn s16l(v: uint8x16_t, i: int) -> int {
    s16(u16s(n8(v))[i])
}

/// Every 16-bit lane of `v` is `t`'s value exactly.
pub open spec fn x16(v: uint8x16_t, t: Seq<int>) -> bool {
    t.len() == 8 && forall|i: int| 0 <= i < 8 ==> #[trigger] s16l(v, i) == t[i]
}

pub open spec fn vsum(a: Seq<int>, b: Seq<int>) -> Seq<int> {
    Seq::new(8, |i: int| a[i] + b[i])
}

pub open spec fn vdif(a: Seq<int>, b: Seq<int>) -> Seq<int> {
    Seq::new(8, |i: int| a[i] - b[i])
}

/// Eight exact values, all zero.
pub open spec fn zero8(t: Seq<int>) -> bool {
    t.len() == 8 && forall|i: int| 0 <= i < 8 ==> #[trigger] t[i] == 0
}

/// Eight exact values of magnitude at most `b`.
pub open spec fn in8(t: Seq<int>, b: int) -> bool {
    t.len() == 8 && forall|i: int| 0 <= i < 8 ==> -b <= #[trigger] t[i] <= b
}

/// Every 32-bit lane of `v` is output `k` of a pass over lane `off + i` of
/// the inputs, modulo 2^32.
pub open spec fn pc16(v: uint8x16_t, t0: Seq<int>, t1: Seq<int>, t2: Seq<int>, t3: Seq<int>, t4: Seq<int>, t5: Seq<int>, t6: Seq<int>, t7: Seq<int>, off: int, k: int) -> bool {
    forall|i: int| 0 <= i < 4 ==> cong(#[trigger] l32(v, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, off + i))[k])
}

/// `s` is `acc + a * c` modulo 2^32.
#[verifier::opaque]
pub open spec fn rmla(s: int, acc: int, a: int, c: int) -> bool {
    s == (acc + a * c) % 0x1_0000_0000
}

// ---------------------------------------------------------------------------
// The constants
// ---------------------------------------------------------------------------

/// The multipliers of the pass, three vectors of eight 16-bit lanes. They
/// are read from memory, not written as immediates, so that each multiply
/// names one lane of a register.
pub open spec fn kt_spec() -> Seq<i16> {
    seq![
        4433i16, (-10704i16), 10703i16, 8192i16, (-6436i16), 9633i16, 6437i16, (-4927i16),
        (-7373i16), (-4176i16), (-20995i16), 4177i16, 4926i16, 2260i16, (-11362i16), (-2259i16),
        11363i16, 0i16, 0i16, 0i16, 0i16, 0i16, 0i16, 0i16,
    ]
}

pub fn idct_consts() -> (t: [i16; 24])
    ensures
        t@ == kt_spec(),
{
    let t: [i16; 24] = [
        4433, -10704, 10703, 8192, -6436, 9633, 6437, -4927,
        -7373, -4176, -20995, 4177, 4926, 2260, -11362, -2259,
        11363, 0, 0, 0, 0, 0, 0, 0,
    ];
    assert(t@ =~= kt_spec());
    t
}

/// The three vectors hold the table.
pub open spec fn kok(k0: uint8x16_t, k1: uint8x16_t, k2: uint8x16_t) -> bool {
    &&& s16l(k0, 0) == 4433 && s16l(k0, 1) == -10704 && s16l(k0, 2) == 10703 && s16l(k0, 3) == 8192
    &&& s16l(k0, 4) == -6436 && s16l(k0, 5) == 9633 && s16l(k0, 6) == 6437 && s16l(k0, 7) == -4927
    &&& s16l(k1, 0) == -7373 && s16l(k1, 1) == -4176 && s16l(k1, 2) == -20995 && s16l(k1, 3) == 4177
    &&& s16l(k1, 4) == 4926 && s16l(k1, 5) == 2260 && s16l(k1, 6) == -11362 && s16l(k1, 7) == -2259
    &&& s16l(k2, 0) == 11363
}

/// A 16-bit value read back as signed is the value.
proof fn lemma_s16_cast(x: i16, u: u16)
    requires
        u == x as u16,
    ensures
        s16(u) == x as int,
{
    assert(u as int == if x < 0 {
        x as int + 0x10000
    } else {
        x as int
    }) by (bit_vector)
        requires
            u == x as u16,
    ;
}

#[inline(always)]
fn kload(kt: &[i16; 24]) -> (k: (uint8x16_t, uint8x16_t, uint8x16_t))
    requires
        neon(),
        kt@ == kt_spec(),
    ensures
        kok(k.0, k.1, k.2),
{
    let s: &[i16] = kt;
    let k0 = vld1q_s16_at(s, 0);
    let k1 = vld1q_s16_at(s, 8);
    let k2 = vld1q_s16_at(s, 16);
    proof {
        assert forall|i: int| 0 <= i < 8 implies #[trigger] s16l(k0, i) == kt@[i] as int by {
            assert(s@.subrange(0, 8)[i] == kt@[i]);
            lemma_s16_cast(kt@[i], u16s(n8(k0))[i]);
        }
        assert forall|i: int| 0 <= i < 8 implies #[trigger] s16l(k1, i) == kt@[8 + i] as int by {
            assert(s@.subrange(8, 16)[i] == kt@[8 + i]);
            lemma_s16_cast(kt@[8 + i], u16s(n8(k1))[i]);
        }
        assert forall|i: int| 0 <= i < 8 implies #[trigger] s16l(k2, i) == kt@[16 + i] as int by {
            assert(s@.subrange(16, 24)[i] == kt@[16 + i]);
            lemma_s16_cast(kt@[16 + i], u16s(n8(k2))[i]);
        }
        assert(s16l(k0, 0) == kt@[0] && s16l(k0, 1) == kt@[1] && s16l(k0, 2) == kt@[2] && s16l(k0, 3) == kt@[3]);
        assert(s16l(k0, 4) == kt@[4] && s16l(k0, 5) == kt@[5] && s16l(k0, 6) == kt@[6] && s16l(k0, 7) == kt@[7]);
        assert(s16l(k1, 0) == kt@[8] && s16l(k1, 1) == kt@[9] && s16l(k1, 2) == kt@[10] && s16l(k1, 3) == kt@[11]);
        assert(s16l(k1, 4) == kt@[12] && s16l(k1, 5) == kt@[13] && s16l(k1, 6) == kt@[14] && s16l(k1, 7) == kt@[15]);
        assert(s16l(k2, 0) == kt@[16]);
    }
    (k0, k1, k2)
}

// ---------------------------------------------------------------------------
// The widening multiplies
// ---------------------------------------------------------------------------

/// The low four lanes of `a` times lane `L` of `k`.
#[inline(always)]
fn mlo<const L: i32>(a: uint8x16_t, k: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        forall|i: int| 0 <= i < 4 ==> rmul(#[trigger] l32(r, i), s16l(a, i), s16l(k, L as int)),
{
    reveal(rmul);
    vmull_lo_laneq_s16::<L>(a, k)
}

/// The high four lanes of `a` times lane `L` of `k`.
#[inline(always)]
fn mhi<const L: i32>(a: uint8x16_t, k: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        forall|i: int| 0 <= i < 4 ==> rmul(#[trigger] l32(r, i), s16l(a, 4 + i), s16l(k, L as int)),
{
    reveal(rmul);
    vmull_hi_laneq_s16::<L>(a, k)
}

/// `acc` plus the low four lanes of `a` times lane `L` of `k`.
#[inline(always)]
fn alo<const L: i32>(acc: uint8x16_t, a: uint8x16_t, k: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        forall|i: int| 0 <= i < 4 ==> rmla(#[trigger] l32(r, i), l32(acc, i), s16l(a, i), s16l(k, L as int)),
{
    reveal(rmla);
    vmlal_lo_laneq_s16::<L>(acc, a, k)
}

/// `acc` plus the high four lanes of `a` times lane `L` of `k`.
#[inline(always)]
fn ahi<const L: i32>(acc: uint8x16_t, a: uint8x16_t, k: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        forall|i: int| 0 <= i < 4 ==> rmla(#[trigger] l32(r, i), l32(acc, i), s16l(a, 4 + i), s16l(k, L as int)),
{
    reveal(rmla);
    vmlal_hi_laneq_s16::<L>(acc, a, k)
}

// BEGIN generated by scripts/gen_idct16.py
/// One lane of `vp16_lo` and `vp16_hi`: the lane values `s1`..`s30`, each made
/// from earlier ones modulo 2^32, end congruent to `idct_1d` of the exact
/// inputs.
#[verifier::rlimit(60)]
#[verifier::spinoff_prover]
proof fn lemma_vp16_lane(t0: int, t1: int, t2: int, t3: int, t4: int, t5: int, t6: int, t7: int, s1: int, s2: int, s3: int, s4: int, s5: int, s6: int, s7: int, s8: int, s9: int, s10: int, s11: int, s12: int, s13: int, s14: int, s15: int, s16: int, s17: int, s18: int, s19: int, s20: int, s21: int, s22: int, s23: int, s24: int, s25: int, s26: int, s27: int, s28: int, s29: int, s30: int)
    requires
        rmul(s1, t2, 4433),
        rmla(s2, s1, t6, -10704),
        rmul(s3, t2, 10703),
        rmla(s4, s3, t6, 4433),
        rmul(s5, (t0 + t4), 8192),
        rmul(s6, (t0 - t4), 8192),
        radd(s7, s5, s4),
        rsub(s8, s5, s4),
        radd(s9, s6, s2),
        rsub(s10, s6, s2),
        rmul(s11, (t7 + t3), -6436),
        rmla(s12, s11, (t5 + t1), 9633),
        rmul(s13, (t7 + t3), 9633),
        rmla(s14, s13, (t5 + t1), 6437),
        rmla(s15, s12, t7, -4927),
        rmla(s16, s15, t1, -7373),
        rmla(s17, s14, t5, -4176),
        rmla(s18, s17, t3, -20995),
        rmla(s19, s12, t3, 4177),
        rmla(s20, s19, t5, -20995),
        rmla(s21, s14, t1, 4926),
        rmla(s22, s21, t7, -7373),
        radd(s23, s7, s22),
        radd(s24, s9, s20),
        radd(s25, s10, s18),
        radd(s26, s8, s16),
        rsub(s27, s8, s16),
        rsub(s28, s10, s18),
        rsub(s29, s9, s20),
        rsub(s30, s7, s22),
    ensures
        cong(s23, idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[0]),
        cong(s24, idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[1]),
        cong(s25, idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[2]),
        cong(s26, idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[3]),
        cong(s27, idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[4]),
        cong(s28, idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[5]),
        cong(s29, idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[6]),
        cong(s30, idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[7]),
{
    hide(idct_1d);
    reveal(radd);
    reveal(rsub);
    reveal(rmul);
    reveal(rmla);
    let g1 = t2 * (4433);
    let e1 = -((t2 * (4433)) / 0x1_0000_0000);
    assert(s1 == g1 + 0x1_0000_0000 * e1);
    let g2 = g1 + t6 * (-10704);
    let e2 = e1 - (s1 + t6 * (-10704)) / 0x1_0000_0000;
    assert(s2 == g2 + 0x1_0000_0000 * e2);
    let g3 = t2 * (10703);
    let e3 = -((t2 * (10703)) / 0x1_0000_0000);
    assert(s3 == g3 + 0x1_0000_0000 * e3);
    let g4 = g3 + t6 * (4433);
    let e4 = e3 - (s3 + t6 * (4433)) / 0x1_0000_0000;
    assert(s4 == g4 + 0x1_0000_0000 * e4);
    let g5 = (t0 + t4) * (8192);
    let e5 = -(((t0 + t4) * (8192)) / 0x1_0000_0000);
    assert(s5 == g5 + 0x1_0000_0000 * e5);
    let g6 = (t0 - t4) * (8192);
    let e6 = -(((t0 - t4) * (8192)) / 0x1_0000_0000);
    assert(s6 == g6 + 0x1_0000_0000 * e6);
    let g7 = g5 + g4;
    let e7 = e5 + e4 - (s5 + s4) / 0x1_0000_0000;
    assert(s7 == g7 + 0x1_0000_0000 * e7);
    let g8 = g5 - g4;
    let e8 = e5 - e4 + 1 - (s5 - s4 + 0x1_0000_0000) / 0x1_0000_0000;
    assert(s8 == g8 + 0x1_0000_0000 * e8);
    let g9 = g6 + g2;
    let e9 = e6 + e2 - (s6 + s2) / 0x1_0000_0000;
    assert(s9 == g9 + 0x1_0000_0000 * e9);
    let g10 = g6 - g2;
    let e10 = e6 - e2 + 1 - (s6 - s2 + 0x1_0000_0000) / 0x1_0000_0000;
    assert(s10 == g10 + 0x1_0000_0000 * e10);
    let g11 = (t7 + t3) * (-6436);
    let e11 = -(((t7 + t3) * (-6436)) / 0x1_0000_0000);
    assert(s11 == g11 + 0x1_0000_0000 * e11);
    let g12 = g11 + (t5 + t1) * (9633);
    let e12 = e11 - (s11 + (t5 + t1) * (9633)) / 0x1_0000_0000;
    assert(s12 == g12 + 0x1_0000_0000 * e12);
    let g13 = (t7 + t3) * (9633);
    let e13 = -(((t7 + t3) * (9633)) / 0x1_0000_0000);
    assert(s13 == g13 + 0x1_0000_0000 * e13);
    let g14 = g13 + (t5 + t1) * (6437);
    let e14 = e13 - (s13 + (t5 + t1) * (6437)) / 0x1_0000_0000;
    assert(s14 == g14 + 0x1_0000_0000 * e14);
    let g15 = g12 + t7 * (-4927);
    let e15 = e12 - (s12 + t7 * (-4927)) / 0x1_0000_0000;
    assert(s15 == g15 + 0x1_0000_0000 * e15);
    let g16 = g15 + t1 * (-7373);
    let e16 = e15 - (s15 + t1 * (-7373)) / 0x1_0000_0000;
    assert(s16 == g16 + 0x1_0000_0000 * e16);
    let g17 = g14 + t5 * (-4176);
    let e17 = e14 - (s14 + t5 * (-4176)) / 0x1_0000_0000;
    assert(s17 == g17 + 0x1_0000_0000 * e17);
    let g18 = g17 + t3 * (-20995);
    let e18 = e17 - (s17 + t3 * (-20995)) / 0x1_0000_0000;
    assert(s18 == g18 + 0x1_0000_0000 * e18);
    let g19 = g12 + t3 * (4177);
    let e19 = e12 - (s12 + t3 * (4177)) / 0x1_0000_0000;
    assert(s19 == g19 + 0x1_0000_0000 * e19);
    let g20 = g19 + t5 * (-20995);
    let e20 = e19 - (s19 + t5 * (-20995)) / 0x1_0000_0000;
    assert(s20 == g20 + 0x1_0000_0000 * e20);
    let g21 = g14 + t1 * (4926);
    let e21 = e14 - (s14 + t1 * (4926)) / 0x1_0000_0000;
    assert(s21 == g21 + 0x1_0000_0000 * e21);
    let g22 = g21 + t7 * (-7373);
    let e22 = e21 - (s21 + t7 * (-7373)) / 0x1_0000_0000;
    assert(s22 == g22 + 0x1_0000_0000 * e22);
    let g23 = g7 + g22;
    let e23 = e7 + e22 - (s7 + s22) / 0x1_0000_0000;
    assert(s23 == g23 + 0x1_0000_0000 * e23);
    let g24 = g9 + g20;
    let e24 = e9 + e20 - (s9 + s20) / 0x1_0000_0000;
    assert(s24 == g24 + 0x1_0000_0000 * e24);
    let g25 = g10 + g18;
    let e25 = e10 + e18 - (s10 + s18) / 0x1_0000_0000;
    assert(s25 == g25 + 0x1_0000_0000 * e25);
    let g26 = g8 + g16;
    let e26 = e8 + e16 - (s8 + s16) / 0x1_0000_0000;
    assert(s26 == g26 + 0x1_0000_0000 * e26);
    let g27 = g8 - g16;
    let e27 = e8 - e16 + 1 - (s8 - s16 + 0x1_0000_0000) / 0x1_0000_0000;
    assert(s27 == g27 + 0x1_0000_0000 * e27);
    let g28 = g10 - g18;
    let e28 = e10 - e18 + 1 - (s10 - s18 + 0x1_0000_0000) / 0x1_0000_0000;
    assert(s28 == g28 + 0x1_0000_0000 * e28);
    let g29 = g9 - g20;
    let e29 = e9 - e20 + 1 - (s9 - s20 + 0x1_0000_0000) / 0x1_0000_0000;
    assert(s29 == g29 + 0x1_0000_0000 * e29);
    let g30 = g7 - g22;
    let e30 = e7 - e22 + 1 - (s7 - s22 + 0x1_0000_0000) / 0x1_0000_0000;
    assert(s30 == g30 + 0x1_0000_0000 * e30);
    let c1 = t2 + t6;
    let c2 = c1 * (4433);
    let c3 = t6 * (-15137);
    let c4 = c2 + c3;
    let c5 = t2 * (6270);
    let c6 = c2 + c5;
    let c7 = t0 + t4;
    let c8 = c7 * (8192);
    let c9 = t0 - t4;
    let c10 = c9 * (8192);
    let c11 = c8 + c6;
    let c12 = c8 - c6;
    let c13 = c10 + c4;
    let c14 = c10 - c4;
    let c15 = t7 + t1;
    let c16 = t5 + t3;
    let c17 = t7 + t3;
    let c18 = t5 + t1;
    let c19 = c17 + c18;
    let c20 = c19 * (9633);
    let c21 = c15 * (-7373);
    let c22 = c16 * (-20995);
    let c23 = c17 * (-16069);
    let c24 = c23 + c20;
    let c25 = c18 * (-3196);
    let c26 = c25 + c20;
    let c27 = t7 * (2446);
    let c28 = c27 + c21;
    let c29 = c28 + c24;
    let c30 = t5 * (16819);
    let c31 = c30 + c22;
    let c32 = c31 + c26;
    let c33 = t3 * (25172);
    let c34 = c33 + c22;
    let c35 = c34 + c24;
    let c36 = t1 * (12299);
    let c37 = c36 + c21;
    let c38 = c37 + c26;
    let c39 = c11 + c38;
    let c40 = c13 + c35;
    let c41 = c14 + c32;
    let c42 = c12 + c29;
    let c43 = c12 - c29;
    let c44 = c14 - c32;
    let c45 = c13 - c35;
    let c46 = c11 - c38;
    lemma_pass_link(t0, t1, t2, t3, t4, t5, t6, t7, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46);
    assert(g23 == c39);
    lemma_cong_k(s23, g23, e23);
    assert(g24 == c40);
    lemma_cong_k(s24, g24, e24);
    assert(g25 == c41);
    lemma_cong_k(s25, g25, e25);
    assert(g26 == c42);
    lemma_cong_k(s26, g26, e26);
    assert(g27 == c43);
    lemma_cong_k(s27, g27, e27);
    assert(g28 == c44);
    lemma_cong_k(s28, g28, e28);
    assert(g29 == c45);
    lemma_cong_k(s29, g29, e29);
    assert(g30 == c46);
    lemma_cong_k(s30, g30, e30);
}

/// One pass over the low four columns of 16-bit rows: each
/// result is right modulo 2^32, lane by lane.
#[inline(always)]
fn vp16_lo(x0: uint8x16_t, x1: uint8x16_t, x2: uint8x16_t, x3: uint8x16_t, x4: uint8x16_t, x5: uint8x16_t, x6: uint8x16_t, x7: uint8x16_t, pe: uint8x16_t, pd: uint8x16_t, pz3: uint8x16_t, pz4: uint8x16_t, k0: uint8x16_t, k1: uint8x16_t, k2: uint8x16_t, Ghost(t0): Ghost<Seq<int>>, Ghost(t1): Ghost<Seq<int>>, Ghost(t2): Ghost<Seq<int>>, Ghost(t3): Ghost<Seq<int>>, Ghost(t4): Ghost<Seq<int>>, Ghost(t5): Ghost<Seq<int>>, Ghost(t6): Ghost<Seq<int>>, Ghost(t7): Ghost<Seq<int>>) -> (r: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t))
    requires
        neon(),
        x16(x0, t0),
        x16(x1, t1),
        x16(x2, t2),
        x16(x3, t3),
        x16(x4, t4),
        x16(x5, t5),
        x16(x6, t6),
        x16(x7, t7),
        x16(pe, vsum(t0, t4)),
        x16(pd, vdif(t0, t4)),
        x16(pz3, vsum(t7, t3)),
        x16(pz4, vsum(t5, t1)),
        kok(k0, k1, k2),
    ensures
        pc16(r.0, t0, t1, t2, t3, t4, t5, t6, t7, 0, 0),
        pc16(r.1, t0, t1, t2, t3, t4, t5, t6, t7, 0, 1),
        pc16(r.2, t0, t1, t2, t3, t4, t5, t6, t7, 0, 2),
        pc16(r.3, t0, t1, t2, t3, t4, t5, t6, t7, 0, 3),
        pc16(r.4, t0, t1, t2, t3, t4, t5, t6, t7, 0, 4),
        pc16(r.5, t0, t1, t2, t3, t4, t5, t6, t7, 0, 5),
        pc16(r.6, t0, t1, t2, t3, t4, t5, t6, t7, 0, 6),
        pc16(r.7, t0, t1, t2, t3, t4, t5, t6, t7, 0, 7),
{
    hide(idct_1d);
    hide(cong);
    hide(l32);
    let v1 = mlo::<0>(x2, k0);
    let v2 = alo::<1>(v1, x6, k0);
    let v3 = mlo::<2>(x2, k0);
    let v4 = alo::<0>(v3, x6, k0);
    let v5 = mlo::<3>(pe, k0);
    let v6 = mlo::<3>(pd, k0);
    let v7 = vadd(v5, v4);
    let v8 = vsub(v5, v4);
    let v9 = vadd(v6, v2);
    let v10 = vsub(v6, v2);
    let v11 = mlo::<4>(pz3, k0);
    let v12 = alo::<5>(v11, pz4, k0);
    let v13 = mlo::<5>(pz3, k0);
    let v14 = alo::<6>(v13, pz4, k0);
    let v15 = alo::<7>(v12, x7, k0);
    let v16 = alo::<0>(v15, x1, k1);
    let v17 = alo::<1>(v14, x5, k1);
    let v18 = alo::<2>(v17, x3, k1);
    let v19 = alo::<3>(v12, x3, k1);
    let v20 = alo::<2>(v19, x5, k1);
    let v21 = alo::<4>(v14, x1, k1);
    let v22 = alo::<0>(v21, x7, k1);
    let v23 = vadd(v7, v22);
    let v24 = vadd(v9, v20);
    let v25 = vadd(v10, v18);
    let v26 = vadd(v8, v16);
    let v27 = vsub(v8, v16);
    let v28 = vsub(v10, v18);
    let v29 = vsub(v9, v20);
    let v30 = vsub(v7, v22);
    proof {
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v23, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[0]) by {
            assert(vsum(t0, t4)[0 + i] == t0[0 + i] + t4[0 + i] && vdif(t0, t4)[0 + i] == t0[0 + i] - t4[0 + i]);
            assert(vsum(t7, t3)[0 + i] == t7[0 + i] + t3[0 + i] && vsum(t5, t1)[0 + i] == t5[0 + i] + t1[0 + i]);
            lemma_vp16_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], t4[0 + i], t5[0 + i], t6[0 + i], t7[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v24, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[1]) by {
            assert(vsum(t0, t4)[0 + i] == t0[0 + i] + t4[0 + i] && vdif(t0, t4)[0 + i] == t0[0 + i] - t4[0 + i]);
            assert(vsum(t7, t3)[0 + i] == t7[0 + i] + t3[0 + i] && vsum(t5, t1)[0 + i] == t5[0 + i] + t1[0 + i]);
            lemma_vp16_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], t4[0 + i], t5[0 + i], t6[0 + i], t7[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v25, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[2]) by {
            assert(vsum(t0, t4)[0 + i] == t0[0 + i] + t4[0 + i] && vdif(t0, t4)[0 + i] == t0[0 + i] - t4[0 + i]);
            assert(vsum(t7, t3)[0 + i] == t7[0 + i] + t3[0 + i] && vsum(t5, t1)[0 + i] == t5[0 + i] + t1[0 + i]);
            lemma_vp16_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], t4[0 + i], t5[0 + i], t6[0 + i], t7[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v26, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[3]) by {
            assert(vsum(t0, t4)[0 + i] == t0[0 + i] + t4[0 + i] && vdif(t0, t4)[0 + i] == t0[0 + i] - t4[0 + i]);
            assert(vsum(t7, t3)[0 + i] == t7[0 + i] + t3[0 + i] && vsum(t5, t1)[0 + i] == t5[0 + i] + t1[0 + i]);
            lemma_vp16_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], t4[0 + i], t5[0 + i], t6[0 + i], t7[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v27, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[4]) by {
            assert(vsum(t0, t4)[0 + i] == t0[0 + i] + t4[0 + i] && vdif(t0, t4)[0 + i] == t0[0 + i] - t4[0 + i]);
            assert(vsum(t7, t3)[0 + i] == t7[0 + i] + t3[0 + i] && vsum(t5, t1)[0 + i] == t5[0 + i] + t1[0 + i]);
            lemma_vp16_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], t4[0 + i], t5[0 + i], t6[0 + i], t7[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v28, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[5]) by {
            assert(vsum(t0, t4)[0 + i] == t0[0 + i] + t4[0 + i] && vdif(t0, t4)[0 + i] == t0[0 + i] - t4[0 + i]);
            assert(vsum(t7, t3)[0 + i] == t7[0 + i] + t3[0 + i] && vsum(t5, t1)[0 + i] == t5[0 + i] + t1[0 + i]);
            lemma_vp16_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], t4[0 + i], t5[0 + i], t6[0 + i], t7[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v29, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[6]) by {
            assert(vsum(t0, t4)[0 + i] == t0[0 + i] + t4[0 + i] && vdif(t0, t4)[0 + i] == t0[0 + i] - t4[0 + i]);
            assert(vsum(t7, t3)[0 + i] == t7[0 + i] + t3[0 + i] && vsum(t5, t1)[0 + i] == t5[0 + i] + t1[0 + i]);
            lemma_vp16_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], t4[0 + i], t5[0 + i], t6[0 + i], t7[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v30, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[7]) by {
            assert(vsum(t0, t4)[0 + i] == t0[0 + i] + t4[0 + i] && vdif(t0, t4)[0 + i] == t0[0 + i] - t4[0 + i]);
            assert(vsum(t7, t3)[0 + i] == t7[0 + i] + t3[0 + i] && vsum(t5, t1)[0 + i] == t5[0 + i] + t1[0 + i]);
            lemma_vp16_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], t4[0 + i], t5[0 + i], t6[0 + i], t7[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
    }
    (v23, v24, v25, v26, v27, v28, v29, v30)
}

/// One pass over the high four columns of 16-bit rows: each
/// result is right modulo 2^32, lane by lane.
#[inline(always)]
fn vp16_hi(x0: uint8x16_t, x1: uint8x16_t, x2: uint8x16_t, x3: uint8x16_t, x4: uint8x16_t, x5: uint8x16_t, x6: uint8x16_t, x7: uint8x16_t, pe: uint8x16_t, pd: uint8x16_t, pz3: uint8x16_t, pz4: uint8x16_t, k0: uint8x16_t, k1: uint8x16_t, k2: uint8x16_t, Ghost(t0): Ghost<Seq<int>>, Ghost(t1): Ghost<Seq<int>>, Ghost(t2): Ghost<Seq<int>>, Ghost(t3): Ghost<Seq<int>>, Ghost(t4): Ghost<Seq<int>>, Ghost(t5): Ghost<Seq<int>>, Ghost(t6): Ghost<Seq<int>>, Ghost(t7): Ghost<Seq<int>>) -> (r: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t))
    requires
        neon(),
        x16(x0, t0),
        x16(x1, t1),
        x16(x2, t2),
        x16(x3, t3),
        x16(x4, t4),
        x16(x5, t5),
        x16(x6, t6),
        x16(x7, t7),
        x16(pe, vsum(t0, t4)),
        x16(pd, vdif(t0, t4)),
        x16(pz3, vsum(t7, t3)),
        x16(pz4, vsum(t5, t1)),
        kok(k0, k1, k2),
    ensures
        pc16(r.0, t0, t1, t2, t3, t4, t5, t6, t7, 4, 0),
        pc16(r.1, t0, t1, t2, t3, t4, t5, t6, t7, 4, 1),
        pc16(r.2, t0, t1, t2, t3, t4, t5, t6, t7, 4, 2),
        pc16(r.3, t0, t1, t2, t3, t4, t5, t6, t7, 4, 3),
        pc16(r.4, t0, t1, t2, t3, t4, t5, t6, t7, 4, 4),
        pc16(r.5, t0, t1, t2, t3, t4, t5, t6, t7, 4, 5),
        pc16(r.6, t0, t1, t2, t3, t4, t5, t6, t7, 4, 6),
        pc16(r.7, t0, t1, t2, t3, t4, t5, t6, t7, 4, 7),
{
    hide(idct_1d);
    hide(cong);
    hide(l32);
    let v1 = mhi::<0>(x2, k0);
    let v2 = ahi::<1>(v1, x6, k0);
    let v3 = mhi::<2>(x2, k0);
    let v4 = ahi::<0>(v3, x6, k0);
    let v5 = mhi::<3>(pe, k0);
    let v6 = mhi::<3>(pd, k0);
    let v7 = vadd(v5, v4);
    let v8 = vsub(v5, v4);
    let v9 = vadd(v6, v2);
    let v10 = vsub(v6, v2);
    let v11 = mhi::<4>(pz3, k0);
    let v12 = ahi::<5>(v11, pz4, k0);
    let v13 = mhi::<5>(pz3, k0);
    let v14 = ahi::<6>(v13, pz4, k0);
    let v15 = ahi::<7>(v12, x7, k0);
    let v16 = ahi::<0>(v15, x1, k1);
    let v17 = ahi::<1>(v14, x5, k1);
    let v18 = ahi::<2>(v17, x3, k1);
    let v19 = ahi::<3>(v12, x3, k1);
    let v20 = ahi::<2>(v19, x5, k1);
    let v21 = ahi::<4>(v14, x1, k1);
    let v22 = ahi::<0>(v21, x7, k1);
    let v23 = vadd(v7, v22);
    let v24 = vadd(v9, v20);
    let v25 = vadd(v10, v18);
    let v26 = vadd(v8, v16);
    let v27 = vsub(v8, v16);
    let v28 = vsub(v10, v18);
    let v29 = vsub(v9, v20);
    let v30 = vsub(v7, v22);
    proof {
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v23, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[0]) by {
            assert(vsum(t0, t4)[4 + i] == t0[4 + i] + t4[4 + i] && vdif(t0, t4)[4 + i] == t0[4 + i] - t4[4 + i]);
            assert(vsum(t7, t3)[4 + i] == t7[4 + i] + t3[4 + i] && vsum(t5, t1)[4 + i] == t5[4 + i] + t1[4 + i]);
            lemma_vp16_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], t4[4 + i], t5[4 + i], t6[4 + i], t7[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v24, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[1]) by {
            assert(vsum(t0, t4)[4 + i] == t0[4 + i] + t4[4 + i] && vdif(t0, t4)[4 + i] == t0[4 + i] - t4[4 + i]);
            assert(vsum(t7, t3)[4 + i] == t7[4 + i] + t3[4 + i] && vsum(t5, t1)[4 + i] == t5[4 + i] + t1[4 + i]);
            lemma_vp16_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], t4[4 + i], t5[4 + i], t6[4 + i], t7[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v25, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[2]) by {
            assert(vsum(t0, t4)[4 + i] == t0[4 + i] + t4[4 + i] && vdif(t0, t4)[4 + i] == t0[4 + i] - t4[4 + i]);
            assert(vsum(t7, t3)[4 + i] == t7[4 + i] + t3[4 + i] && vsum(t5, t1)[4 + i] == t5[4 + i] + t1[4 + i]);
            lemma_vp16_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], t4[4 + i], t5[4 + i], t6[4 + i], t7[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v26, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[3]) by {
            assert(vsum(t0, t4)[4 + i] == t0[4 + i] + t4[4 + i] && vdif(t0, t4)[4 + i] == t0[4 + i] - t4[4 + i]);
            assert(vsum(t7, t3)[4 + i] == t7[4 + i] + t3[4 + i] && vsum(t5, t1)[4 + i] == t5[4 + i] + t1[4 + i]);
            lemma_vp16_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], t4[4 + i], t5[4 + i], t6[4 + i], t7[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v27, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[4]) by {
            assert(vsum(t0, t4)[4 + i] == t0[4 + i] + t4[4 + i] && vdif(t0, t4)[4 + i] == t0[4 + i] - t4[4 + i]);
            assert(vsum(t7, t3)[4 + i] == t7[4 + i] + t3[4 + i] && vsum(t5, t1)[4 + i] == t5[4 + i] + t1[4 + i]);
            lemma_vp16_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], t4[4 + i], t5[4 + i], t6[4 + i], t7[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v28, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[5]) by {
            assert(vsum(t0, t4)[4 + i] == t0[4 + i] + t4[4 + i] && vdif(t0, t4)[4 + i] == t0[4 + i] - t4[4 + i]);
            assert(vsum(t7, t3)[4 + i] == t7[4 + i] + t3[4 + i] && vsum(t5, t1)[4 + i] == t5[4 + i] + t1[4 + i]);
            lemma_vp16_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], t4[4 + i], t5[4 + i], t6[4 + i], t7[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v29, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[6]) by {
            assert(vsum(t0, t4)[4 + i] == t0[4 + i] + t4[4 + i] && vdif(t0, t4)[4 + i] == t0[4 + i] - t4[4 + i]);
            assert(vsum(t7, t3)[4 + i] == t7[4 + i] + t3[4 + i] && vsum(t5, t1)[4 + i] == t5[4 + i] + t1[4 + i]);
            lemma_vp16_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], t4[4 + i], t5[4 + i], t6[4 + i], t7[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v30, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[7]) by {
            assert(vsum(t0, t4)[4 + i] == t0[4 + i] + t4[4 + i] && vdif(t0, t4)[4 + i] == t0[4 + i] - t4[4 + i]);
            assert(vsum(t7, t3)[4 + i] == t7[4 + i] + t3[4 + i] && vsum(t5, t1)[4 + i] == t5[4 + i] + t1[4 + i]);
            lemma_vp16_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], t4[4 + i], t5[4 + i], t6[4 + i], t7[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i), l32(v24, i), l32(v25, i), l32(v26, i), l32(v27, i), l32(v28, i), l32(v29, i), l32(v30, i));
        }
    }
    (v23, v24, v25, v26, v27, v28, v29, v30)
}

/// One lane of `vp16s_lo` and `vp16s_hi`: the lane values `s1`..`s23`, each made
/// from earlier ones modulo 2^32, end congruent to `idct_1d` of the exact
/// inputs, inputs 4 to 7 being zero.
#[verifier::rlimit(60)]
#[verifier::spinoff_prover]
proof fn lemma_vp16s_lane(t0: int, t1: int, t2: int, t3: int, s1: int, s2: int, s3: int, s4: int, s5: int, s6: int, s7: int, s8: int, s9: int, s10: int, s11: int, s12: int, s13: int, s14: int, s15: int, s16: int, s17: int, s18: int, s19: int, s20: int, s21: int, s22: int, s23: int)
    requires
        rmul(s1, t2, 4433),
        rmul(s2, t2, 10703),
        rmul(s3, t0, 8192),
        radd(s4, s3, s2),
        rsub(s5, s3, s2),
        radd(s6, s3, s1),
        rsub(s7, s3, s1),
        rmul(s8, t1, 2260),
        rmla(s9, s8, t3, -6436),
        rmul(s10, t3, -11362),
        rmla(s11, s10, t1, 6437),
        rmul(s12, t3, -2259),
        rmla(s13, s12, t1, 9633),
        rmul(s14, t1, 11363),
        rmla(s15, s14, t3, 9633),
        radd(s16, s4, s15),
        radd(s17, s6, s13),
        radd(s18, s7, s11),
        radd(s19, s5, s9),
        rsub(s20, s5, s9),
        rsub(s21, s7, s11),
        rsub(s22, s6, s13),
        rsub(s23, s4, s15),
    ensures
        cong(s16, idct_1d(seq![t0, t1, t2, t3, 0int, 0int, 0int, 0int])[0]),
        cong(s17, idct_1d(seq![t0, t1, t2, t3, 0int, 0int, 0int, 0int])[1]),
        cong(s18, idct_1d(seq![t0, t1, t2, t3, 0int, 0int, 0int, 0int])[2]),
        cong(s19, idct_1d(seq![t0, t1, t2, t3, 0int, 0int, 0int, 0int])[3]),
        cong(s20, idct_1d(seq![t0, t1, t2, t3, 0int, 0int, 0int, 0int])[4]),
        cong(s21, idct_1d(seq![t0, t1, t2, t3, 0int, 0int, 0int, 0int])[5]),
        cong(s22, idct_1d(seq![t0, t1, t2, t3, 0int, 0int, 0int, 0int])[6]),
        cong(s23, idct_1d(seq![t0, t1, t2, t3, 0int, 0int, 0int, 0int])[7]),
{
    hide(idct_1d);
    reveal(radd);
    reveal(rsub);
    reveal(rmul);
    reveal(rmla);
    let g1 = t2 * (4433);
    let e1 = -((t2 * (4433)) / 0x1_0000_0000);
    assert(s1 == g1 + 0x1_0000_0000 * e1);
    let g2 = t2 * (10703);
    let e2 = -((t2 * (10703)) / 0x1_0000_0000);
    assert(s2 == g2 + 0x1_0000_0000 * e2);
    let g3 = t0 * (8192);
    let e3 = -((t0 * (8192)) / 0x1_0000_0000);
    assert(s3 == g3 + 0x1_0000_0000 * e3);
    let g4 = g3 + g2;
    let e4 = e3 + e2 - (s3 + s2) / 0x1_0000_0000;
    assert(s4 == g4 + 0x1_0000_0000 * e4);
    let g5 = g3 - g2;
    let e5 = e3 - e2 + 1 - (s3 - s2 + 0x1_0000_0000) / 0x1_0000_0000;
    assert(s5 == g5 + 0x1_0000_0000 * e5);
    let g6 = g3 + g1;
    let e6 = e3 + e1 - (s3 + s1) / 0x1_0000_0000;
    assert(s6 == g6 + 0x1_0000_0000 * e6);
    let g7 = g3 - g1;
    let e7 = e3 - e1 + 1 - (s3 - s1 + 0x1_0000_0000) / 0x1_0000_0000;
    assert(s7 == g7 + 0x1_0000_0000 * e7);
    let g8 = t1 * (2260);
    let e8 = -((t1 * (2260)) / 0x1_0000_0000);
    assert(s8 == g8 + 0x1_0000_0000 * e8);
    let g9 = g8 + t3 * (-6436);
    let e9 = e8 - (s8 + t3 * (-6436)) / 0x1_0000_0000;
    assert(s9 == g9 + 0x1_0000_0000 * e9);
    let g10 = t3 * (-11362);
    let e10 = -((t3 * (-11362)) / 0x1_0000_0000);
    assert(s10 == g10 + 0x1_0000_0000 * e10);
    let g11 = g10 + t1 * (6437);
    let e11 = e10 - (s10 + t1 * (6437)) / 0x1_0000_0000;
    assert(s11 == g11 + 0x1_0000_0000 * e11);
    let g12 = t3 * (-2259);
    let e12 = -((t3 * (-2259)) / 0x1_0000_0000);
    assert(s12 == g12 + 0x1_0000_0000 * e12);
    let g13 = g12 + t1 * (9633);
    let e13 = e12 - (s12 + t1 * (9633)) / 0x1_0000_0000;
    assert(s13 == g13 + 0x1_0000_0000 * e13);
    let g14 = t1 * (11363);
    let e14 = -((t1 * (11363)) / 0x1_0000_0000);
    assert(s14 == g14 + 0x1_0000_0000 * e14);
    let g15 = g14 + t3 * (9633);
    let e15 = e14 - (s14 + t3 * (9633)) / 0x1_0000_0000;
    assert(s15 == g15 + 0x1_0000_0000 * e15);
    let g16 = g4 + g15;
    let e16 = e4 + e15 - (s4 + s15) / 0x1_0000_0000;
    assert(s16 == g16 + 0x1_0000_0000 * e16);
    let g17 = g6 + g13;
    let e17 = e6 + e13 - (s6 + s13) / 0x1_0000_0000;
    assert(s17 == g17 + 0x1_0000_0000 * e17);
    let g18 = g7 + g11;
    let e18 = e7 + e11 - (s7 + s11) / 0x1_0000_0000;
    assert(s18 == g18 + 0x1_0000_0000 * e18);
    let g19 = g5 + g9;
    let e19 = e5 + e9 - (s5 + s9) / 0x1_0000_0000;
    assert(s19 == g19 + 0x1_0000_0000 * e19);
    let g20 = g5 - g9;
    let e20 = e5 - e9 + 1 - (s5 - s9 + 0x1_0000_0000) / 0x1_0000_0000;
    assert(s20 == g20 + 0x1_0000_0000 * e20);
    let g21 = g7 - g11;
    let e21 = e7 - e11 + 1 - (s7 - s11 + 0x1_0000_0000) / 0x1_0000_0000;
    assert(s21 == g21 + 0x1_0000_0000 * e21);
    let g22 = g6 - g13;
    let e22 = e6 - e13 + 1 - (s6 - s13 + 0x1_0000_0000) / 0x1_0000_0000;
    assert(s22 == g22 + 0x1_0000_0000 * e22);
    let g23 = g4 - g15;
    let e23 = e4 - e15 + 1 - (s4 - s15 + 0x1_0000_0000) / 0x1_0000_0000;
    assert(s23 == g23 + 0x1_0000_0000 * e23);
    let c1 = t2 + 0int;
    let c2 = c1 * (4433);
    let c3 = 0int * (-15137);
    let c4 = c2 + c3;
    let c5 = t2 * (6270);
    let c6 = c2 + c5;
    let c7 = t0 + 0int;
    let c8 = c7 * (8192);
    let c9 = t0 - 0int;
    let c10 = c9 * (8192);
    let c11 = c8 + c6;
    let c12 = c8 - c6;
    let c13 = c10 + c4;
    let c14 = c10 - c4;
    let c15 = 0int + t1;
    let c16 = 0int + t3;
    let c17 = 0int + t3;
    let c18 = 0int + t1;
    let c19 = c17 + c18;
    let c20 = c19 * (9633);
    let c21 = c15 * (-7373);
    let c22 = c16 * (-20995);
    let c23 = c17 * (-16069);
    let c24 = c23 + c20;
    let c25 = c18 * (-3196);
    let c26 = c25 + c20;
    let c27 = 0int * (2446);
    let c28 = c27 + c21;
    let c29 = c28 + c24;
    let c30 = 0int * (16819);
    let c31 = c30 + c22;
    let c32 = c31 + c26;
    let c33 = t3 * (25172);
    let c34 = c33 + c22;
    let c35 = c34 + c24;
    let c36 = t1 * (12299);
    let c37 = c36 + c21;
    let c38 = c37 + c26;
    let c39 = c11 + c38;
    let c40 = c13 + c35;
    let c41 = c14 + c32;
    let c42 = c12 + c29;
    let c43 = c12 - c29;
    let c44 = c14 - c32;
    let c45 = c13 - c35;
    let c46 = c11 - c38;
    lemma_pass_link(t0, t1, t2, t3, 0int, 0int, 0int, 0int, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46);
    assert(g16 == c39);
    lemma_cong_k(s16, g16, e16);
    assert(g17 == c40);
    lemma_cong_k(s17, g17, e17);
    assert(g18 == c41);
    lemma_cong_k(s18, g18, e18);
    assert(g19 == c42);
    lemma_cong_k(s19, g19, e19);
    assert(g20 == c43);
    lemma_cong_k(s20, g20, e20);
    assert(g21 == c44);
    lemma_cong_k(s21, g21, e21);
    assert(g22 == c45);
    lemma_cong_k(s22, g22, e22);
    assert(g23 == c46);
    lemma_cong_k(s23, g23, e23);
}

/// One pass over the low four columns of 16-bit rows, rows 4 to 7 being zero: each
/// result is right modulo 2^32, lane by lane.
#[inline(always)]
fn vp16s_lo(x0: uint8x16_t, x1: uint8x16_t, x2: uint8x16_t, x3: uint8x16_t, k0: uint8x16_t, k1: uint8x16_t, k2: uint8x16_t, Ghost(t0): Ghost<Seq<int>>, Ghost(t1): Ghost<Seq<int>>, Ghost(t2): Ghost<Seq<int>>, Ghost(t3): Ghost<Seq<int>>, Ghost(t4): Ghost<Seq<int>>, Ghost(t5): Ghost<Seq<int>>, Ghost(t6): Ghost<Seq<int>>, Ghost(t7): Ghost<Seq<int>>) -> (r: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t))
    requires
        neon(),
        x16(x0, t0),
        x16(x1, t1),
        x16(x2, t2),
        x16(x3, t3),
        zero8(t4),
        zero8(t5),
        zero8(t6),
        zero8(t7),
        kok(k0, k1, k2),
    ensures
        pc16(r.0, t0, t1, t2, t3, t4, t5, t6, t7, 0, 0),
        pc16(r.1, t0, t1, t2, t3, t4, t5, t6, t7, 0, 1),
        pc16(r.2, t0, t1, t2, t3, t4, t5, t6, t7, 0, 2),
        pc16(r.3, t0, t1, t2, t3, t4, t5, t6, t7, 0, 3),
        pc16(r.4, t0, t1, t2, t3, t4, t5, t6, t7, 0, 4),
        pc16(r.5, t0, t1, t2, t3, t4, t5, t6, t7, 0, 5),
        pc16(r.6, t0, t1, t2, t3, t4, t5, t6, t7, 0, 6),
        pc16(r.7, t0, t1, t2, t3, t4, t5, t6, t7, 0, 7),
{
    hide(idct_1d);
    hide(cong);
    hide(l32);
    let v1 = mlo::<0>(x2, k0);
    let v2 = mlo::<2>(x2, k0);
    let v3 = mlo::<3>(x0, k0);
    let v4 = vadd(v3, v2);
    let v5 = vsub(v3, v2);
    let v6 = vadd(v3, v1);
    let v7 = vsub(v3, v1);
    let v8 = mlo::<5>(x1, k1);
    let v9 = alo::<4>(v8, x3, k0);
    let v10 = mlo::<6>(x3, k1);
    let v11 = alo::<6>(v10, x1, k0);
    let v12 = mlo::<7>(x3, k1);
    let v13 = alo::<5>(v12, x1, k0);
    let v14 = mlo::<0>(x1, k2);
    let v15 = alo::<5>(v14, x3, k0);
    let v16 = vadd(v4, v15);
    let v17 = vadd(v6, v13);
    let v18 = vadd(v7, v11);
    let v19 = vadd(v5, v9);
    let v20 = vsub(v5, v9);
    let v21 = vsub(v7, v11);
    let v22 = vsub(v6, v13);
    let v23 = vsub(v4, v15);
    proof {
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v16, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[0]) by {
            lemma_vp16s_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i) =~= seq![t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v17, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[1]) by {
            lemma_vp16s_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i) =~= seq![t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v18, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[2]) by {
            lemma_vp16s_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i) =~= seq![t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v19, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[3]) by {
            lemma_vp16s_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i) =~= seq![t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v20, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[4]) by {
            lemma_vp16s_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i) =~= seq![t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v21, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[5]) by {
            lemma_vp16s_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i) =~= seq![t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v22, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[6]) by {
            lemma_vp16s_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i) =~= seq![t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v23, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i))[7]) by {
            lemma_vp16s_lane(t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 0 + i) =~= seq![t0[0 + i], t1[0 + i], t2[0 + i], t3[0 + i], 0int, 0int, 0int, 0int]);
        }
    }
    (v16, v17, v18, v19, v20, v21, v22, v23)
}

/// One pass over the high four columns of 16-bit rows, rows 4 to 7 being zero: each
/// result is right modulo 2^32, lane by lane.
#[inline(always)]
fn vp16s_hi(x0: uint8x16_t, x1: uint8x16_t, x2: uint8x16_t, x3: uint8x16_t, k0: uint8x16_t, k1: uint8x16_t, k2: uint8x16_t, Ghost(t0): Ghost<Seq<int>>, Ghost(t1): Ghost<Seq<int>>, Ghost(t2): Ghost<Seq<int>>, Ghost(t3): Ghost<Seq<int>>, Ghost(t4): Ghost<Seq<int>>, Ghost(t5): Ghost<Seq<int>>, Ghost(t6): Ghost<Seq<int>>, Ghost(t7): Ghost<Seq<int>>) -> (r: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t))
    requires
        neon(),
        x16(x0, t0),
        x16(x1, t1),
        x16(x2, t2),
        x16(x3, t3),
        zero8(t4),
        zero8(t5),
        zero8(t6),
        zero8(t7),
        kok(k0, k1, k2),
    ensures
        pc16(r.0, t0, t1, t2, t3, t4, t5, t6, t7, 4, 0),
        pc16(r.1, t0, t1, t2, t3, t4, t5, t6, t7, 4, 1),
        pc16(r.2, t0, t1, t2, t3, t4, t5, t6, t7, 4, 2),
        pc16(r.3, t0, t1, t2, t3, t4, t5, t6, t7, 4, 3),
        pc16(r.4, t0, t1, t2, t3, t4, t5, t6, t7, 4, 4),
        pc16(r.5, t0, t1, t2, t3, t4, t5, t6, t7, 4, 5),
        pc16(r.6, t0, t1, t2, t3, t4, t5, t6, t7, 4, 6),
        pc16(r.7, t0, t1, t2, t3, t4, t5, t6, t7, 4, 7),
{
    hide(idct_1d);
    hide(cong);
    hide(l32);
    let v1 = mhi::<0>(x2, k0);
    let v2 = mhi::<2>(x2, k0);
    let v3 = mhi::<3>(x0, k0);
    let v4 = vadd(v3, v2);
    let v5 = vsub(v3, v2);
    let v6 = vadd(v3, v1);
    let v7 = vsub(v3, v1);
    let v8 = mhi::<5>(x1, k1);
    let v9 = ahi::<4>(v8, x3, k0);
    let v10 = mhi::<6>(x3, k1);
    let v11 = ahi::<6>(v10, x1, k0);
    let v12 = mhi::<7>(x3, k1);
    let v13 = ahi::<5>(v12, x1, k0);
    let v14 = mhi::<0>(x1, k2);
    let v15 = ahi::<5>(v14, x3, k0);
    let v16 = vadd(v4, v15);
    let v17 = vadd(v6, v13);
    let v18 = vadd(v7, v11);
    let v19 = vadd(v5, v9);
    let v20 = vsub(v5, v9);
    let v21 = vsub(v7, v11);
    let v22 = vsub(v6, v13);
    let v23 = vsub(v4, v15);
    proof {
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v16, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[0]) by {
            lemma_vp16s_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i) =~= seq![t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v17, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[1]) by {
            lemma_vp16s_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i) =~= seq![t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v18, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[2]) by {
            lemma_vp16s_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i) =~= seq![t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v19, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[3]) by {
            lemma_vp16s_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i) =~= seq![t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v20, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[4]) by {
            lemma_vp16s_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i) =~= seq![t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v21, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[5]) by {
            lemma_vp16s_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i) =~= seq![t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v22, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[6]) by {
            lemma_vp16s_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i) =~= seq![t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], 0int, 0int, 0int, 0int]);
        }
        assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v23, i), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i))[7]) by {
            lemma_vp16s_lane(t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], l32(v1, i), l32(v2, i), l32(v3, i), l32(v4, i), l32(v5, i), l32(v6, i), l32(v7, i), l32(v8, i), l32(v9, i), l32(v10, i), l32(v11, i), l32(v12, i), l32(v13, i), l32(v14, i), l32(v15, i), l32(v16, i), l32(v17, i), l32(v18, i), l32(v19, i), l32(v20, i), l32(v21, i), l32(v22, i), l32(v23, i));
            assert(col(t0, t1, t2, t3, t4, t5, t6, t7, 4 + i) =~= seq![t0[4 + i], t1[4 + i], t2[4 + i], t3[4 + i], 0int, 0int, 0int, 0int]);
        }
    }
    (v16, v17, v18, v19, v20, v21, v22, v23)
}

/// A result of a pass is at most 11363 times the sum of its inputs'
/// magnitudes.
#[verifier::rlimit(60)]
#[verifier::spinoff_prover]
pub proof fn lemma_pass_wbound(t0: int, t1: int, t2: int, t3: int, t4: int, t5: int, t6: int, t7: int, a0: int, a1: int, a2: int, a3: int, a4: int, a5: int, a6: int, a7: int)
    requires
        -a0 <= t0 <= a0,
        -a1 <= t1 <= a1,
        -a2 <= t2 <= a2,
        -a3 <= t3 <= a3,
        -a4 <= t4 <= a4,
        -a5 <= t5 <= a5,
        -a6 <= t6 <= a6,
        -a7 <= t7 <= a7,
    ensures
        -11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) <= idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[0] <= 11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7),
        -11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) <= idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[1] <= 11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7),
        -11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) <= idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[2] <= 11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7),
        -11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) <= idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[3] <= 11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7),
        -11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) <= idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[4] <= 11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7),
        -11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) <= idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[5] <= 11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7),
        -11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) <= idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[6] <= 11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7),
        -11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) <= idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[7] <= 11363 * (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7),
{
    hide(idct_1d);
    let c1 = t2 + t6;
    let c2 = c1 * (4433);
    let c3 = t6 * (-15137);
    let c4 = c2 + c3;
    let c5 = t2 * (6270);
    let c6 = c2 + c5;
    let c7 = t0 + t4;
    let c8 = c7 * (8192);
    let c9 = t0 - t4;
    let c10 = c9 * (8192);
    let c11 = c8 + c6;
    let c12 = c8 - c6;
    let c13 = c10 + c4;
    let c14 = c10 - c4;
    let c15 = t7 + t1;
    let c16 = t5 + t3;
    let c17 = t7 + t3;
    let c18 = t5 + t1;
    let c19 = c17 + c18;
    let c20 = c19 * (9633);
    let c21 = c15 * (-7373);
    let c22 = c16 * (-20995);
    let c23 = c17 * (-16069);
    let c24 = c23 + c20;
    let c25 = c18 * (-3196);
    let c26 = c25 + c20;
    let c27 = t7 * (2446);
    let c28 = c27 + c21;
    let c29 = c28 + c24;
    let c30 = t5 * (16819);
    let c31 = c30 + c22;
    let c32 = c31 + c26;
    let c33 = t3 * (25172);
    let c34 = c33 + c22;
    let c35 = c34 + c24;
    let c36 = t1 * (12299);
    let c37 = c36 + c21;
    let c38 = c37 + c26;
    let c39 = c11 + c38;
    let c40 = c13 + c35;
    let c41 = c14 + c32;
    let c42 = c12 + c29;
    let c43 = c12 - c29;
    let c44 = c14 - c32;
    let c45 = c13 - c35;
    let c46 = c11 - c38;
    lemma_pass_link(t0, t1, t2, t3, t4, t5, t6, t7, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46);
    assert(c39 == (8192) * t0 + (11363) * t1 + (10703) * t2 + (9633) * t3 + (8192) * t4 + (6437) * t5 + (4433) * t6 + (2260) * t7);
    assert(c40 == (8192) * t0 + (9633) * t1 + (4433) * t2 + (-2259) * t3 + (-8192) * t4 + (-11362) * t5 + (-10704) * t6 + (-6436) * t7);
    assert(c41 == (8192) * t0 + (6437) * t1 + (-4433) * t2 + (-11362) * t3 + (-8192) * t4 + (2261) * t5 + (10704) * t6 + (9633) * t7);
    assert(c42 == (8192) * t0 + (2260) * t1 + (-10703) * t2 + (-6436) * t3 + (8192) * t4 + (9633) * t5 + (-4433) * t6 + (-11363) * t7);
    assert(c43 == (8192) * t0 + (-2260) * t1 + (-10703) * t2 + (6436) * t3 + (8192) * t4 + (-9633) * t5 + (-4433) * t6 + (11363) * t7);
    assert(c44 == (8192) * t0 + (-6437) * t1 + (-4433) * t2 + (11362) * t3 + (-8192) * t4 + (-2261) * t5 + (10704) * t6 + (-9633) * t7);
    assert(c45 == (8192) * t0 + (-9633) * t1 + (4433) * t2 + (2259) * t3 + (-8192) * t4 + (11362) * t5 + (-10704) * t6 + (6436) * t7);
    assert(c46 == (8192) * t0 + (-11363) * t1 + (10703) * t2 + (-9633) * t3 + (8192) * t4 + (-6437) * t5 + (4433) * t6 + (-2260) * t7);
}

/// 16 more in input 0 is 2^17 more in every result of a pass.
pub proof fn lemma_pass_shift16(t0: int, t1: int, t2: int, t3: int, t4: int, t5: int, t6: int, t7: int)
    ensures
        idct_1d(seq![t0 + 16, t1, t2, t3, t4, t5, t6, t7])[0] == idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[0] + 131072,
        idct_1d(seq![t0 + 16, t1, t2, t3, t4, t5, t6, t7])[1] == idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[1] + 131072,
        idct_1d(seq![t0 + 16, t1, t2, t3, t4, t5, t6, t7])[2] == idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[2] + 131072,
        idct_1d(seq![t0 + 16, t1, t2, t3, t4, t5, t6, t7])[3] == idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[3] + 131072,
        idct_1d(seq![t0 + 16, t1, t2, t3, t4, t5, t6, t7])[4] == idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[4] + 131072,
        idct_1d(seq![t0 + 16, t1, t2, t3, t4, t5, t6, t7])[5] == idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[5] + 131072,
        idct_1d(seq![t0 + 16, t1, t2, t3, t4, t5, t6, t7])[6] == idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[6] + 131072,
        idct_1d(seq![t0 + 16, t1, t2, t3, t4, t5, t6, t7])[7] == idct_1d(seq![t0, t1, t2, t3, t4, t5, t6, t7])[7] + 131072,
{
    hide(idct_1d);
    let c1 = t2 + t6;
    let c2 = c1 * (4433);
    let c3 = t6 * (-15137);
    let c4 = c2 + c3;
    let c5 = t2 * (6270);
    let c6 = c2 + c5;
    let c7 = t0 + t4;
    let c8 = c7 * (8192);
    let c9 = t0 - t4;
    let c10 = c9 * (8192);
    let c11 = c8 + c6;
    let c12 = c8 - c6;
    let c13 = c10 + c4;
    let c14 = c10 - c4;
    let c15 = t7 + t1;
    let c16 = t5 + t3;
    let c17 = t7 + t3;
    let c18 = t5 + t1;
    let c19 = c17 + c18;
    let c20 = c19 * (9633);
    let c21 = c15 * (-7373);
    let c22 = c16 * (-20995);
    let c23 = c17 * (-16069);
    let c24 = c23 + c20;
    let c25 = c18 * (-3196);
    let c26 = c25 + c20;
    let c27 = t7 * (2446);
    let c28 = c27 + c21;
    let c29 = c28 + c24;
    let c30 = t5 * (16819);
    let c31 = c30 + c22;
    let c32 = c31 + c26;
    let c33 = t3 * (25172);
    let c34 = c33 + c22;
    let c35 = c34 + c24;
    let c36 = t1 * (12299);
    let c37 = c36 + c21;
    let c38 = c37 + c26;
    let c39 = c11 + c38;
    let c40 = c13 + c35;
    let c41 = c14 + c32;
    let c42 = c12 + c29;
    let c43 = c12 - c29;
    let c44 = c14 - c32;
    let c45 = c13 - c35;
    let c46 = c11 - c38;
    lemma_pass_link(t0, t1, t2, t3, t4, t5, t6, t7, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46);
    let b1 = t2 + t6;
    let b2 = b1 * (4433);
    let b3 = t6 * (-15137);
    let b4 = b2 + b3;
    let b5 = t2 * (6270);
    let b6 = b2 + b5;
    let b7 = (t0 + 16) + t4;
    let b8 = b7 * (8192);
    let b9 = (t0 + 16) - t4;
    let b10 = b9 * (8192);
    let b11 = b8 + b6;
    let b12 = b8 - b6;
    let b13 = b10 + b4;
    let b14 = b10 - b4;
    let b15 = t7 + t1;
    let b16 = t5 + t3;
    let b17 = t7 + t3;
    let b18 = t5 + t1;
    let b19 = b17 + b18;
    let b20 = b19 * (9633);
    let b21 = b15 * (-7373);
    let b22 = b16 * (-20995);
    let b23 = b17 * (-16069);
    let b24 = b23 + b20;
    let b25 = b18 * (-3196);
    let b26 = b25 + b20;
    let b27 = t7 * (2446);
    let b28 = b27 + b21;
    let b29 = b28 + b24;
    let b30 = t5 * (16819);
    let b31 = b30 + b22;
    let b32 = b31 + b26;
    let b33 = t3 * (25172);
    let b34 = b33 + b22;
    let b35 = b34 + b24;
    let b36 = t1 * (12299);
    let b37 = b36 + b21;
    let b38 = b37 + b26;
    let b39 = b11 + b38;
    let b40 = b13 + b35;
    let b41 = b14 + b32;
    let b42 = b12 + b29;
    let b43 = b12 - b29;
    let b44 = b14 - b32;
    let b45 = b13 - b35;
    let b46 = b11 - b38;
    lemma_pass_link((t0 + 16), t1, t2, t3, t4, t5, t6, t7, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46);
    assert(b39 == c39 + 131072);
    assert(b40 == c40 + 131072);
    assert(b41 == c41 + 131072);
    assert(b42 == c42 + 131072);
    assert(b43 == c43 + 131072);
    assert(b44 == c44 + 131072);
    assert(b45 == c45 + 131072);
    assert(b46 == c46 + 131072);
}
// END generated

// ---------------------------------------------------------------------------
// Exact 16-bit arithmetic
// ---------------------------------------------------------------------------

proof fn lemma_add16_exact(x: u16, y: u16, r: u16)
    requires
        r as int == (x + y) % 0x10000,
        -32768 <= s16(x) + s16(y) <= 32767,
    ensures
        s16(r) == s16(x) + s16(y),
{
}

proof fn lemma_sub16_exact(x: u16, y: u16, r: u16)
    requires
        r as int == (x - y + 0x10000) % 0x10000,
        -32768 <= s16(x) - s16(y) <= 32767,
    ensures
        s16(r) == s16(x) - s16(y),
{
}

/// The sum of two rows whose values are small enough that it is exact.
#[inline(always)]
fn add16x(a: uint8x16_t, b: uint8x16_t, Ghost(ta): Ghost<Seq<int>>, Ghost(tb): Ghost<Seq<int>>) -> (r: uint8x16_t)
    requires
        neon(),
        x16(a, ta),
        x16(b, tb),
        in8(ta, 16383),
        in8(tb, 16383),
    ensures
        x16(r, vsum(ta, tb)),
{
    let r = vaddq_s16(a, b);
    proof {
        assert forall|i: int| 0 <= i < 8 implies #[trigger] s16l(r, i) == vsum(ta, tb)[i] by {
            assert(s16l(a, i) == ta[i] && s16l(b, i) == tb[i]);
            lemma_add16_exact(u16s(n8(a))[i], u16s(n8(b))[i], u16s(n8(r))[i]);
        }
    }
    r
}

/// The difference of two rows whose values are small enough that it is
/// exact.
#[inline(always)]
fn sub16x(a: uint8x16_t, b: uint8x16_t, Ghost(ta): Ghost<Seq<int>>, Ghost(tb): Ghost<Seq<int>>) -> (r: uint8x16_t)
    requires
        neon(),
        x16(a, ta),
        x16(b, tb),
        in8(ta, 16383),
        in8(tb, 16383),
    ensures
        x16(r, vdif(ta, tb)),
{
    let r = vsubq_s16(a, b);
    proof {
        assert forall|i: int| 0 <= i < 8 implies #[trigger] s16l(r, i) == vdif(ta, tb)[i] by {
            assert(s16l(a, i) == ta[i] && s16l(b, i) == tb[i]);
            lemma_sub16_exact(u16s(n8(a))[i], u16s(n8(b))[i], u16s(n8(r))[i]);
        }
    }
    r
}

/// Eight values, each 16 more.
pub open spec fn sh16(t: Seq<int>) -> Seq<int> {
    Seq::new(8, |i: int| t[i] + 16)
}

/// A row plus 16 in every lane.
#[inline(always)]
fn addk16(a: uint8x16_t, Ghost(ta): Ghost<Seq<int>>) -> (r: uint8x16_t)
    requires
        neon(),
        x16(a, ta),
        in8(ta, 16000),
    ensures
        x16(r, sh16(ta)),
        in8(sh16(ta), 16383),
{
    let k = vdupq_n_s16(16);
    let r = vaddq_s16(a, k);
    proof {
        assert forall|i: int| 0 <= i < 8 implies #[trigger] s16l(r, i) == sh16(ta)[i] by {
            assert(s16l(a, i) == ta[i]);
            assert(u16s(n8(k))[i] == 16);
            lemma_add16_exact(u16s(n8(a))[i], u16s(n8(k))[i], u16s(n8(r))[i]);
        }
        assert forall|i: int| 0 <= i < 8 implies -16383 <= #[trigger] sh16(ta)[i] <= 16383 by {
            assert(-16000 <= ta[i] <= 16000);
        }
    }
    r
}

// ---------------------------------------------------------------------------
// Dequantization, and the guard on the block's size
// ---------------------------------------------------------------------------

/// Row `r` of a block.
pub open spec fn dr(dq: Seq<int>, r: int) -> Seq<int> {
    Seq::new(8, |j: int| dq[8 * r + j])
}

/// Column `j` of a block.
pub open spec fn dcol(dq: Seq<int>, j: int) -> Seq<int> {
    Seq::new(8, |i: int| dq[8 * i + j])
}

pub open spec fn iabs(x: int) -> int {
    if x < 0 {
        -x
    } else {
        x
    }
}

/// The sum of the magnitudes in column `j`.
pub open spec fn acol(dq: Seq<int>, j: int) -> int {
    iabs(dq[j]) + iabs(dq[8 + j]) + iabs(dq[16 + j]) + iabs(dq[24 + j]) + iabs(dq[32 + j]) + iabs(dq[40 + j]) + iabs(
        dq[48 + j],
    ) + iabs(dq[56 + j])
}

/// The sum of the magnitudes in the block.
pub open spec fn atot(dq: Seq<int>) -> int {
    acol(dq, 0) + acol(dq, 1) + acol(dq, 2) + acol(dq, 3) + acol(dq, 4) + acol(dq, 5) + acol(dq, 6) + acol(dq, 7)
}

/// The largest block total for which the transform fits: the first pass's
/// results then fit 16 bits with room for the second pass's sums, and the
/// second pass's are inside the ten bits the range limit reads, so
/// saturating is the same as its table.
pub open spec fn tot_max() -> int {
    2120
}

/// One dequantized value from the 16-bit product: exact, because the guard
/// bounds it.
proof fn lemma_deq16_lane(av: i16, qv: u16, lane: u16, mx: int, mq: int)
    requires
        lane as int == ((#[verifier::truncate] (av as u16)) as int * qv as int) % 0x1_0000,
        ab16((#[verifier::truncate] (av as u16)) as int) <= mx,
        qv <= mq,
        mx * mq <= 16383,
    ensures
        s16(lane) == av as int * sx16(qv as int),
        -16383 <= av as int * sx16(qv as int) <= 16383,
{
    let cu = #[verifier::truncate] (av as u16);
    assert(cu as int == if av < 0 {
        av as int + 0x10000
    } else {
        av as int
    }) by (bit_vector)
        requires
            cu == #[verifier::truncate] (av as u16),
    ;
    let (ai, qi) = (av as int, qv as int);
    if mx == 0 {
        assert(av == 0);
        assert(ai * sx16(qi) == 0 && cu as int * qi == 0) by (nonlinear_arith)
            requires
                ai == 0,
                cu == 0,
        ;
    } else {
        assert(mq <= 16383) by (nonlinear_arith)
            requires
                mx >= 1,
                mx * mq <= 16383,
                mq >= 0,
        ;
        assert(sx16(qi) == qi);
        let x = ai * qi;
        assert(x <= mx * qi && -(mx * qi) <= x) by (nonlinear_arith)
            requires
                -mx <= ai <= mx,
                0 <= qi,
                x == ai * qi,
        ;
        assert(mx * qi <= mx * mq) by (nonlinear_arith)
            requires
                0 <= qi <= mq,
                mx >= 0,
        ;
        let n: int = if av < 0 {
            1
        } else {
            0
        };
        assert(cu as int * qi == x + 0x1_0000 * (n * qi)) by (nonlinear_arith)
            requires
                cu as int == ai + 0x1_0000 * n,
                x == ai * qi,
        ;
        lemma_mod_multiples_vanish(n * qi, x, 0x1_0000);
    }
}

/// A row dequantized in 16 bits.
#[inline(always)]
fn deq16(c: uint8x16_t, q: uint8x16_t, Ghost(a): Ghost<Seq<i16>>, Ghost(o): Ghost<int>, Ghost(qs): Ghost<Seq<u16>>, Ghost(r): Ghost<int>, Ghost(mx): Ghost<int>, Ghost(mq): Ghost<int>) -> (d: uint8x16_t)
    requires
        neon(),
        0 <= r < 8,
        0 <= o,
        o + 64 <= a.len(),
        qs.len() == 64,
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(c, i) == (#[verifier::truncate] (a[o + 8 * r + i] as u16)) as int,
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(q, i) == qs[8 * r + i] as int,
        forall|i: int| 0 <= i < 8 ==> ab16(#[trigger] l16(c, i)) <= mx,
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(q, i) <= mq,
        mx * mq <= 16383,
    ensures
        x16(d, dr(dequant(a, o, qs), r)),
        in8(dr(dequant(a, o, qs), r), 16383),
{
    let d = vmulq_u16(c, q);
    proof {
        let dq = dequant(a, o, qs);
        assert forall|i: int| 0 <= i < 8 implies #[trigger] s16l(d, i) == dr(dq, r)[i] && -16383 <= dr(dq, r)[i] <= 16383 by {
            assert(l16(c, i) == (#[verifier::truncate] (a[o + 8 * r + i] as u16)) as int);
            assert(l16(q, i) == qs[8 * r + i] as int);
            assert(ab16(l16(c, i)) <= mx && l16(q, i) <= mq);
            lemma_deq16_lane(a[o + 8 * r + i], qs[8 * r + i], u16s(n8(d))[i], mx, mq);
        }
        assert forall|i: int| 0 <= i < 8 implies -16383 <= #[trigger] dr(dq, r)[i] <= 16383 by {
            assert(s16l(d, i) == dr(dq, r)[i]);
        }
    }
    d
}

/// A row of coefficients that are all zero dequantizes to zeros.
proof fn lemma_zero_row(c: uint8x16_t, a: Seq<i16>, o: int, qs: Seq<u16>, r: int)
    requires
        0 <= r < 8,
        0 <= o,
        o + 64 <= a.len(),
        qs.len() == 64,
        forall|i: int| 0 <= i < 8 ==> #[trigger] l16(c, i) == (#[verifier::truncate] (a[o + 8 * r + i] as u16)) as int,
        forall|i: int| 0 <= i < 8 ==> ab16(#[trigger] l16(c, i)) <= 0,
    ensures
        zero8(dr(dequant(a, o, qs), r)),
{
    let dq = dequant(a, o, qs);
    assert forall|i: int| 0 <= i < 8 implies #[trigger] dr(dq, r)[i] == 0 by {
        assert(ab16(l16(c, i)) <= 0);
        lemma_dq_zero(a, o, qs, 8 * r + i, l16(c, i));
    }
}

/// The magnitudes of four rows, summed down the columns.
#[inline(always)]
fn colsum4(d0: uint8x16_t, d1: uint8x16_t, d2: uint8x16_t, d3: uint8x16_t, Ghost(t0): Ghost<Seq<int>>, Ghost(t1): Ghost<Seq<int>>, Ghost(t2): Ghost<Seq<int>>, Ghost(t3): Ghost<Seq<int>>) -> (s: uint8x16_t)
    requires
        neon(),
        x16(d0, t0),
        x16(d1, t1),
        x16(d2, t2),
        x16(d3, t3),
        in8(t0, 16383),
        in8(t1, 16383),
        in8(t2, 16383),
        in8(t3, 16383),
    ensures
        forall|j: int| 0 <= j < 8 ==> #[trigger] l16(s, j) == iabs(t0[j]) + iabs(t1[j]) + iabs(t2[j]) + iabs(t3[j]),
{
    let b0 = vabsq_s16(d0);
    let b1 = vabsq_s16(d1);
    let b2 = vabsq_s16(d2);
    let b3 = vabsq_s16(d3);
    let s01 = vaddq_s16(b0, b1);
    let s23 = vaddq_s16(b2, b3);
    let s = vaddq_s16(s01, s23);
    proof {
        assert forall|j: int| 0 <= j < 8 implies #[trigger] l16(s, j) == iabs(t0[j]) + iabs(t1[j]) + iabs(t2[j]) + iabs(
            t3[j],
        ) by {
            assert(s16l(d0, j) == t0[j] && s16l(d1, j) == t1[j] && s16l(d2, j) == t2[j] && s16l(d3, j) == t3[j]);
            assert(l16(b0, j) == iabs(t0[j]) && l16(b1, j) == iabs(t1[j]) && l16(b2, j) == iabs(t2[j]) && l16(b3, j)
                == iabs(t3[j]));
            assert(l16(s01, j) == l16(b0, j) + l16(b1, j));
            assert(l16(s23, j) == l16(b2, j) + l16(b3, j));
        }
    }
    s
}

/// The sum of eight 16-bit lanes, written out.
proof fn lemma_sum8(a: Seq<u16>)
    requires
        a.len() == 8,
    ensures
        sum_u16(a) == a[0] + a[1] + a[2] + a[3] + a[4] + a[5] + a[6] + a[7],
{
    let a7 = a.drop_last();
    let a6 = a7.drop_last();
    let a5 = a6.drop_last();
    let a4 = a5.drop_last();
    let a3 = a4.drop_last();
    let a2 = a3.drop_last();
    let a1 = a2.drop_last();
    let a0 = a1.drop_last();
    assert(sum_u16(a0) == 0);
    assert(sum_u16(a1) == sum_u16(a0) + a1.last());
    assert(sum_u16(a2) == sum_u16(a1) + a2.last());
    assert(sum_u16(a3) == sum_u16(a2) + a3.last());
    assert(sum_u16(a4) == sum_u16(a3) + a4.last());
    assert(sum_u16(a5) == sum_u16(a4) + a5.last());
    assert(sum_u16(a6) == sum_u16(a5) + a6.last());
    assert(sum_u16(a7) == sum_u16(a6) + a7.last());
    assert(sum_u16(a) == sum_u16(a7) + a.last());
}

/// The sum of the lanes.
#[inline(always)]
fn total(s: uint8x16_t) -> (t: u32)
    requires
        neon(),
    ensures
        t == l16(s, 0) + l16(s, 1) + l16(s, 2) + l16(s, 3) + l16(s, 4) + l16(s, 5) + l16(s, 6) + l16(s, 7),
{
    proof {
        lemma_sum8(u16s(n8(s)));
    }
    vaddlvq_u16(s)
}

/// The sum of the lanes of two vectors, right whenever it is small.
#[inline(always)]
fn total2(a: uint8x16_t, b: uint8x16_t) -> (t: u32)
    requires
        neon(),
    ensures
        t <= 65534 ==> t == l16(a, 0) + l16(a, 1) + l16(a, 2) + l16(a, 3) + l16(a, 4) + l16(a, 5) + l16(a, 6) + l16(a, 7)
            + l16(b, 0) + l16(b, 1) + l16(b, 2) + l16(b, 3) + l16(b, 4) + l16(b, 5) + l16(b, 6) + l16(b, 7),
{
    let s = vqaddq_u16(a, b);
    let t = total(s);
    proof {
        assert forall|j: int| 0 <= j < 8 implies #[trigger] l16(s, j) == (if l16(a, j) + l16(b, j) > 0xffff {
            0xffff
        } else {
            l16(a, j) + l16(b, j)
        }) by {}
        assert(l16(s, 0) >= 0 && l16(s, 1) >= 0 && l16(s, 2) >= 0 && l16(s, 3) >= 0 && l16(s, 4) >= 0 && l16(s, 5) >= 0
            && l16(s, 6) >= 0 && l16(s, 7) >= 0);
    }
    t
}

proof fn lemma_acol_nonneg(dq: Seq<int>, j: int)
    ensures
        acol(dq, j) >= 0,
{
}

/// A column's sum is at most the block's.
proof fn lemma_acol_le(dq: Seq<int>, j: int)
    requires
        0 <= j < 8,
    ensures
        0 <= acol(dq, j) <= atot(dq),
{
    hide(acol);
    lemma_acol_nonneg(dq, 0);
    lemma_acol_nonneg(dq, 1);
    lemma_acol_nonneg(dq, 2);
    lemma_acol_nonneg(dq, 3);
    lemma_acol_nonneg(dq, 4);
    lemma_acol_nonneg(dq, 5);
    lemma_acol_nonneg(dq, 6);
    lemma_acol_nonneg(dq, 7);
}

/// The first pass's results in column `j` are bounded by the column's sum
/// of magnitudes, and fit 16 bits when the guard holds.
proof fn lemma_ws_bound(dq: Seq<int>, j: int, r: int)
    requires
        dq.len() == 64,
        0 <= j < 8,
        0 <= r < 8,
        acol(dq, j) <= tot_max(),
    ensures
        -11363 * acol(dq, j) <= idct_1d(dcol(dq, j))[r] <= 11363 * acol(dq, j),
        idct_col(dq, j, r) == descale(idct_1d(dcol(dq, j))[r], 11),
        -((11363 * acol(dq, j)) / 2048 + 1) <= idct_col(dq, j, r) <= (11363 * acol(dq, j)) / 2048 + 1,
{
    hide(idct_1d);
    let c = dcol(dq, j);
    assert(c =~= seq![dq[j], dq[8 + j], dq[16 + j], dq[24 + j], dq[32 + j], dq[40 + j], dq[48 + j], dq[56 + j]]);
    lemma_pass_wbound(
        dq[j],
        dq[8 + j],
        dq[16 + j],
        dq[24 + j],
        dq[32 + j],
        dq[40 + j],
        dq[48 + j],
        dq[56 + j],
        iabs(dq[j]),
        iabs(dq[8 + j]),
        iabs(dq[16 + j]),
        iabs(dq[24 + j]),
        iabs(dq[32 + j]),
        iabs(dq[40 + j]),
        iabs(dq[48 + j]),
        iabs(dq[56 + j]),
    );
    vstd::arithmetic::power2::lemma2_to64();
    let p = idct_1d(c)[r];
    assert(descale(p, 11) == (p + 1024) / 2048);
    assert(idct_col(dq, j, r) == wrap32(descale(idct_1d(c)[r], 11)));
}

/// Every result of the first pass is small.
pub open spec fn wsmall(dq: Seq<int>) -> bool {
    forall|j: int, r: int| 0 <= j < 8 && 0 <= r < 8 ==> -11764 <= #[trigger] idct_col(dq, j, r) <= 11764
}

proof fn lemma_wsmall(dq: Seq<int>)
    requires
        dq.len() == 64,
        atot(dq) <= tot_max(),
    ensures
        wsmall(dq),
{
    hide(idct_col);
    hide(idct_1d);
    hide(acol);
    hide(atot);
    assert forall|j: int, r: int| 0 <= j < 8 && 0 <= r < 8 implies -11764 <= #[trigger] idct_col(dq, j, r) <= 11764 by {
        lemma_acol_le(dq, j);
        lemma_ws_bound(dq, j, r);
    }
}

/// The second pass's results, with the rounding added, are inside 28 bits:
/// the sample is inside the ten bits the range limit reads.
proof fn lemma_ex_bound(dq: Seq<int>, r: int, k: int)
    requires
        dq.len() == 64,
        0 <= r < 8,
        0 <= k < 8,
        atot(dq) <= tot_max(),
    ensures
        -0x800_0000 <= idct_1d(rowv(dq, r))[k] + 131072 < 0x800_0000,
{
    hide(idct_col);
    hide(idct_1d);
    hide(acol);
    lemma_acol_le(dq, 0);
    lemma_acol_le(dq, 1);
    lemma_acol_le(dq, 2);
    lemma_acol_le(dq, 3);
    lemma_acol_le(dq, 4);
    lemma_acol_le(dq, 5);
    lemma_acol_le(dq, 6);
    lemma_acol_le(dq, 7);
    lemma_ws_bound(dq, 0, r);
    lemma_ws_bound(dq, 1, r);
    lemma_ws_bound(dq, 2, r);
    lemma_ws_bound(dq, 3, r);
    lemma_ws_bound(dq, 4, r);
    lemma_ws_bound(dq, 5, r);
    lemma_ws_bound(dq, 6, r);
    lemma_ws_bound(dq, 7, r);
    let b0 = (11363 * acol(dq, 0)) / 2048 + 1;
    let b1 = (11363 * acol(dq, 1)) / 2048 + 1;
    let b2 = (11363 * acol(dq, 2)) / 2048 + 1;
    let b3 = (11363 * acol(dq, 3)) / 2048 + 1;
    let b4 = (11363 * acol(dq, 4)) / 2048 + 1;
    let b5 = (11363 * acol(dq, 5)) / 2048 + 1;
    let b6 = (11363 * acol(dq, 6)) / 2048 + 1;
    let b7 = (11363 * acol(dq, 7)) / 2048 + 1;
    assert(rowv(dq, r) =~= seq![
        idct_col(dq, 0, r),
        idct_col(dq, 1, r),
        idct_col(dq, 2, r),
        idct_col(dq, 3, r),
        idct_col(dq, 4, r),
        idct_col(dq, 5, r),
        idct_col(dq, 6, r),
        idct_col(dq, 7, r),
    ]);
    assert(b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 <= 11770);
    lemma_pass_wbound(
        idct_col(dq, 0, r),
        idct_col(dq, 1, r),
        idct_col(dq, 2, r),
        idct_col(dq, 3, r),
        idct_col(dq, 4, r),
        idct_col(dq, 5, r),
        idct_col(dq, 6, r),
        idct_col(dq, 7, r),
        b0,
        b1,
        b2,
        b3,
        b4,
        b5,
        b6,
        b7,
    );
}

/// The first pass's shift of one lane, cut to 16 bits: exact, because the
/// pass was and the result fits.
proof fn lemma_nar_lane(a: u32, g: int, w: u16)
    requires
        cong(a as int, g),
        -0x7000_0000 <= g <= 0x7000_0000,
        w as int == ((s32(a) + 1024) / 2048) % 0x1_0000,
        -32768 <= descale(g, 11) <= 32767,
    ensures
        s16(w) == descale(g, 11),
{
    vstd::arithmetic::power2::lemma2_to64();
    let k = (a - g) / 0x1_0000_0000;
    assert(a - g == 0x1_0000_0000 * k);
    assert(s32(a) == g);
    assert(descale(g, 11) == (g + 1024) / 2048);
}

// ---------------------------------------------------------------------------
// The first pass's narrowing
// ---------------------------------------------------------------------------

/// `pc16` for the first pass: the inputs are the rows of the block.
pub open spec fn pd16(v: uint8x16_t, dq: Seq<int>, off: int, k: int) -> bool {
    pc16(v, dr(dq, 0), dr(dq, 1), dr(dq, 2), dr(dq, 3), dr(dq, 4), dr(dq, 5), dr(dq, 6), dr(dq, 7), off, k)
}

/// The lanes of the rows, read down a column, are the column.
proof fn lemma_dcol(dq: Seq<int>, j: int)
    requires
        0 <= j < 8,
    ensures
        col(dr(dq, 0), dr(dq, 1), dr(dq, 2), dr(dq, 3), dr(dq, 4), dr(dq, 5), dr(dq, 6), dr(dq, 7), j) =~= dcol(dq, j),
{
}

/// The two halves of output `k` of the first pass, narrowed: row `k` of
/// the workspace, exactly.
proof fn lemma_nar1(lo: uint8x16_t, hi: uint8x16_t, w: uint8x16_t, dq: Seq<int>, k: int)
    requires
        dq.len() == 64,
        0 <= k < 8,
        atot(dq) <= tot_max(),
        pd16(lo, dq, 0, k),
        pd16(hi, dq, 4, k),
        u16s(n8(w)) == rshrn_s32(u32s(n8(lo)), 11) + rshrn_s32(u32s(n8(hi)), 11),
    ensures
        x16(w, rowv(dq, k)),
{
    hide(idct_1d);
    hide(idct_col);
    hide(cong);
    hide(acol);
    hide(atot);
    reveal_with_fuel(pow2_spec, 12);
    assert forall|j: int| 0 <= j < 8 implies #[trigger] s16l(w, j) == rowv(dq, k)[j] by {
        lemma_dcol(dq, j);
        lemma_acol_le(dq, j);
        lemma_ws_bound(dq, j, k);
        let g = idct_1d(dcol(dq, j))[k];
        if j < 4 {
            assert(cong(l32(lo, j), idct_1d(col(dr(dq, 0), dr(dq, 1), dr(dq, 2), dr(dq, 3), dr(dq, 4), dr(dq, 5), dr(dq, 6), dr(dq, 7), 0 + j))[k]));
            assert(u16s(n8(w))[j] == rshrn_s32(u32s(n8(lo)), 11)[j]);
            lemma_nar_lane(u32s(n8(lo))[j], g, u16s(n8(w))[j]);
        } else {
            assert(cong(l32(hi, j - 4), idct_1d(col(dr(dq, 0), dr(dq, 1), dr(dq, 2), dr(dq, 3), dr(dq, 4), dr(dq, 5), dr(dq, 6), dr(dq, 7), 4 + (j - 4)))[k]));
            assert(u16s(n8(w))[j] == rshrn_s32(u32s(n8(hi)), 11)[j - 4]);
            lemma_nar_lane(u32s(n8(hi))[j - 4], g, u16s(n8(w))[j]);
        }
    }
}

/// The same when columns 4 to 7 of the block are zero: only the low half
/// was computed, and the high half of the row is zero.
proof fn lemma_nar1_lo(lo: uint8x16_t, w: uint8x16_t, dq: Seq<int>, k: int)
    requires
        dq.len() == 64,
        0 <= k < 8,
        atot(dq) <= tot_max(),
        hz(dq),
        pd16(lo, dq, 0, k),
        u16s(n8(w)) == rshrn_s32(u32s(n8(lo)), 11) + splat16(0, 4),
    ensures
        x16(w, rowv(dq, k)),
{
    hide(idct_1d);
    hide(idct_col);
    hide(cong);
    hide(acol);
    hide(atot);
    hide(hz);
    reveal_with_fuel(pow2_spec, 12);
    assert forall|j: int| 0 <= j < 8 implies #[trigger] s16l(w, j) == rowv(dq, k)[j] by {
        if j < 4 {
            lemma_dcol(dq, j);
            lemma_acol_le(dq, j);
            lemma_ws_bound(dq, j, k);
            let g = idct_1d(dcol(dq, j))[k];
            assert(cong(l32(lo, j), idct_1d(col(dr(dq, 0), dr(dq, 1), dr(dq, 2), dr(dq, 3), dr(dq, 4), dr(dq, 5), dr(dq, 6), dr(dq, 7), 0 + j))[k]));
            assert(u16s(n8(w))[j] == rshrn_s32(u32s(n8(lo)), 11)[j]);
            lemma_nar_lane(u32s(n8(lo))[j], g, u16s(n8(w))[j]);
        } else {
            let jo: int = if k < 4 {
                0
            } else {
                4
            };
            lemma_uc_zero(dq, j, jo);
            assert(uc(dq, j, jo)[k - jo] == 0);
            assert(u16s(n8(w))[j] == splat16(0, 4)[j - 4]);
        }
    }
}

/// The first pass's eight results narrowed to the workspace's rows.
#[inline(always)]
fn nar8(lo: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t), hi: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t), Ghost(dq): Ghost<Seq<int>>) -> (w: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t))
    requires
        neon(),
        dq.len() == 64,
        atot(dq) <= tot_max(),
        pd16(lo.0, dq, 0, 0),
        pd16(lo.1, dq, 0, 1),
        pd16(lo.2, dq, 0, 2),
        pd16(lo.3, dq, 0, 3),
        pd16(lo.4, dq, 0, 4),
        pd16(lo.5, dq, 0, 5),
        pd16(lo.6, dq, 0, 6),
        pd16(lo.7, dq, 0, 7),
        pd16(hi.0, dq, 4, 0),
        pd16(hi.1, dq, 4, 1),
        pd16(hi.2, dq, 4, 2),
        pd16(hi.3, dq, 4, 3),
        pd16(hi.4, dq, 4, 4),
        pd16(hi.5, dq, 4, 5),
        pd16(hi.6, dq, 4, 6),
        pd16(hi.7, dq, 4, 7),
    ensures
        x16(w.0, rowv(dq, 0)),
        x16(w.1, rowv(dq, 1)),
        x16(w.2, rowv(dq, 2)),
        x16(w.3, rowv(dq, 3)),
        x16(w.4, rowv(dq, 4)),
        x16(w.5, rowv(dq, 5)),
        x16(w.6, rowv(dq, 6)),
        x16(w.7, rowv(dq, 7)),
{
    let w0 = vrshrn2_n_s32::<11>(lo.0, hi.0);
    let w1 = vrshrn2_n_s32::<11>(lo.1, hi.1);
    let w2 = vrshrn2_n_s32::<11>(lo.2, hi.2);
    let w3 = vrshrn2_n_s32::<11>(lo.3, hi.3);
    let w4 = vrshrn2_n_s32::<11>(lo.4, hi.4);
    let w5 = vrshrn2_n_s32::<11>(lo.5, hi.5);
    let w6 = vrshrn2_n_s32::<11>(lo.6, hi.6);
    let w7 = vrshrn2_n_s32::<11>(lo.7, hi.7);
    proof {
        lemma_nar1(lo.0, hi.0, w0, dq, 0);
        lemma_nar1(lo.1, hi.1, w1, dq, 1);
        lemma_nar1(lo.2, hi.2, w2, dq, 2);
        lemma_nar1(lo.3, hi.3, w3, dq, 3);
        lemma_nar1(lo.4, hi.4, w4, dq, 4);
        lemma_nar1(lo.5, hi.5, w5, dq, 5);
        lemma_nar1(lo.6, hi.6, w6, dq, 6);
        lemma_nar1(lo.7, hi.7, w7, dq, 7);
    }
    (w0, w1, w2, w3, w4, w5, w6, w7)
}

/// The same from the low half alone, for a block whose columns 4 to 7 are
/// zero.
#[inline(always)]
fn nar8_lo(lo: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t), Ghost(dq): Ghost<Seq<int>>) -> (w: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t))
    requires
        neon(),
        dq.len() == 64,
        atot(dq) <= tot_max(),
        hz(dq),
        pd16(lo.0, dq, 0, 0),
        pd16(lo.1, dq, 0, 1),
        pd16(lo.2, dq, 0, 2),
        pd16(lo.3, dq, 0, 3),
        pd16(lo.4, dq, 0, 4),
        pd16(lo.5, dq, 0, 5),
        pd16(lo.6, dq, 0, 6),
        pd16(lo.7, dq, 0, 7),
    ensures
        x16(w.0, rowv(dq, 0)),
        x16(w.1, rowv(dq, 1)),
        x16(w.2, rowv(dq, 2)),
        x16(w.3, rowv(dq, 3)),
        x16(w.4, rowv(dq, 4)),
        x16(w.5, rowv(dq, 5)),
        x16(w.6, rowv(dq, 6)),
        x16(w.7, rowv(dq, 7)),
{
    let w0 = vrshrn_lo_n_s32::<11>(lo.0);
    let w1 = vrshrn_lo_n_s32::<11>(lo.1);
    let w2 = vrshrn_lo_n_s32::<11>(lo.2);
    let w3 = vrshrn_lo_n_s32::<11>(lo.3);
    let w4 = vrshrn_lo_n_s32::<11>(lo.4);
    let w5 = vrshrn_lo_n_s32::<11>(lo.5);
    let w6 = vrshrn_lo_n_s32::<11>(lo.6);
    let w7 = vrshrn_lo_n_s32::<11>(lo.7);
    proof {
        lemma_nar1_lo(lo.0, w0, dq, 0);
        lemma_nar1_lo(lo.1, w1, dq, 1);
        lemma_nar1_lo(lo.2, w2, dq, 2);
        lemma_nar1_lo(lo.3, w3, dq, 3);
        lemma_nar1_lo(lo.4, w4, dq, 4);
        lemma_nar1_lo(lo.5, w5, dq, 5);
        lemma_nar1_lo(lo.6, w6, dq, 6);
        lemma_nar1_lo(lo.7, w7, dq, 7);
    }
    (w0, w1, w2, w3, w4, w5, w6, w7)
}

// ---------------------------------------------------------------------------
// The transpose between the passes
// ---------------------------------------------------------------------------

/// The 16-bit lanes of a 32-bit interleave.
proof fn lemma_z32_16(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>, hi: bool)
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
            &&& u16s(r)[0] == u16s(a)[o] && u16s(r)[1] == u16s(a)[o + 1]
            &&& u16s(r)[2] == u16s(b)[o] && u16s(r)[3] == u16s(b)[o + 1]
            &&& u16s(r)[4] == u16s(a)[o + 2] && u16s(r)[5] == u16s(a)[o + 3]
            &&& u16s(r)[6] == u16s(b)[o + 2] && u16s(r)[7] == u16s(b)[o + 3]
        }),
{
    let k: int = if hi {
        2
    } else {
        0
    };
    assert(u32s(r)[0] == u32s(a)[k] && u32s(r)[1] == u32s(b)[k] && u32s(r)[2] == u32s(a)[k + 1] && u32s(r)[3] == u32s(
        b,
    )[k + 1]);
    lemma_u16s_of_u32s(r);
    lemma_u16s_of_u32s(a);
    lemma_u16s_of_u32s(b);
    assert(u16s(r)[2 * 0int] == (u32s(r)[0] & 0xffff) as u16 && u16s(r)[2 * 1int] == (u32s(r)[1] & 0xffff) as u16);
    assert(u16s(r)[2 * 2int] == (u32s(r)[2] & 0xffff) as u16 && u16s(r)[2 * 3int] == (u32s(r)[3] & 0xffff) as u16);
    assert(u16s(a)[2 * k] == (u32s(a)[k] & 0xffff) as u16 && u16s(a)[2 * (k + 1)] == (u32s(a)[k + 1] & 0xffff) as u16);
    assert(u16s(b)[2 * k] == (u32s(b)[k] & 0xffff) as u16 && u16s(b)[2 * (k + 1)] == (u32s(b)[k + 1] & 0xffff) as u16);
}

/// The 16-bit lanes of a 64-bit interleave.
proof fn lemma_z64_16(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>, hi: bool)
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
            &&& u16s(r)[0] == u16s(a)[o] && u16s(r)[1] == u16s(a)[o + 1]
            &&& u16s(r)[2] == u16s(a)[o + 2] && u16s(r)[3] == u16s(a)[o + 3]
            &&& u16s(r)[4] == u16s(b)[o] && u16s(r)[5] == u16s(b)[o + 1]
            &&& u16s(r)[6] == u16s(b)[o + 2] && u16s(r)[7] == u16s(b)[o + 3]
        }),
{
    let k: int = if hi {
        2
    } else {
        0
    };
    lemma_zip64(a, b, r, hi);
    lemma_u16s_of_u32s(r);
    lemma_u16s_of_u32s(a);
    lemma_u16s_of_u32s(b);
    assert(u16s(r)[2 * 0int] == (u32s(r)[0] & 0xffff) as u16 && u16s(r)[2 * 1int] == (u32s(r)[1] & 0xffff) as u16);
    assert(u16s(r)[2 * 2int] == (u32s(r)[2] & 0xffff) as u16 && u16s(r)[2 * 3int] == (u32s(r)[3] & 0xffff) as u16);
    assert(u16s(a)[2 * k] == (u32s(a)[k] & 0xffff) as u16 && u16s(a)[2 * (k + 1)] == (u32s(a)[k + 1] & 0xffff) as u16);
    assert(u16s(b)[2 * k] == (u32s(b)[k] & 0xffff) as u16 && u16s(b)[2 * (k + 1)] == (u32s(b)[k + 1] & 0xffff) as u16);
}

/// `v` holds 16-bit lane `k` of each of eight vectors.
pub open spec fn trc16(v: uint8x16_t, w0: uint8x16_t, w1: uint8x16_t, w2: uint8x16_t, w3: uint8x16_t, w4: uint8x16_t, w5: uint8x16_t, w6: uint8x16_t, w7: uint8x16_t, k: int) -> bool {
    u16s(n8(v))[0] == u16s(n8(w0))[k]
        && u16s(n8(v))[1] == u16s(n8(w1))[k]
        && u16s(n8(v))[2] == u16s(n8(w2))[k]
        && u16s(n8(v))[3] == u16s(n8(w3))[k]
        && u16s(n8(v))[4] == u16s(n8(w4))[k]
        && u16s(n8(v))[5] == u16s(n8(w5))[k]
        && u16s(n8(v))[6] == u16s(n8(w6))[k]
        && u16s(n8(v))[7] == u16s(n8(w7))[k]
}

/// Eight vectors of eight 16-bit lanes, transposed.
#[inline(always)]
fn tr8(w0: uint8x16_t, w1: uint8x16_t, w2: uint8x16_t, w3: uint8x16_t, w4: uint8x16_t, w5: uint8x16_t, w6: uint8x16_t, w7: uint8x16_t) -> (x: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t))
    requires
        neon(),
    ensures
        trc16(x.0, w0, w1, w2, w3, w4, w5, w6, w7, 0),
        trc16(x.1, w0, w1, w2, w3, w4, w5, w6, w7, 1),
        trc16(x.2, w0, w1, w2, w3, w4, w5, w6, w7, 2),
        trc16(x.3, w0, w1, w2, w3, w4, w5, w6, w7, 3),
        trc16(x.4, w0, w1, w2, w3, w4, w5, w6, w7, 4),
        trc16(x.5, w0, w1, w2, w3, w4, w5, w6, w7, 5),
        trc16(x.6, w0, w1, w2, w3, w4, w5, w6, w7, 6),
        trc16(x.7, w0, w1, w2, w3, w4, w5, w6, w7, 7),
{
    let a0 = vzip1q_u16(w0, w1);
    let a1 = vzip2q_u16(w0, w1);
    let b0 = vzip1q_u16(w2, w3);
    let b1 = vzip2q_u16(w2, w3);
    let c0 = vzip1q_u16(w4, w5);
    let c1 = vzip2q_u16(w4, w5);
    let d0 = vzip1q_u16(w6, w7);
    let d1 = vzip2q_u16(w6, w7);
    let e0 = vzip1q_u32(a0, b0);
    let e1 = vzip2q_u32(a0, b0);
    let e2 = vzip1q_u32(a1, b1);
    let e3 = vzip2q_u32(a1, b1);
    let f0 = vzip1q_u32(c0, d0);
    let f1 = vzip2q_u32(c0, d0);
    let f2 = vzip1q_u32(c1, d1);
    let f3 = vzip2q_u32(c1, d1);
    let x0 = vzip1q_u64(e0, f0);
    let x1 = vzip2q_u64(e0, f0);
    let x2 = vzip1q_u64(e1, f1);
    let x3 = vzip2q_u64(e1, f1);
    let x4 = vzip1q_u64(e2, f2);
    let x5 = vzip2q_u64(e2, f2);
    let x6 = vzip1q_u64(e3, f3);
    let x7 = vzip2q_u64(e3, f3);
    proof {
        assert(u16s(n8(a0))[0] == u16s(n8(w0))[0] && u16s(n8(a0))[1] == u16s(n8(w1))[0] && u16s(n8(a0))[2] == u16s(n8(w0))[1] && u16s(n8(a0))[3] == u16s(n8(w1))[1] && u16s(n8(a0))[4] == u16s(n8(w0))[2] && u16s(n8(a0))[5] == u16s(n8(w1))[2] && u16s(n8(a0))[6] == u16s(n8(w0))[3] && u16s(n8(a0))[7] == u16s(n8(w1))[3]);
        assert(u16s(n8(a1))[0] == u16s(n8(w0))[4] && u16s(n8(a1))[1] == u16s(n8(w1))[4] && u16s(n8(a1))[2] == u16s(n8(w0))[5] && u16s(n8(a1))[3] == u16s(n8(w1))[5] && u16s(n8(a1))[4] == u16s(n8(w0))[6] && u16s(n8(a1))[5] == u16s(n8(w1))[6] && u16s(n8(a1))[6] == u16s(n8(w0))[7] && u16s(n8(a1))[7] == u16s(n8(w1))[7]);
        assert(u16s(n8(b0))[0] == u16s(n8(w2))[0] && u16s(n8(b0))[1] == u16s(n8(w3))[0] && u16s(n8(b0))[2] == u16s(n8(w2))[1] && u16s(n8(b0))[3] == u16s(n8(w3))[1] && u16s(n8(b0))[4] == u16s(n8(w2))[2] && u16s(n8(b0))[5] == u16s(n8(w3))[2] && u16s(n8(b0))[6] == u16s(n8(w2))[3] && u16s(n8(b0))[7] == u16s(n8(w3))[3]);
        assert(u16s(n8(b1))[0] == u16s(n8(w2))[4] && u16s(n8(b1))[1] == u16s(n8(w3))[4] && u16s(n8(b1))[2] == u16s(n8(w2))[5] && u16s(n8(b1))[3] == u16s(n8(w3))[5] && u16s(n8(b1))[4] == u16s(n8(w2))[6] && u16s(n8(b1))[5] == u16s(n8(w3))[6] && u16s(n8(b1))[6] == u16s(n8(w2))[7] && u16s(n8(b1))[7] == u16s(n8(w3))[7]);
        assert(u16s(n8(c0))[0] == u16s(n8(w4))[0] && u16s(n8(c0))[1] == u16s(n8(w5))[0] && u16s(n8(c0))[2] == u16s(n8(w4))[1] && u16s(n8(c0))[3] == u16s(n8(w5))[1] && u16s(n8(c0))[4] == u16s(n8(w4))[2] && u16s(n8(c0))[5] == u16s(n8(w5))[2] && u16s(n8(c0))[6] == u16s(n8(w4))[3] && u16s(n8(c0))[7] == u16s(n8(w5))[3]);
        assert(u16s(n8(c1))[0] == u16s(n8(w4))[4] && u16s(n8(c1))[1] == u16s(n8(w5))[4] && u16s(n8(c1))[2] == u16s(n8(w4))[5] && u16s(n8(c1))[3] == u16s(n8(w5))[5] && u16s(n8(c1))[4] == u16s(n8(w4))[6] && u16s(n8(c1))[5] == u16s(n8(w5))[6] && u16s(n8(c1))[6] == u16s(n8(w4))[7] && u16s(n8(c1))[7] == u16s(n8(w5))[7]);
        assert(u16s(n8(d0))[0] == u16s(n8(w6))[0] && u16s(n8(d0))[1] == u16s(n8(w7))[0] && u16s(n8(d0))[2] == u16s(n8(w6))[1] && u16s(n8(d0))[3] == u16s(n8(w7))[1] && u16s(n8(d0))[4] == u16s(n8(w6))[2] && u16s(n8(d0))[5] == u16s(n8(w7))[2] && u16s(n8(d0))[6] == u16s(n8(w6))[3] && u16s(n8(d0))[7] == u16s(n8(w7))[3]);
        assert(u16s(n8(d1))[0] == u16s(n8(w6))[4] && u16s(n8(d1))[1] == u16s(n8(w7))[4] && u16s(n8(d1))[2] == u16s(n8(w6))[5] && u16s(n8(d1))[3] == u16s(n8(w7))[5] && u16s(n8(d1))[4] == u16s(n8(w6))[6] && u16s(n8(d1))[5] == u16s(n8(w7))[6] && u16s(n8(d1))[6] == u16s(n8(w6))[7] && u16s(n8(d1))[7] == u16s(n8(w7))[7]);
        lemma_z32_16(n8(a0), n8(b0), n8(e0), false);
        lemma_z32_16(n8(a0), n8(b0), n8(e1), true);
        lemma_z32_16(n8(a1), n8(b1), n8(e2), false);
        lemma_z32_16(n8(a1), n8(b1), n8(e3), true);
        lemma_z32_16(n8(c0), n8(d0), n8(f0), false);
        lemma_z32_16(n8(c0), n8(d0), n8(f1), true);
        lemma_z32_16(n8(c1), n8(d1), n8(f2), false);
        lemma_z32_16(n8(c1), n8(d1), n8(f3), true);
        lemma_z64_16(n8(e0), n8(f0), n8(x0), false);
        lemma_z64_16(n8(e0), n8(f0), n8(x1), true);
        lemma_z64_16(n8(e1), n8(f1), n8(x2), false);
        lemma_z64_16(n8(e1), n8(f1), n8(x3), true);
        lemma_z64_16(n8(e2), n8(f2), n8(x4), false);
        lemma_z64_16(n8(e2), n8(f2), n8(x5), true);
        lemma_z64_16(n8(e3), n8(f3), n8(x6), false);
        lemma_z64_16(n8(e3), n8(f3), n8(x7), true);
    }
    (x0, x1, x2, x3, x4, x5, x6, x7)
}

/// Column `k` of the workspace.
pub open spec fn wsc(dq: Seq<int>, k: int) -> Seq<int> {
    Seq::new(8, |r: int| idct_col(dq, k, r))
}

/// A transposed vector holds a column of the workspace.
proof fn lemma_tr_x16(x: uint8x16_t, w0: uint8x16_t, w1: uint8x16_t, w2: uint8x16_t, w3: uint8x16_t, w4: uint8x16_t, w5: uint8x16_t, w6: uint8x16_t, w7: uint8x16_t, dq: Seq<int>, k: int)
    requires
        0 <= k < 8,
        trc16(x, w0, w1, w2, w3, w4, w5, w6, w7, k),
        x16(w0, rowv(dq, 0)),
        x16(w1, rowv(dq, 1)),
        x16(w2, rowv(dq, 2)),
        x16(w3, rowv(dq, 3)),
        x16(w4, rowv(dq, 4)),
        x16(w5, rowv(dq, 5)),
        x16(w6, rowv(dq, 6)),
        x16(w7, rowv(dq, 7)),
    ensures
        x16(x, wsc(dq, k)),
{
    hide(idct_col);
    assert forall|r: int| 0 <= r < 8 implies #[trigger] s16l(x, r) == wsc(dq, k)[r] by {
        if r == 0 {
            assert(s16l(w0, k) == rowv(dq, 0)[k]);
        }
        if r == 1 {
            assert(s16l(w1, k) == rowv(dq, 1)[k]);
        }
        if r == 2 {
            assert(s16l(w2, k) == rowv(dq, 2)[k]);
        }
        if r == 3 {
            assert(s16l(w3, k) == rowv(dq, 3)[k]);
        }
        if r == 4 {
            assert(s16l(w4, k) == rowv(dq, 4)[k]);
        }
        if r == 5 {
            assert(s16l(w5, k) == rowv(dq, 5)[k]);
        }
        if r == 6 {
            assert(s16l(w6, k) == rowv(dq, 6)[k]);
        }
        if r == 7 {
            assert(s16l(w7, k) == rowv(dq, 7)[k]);
        }
    }
}

// ---------------------------------------------------------------------------
// The second pass
// ---------------------------------------------------------------------------

/// A pass over a row of the workspace with 16 added to its first value is
/// the second pass's result plus the rounding.
proof fn lemma_p2_lane(dq: Seq<int>, r: int, k: int)
    requires
        0 <= r < 8,
        0 <= k < 8,
    ensures
        idct_1d(col(sh16(wsc(dq, 0)), wsc(dq, 1), wsc(dq, 2), wsc(dq, 3), wsc(dq, 4), wsc(dq, 5), wsc(dq, 6), wsc(dq, 7), r))[k] == idct_1d(rowv(dq, r))[k] + 131072,
{
    hide(idct_1d);
    hide(idct_col);
    lemma_pass_shift16(idct_col(dq, 0, r), idct_col(dq, 1, r), idct_col(dq, 2, r), idct_col(dq, 3, r), idct_col(dq, 4, r), idct_col(dq, 5, r), idct_col(dq, 6, r), idct_col(dq, 7, r));
    assert(col(sh16(wsc(dq, 0)), wsc(dq, 1), wsc(dq, 2), wsc(dq, 3), wsc(dq, 4), wsc(dq, 5), wsc(dq, 6), wsc(dq, 7), r) =~= seq![idct_col(dq, 0, r) + 16, idct_col(dq, 1, r), idct_col(dq, 2, r), idct_col(dq, 3, r), idct_col(dq, 4, r), idct_col(dq, 5, r), idct_col(dq, 6, r), idct_col(dq, 7, r)]);
    assert(rowv(dq, r) =~= seq![idct_col(dq, 0, r), idct_col(dq, 1, r), idct_col(dq, 2, r), idct_col(dq, 3, r), idct_col(dq, 4, r), idct_col(dq, 5, r), idct_col(dq, 6, r), idct_col(dq, 7, r)]);
}

/// A result of the pass over the workspace's columns, as the second pass's
/// result with the rounding added.
proof fn lemma_p2_lcf(v: uint8x16_t, dq: Seq<int>, off: int, k: int)
    requires
        0 <= k < 8,
        off == 0 || off == 4,
        pc16(v, sh16(wsc(dq, 0)), wsc(dq, 1), wsc(dq, 2), wsc(dq, 3), wsc(dq, 4), wsc(dq, 5), wsc(dq, 6), wsc(dq, 7), off, k),
    ensures
        lcf(v, ex(dq, k, off)),
{
    hide(cong);
    hide(idct_1d);
    hide(idct_col);
    assert forall|i: int| 0 <= i < 4 implies cong(#[trigger] l32(v, i), ex(dq, k, off)[i] + 131072) by {
        lemma_p2_lane(dq, off + i, k);
        assert(cong(l32(v, i), idct_1d(col(sh16(wsc(dq, 0)), wsc(dq, 1), wsc(dq, 2), wsc(dq, 3), wsc(dq, 4), wsc(dq, 5), wsc(dq, 6), wsc(dq, 7), off + i))[k]));
    }
}

/// A column of a small workspace is small.
proof fn lemma_wsc_in8(dq: Seq<int>, k: int, b: int)
    requires
        0 <= k < 8,
        wsmall(dq),
        b >= 11764,
    ensures
        in8(wsc(dq, k), b),
{
    hide(idct_col);
    assert forall|i: int| 0 <= i < 8 implies -b <= #[trigger] wsc(dq, k)[i] <= b by {
        assert(-11764 <= idct_col(dq, k, i) <= 11764);
    }
}

/// Columns 4 to 7 of the workspace are zero when the block's are.
proof fn lemma_wsc_zero(dq: Seq<int>, k: int)
    requires
        dq.len() == 64,
        hz(dq),
        4 <= k < 8,
    ensures
        zero8(wsc(dq, k)),
{
    hide(idct_col);
    hide(hz);
    lemma_uc_zero(dq, k, 0);
    lemma_uc_zero(dq, k, 4);
    assert forall|i: int| 0 <= i < 8 implies #[trigger] wsc(dq, k)[i] == 0 by {
        if i < 4 {
            assert(uc(dq, k, 0)[i] == 0);
        } else {
            assert(uc(dq, k, 4)[i - 4] == 0);
        }
    }
}

/// The second pass over the workspace's columns: every result with the
/// rounding added, the low four rows and the high four.
#[inline(always)]
fn p2_full(x0: uint8x16_t, x1: uint8x16_t, x2: uint8x16_t, x3: uint8x16_t, x4: uint8x16_t, x5: uint8x16_t, x6: uint8x16_t, x7: uint8x16_t, k0: uint8x16_t, k1: uint8x16_t, k2: uint8x16_t, Ghost(dq): Ghost<Seq<int>>) -> (r: ((uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t), (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t)))
    requires
        neon(),
        kok(k0, k1, k2),
        wsmall(dq),
        x16(x0, wsc(dq, 0)),
        x16(x1, wsc(dq, 1)),
        x16(x2, wsc(dq, 2)),
        x16(x3, wsc(dq, 3)),
        x16(x4, wsc(dq, 4)),
        x16(x5, wsc(dq, 5)),
        x16(x6, wsc(dq, 6)),
        x16(x7, wsc(dq, 7)),
    ensures
        lcf(r.0.0, ex(dq, 0, 0)),
        lcf(r.0.1, ex(dq, 1, 0)),
        lcf(r.0.2, ex(dq, 2, 0)),
        lcf(r.0.3, ex(dq, 3, 0)),
        lcf(r.0.4, ex(dq, 4, 0)),
        lcf(r.0.5, ex(dq, 5, 0)),
        lcf(r.0.6, ex(dq, 6, 0)),
        lcf(r.0.7, ex(dq, 7, 0)),
        lcf(r.1.0, ex(dq, 0, 4)),
        lcf(r.1.1, ex(dq, 1, 4)),
        lcf(r.1.2, ex(dq, 2, 4)),
        lcf(r.1.3, ex(dq, 3, 4)),
        lcf(r.1.4, ex(dq, 4, 4)),
        lcf(r.1.5, ex(dq, 5, 4)),
        lcf(r.1.6, ex(dq, 6, 4)),
        lcf(r.1.7, ex(dq, 7, 4)),
{
    hide(idct_1d);
    hide(idct_col);
    hide(cong);
    hide(lcf);
    hide(pc16);
    hide(wsmall);
    hide(kok);
    proof {
        lemma_wsc_in8(dq, 0, 16000);
        lemma_wsc_in8(dq, 1, 16383);
        lemma_wsc_in8(dq, 2, 16383);
        lemma_wsc_in8(dq, 3, 16383);
        lemma_wsc_in8(dq, 4, 16383);
        lemma_wsc_in8(dq, 5, 16383);
        lemma_wsc_in8(dq, 6, 16383);
        lemma_wsc_in8(dq, 7, 16383);
    }
    let y0 = addk16(x0, Ghost(wsc(dq, 0)));
    let pe = add16x(y0, x4, Ghost(sh16(wsc(dq, 0))), Ghost(wsc(dq, 4)));
    let pd = sub16x(y0, x4, Ghost(sh16(wsc(dq, 0))), Ghost(wsc(dq, 4)));
    let pz3 = add16x(x7, x3, Ghost(wsc(dq, 7)), Ghost(wsc(dq, 3)));
    let pz4 = add16x(x5, x1, Ghost(wsc(dq, 5)), Ghost(wsc(dq, 1)));
    let lo = vp16_lo(y0, x1, x2, x3, x4, x5, x6, x7, pe, pd, pz3, pz4, k0, k1, k2, Ghost(sh16(wsc(dq, 0))), Ghost(wsc(dq, 1)), Ghost(wsc(dq, 2)), Ghost(wsc(dq, 3)), Ghost(wsc(dq, 4)), Ghost(wsc(dq, 5)), Ghost(wsc(dq, 6)), Ghost(wsc(dq, 7)));
    let hi = vp16_hi(y0, x1, x2, x3, x4, x5, x6, x7, pe, pd, pz3, pz4, k0, k1, k2, Ghost(sh16(wsc(dq, 0))), Ghost(wsc(dq, 1)), Ghost(wsc(dq, 2)), Ghost(wsc(dq, 3)), Ghost(wsc(dq, 4)), Ghost(wsc(dq, 5)), Ghost(wsc(dq, 6)), Ghost(wsc(dq, 7)));
    proof {
        reveal(pc16);
        lemma_p2_lcf(lo.0, dq, 0, 0);
        lemma_p2_lcf(lo.1, dq, 0, 1);
        lemma_p2_lcf(lo.2, dq, 0, 2);
        lemma_p2_lcf(lo.3, dq, 0, 3);
        lemma_p2_lcf(lo.4, dq, 0, 4);
        lemma_p2_lcf(lo.5, dq, 0, 5);
        lemma_p2_lcf(lo.6, dq, 0, 6);
        lemma_p2_lcf(lo.7, dq, 0, 7);
        lemma_p2_lcf(hi.0, dq, 4, 0);
        lemma_p2_lcf(hi.1, dq, 4, 1);
        lemma_p2_lcf(hi.2, dq, 4, 2);
        lemma_p2_lcf(hi.3, dq, 4, 3);
        lemma_p2_lcf(hi.4, dq, 4, 4);
        lemma_p2_lcf(hi.5, dq, 4, 5);
        lemma_p2_lcf(hi.6, dq, 4, 6);
        lemma_p2_lcf(hi.7, dq, 4, 7);
    }
    (lo, hi)
}

/// The second pass when columns 4 to 7 of the block, and so of the
/// workspace, are zero.
#[inline(always)]
fn p2_sparse(x0: uint8x16_t, x1: uint8x16_t, x2: uint8x16_t, x3: uint8x16_t, k0: uint8x16_t, k1: uint8x16_t, k2: uint8x16_t, Ghost(dq): Ghost<Seq<int>>) -> (r: ((uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t), (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t)))
    requires
        neon(),
        kok(k0, k1, k2),
        wsmall(dq),
        dq.len() == 64,
        hz(dq),
        x16(x0, wsc(dq, 0)),
        x16(x1, wsc(dq, 1)),
        x16(x2, wsc(dq, 2)),
        x16(x3, wsc(dq, 3)),
    ensures
        lcf(r.0.0, ex(dq, 0, 0)),
        lcf(r.0.1, ex(dq, 1, 0)),
        lcf(r.0.2, ex(dq, 2, 0)),
        lcf(r.0.3, ex(dq, 3, 0)),
        lcf(r.0.4, ex(dq, 4, 0)),
        lcf(r.0.5, ex(dq, 5, 0)),
        lcf(r.0.6, ex(dq, 6, 0)),
        lcf(r.0.7, ex(dq, 7, 0)),
        lcf(r.1.0, ex(dq, 0, 4)),
        lcf(r.1.1, ex(dq, 1, 4)),
        lcf(r.1.2, ex(dq, 2, 4)),
        lcf(r.1.3, ex(dq, 3, 4)),
        lcf(r.1.4, ex(dq, 4, 4)),
        lcf(r.1.5, ex(dq, 5, 4)),
        lcf(r.1.6, ex(dq, 6, 4)),
        lcf(r.1.7, ex(dq, 7, 4)),
{
    hide(idct_1d);
    hide(idct_col);
    hide(cong);
    hide(lcf);
    hide(pc16);
    hide(wsmall);
    hide(kok);
    hide(hz);
    proof {
        lemma_wsc_in8(dq, 0, 16000);
        lemma_wsc_zero(dq, 4);
        lemma_wsc_zero(dq, 5);
        lemma_wsc_zero(dq, 6);
        lemma_wsc_zero(dq, 7);
    }
    let y0 = addk16(x0, Ghost(wsc(dq, 0)));
    let lo = vp16s_lo(y0, x1, x2, x3, k0, k1, k2, Ghost(sh16(wsc(dq, 0))), Ghost(wsc(dq, 1)), Ghost(wsc(dq, 2)), Ghost(wsc(dq, 3)), Ghost(wsc(dq, 4)), Ghost(wsc(dq, 5)), Ghost(wsc(dq, 6)), Ghost(wsc(dq, 7)));
    let hi = vp16s_hi(y0, x1, x2, x3, k0, k1, k2, Ghost(sh16(wsc(dq, 0))), Ghost(wsc(dq, 1)), Ghost(wsc(dq, 2)), Ghost(wsc(dq, 3)), Ghost(wsc(dq, 4)), Ghost(wsc(dq, 5)), Ghost(wsc(dq, 6)), Ghost(wsc(dq, 7)));
    proof {
        reveal(pc16);
        lemma_p2_lcf(lo.0, dq, 0, 0);
        lemma_p2_lcf(lo.1, dq, 0, 1);
        lemma_p2_lcf(lo.2, dq, 0, 2);
        lemma_p2_lcf(lo.3, dq, 0, 3);
        lemma_p2_lcf(lo.4, dq, 0, 4);
        lemma_p2_lcf(lo.5, dq, 0, 5);
        lemma_p2_lcf(lo.6, dq, 0, 6);
        lemma_p2_lcf(lo.7, dq, 0, 7);
        lemma_p2_lcf(hi.0, dq, 4, 0);
        lemma_p2_lcf(hi.1, dq, 4, 1);
        lemma_p2_lcf(hi.2, dq, 4, 2);
        lemma_p2_lcf(hi.3, dq, 4, 3);
        lemma_p2_lcf(hi.4, dq, 4, 4);
        lemma_p2_lcf(hi.5, dq, 4, 5);
        lemma_p2_lcf(hi.6, dq, 4, 6);
        lemma_p2_lcf(hi.7, dq, 4, 7);
    }
    (lo, hi)
}

// ---------------------------------------------------------------------------
// The second pass's shift and range limit
// ---------------------------------------------------------------------------

/// Four second-pass results that, with the rounding, are inside 28 bits.
pub open spec fn fit27(t: Seq<int>) -> bool {
    forall|i: int| 0 <= i < 4 ==> -0x800_0000 <= #[trigger] t[i] + 131072 < 0x800_0000
}

/// One lane from the second pass's sum, which holds the rounding, through
/// its high half, the narrowing shift that saturates to a signed byte and
/// the flip of the sign bit: the range limit of the exact value. The value
/// is inside the ten bits the range limit reads, so saturating is the
/// same as the limit's table.
proof fn lemma_fin16_lane(u: u32, t: int, h: u16, g: u16, b: u8, z: u8)
    requires
        cong(u as int, t + 131072),
        -0x800_0000 <= t + 131072 < 0x800_0000,
        h == (u >> 16u32) as u16,
        g as int == (s16(h) / 4) % 0x10000,
        b as int == sat_s8(s16(g)) % 256,
        z == b ^ 128u8,
    ensures
        z == rl18(t),
{
    vstd::arithmetic::power2::lemma2_to64();
    let v = t + 131072;
    let k = (u - v) / 0x1_0000_0000;
    assert(u - v == 0x1_0000_0000 * k);
    assert(s32(u) == v);
    assert(h as u32 == u / 65536u32) by (bit_vector)
        requires
            h == (u >> 16u32) as u16,
    ;
    assert(s16(h) == v / 65536);
    let d = v / 262144;
    assert(s16(h) / 4 == d);
    assert(-512 <= d <= 511);
    assert(descale(t, 18) == d);
    assert(s16(g) == d);
    assert(z == (if b < 128 {
        b + 128
    } else {
        b - 128
    }) as u8) by (bit_vector)
        requires
            z == b ^ 128u8,
    ;
}

/// Sixteen samples from the two halves of two columns' second-pass sums.
#[inline(always)]
fn finpair16(la: uint8x16_t, ha: uint8x16_t, lb: uint8x16_t, hb: uint8x16_t, Ghost(ta): Ghost<Seq<int>>, Ghost(tb): Ghost<Seq<int>>, Ghost(tc): Ghost<Seq<int>>, Ghost(td): Ghost<Seq<int>>) -> (r: uint8x16_t)
    requires
        neon(),
        lcf(la, ta),
        lcf(ha, tb),
        lcf(lb, tc),
        lcf(hb, td),
        fit27(ta),
        fit27(tb),
        fit27(tc),
        fit27(td),
    ensures
        forall|j: int| 0 <= j < 16 ==> #[trigger] n8(r)[j] == rl18(sel4(ta, tb, tc, td, j)),
{
    hide(cong);
    hide(rl18);
    let h1 = vuzp2q_u16(la, ha);
    let h2 = vuzp2q_u16(lb, hb);
    let p = vqshrn2_n_s16::<2>(h1, h2);
    let r = veorq_u8(p, vdupq_n_u8(128));
    proof {
        reveal_with_fuel(pow2_spec, 4);
        let g1 = srai16(u16s(n8(h1)), 2);
        let g2 = srai16(u16s(n8(h2)), 2);
        lemma_u16s_of_u32s(n8(la));
        lemma_u16s_of_u32s(n8(ha));
        lemma_u16s_of_u32s(n8(lb));
        lemma_u16s_of_u32s(n8(hb));
        assert forall|j: int| 0 <= j < 16 implies #[trigger] n8(r)[j] == rl18(sel4(ta, tb, tc, td, j)) by {
            assert(n8(r)[j] == n8(p)[j] ^ 128u8);
            if j < 4 {
                assert(u16s(n8(la))[2 * j] == (u32s(n8(la))[j] & 0xffff) as u16);
                assert(cong(l32(la, j), ta[j] + 131072));
                lemma_fin16_lane(u32s(n8(la))[j], ta[j], u16s(n8(h1))[j], g1[j], n8(p)[j], n8(r)[j]);
            } else if j < 8 {
                assert(u16s(n8(ha))[2 * (j - 4)] == (u32s(n8(ha))[j - 4] & 0xffff) as u16);
                assert(cong(l32(ha, j - 4), tb[j - 4] + 131072));
                lemma_fin16_lane(u32s(n8(ha))[j - 4], tb[j - 4], u16s(n8(h1))[j], g1[j], n8(p)[j], n8(r)[j]);
            } else if j < 12 {
                assert(u16s(n8(lb))[2 * (j - 8)] == (u32s(n8(lb))[j - 8] & 0xffff) as u16);
                assert(cong(l32(lb, j - 8), tc[j - 8] + 131072));
                lemma_fin16_lane(u32s(n8(lb))[j - 8], tc[j - 8], u16s(n8(h2))[j - 8], g2[j - 8], n8(p)[j], n8(r)[j]);
            } else {
                assert(u16s(n8(hb))[2 * (j - 12)] == (u32s(n8(hb))[j - 12] & 0xffff) as u16);
                assert(cong(l32(hb, j - 12), td[j - 12] + 131072));
                lemma_fin16_lane(u32s(n8(hb))[j - 12], td[j - 12], u16s(n8(h2))[j - 8], g2[j - 8], n8(p)[j], n8(r)[j]);
            }
        }
    }
    r
}

// ---------------------------------------------------------------------------
// The whole transform
// ---------------------------------------------------------------------------

/// The second pass's sums, shifted, limited and stored.
#[inline(always)]
fn fin16(lo: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t), hi: (uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t, uint8x16_t), out: &mut [u8], row0: usize, col0: usize, stride: usize, Ghost(dq): Ghost<Seq<int>>) -> (blk: Ghost<Seq<u8>>)
    requires
        neon(),
        dq.len() == 64,
        atot(dq) <= tot_max(),
        col0 + 8 <= stride,
        (row0 + 8) * stride <= old(out)@.len(),
        lcf(lo.0, ex(dq, 0, 0)),
        lcf(lo.1, ex(dq, 1, 0)),
        lcf(lo.2, ex(dq, 2, 0)),
        lcf(lo.3, ex(dq, 3, 0)),
        lcf(lo.4, ex(dq, 4, 0)),
        lcf(lo.5, ex(dq, 5, 0)),
        lcf(lo.6, ex(dq, 6, 0)),
        lcf(lo.7, ex(dq, 7, 0)),
        lcf(hi.0, ex(dq, 0, 4)),
        lcf(hi.1, ex(dq, 1, 4)),
        lcf(hi.2, ex(dq, 2, 4)),
        lcf(hi.3, ex(dq, 3, 4)),
        lcf(hi.4, ex(dq, 4, 4)),
        lcf(hi.5, ex(dq, 5, 4)),
        lcf(hi.6, ex(dq, 6, 4)),
        lcf(hi.7, ex(dq, 7, 4)),
    ensures
        final(out)@.len() == old(out)@.len(),
        blk@.len() == 64,
        forall|k: int| 0 <= k < 64 ==> (#[trigger] blk@[k]) == idct(dq, k / 8, k % 8),
        forall|j: int|
            0 <= j < final(out)@.len() ==> (#[trigger] final(out)@[j]) == if in_rows(j, stride as int, row0 as int, col0 as int, 8) {
                blk@[8 * (j / (stride as int) - row0) + (j % (stride as int) - col0)]
            } else {
                old(out)@[j]
            },
{
    hide(idct_1d);
    hide(idct_col);
    hide(idct);
    hide(lcf);
    hide(acol);
    hide(atot);
    proof {
        assert forall|k: int, jo: int| 0 <= k < 8 && (jo == 0 || jo == 4) implies fit27(#[trigger] ex(dq, k, jo)) by {
            assert forall|i: int| 0 <= i < 4 implies -0x800_0000 <= #[trigger] ex(dq, k, jo)[i] + 131072 < 0x800_0000 by {
                lemma_ex_bound(dq, jo + i, k);
            }
        }
        assert(fit27(ex(dq, 0, 0)) && fit27(ex(dq, 0, 4)));
        assert(fit27(ex(dq, 1, 0)) && fit27(ex(dq, 1, 4)));
        assert(fit27(ex(dq, 2, 0)) && fit27(ex(dq, 2, 4)));
        assert(fit27(ex(dq, 3, 0)) && fit27(ex(dq, 3, 4)));
        assert(fit27(ex(dq, 4, 0)) && fit27(ex(dq, 4, 4)));
        assert(fit27(ex(dq, 5, 0)) && fit27(ex(dq, 5, 4)));
        assert(fit27(ex(dq, 6, 0)) && fit27(ex(dq, 6, 4)));
        assert(fit27(ex(dq, 7, 0)) && fit27(ex(dq, 7, 4)));
    }
    let r0 = finpair16(lo.0, hi.0, lo.4, hi.4, Ghost(ex(dq, 0, 0)), Ghost(ex(dq, 0, 4)), Ghost(ex(dq, 4, 0)), Ghost(ex(dq, 4, 4)));
    let r1 = finpair16(lo.1, hi.1, lo.5, hi.5, Ghost(ex(dq, 1, 0)), Ghost(ex(dq, 1, 4)), Ghost(ex(dq, 5, 0)), Ghost(ex(dq, 5, 4)));
    let r2 = finpair16(lo.2, hi.2, lo.6, hi.6, Ghost(ex(dq, 2, 0)), Ghost(ex(dq, 2, 4)), Ghost(ex(dq, 6, 0)), Ghost(ex(dq, 6, 4)));
    let r3 = finpair16(lo.3, hi.3, lo.7, hi.7, Ghost(ex(dq, 3, 0)), Ghost(ex(dq, 3, 4)), Ghost(ex(dq, 7, 0)), Ghost(ex(dq, 7, 4)));
    emit_rows(r0, r1, r2, r3, out, row0, col0, stride, Ghost(dq))
}

/// A block with values everywhere: both passes in full.
#[inline(always)]
fn run_full(d0: uint8x16_t, d1: uint8x16_t, d2: uint8x16_t, d3: uint8x16_t, d4: uint8x16_t, d5: uint8x16_t, d6: uint8x16_t, d7: uint8x16_t, k0: uint8x16_t, k1: uint8x16_t, k2: uint8x16_t, out: &mut [u8], row0: usize, col0: usize, stride: usize, Ghost(dq): Ghost<Seq<int>>) -> (blk: Ghost<Seq<u8>>)
    requires
        neon(),
        dq.len() == 64,
        atot(dq) <= tot_max(),
        kok(k0, k1, k2),
        col0 + 8 <= stride,
        (row0 + 8) * stride <= old(out)@.len(),
        x16(d0, dr(dq, 0)),
        in8(dr(dq, 0), 16383),
        x16(d1, dr(dq, 1)),
        in8(dr(dq, 1), 16383),
        x16(d2, dr(dq, 2)),
        in8(dr(dq, 2), 16383),
        x16(d3, dr(dq, 3)),
        in8(dr(dq, 3), 16383),
        x16(d4, dr(dq, 4)),
        in8(dr(dq, 4), 16383),
        x16(d5, dr(dq, 5)),
        in8(dr(dq, 5), 16383),
        x16(d6, dr(dq, 6)),
        in8(dr(dq, 6), 16383),
        x16(d7, dr(dq, 7)),
        in8(dr(dq, 7), 16383),
    ensures
        final(out)@.len() == old(out)@.len(),
        blk@.len() == 64,
        forall|k: int| 0 <= k < 64 ==> (#[trigger] blk@[k]) == idct(dq, k / 8, k % 8),
        forall|j: int|
            0 <= j < final(out)@.len() ==> (#[trigger] final(out)@[j]) == if in_rows(j, stride as int, row0 as int, col0 as int, 8) {
                blk@[8 * (j / (stride as int) - row0) + (j % (stride as int) - col0)]
            } else {
                old(out)@[j]
            },
{
    hide(idct_1d);
    hide(idct_col);
    hide(idct);
    hide(cong);
    hide(lcf);
    hide(pc16);
    hide(wsmall);
    hide(kok);
    hide(acol);
    hide(atot);
    hide(trc16);
    hide(x16);
    hide(in8);
    hide(zero8);
    proof {
        reveal(in8);
    }
    let pe = add16x(d0, d4, Ghost(dr(dq, 0)), Ghost(dr(dq, 4)));
    let pd = sub16x(d0, d4, Ghost(dr(dq, 0)), Ghost(dr(dq, 4)));
    let pz3 = add16x(d7, d3, Ghost(dr(dq, 7)), Ghost(dr(dq, 3)));
    let pz4 = add16x(d5, d1, Ghost(dr(dq, 5)), Ghost(dr(dq, 1)));
    let lo = vp16_lo(d0, d1, d2, d3, d4, d5, d6, d7, pe, pd, pz3, pz4, k0, k1, k2, Ghost(dr(dq, 0)), Ghost(dr(dq, 1)), Ghost(dr(dq, 2)), Ghost(dr(dq, 3)), Ghost(dr(dq, 4)), Ghost(dr(dq, 5)), Ghost(dr(dq, 6)), Ghost(dr(dq, 7)));
    let hi = vp16_hi(d0, d1, d2, d3, d4, d5, d6, d7, pe, pd, pz3, pz4, k0, k1, k2, Ghost(dr(dq, 0)), Ghost(dr(dq, 1)), Ghost(dr(dq, 2)), Ghost(dr(dq, 3)), Ghost(dr(dq, 4)), Ghost(dr(dq, 5)), Ghost(dr(dq, 6)), Ghost(dr(dq, 7)));
    let w = nar8(lo, hi, Ghost(dq));
    let x = tr8(w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7);
    proof {
        reveal(x16);
        reveal(trc16);
        lemma_tr_x16(x.0, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 0);
        lemma_tr_x16(x.1, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 1);
        lemma_tr_x16(x.2, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 2);
        lemma_tr_x16(x.3, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 3);
        lemma_tr_x16(x.4, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 4);
        lemma_tr_x16(x.5, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 5);
        lemma_tr_x16(x.6, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 6);
        lemma_tr_x16(x.7, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 7);
        lemma_wsmall(dq);
    }
    let (lo2, hi2) = p2_full(x.0, x.1, x.2, x.3, x.4, x.5, x.6, x.7, k0, k1, k2, Ghost(dq));
    fin16(lo2, hi2, out, row0, col0, stride, Ghost(dq))
}

/// A block whose rows 4 to 7 are zero: the first pass is the short one.
#[inline(always)]
fn run_rows(d0: uint8x16_t, d1: uint8x16_t, d2: uint8x16_t, d3: uint8x16_t, k0: uint8x16_t, k1: uint8x16_t, k2: uint8x16_t, out: &mut [u8], row0: usize, col0: usize, stride: usize, Ghost(dq): Ghost<Seq<int>>) -> (blk: Ghost<Seq<u8>>)
    requires
        neon(),
        dq.len() == 64,
        atot(dq) <= tot_max(),
        kok(k0, k1, k2),
        zero8(dr(dq, 4)),
        zero8(dr(dq, 5)),
        zero8(dr(dq, 6)),
        zero8(dr(dq, 7)),
        col0 + 8 <= stride,
        (row0 + 8) * stride <= old(out)@.len(),
        x16(d0, dr(dq, 0)),
        in8(dr(dq, 0), 16383),
        x16(d1, dr(dq, 1)),
        in8(dr(dq, 1), 16383),
        x16(d2, dr(dq, 2)),
        in8(dr(dq, 2), 16383),
        x16(d3, dr(dq, 3)),
        in8(dr(dq, 3), 16383),
    ensures
        final(out)@.len() == old(out)@.len(),
        blk@.len() == 64,
        forall|k: int| 0 <= k < 64 ==> (#[trigger] blk@[k]) == idct(dq, k / 8, k % 8),
        forall|j: int|
            0 <= j < final(out)@.len() ==> (#[trigger] final(out)@[j]) == if in_rows(j, stride as int, row0 as int, col0 as int, 8) {
                blk@[8 * (j / (stride as int) - row0) + (j % (stride as int) - col0)]
            } else {
                old(out)@[j]
            },
{
    hide(idct_1d);
    hide(idct_col);
    hide(idct);
    hide(cong);
    hide(lcf);
    hide(pc16);
    hide(wsmall);
    hide(kok);
    hide(acol);
    hide(atot);
    hide(trc16);
    hide(x16);
    hide(in8);
    hide(zero8);
    let lo = vp16s_lo(d0, d1, d2, d3, k0, k1, k2, Ghost(dr(dq, 0)), Ghost(dr(dq, 1)), Ghost(dr(dq, 2)), Ghost(dr(dq, 3)), Ghost(dr(dq, 4)), Ghost(dr(dq, 5)), Ghost(dr(dq, 6)), Ghost(dr(dq, 7)));
    let hi = vp16s_hi(d0, d1, d2, d3, k0, k1, k2, Ghost(dr(dq, 0)), Ghost(dr(dq, 1)), Ghost(dr(dq, 2)), Ghost(dr(dq, 3)), Ghost(dr(dq, 4)), Ghost(dr(dq, 5)), Ghost(dr(dq, 6)), Ghost(dr(dq, 7)));
    let w = nar8(lo, hi, Ghost(dq));
    let x = tr8(w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7);
    proof {
        reveal(x16);
        reveal(trc16);
        lemma_tr_x16(x.0, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 0);
        lemma_tr_x16(x.1, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 1);
        lemma_tr_x16(x.2, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 2);
        lemma_tr_x16(x.3, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 3);
        lemma_tr_x16(x.4, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 4);
        lemma_tr_x16(x.5, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 5);
        lemma_tr_x16(x.6, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 6);
        lemma_tr_x16(x.7, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 7);
        lemma_wsmall(dq);
    }
    let (lo2, hi2) = p2_full(x.0, x.1, x.2, x.3, x.4, x.5, x.6, x.7, k0, k1, k2, Ghost(dq));
    fin16(lo2, hi2, out, row0, col0, stride, Ghost(dq))
}

/// A block whose rows 4 to 7 and columns 4 to 7 are zero, which is most
/// blocks: half the columns go through the first pass, and both passes are
/// the short ones.
#[inline(always)]
fn run_corner(d0: uint8x16_t, d1: uint8x16_t, d2: uint8x16_t, d3: uint8x16_t, k0: uint8x16_t, k1: uint8x16_t, k2: uint8x16_t, out: &mut [u8], row0: usize, col0: usize, stride: usize, Ghost(dq): Ghost<Seq<int>>) -> (blk: Ghost<Seq<u8>>)
    requires
        neon(),
        dq.len() == 64,
        atot(dq) <= tot_max(),
        kok(k0, k1, k2),
        hz(dq),
        zero8(dr(dq, 4)),
        zero8(dr(dq, 5)),
        zero8(dr(dq, 6)),
        zero8(dr(dq, 7)),
        col0 + 8 <= stride,
        (row0 + 8) * stride <= old(out)@.len(),
        x16(d0, dr(dq, 0)),
        in8(dr(dq, 0), 16383),
        x16(d1, dr(dq, 1)),
        in8(dr(dq, 1), 16383),
        x16(d2, dr(dq, 2)),
        in8(dr(dq, 2), 16383),
        x16(d3, dr(dq, 3)),
        in8(dr(dq, 3), 16383),
    ensures
        final(out)@.len() == old(out)@.len(),
        blk@.len() == 64,
        forall|k: int| 0 <= k < 64 ==> (#[trigger] blk@[k]) == idct(dq, k / 8, k % 8),
        forall|j: int|
            0 <= j < final(out)@.len() ==> (#[trigger] final(out)@[j]) == if in_rows(j, stride as int, row0 as int, col0 as int, 8) {
                blk@[8 * (j / (stride as int) - row0) + (j % (stride as int) - col0)]
            } else {
                old(out)@[j]
            },
{
    hide(idct_1d);
    hide(idct_col);
    hide(idct);
    hide(cong);
    hide(lcf);
    hide(pc16);
    hide(wsmall);
    hide(kok);
    hide(acol);
    hide(atot);
    hide(trc16);
    hide(x16);
    hide(in8);
    hide(zero8);
    hide(hz);
    let lo = vp16s_lo(d0, d1, d2, d3, k0, k1, k2, Ghost(dr(dq, 0)), Ghost(dr(dq, 1)), Ghost(dr(dq, 2)), Ghost(dr(dq, 3)), Ghost(dr(dq, 4)), Ghost(dr(dq, 5)), Ghost(dr(dq, 6)), Ghost(dr(dq, 7)));
    let w = nar8_lo(lo, Ghost(dq));
    let x = tr8(w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7);
    proof {
        reveal(x16);
        reveal(trc16);
        lemma_tr_x16(x.0, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 0);
        lemma_tr_x16(x.1, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 1);
        lemma_tr_x16(x.2, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 2);
        lemma_tr_x16(x.3, w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, dq, 3);
        lemma_wsmall(dq);
    }
    let (lo2, hi2) = p2_sparse(x.0, x.1, x.2, x.3, k0, k1, k2, Ghost(dq));
    fin16(lo2, hi2, out, row0, col0, stride, Ghost(dq))
}

/// The block's total from the column sums of its rows.
proof fn lemma_atot(dq: Seq<int>, slo: uint8x16_t, shi: uint8x16_t, full: bool)
    requires
        forall|j: int| 0 <= j < 8 ==> #[trigger] l16(slo, j) == iabs(dr(dq, 0)[j]) + iabs(dr(dq, 1)[j]) + iabs(dr(dq, 2)[j]) + iabs(dr(dq, 3)[j]),
        full ==> forall|j: int| 0 <= j < 8 ==> #[trigger] l16(shi, j) == iabs(dr(dq, 4)[j]) + iabs(dr(dq, 5)[j]) + iabs(dr(dq, 6)[j]) + iabs(dr(dq, 7)[j]),
        !full ==> zero8(dr(dq, 4)) && zero8(dr(dq, 5)) && zero8(dr(dq, 6)) && zero8(dr(dq, 7)),
    ensures
        atot(dq) == l16(slo, 0) + l16(slo, 1) + l16(slo, 2) + l16(slo, 3) + l16(slo, 4) + l16(slo, 5) + l16(slo, 6) + l16(slo, 7) + (if full {
            l16(shi, 0) + l16(shi, 1) + l16(shi, 2) + l16(shi, 3) + l16(shi, 4) + l16(shi, 5) + l16(shi, 6) + l16(shi, 7)
        } else {
            0
        }),
{
    assert forall|j: int| 0 <= j < 8 implies acol(dq, j) == l16(slo, j) + (if full {
        l16(shi, j)
    } else {
        0
    }) by {
        assert(dr(dq, 0)[j] == dq[8 * 0 + j] && dr(dq, 1)[j] == dq[8 * 1 + j] && dr(dq, 2)[j] == dq[8 * 2 + j] && dr(dq, 3)[j] == dq[8 * 3 + j]);
        assert(dr(dq, 4)[j] == dq[8 * 4 + j] && dr(dq, 5)[j] == dq[8 * 5 + j] && dr(dq, 6)[j] == dq[8 * 6 + j] && dr(dq, 7)[j] == dq[8 * 7 + j]);
    }
}

/// A zero 32-bit lane is two zero 16-bit lanes.
proof fn lemma_pair_zero(b: Seq<u8>, k: int)
    requires
        b.len() == 16,
        0 <= k < 4,
        u32s(b)[k] == 0,
    ensures
        u16s(b)[2 * k] == 0,
        u16s(b)[2 * k + 1] == 0,
{
    lemma_u16s_of_u32s(b);
    assert(u16s(b)[2 * k] == (u32s(b)[k] & 0xffff) as u16 && u16s(b)[2 * k + 1] == (u32s(b)[k] >> 16u32) as u16);
    assert((0u32 & 0xffff) as u16 == 0 && (0u32 >> 16u32) as u16 == 0) by (bit_vector);
}

/// The high 64 bits of a vector are zero: so are its 16-bit lanes 4 to 7.
proof fn lemma_hi64_zero(b: Seq<u8>)
    requires
        b.len() == 16,
        u64s(b)[1] == 0,
    ensures
        forall|i: int| 4 <= i < 8 ==> #[trigger] u16s(b)[i] == 0,
{
    let a0 = u32s(b)[2];
    let a1 = u32s(b)[3];
    assert(u64s(b)[1] == le64(u32s(b)[2 * 1int], u32s(b)[2 * 1int + 1]));
    assert(((a0 as u64) | ((a1 as u64) << 32u64)) == 0 ==> a0 == 0 && a1 == 0) by (bit_vector);
    assert(a0 == 0 && a1 == 0);
    lemma_pair_zero(b, 2);
    lemma_pair_zero(b, 3);
}

/// The block of coefficients at `o`, dequantized by `q` and transformed in
/// 16-bit lanes, when the block is small enough for that, which nearly
/// every block of a photograph is. Returns 0 when it stored the 8 by 8
/// block at row `row0`, column `col0` of the plane `out`, and the ghost
/// result is that block. Otherwise `out` is untouched: 1 is a hint that
/// the block has nothing but its first coefficient, and 2 says that it
/// has more and was not shown to be small.
#[inline(always)]
pub fn idct16_neon(a: &[i16], o: usize, q: &[u16; 64], kt: &[i16; 24], out: &mut [u8], row0: usize, col0: usize, stride: usize) -> (r: (u8, Ghost<Seq<u8>>))
    requires
        neon(),
        kt@ == kt_spec(),
        o + 64 <= a@.len(),
        col0 + 8 <= stride,
        (row0 + 8) * stride <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        r.0 != 0 ==> final(out)@ == old(out)@,
        r.0 == 0 ==> {
            &&& r.1@.len() == 64
            &&& forall|k: int| 0 <= k < 64 ==> (#[trigger] r.1@[k]) == idct(dequant(a@, o as int, q@), k / 8, k % 8)
            &&& forall|j: int|
                0 <= j < final(out)@.len() ==> (#[trigger] final(out)@[j]) == if in_rows(j, stride as int, row0 as int, col0 as int, 8) {
                    r.1@[8 * (j / (stride as int) - row0) + (j % (stride as int) - col0)]
                } else {
                    old(out)@[j]
                }
        },
{
    hide(idct_1d);
    hide(idct_col);
    hide(idct);
    hide(dequant);
    hide(kok);
    hide(acol);
    hide(atot);
    hide(x16);
    hide(in8);
    hide(zero8);
    hide(hz);
    let qs: &[u16] = q;
    let ghost dq = dequant(a@, o as int, q@);
    proof {
        reveal(dequant);
        assert(dq.len() == 64);
    }
    let (c0, q0) = load_row(a, o, qs, 0);
    let (c1, q1) = load_row(a, o, qs, 1);
    let (c2, q2) = load_row(a, o, qs, 2);
    let (c3, q3) = load_row(a, o, qs, 3);
    let (c4, q4) = load_row(a, o, qs, 4);
    let (c5, q5) = load_row(a, o, qs, 5);
    let (c6, q6) = load_row(a, o, qs, 6);
    let (c7, q7) = load_row(a, o, qs, 7);
    let b0 = vabsq_s16(c0);
    let b1 = vabsq_s16(c1);
    let b2 = vabsq_s16(c2);
    let b3 = vabsq_s16(c3);
    let b4 = vabsq_s16(c4);
    let b5 = vabsq_s16(c5);
    let b6 = vabsq_s16(c6);
    let b7 = vabsq_s16(c7);
    let n23 = vmaxq_u16(b2, b3);
    let n1 = vmaxq_u16(b1, n23);
    let glo = vmaxq_u16(b0, n1);
    let g45 = vmaxq_u16(b4, b5);
    let g67 = vmaxq_u16(b6, b7);
    let ghi = vmaxq_u16(g45, g67);
    let m = vmaxq_u16(glo, ghi);
    let mx = vmaxvq_u16(m);
    let mhi = vmaxvq_u16(ghi);
    let mq = max8(q0, q1, q2, q3, q4, q5, q6, q7);
    let hi64 = vgetq_lane_u64_1(glo);
    if mhi == 0 && hi64 == 0 {
        // Lane 0 of `n1` is column 0 of rows 1 to 3; the rest of the low
        // half of `glo` is columns 1 to 3 of rows 0 to 3.
        if ((vgetq_lane_u64_0(glo) >> 16) | (vgetq_lane_u64_0(n1) & 0xffff)) == 0 {
            return (1, Ghost(Seq::empty()));
        }
    }
    assert((mx as u32) * (mq as u32) <= 0xffff * 0xffff) by (nonlinear_arith)
        requires
            mx <= 0xffff,
            mq <= 0xffff,
    ;
    if (mx as u32) * (mq as u32) > 16383 {
        return (2, Ghost(Seq::empty()));
    }
    proof {
        assert forall|i: int| 0 <= i < 8 implies l16(b0, i) <= l16(glo, i) && l16(b1, i) <= l16(glo, i) && l16(b2, i) <= l16(glo, i) && l16(b3, i) <= l16(glo, i) && l16(glo, i) <= mx && l16(b4, i) <= mhi && l16(b5, i) <= mhi && l16(b6, i) <= mhi && l16(b7, i) <= mhi && mhi <= mx by {
            assert(l16(n23, i) >= l16(b2, i) && l16(n23, i) >= l16(b3, i));
            assert(l16(n1, i) >= l16(b1, i) && l16(n1, i) >= l16(n23, i));
            assert(l16(glo, i) >= l16(b0, i) && l16(glo, i) >= l16(n1, i));
            assert(l16(g45, i) >= l16(b4, i) && l16(g45, i) >= l16(b5, i));
            assert(l16(g67, i) >= l16(b6, i) && l16(g67, i) >= l16(b7, i));
            assert(l16(ghi, i) >= l16(g45, i) && l16(ghi, i) >= l16(g67, i));
            assert(l16(m, i) >= l16(glo, i) && l16(m, i) >= l16(ghi, i));
            assert(u16s(n8(m))[i] <= mx);
            assert(u16s(n8(ghi))[i] <= mhi);
            assert(exists|e: int| 0 <= e < 8 && u16s(n8(ghi))[e] == mhi);
            let e = choose|e: int| 0 <= e < 8 && u16s(n8(ghi))[e] == mhi;
            assert(l16(m, e) >= l16(ghi, e));
            assert(u16s(n8(m))[e] <= mx);
        }
        assert forall|i: int| 0 <= i < 8 implies ab16(#[trigger] l16(c0, i)) <= mx by {
            assert(l16(b0, i) <= mx);
        }
        assert forall|i: int| 0 <= i < 8 implies ab16(#[trigger] l16(c1, i)) <= mx by {
            assert(l16(b1, i) <= mx);
        }
        assert forall|i: int| 0 <= i < 8 implies ab16(#[trigger] l16(c2, i)) <= mx by {
            assert(l16(b2, i) <= mx);
        }
        assert forall|i: int| 0 <= i < 8 implies ab16(#[trigger] l16(c3, i)) <= mx by {
            assert(l16(b3, i) <= mx);
        }
        assert forall|i: int| 0 <= i < 8 implies ab16(#[trigger] l16(c4, i)) <= mx by {
            assert(l16(b4, i) <= mx);
        }
        assert forall|i: int| 0 <= i < 8 implies ab16(#[trigger] l16(c5, i)) <= mx by {
            assert(l16(b5, i) <= mx);
        }
        assert forall|i: int| 0 <= i < 8 implies ab16(#[trigger] l16(c6, i)) <= mx by {
            assert(l16(b6, i) <= mx);
        }
        assert forall|i: int| 0 <= i < 8 implies ab16(#[trigger] l16(c7, i)) <= mx by {
            assert(l16(b7, i) <= mx);
        }
    }
    let d0 = deq16(c0, q0, Ghost(a@), Ghost(o as int), Ghost(q@), Ghost(0int), Ghost(mx as int), Ghost(mq as int));
    let d1 = deq16(c1, q1, Ghost(a@), Ghost(o as int), Ghost(q@), Ghost(1int), Ghost(mx as int), Ghost(mq as int));
    let d2 = deq16(c2, q2, Ghost(a@), Ghost(o as int), Ghost(q@), Ghost(2int), Ghost(mx as int), Ghost(mq as int));
    let d3 = deq16(c3, q3, Ghost(a@), Ghost(o as int), Ghost(q@), Ghost(3int), Ghost(mx as int), Ghost(mq as int));
    let slo = colsum4(d0, d1, d2, d3, Ghost(dr(dq, 0)), Ghost(dr(dq, 1)), Ghost(dr(dq, 2)), Ghost(dr(dq, 3)));
    let (k0, k1, k2) = kload(kt);
    if mhi == 0 {
        proof {
            assert forall|i: int| 0 <= i < 8 implies ab16(#[trigger] l16(c4, i)) <= 0 by {
                assert(l16(b4, i) <= mhi);
            }
            lemma_zero_row(c4, a@, o as int, q@, 4);
            assert forall|i: int| 0 <= i < 8 implies ab16(#[trigger] l16(c5, i)) <= 0 by {
                assert(l16(b5, i) <= mhi);
            }
            lemma_zero_row(c5, a@, o as int, q@, 5);
            assert forall|i: int| 0 <= i < 8 implies ab16(#[trigger] l16(c6, i)) <= 0 by {
                assert(l16(b6, i) <= mhi);
            }
            lemma_zero_row(c6, a@, o as int, q@, 6);
            assert forall|i: int| 0 <= i < 8 implies ab16(#[trigger] l16(c7, i)) <= 0 by {
                assert(l16(b7, i) <= mhi);
            }
            lemma_zero_row(c7, a@, o as int, q@, 7);
        }
        let t = total(slo);
        if t > 2120 {
            return (2, Ghost(Seq::empty()));
        }
        proof {
            lemma_atot(dq, slo, slo, false);
        }
        if hi64 == 0 {
            proof {
                lemma_hi64_zero(n8(glo));
                assert forall|x: int| 4 <= x < 8 implies ab16(#[trigger] l16(c0, x)) <= 0 by {
                    assert(l16(b0, x) <= l16(glo, x) && l16(glo, x) == 0);
                }
                assert forall|x: int| 4 <= x < 8 implies ab16(#[trigger] l16(c1, x)) <= 0 by {
                    assert(l16(b1, x) <= l16(glo, x) && l16(glo, x) == 0);
                }
                assert forall|x: int| 4 <= x < 8 implies ab16(#[trigger] l16(c2, x)) <= 0 by {
                    assert(l16(b2, x) <= l16(glo, x) && l16(glo, x) == 0);
                }
                assert forall|x: int| 4 <= x < 8 implies ab16(#[trigger] l16(c3, x)) <= 0 by {
                    assert(l16(b3, x) <= l16(glo, x) && l16(glo, x) == 0);
                }
                lemma_hz(a@, o as int, q@, c0, c1, c2, c3, c4, c5, c6, c7);
            }
            let blk = run_corner(d0, d1, d2, d3, k0, k1, k2, out, row0, col0, stride, Ghost(dq));
            (0, blk)
        } else {
            let blk = run_rows(d0, d1, d2, d3, k0, k1, k2, out, row0, col0, stride, Ghost(dq));
            (0, blk)
        }
    } else {
        let d4 = deq16(c4, q4, Ghost(a@), Ghost(o as int), Ghost(q@), Ghost(4int), Ghost(mx as int), Ghost(mq as int));
        let d5 = deq16(c5, q5, Ghost(a@), Ghost(o as int), Ghost(q@), Ghost(5int), Ghost(mx as int), Ghost(mq as int));
        let d6 = deq16(c6, q6, Ghost(a@), Ghost(o as int), Ghost(q@), Ghost(6int), Ghost(mx as int), Ghost(mq as int));
        let d7 = deq16(c7, q7, Ghost(a@), Ghost(o as int), Ghost(q@), Ghost(7int), Ghost(mx as int), Ghost(mq as int));
        let shi = colsum4(d4, d5, d6, d7, Ghost(dr(dq, 4)), Ghost(dr(dq, 5)), Ghost(dr(dq, 6)), Ghost(dr(dq, 7)));
        let t = total2(slo, shi);
        if t > 2120 {
            return (2, Ghost(Seq::empty()));
        }
        proof {
            lemma_atot(dq, slo, shi, true);
        }
        let blk = run_full(d0, d1, d2, d3, d4, d5, d6, d7, k0, k1, k2, out, row0, col0, stride, Ghost(dq));
        (0, blk)
    }
}

} // verus!

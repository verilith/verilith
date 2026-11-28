//! The encoder's arithmetic, proven equal to `enc_spec`: colour
//! conversion, the forward DCT, quantization and the quantization tables.
use crate::enc_spec::*;
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Colour conversion
// ---------------------------------------------------------------------------
/// One pixel's Y, Cb and Cr. Every numerator is at least 0 (Cb's and Cr's
/// offsets cover the negative terms exactly), so this is unsigned
/// arithmetic.
#[inline(always)]
pub fn ycc_x(r: u8, g: u8, b: u8) -> (o: (u8, u8, u8))
    ensures
        o.0 as int == ycc(r as int, g as int, b as int, 0),
        o.1 as int == ycc(r as int, g as int, b as int, 1),
        o.2 as int == ycc(r as int, g as int, b as int, 2),
{
    let r = r as u32;
    let g = g as u32;
    let b = b as u32;
    let ny = 19595 * r + 38470 * g + 7471 * b + 32768;
    let nb = (32768 * b + 8421375) - (11059 * r + 21709 * g);
    let nr = (32768 * r + 8421375) - (27439 * g + 5329 * b);
    proof {
        assert(ny <= 16777215);
        assert(nb <= 16777215);
        assert(nr <= 16777215);
        lemma_div_is_ordered(ny as int, 16777215, 65536);
        lemma_div_is_ordered(nb as int, 16777215, 65536);
        lemma_div_is_ordered(nr as int, 16777215, 65536);
        lemma_div_pos_is_pos(ny as int, 65536);
        lemma_div_pos_is_pos(nb as int, 65536);
        lemma_div_pos_is_pos(nr as int, 65536);
    }
    ((ny / 65536) as u8, (nb / 65536) as u8, (nr / 65536) as u8)
}

// ---------------------------------------------------------------------------
// The forward DCT
// ---------------------------------------------------------------------------
proof fn lemma_shr2(v: i64)
    ensures
        (v >> 2) == (v as int) / 4,
{
    let m = v & 3;
    let q = v >> 2;
    assert(0 <= m < 4 && v == q * 4 + m) by (bit_vector)
        requires
            m == v & 3,
            q == v >> 2,
    ;
    lemma_fundamental_div_mod_converse(v as int, 4, q as int, m as int);
}

proof fn lemma_shr11(v: i64)
    ensures
        (v >> 11) == (v as int) / 2048,
{
    let m = v & 2047;
    let q = v >> 11;
    assert(0 <= m < 2048 && v == q * 2048 + m) by (bit_vector)
        requires
            m == v & 2047,
            q == v >> 11,
    ;
    lemma_fundamental_div_mod_converse(v as int, 2048, q as int, m as int);
}

proof fn lemma_shr15(v: i64)
    ensures
        (v >> 15) == (v as int) / 32768,
{
    let m = v & 32767;
    let q = v >> 15;
    assert(0 <= m < 32768 && v == q * 32768 + m) by (bit_vector)
        requires
            m == v & 32767,
            q == v >> 15,
    ;
    lemma_fundamental_div_mod_converse(v as int, 32768, q as int, m as int);
}

pub open spec fn s8(d: [i64; 8]) -> Seq<int> {
    Seq::new(8, |i: int| d[i] as int)
}

pub open spec fn s64(d: [i64; 64]) -> Seq<int> {
    Seq::new(64, |i: int| d[i] as int)
}

/// `descale` by 11 or 15 in exec arithmetic.
#[inline(always)]
fn ds(x: i64, first: bool) -> (r: i64)
    requires
        -0x1_0000_0000_0000 < x < 0x1_0000_0000_0000,
    ensures
        r == descale(x as int, if first { 11 } else { 15 }),
        first && -0x200_0000 <= x <= 0x200_0000 ==> -16384 <= r <= 16384,
        !first && -0x4_0000_0000 <= x <= 0x4_0000_0000 ==> -0x10_0000 <= r <= 0x10_0000,
{
    proof {
        lemma2_to64();
    }
    if first {
        let v = x + 1024;
        proof {
            lemma_shr11(v);
            if -0x200_0000 <= x <= 0x200_0000 {
                lemma_div_is_ordered(v as int, 0x200_0000int + 1024, 2048);
                lemma_div_is_ordered(-0x200_0000 + 1024, v as int, 2048);
            }
        }
        v >> 11
    } else {
        let v = x + 16384;
        proof {
            lemma_shr15(v);
            if -0x4_0000_0000 <= x <= 0x4_0000_0000 {
                lemma_div_is_ordered(v as int, 0x4_0000_0000int + 16384, 32768);
                lemma_div_is_ordered(-0x4_0000_0000 + 16384, v as int, 32768);
            }
        }
        v >> 15
    }
}

/// One pass of `jpeg_fdct_islow`.
#[verifier::spinoff_prover]
#[verifier::rlimit(400)]
pub fn fdct8(d: [i64; 8], first: bool) -> (o: [i64; 8])
    requires
        forall|i: int|
            0 <= i < 8 ==> -(if first { 128int } else { 16384int }) <= #[trigger] d[i] <= (if first {
                128int
            } else {
                16384int
            }),
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] o[i] as int == fdct_1d(s8(d), first)[i],
        first ==> forall|i: int| 0 <= i < 8 ==> -16384 <= #[trigger] o[i] <= 16384,
        !first ==> forall|i: int| 0 <= i < 8 ==> -(1i64 << 20) <= #[trigger] o[i] <= (1i64 << 20),
{
    let ghost s = s8(d);
    reveal(fdct_1d);
    let tmp0 = d[0] + d[7];
    let tmp7 = d[0] - d[7];
    let tmp1 = d[1] + d[6];
    let tmp6 = d[1] - d[6];
    let tmp2 = d[2] + d[5];
    let tmp5 = d[2] - d[5];
    let tmp3 = d[3] + d[4];
    let tmp4 = d[3] - d[4];
    let tmp10 = tmp0 + tmp3;
    let tmp13 = tmp0 - tmp3;
    let tmp11 = tmp1 + tmp2;
    let tmp12 = tmp1 - tmp2;
    let o0;
    let o4;
    if first {
        o0 = 4 * (tmp10 + tmp11);
        o4 = 4 * (tmp10 - tmp11);
    } else {
        let a = tmp10 + tmp11 + 2;
        let b = tmp10 - tmp11 + 2;
        proof {
            lemma2_to64();
            lemma_shr2(a);
            lemma_shr2(b);
        }
        o0 = a >> 2;
        o4 = b >> 2;
    }
    let z1 = (tmp12 + tmp13) * 4433;
    let o2 = ds(z1 + tmp13 * 6270, first);
    let o6 = ds(z1 + tmp12 * (-15137), first);
    let y1 = tmp4 + tmp7;
    let y2 = tmp5 + tmp6;
    let y3 = tmp4 + tmp6;
    let y4 = tmp5 + tmp7;
    let z5 = (y3 + y4) * 9633;
    let t4 = tmp4 * 2446;
    let t5 = tmp5 * 16819;
    let t6 = tmp6 * 25172;
    let t7 = tmp7 * 12299;
    let w1 = y1 * (-7373);
    let w2 = y2 * (-20995);
    let w3 = y3 * (-16069) + z5;
    let w4 = y4 * (-3196) + z5;
    let o7 = ds(t4 + w1 + w3, first);
    let o5 = ds(t5 + w2 + w4, first);
    let o3 = ds(t6 + w2 + w3, first);
    let o1 = ds(t7 + w1 + w4, first);
    let o = [o0, o1, o2, o3, o4, o5, o6, o7];
    proof {
        lemma2_to64();
        assert(s[0] == d[0] && s[1] == d[1] && s[2] == d[2] && s[3] == d[3]);
        assert(s[4] == d[4] && s[5] == d[5] && s[6] == d[6] && s[7] == d[7]);
        let r = fdct_1d(s, first);
        assert(r[0] == o0 && r[4] == o4);
        assert(r[2] == o2 && r[6] == o6);
        assert(r[1] == o1 && r[3] == o3 && r[5] == o5 && r[7] == o7);
        if first {
            assert(-16384 <= o2 <= 16384);
            assert(-16384 <= o6 <= 16384);
            assert(-16384 <= o1 <= 16384);
            assert(-16384 <= o3 <= 16384);
            assert(-16384 <= o5 <= 16384);
            assert(-16384 <= o7 <= 16384);
        } else {
            assert((1i64 << 20) == 0x10_0000) by (bit_vector);
        }
    }
    o
}

/// `jpeg_fdct_islow`: the rows, then the columns.
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub fn fdct_x(s: &[i64; 64]) -> (o: [i64; 64])
    requires
        forall|i: int| 0 <= i < 64 ==> -128 <= #[trigger] s[i] <= 128,
    ensures
        forall|i: int| 0 <= i < 64 ==> #[trigger] o[i] as int == fdct(s64(*s))[i],
        forall|i: int| 0 <= i < 64 ==> -(1i64 << 20) <= #[trigger] o[i] <= (1i64 << 20),
{
    let ghost sq = s64(*s);
    let ghost rows = fdct_rows(sq);
    reveal(fdct);
    let mut ws = [0i64; 64];
    let mut r: usize = 0;
    while r < 8
        invariant
            r <= 8,
            sq == s64(*s),
            rows == fdct_rows(sq),
            forall|i: int| 0 <= i < 64 ==> -128 <= #[trigger] s[i] <= 128,
            forall|i: int| 0 <= i < 8 * r ==> #[trigger] ws[i] as int == rows[i],
            forall|i: int| 0 <= i < 8 * r ==> -16384 <= #[trigger] ws[i] <= 16384,
        decreases 8 - r,
    {
        let b = 8 * r;
        let d = [s[b], s[b + 1], s[b + 2], s[b + 3], s[b + 4], s[b + 5], s[b + 6], s[b + 7]];
        let o = fdct8(d, true);
        proof {
            assert(s8(d) =~= Seq::new(8, |j: int| sq[8 * r + j]));
        }
        let mut j: usize = 0;
        while j < 8
            invariant
                r < 8,
                j <= 8,
                b == 8 * r,
                rows == fdct_rows(sq),
                s8(d) == Seq::new(8, |j: int| sq[8 * r + j]),
                forall|i: int| 0 <= i < 8 ==> #[trigger] o[i] as int == fdct_1d(s8(d), true)[i],
                forall|i: int| 0 <= i < 8 ==> -16384 <= #[trigger] o[i] <= 16384,
                forall|i: int| 0 <= i < 8 * r + j ==> #[trigger] ws[i] as int == rows[i],
                forall|i: int| 0 <= i < 8 * r + j ==> -16384 <= #[trigger] ws[i] <= 16384,
            decreases 8 - j,
        {
            ws[b + j] = o[j];
            proof {
                let i = 8 * r + j;
                assert(i / 8 == r as int && i % 8 == j as int);
                assert(Seq::new(8, |jj: int| sq[8 * (i / 8) + jj]) =~= s8(d));
            }
            j += 1;
        }
        r += 1;
    }
    let mut o = [0i64; 64];
    let mut x: usize = 0;
    while x < 8
        invariant
            x <= 8,
            rows == fdct_rows(sq),
            sq == s64(*s),
            forall|i: int| 0 <= i < 64 ==> #[trigger] ws[i] as int == rows[i],
            forall|i: int| 0 <= i < 64 ==> -16384 <= #[trigger] ws[i] <= 16384,
            forall|i: int| 0 <= i < 64 && i % 8 < x ==> #[trigger] o[i] as int == fdct(sq)[i],
            forall|i: int| 0 <= i < 64 && i % 8 < x ==> -(1i64 << 20) <= #[trigger] o[i] <= (1i64 << 20),
        decreases 8 - x,
    {
        let d = [ws[x], ws[8 + x], ws[16 + x], ws[24 + x], ws[32 + x], ws[40 + x], ws[48 + x], ws[56 + x]];
        let c = fdct8(d, false);
        proof {
            assert(s8(d) =~= Seq::new(8, |j: int| rows[8 * j + x]));
        }
        let mut y: usize = 0;
        while y < 8
            invariant
                x < 8,
                y <= 8,
                rows == fdct_rows(sq),
                s8(d) == Seq::new(8, |j: int| rows[8 * j + x]),
                forall|i: int| 0 <= i < 8 ==> #[trigger] c[i] as int == fdct_1d(s8(d), false)[i],
                forall|i: int| 0 <= i < 8 ==> -(1i64 << 20) <= #[trigger] c[i] <= (1i64 << 20),
                forall|i: int|
                    0 <= i < 64 && (i % 8 < x || (i % 8 == x && i / 8 < y)) ==> #[trigger] o[i] as int == fdct(
                        sq,
                    )[i],
                forall|i: int|
                    0 <= i < 64 && (i % 8 < x || (i % 8 == x && i / 8 < y)) ==> -(1i64 << 20) <= #[trigger] o[i]
                        <= (1i64 << 20),
            decreases 8 - y,
        {
            o[8 * y + x] = c[y];
            proof {
                reveal(fdct);
                let i = 8 * y + x;
                assert(i / 8 == y as int && i % 8 == x as int);
                assert(Seq::new(8, |j: int| rows[8 * j + i % 8]) =~= s8(d));
            }
            y += 1;
        }
        x += 1;
    }
    o
}

// ---------------------------------------------------------------------------
// Quantization
// ---------------------------------------------------------------------------
pub fn quant_x(t: i64, q: u8, k: usize) -> (r: i16)
    requires
        -(1i64 << 20) <= t <= (1i64 << 20),
        q >= 1,
    ensures
        r as int == quant(t as int, q as int, k as int),
{
    proof {
        assert((1i64 << 20) == 0x10_0000) by (bit_vector);
    }
    let d = 8 * (q as i64);
    let v = if t < 0 {
        -((-t + d / 2) / d)
    } else {
        (t + d / 2) / d
    };
    let lo: i64 = if k == 0 {
        -1024
    } else {
        -1023
    };
    if v < lo {
        lo as i16
    } else if v > 1023 {
        1023
    } else {
        v as i16
    }
}

/// Division by multiplication: for `n` below 2^21 and `d` from 1 to 2^11,
/// `n / d` is `n * m >> 32` with `m` the quotient 2^32 / `d` rounded up.
pub proof fn lemma_recip(n: int, d: int, m: int)
    requires
        0 <= n < 0x20_0000,
        1 <= d <= 0x800,
        m == (0x1_0000_0000 + d - 1) / d,
    ensures
        (n * m) / 0x1_0000_0000 == n / d,
{
    let p = 0x1_0000_0000int;
    lemma_fundamental_div_mod(p + d - 1, d);
    lemma_mod_bound(p + d - 1, d);
    let e = m * d - p;
    assert(0 <= e < d) by {
        assert(d * m == p + d - 1 - (p + d - 1) % d);
        lemma_mul_is_commutative(d, m);
    }
    let q = n / d;
    let r = n % d;
    lemma_fundamental_div_mod(n, d);
    lemma_mod_bound(n, d);
    lemma_div_pos_is_pos(n, d);
    assert(n * e < p) by (nonlinear_arith)
        requires
            0 <= n < 0x20_0000,
            0 <= e < d,
            d <= 0x800,
            p == 0x1_0000_0000int,
    ;
    assert(n * m * d == n * p + n * e) by (nonlinear_arith)
        requires
            e == m * d - p,
    ;
    assert(q * p <= n * m) by (nonlinear_arith)
        requires
            n * m * d == n * p + n * e,
            n * e >= 0,
            n == d * q + r,
            0 <= r,
            d >= 1,
            p > 0,
            q >= 0,
    ;
    assert(n * m < (q + 1) * p) by (nonlinear_arith)
        requires
            n * m * d == n * p + n * e,
            n * e < p,
            n == d * q + r,
            r < d,
            d >= 1,
            p > 0,
    ;
    lemma_fundamental_div_mod_converse(n * m, p, q, n * m - q * p);
}

/// The reciprocal of `8 * q` for `quant_r`.
pub fn recip(q: u8) -> (m: u64)
    requires
        q >= 1,
    ensures
        m as int == (0x1_0000_0000 + 8 * q - 1) / (8 * q as int),
        m <= 0x2000_0100,
{
    let d = 8 * (q as u64);
    proof {
        lemma_div_is_ordered_by_denominator(0x1_0000_0000 + 8 * q - 1, 8, 8 * q as int);
        lemma_div_is_ordered(0x1_0000_0000 + 8 * q - 1, 0x1_0000_0000int + 2039, 8);
    }
    (0x1_0000_0000 + d - 1) / d
}

/// `quant_x` with the division done as a multiplication.
#[inline(always)]
pub fn quant_r(t: i64, q: u8, m: u64, k: usize) -> (r: i16)
    requires
        -(1i64 << 20) <= t <= (1i64 << 20),
        q >= 1,
        m as int == (0x1_0000_0000 + 8 * q - 1) / (8 * q as int),
        m <= 0x2000_0100,
    ensures
        r as int == quant(t as int, q as int, k as int),
{
    proof {
        assert((1i64 << 20) == 0x10_0000) by (bit_vector);
    }
    let d = 8 * (q as u64);
    let a: u64 = if t < 0 {
        (-t) as u64
    } else {
        t as u64
    };
    let n = a + d / 2;
    proof {
        lemma_recip(n as int, d as int, m as int);
        assert(n * m <= 0x20_0000 * 0x2000_0100) by (nonlinear_arith)
            requires
                n < 0x20_0000,
                m <= 0x2000_0100,
        ;
    }
    let nm = n * m;
    proof {
        vstd::bits::lemma_u64_shr_is_div(nm, 32);
        lemma2_to64();
    }
    let u = (nm >> 32) as i64;
    let v = if t < 0 {
        -u
    } else {
        u
    };
    let lo: i64 = if k == 0 {
        -1024
    } else {
        -1023
    };
    if v < lo {
        lo as i16
    } else if v > 1023 {
        1023
    } else {
        v as i16
    }
}

// ---------------------------------------------------------------------------
// Quantization tables
// ---------------------------------------------------------------------------
pub fn qtab_x(quality: u8, n: u8) -> (r: [u8; 64])
    ensures
        r@ == qtab(quality as int, n as int),
        forall|i: int| 0 <= i < 64 ==> #[trigger] r[i] >= 1,
{
    let q: u32 = if quality == 0 {
        1
    } else if quality > 100 {
        100
    } else {
        quality as u32
    };
    let scale: u32 = if q < 50 {
        5000 / q
    } else {
        200 - 2 * q
    };
    proof {
        assert(scale as int == qscale(quality as int));
        lemma_div_is_ordered(5000, 5000, q as int);
        assert(scale <= 5000) by {
            if q < 50 {
                lemma_div_is_ordered_by_denominator(5000, 1, q as int);
            }
        }
    }
    let mut r = [0u8; 64];
    let mut i: usize = 0;
    while i < 64
        invariant
            i <= 64,
            scale as int == qscale(quality as int),
            scale <= 5000,
            forall|j: int| 0 <= j < i ==> #[trigger] r[j] == qtab(quality as int, n as int)[j],
            forall|j: int| 0 <= j < i ==> #[trigger] r[j] >= 1,
        decreases 64 - i,
    {
        let basic: u32 = if n == 0 {
            STD_LUM_Q[i] as u32
        } else {
            STD_CHR_Q[i] as u32
        };
        assert(basic * scale <= 255 * 5000) by (nonlinear_arith)
            requires
                basic <= 255,
                scale <= 5000,
        ;
        let t = (basic * scale + 50) / 100;
        r[i] = if t == 0 {
            1
        } else if t > 255 {
            255
        } else {
            t as u8
        };
        i += 1;
    }
    proof {
        assert(r@ =~= qtab(quality as int, n as int));
    }
    r
}

} // verus!

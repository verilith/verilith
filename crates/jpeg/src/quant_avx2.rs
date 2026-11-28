//! The encoder's quantization on AVX2, eight coefficients at a time,
//! proven equal to `enc_spec::quant`. Each lane does what `quant_r` does:
//! the magnitude plus half the divisor, times the reciprocal, the high 32
//! bits of the 64-bit product (`vpmuludq`, on the even and then the odd
//! lanes), and the sign put back. The clamp to the coefficient range is
//! left to the caller, one lane at a time.
use crate::enc_spec::*;
#[cfg(verus_only)]
use crate::enc_front::lemma_recip;
#[cfg(verus_only)]
use crate::fdct_avx2::{bnd, lv};
use verilith_simd::arch::*;
use verilith_simd::cpu::*;
#[cfg(verus_only)]
use verilith_simd::lanes::*;
use verilith_simd::mem::*;
#[cfg(verus_only)]
use verilith_simd::ops::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::cpu::group_cpu};

/// 32-bit lane `m` of `v`, unsigned.
pub open spec fn uq(v: __m256i, m: int) -> int {
    u32x8(v)[m] as int
}

/// The rounded quotient `quant` takes before its clamp.
pub open spec fn qdiv(t: int, q: int) -> int {
    let d = 8 * q;
    if t < 0 {
        -((-t + d / 2) / d)
    } else {
        (t + d / 2) / d
    }
}

/// `quant` is `qdiv`, clamped.
pub proof fn lemma_quant_qdiv(t: int, q: int, k: int)
    ensures
        quant(t, q, k) == clamp_coef(qdiv(t, q), k),
{
}

/// Lane `2 i` and `2 i + 1` of a vector are the low and high halves of its
/// 64-bit lane `i`.
proof fn lemma_halves(v: __m256i, i: int)
    requires
        0 <= i < 4,
    ensures
        u64x4(v)[i] as int == uq(v, 2 * i) + 0x1_0000_0000 * uq(v, 2 * i + 1),
{
    let w0 = u32x8(v)[2 * i];
    let w1 = u32x8(v)[2 * i + 1];
    assert(u64x4(v)[i] == le64(w0, w1));
    assert((w0 as u64) | ((w1 as u64) << 32u64) == (w0 as u64) + 0x1_0000_0000u64 * (w1 as u64)) by (bit_vector);
}

/// A 64-bit lane below 2^32 * 2^32 in halves, read back.
proof fn lemma_split(x: u64)
    ensures
        x as int == (x as int % 0x1_0000_0000) + 0x1_0000_0000 * (x as int / 0x1_0000_0000),
{
    lemma_fundamental_div_mod(x as int, 0x1_0000_0000);
}

/// What `w` is, from its 64-bit lanes: lane `2 i` is the low half of 64-bit
/// lane `i`, lane `2 i + 1` the high half.
proof fn lemma_from64(v: __m256i, i: int)
    requires
        0 <= i < 4,
    ensures
        uq(v, 2 * i) == u64x4(v)[i] as int % 0x1_0000_0000,
        uq(v, 2 * i + 1) == u64x4(v)[i] as int / 0x1_0000_0000,
{
    lemma_halves(v, i);
    let a = uq(v, 2 * i);
    let b = uq(v, 2 * i + 1);
    assert(0 <= a < 0x1_0000_0000);
    lemma_fundamental_div_mod_converse(a + 0x1_0000_0000 * b, 0x1_0000_0000, b, a);
}

/// The sign of each lane, as a factor: 1, or -1 modulo 2^32.
#[inline(always)]
fn signs(o: __m256i) -> (g: __m256i)
    requires
        avx2(),
        bnd(o, 0x10_0000),
    ensures
        forall|m: int| 0 <= m < 8 ==> #[trigger] uq(g, m) == if lv(o, m) < 0 { 0xffff_ffffint } else { 1int },
{
    let s = _mm256_srai_epi32::<31>(o);
    let s2 = _mm256_add_epi32(s, s);
    let one = _mm256_set1_epi32(1);
    let g = _mm256_add_epi32(s2, one);
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] uq(g, m) == if lv(o, m) < 0 { 0xffff_ffffint } else { 1int } by {
            let x = lv(o, m);
            assert(-0x10_0000 <= x <= 0x10_0000);
            reveal_with_fuel(pow2_spec, 32);
            lemma2_to64();
            assert(pow2_spec(31) == 0x8000_0000) by {
                lemma2_to64_rest();
            }
            if x < 0 {
                assert(x / 0x8000_0000int == -1) by {
                    lemma_fundamental_div_mod_converse(x, 0x8000_0000, -1, x + 0x8000_0000);
                }
                assert(uq(s, m) == 0xffff_ffff) by {
                    assert((-1int) % 0x1_0000_0000 == 0xffff_ffff) by {
                        lemma_fundamental_div_mod_converse(-1, 0x1_0000_0000, -1, 0xffff_ffff);
                    }
                }
                assert(uq(s2, m) == 0xffff_fffe);
                assert(uq(g, m) == 0xffff_ffff);
            } else {
                assert(x / 0x8000_0000int == 0) by {
                    lemma_fundamental_div_mod_converse(x, 0x8000_0000, 0, x);
                }
                assert(uq(s, m) == 0);
                assert(uq(s2, m) == 0);
                assert(uq(g, m) == 1);
            }
        }
    }
    g
}

/// Times the sign factor: a lane's magnitude, or a magnitude given its sign.
#[inline(always)]
fn by_sign(a: __m256i, g: __m256i, Ghost(neg): Ghost<Seq<bool>>, Ghost(x): Ghost<Seq<int>>) -> (r: __m256i)
    requires
        avx2(),
        neg.len() == 8,
        x.len() == 8,
        forall|m: int| 0 <= m < 8 ==> #[trigger] uq(g, m) == if neg[m] { 0xffff_ffffint } else { 1int },
        forall|m: int| 0 <= m < 8 ==> -0x7fff_ffff <= #[trigger] x[m] <= 0x7fff_ffff,
        forall|m: int| 0 <= m < 8 ==> #[trigger] uq(a, m) == (x[m] + 0x1_0000_0000) % 0x1_0000_0000,
    ensures
        forall|m: int| 0 <= m < 8 ==> #[trigger] uq(r, m) == (if neg[m] { -x[m] } else { x[m] } + 0x1_0000_0000) % 0x1_0000_0000,
{
    let r = _mm256_mullo_epi32(a, g);
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] uq(r, m) == (if neg[m] { -x[m] } else { x[m] } + 0x1_0000_0000) % 0x1_0000_0000 by {
            let p = 0x1_0000_0000int;
            let v = x[m];
            let u = uq(a, m);
            assert(uq(r, m) == (u * uq(g, m)) % p);
            lemma_fundamental_div_mod(v + p, p);
            let k = (v + p) / p;
            assert(u == v + p - k * p);
            if neg[m] {
                assert(u * (p - 1) == (-v + p) + p * (u - 2 + k)) by (nonlinear_arith)
                    requires
                        u == v + p - k * p,
                ;
                lemma_mod_multiples_vanish(u - 2 + k, -v + p, p);
                assert(p * (u - 2 + k) + (-v + p) == u * (p - 1));
            } else {
                assert(u * 1 == u);
                lemma_mod_multiples_vanish(1 - k, v + p - k * p + k * p - p, p);
                assert(u == p * (1 - k) + v);
                lemma_mod_multiples_vanish(1 - k, v, p);
                lemma_mod_multiples_vanish(1, v, p);
                assert((v + p) % p == v % p) by {
                    lemma_mod_multiples_vanish(1, v, p);
                }
                assert(u % p == v % p) by {
                    lemma_mod_multiples_vanish(1 - k, v, p);
                }
                lemma_mod_twice(u, p);
                lemma_small_mod(u as nat, p as nat);
            }
        }
    }
    r
}

/// The high 32 bits of each lane's product with `m`.
#[inline(always)]
fn mulhi32(n: __m256i, m: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        forall|j: int| 0 <= j < 8 ==> #[trigger] uq(r, j) == (uq(n, j) * uq(m, j)) / 0x1_0000_0000,
{
    let pe = _mm256_mul_epu32(n, m);
    let n1 = _mm256_srli_epi64::<32>(n);
    let m1 = _mm256_srli_epi64::<32>(m);
    let po = _mm256_mul_epu32(n1, m1);
    let e = _mm256_srli_epi64::<32>(pe);
    let o1 = _mm256_srli_epi64::<32>(po);
    let o = _mm256_slli_epi64::<32>(o1);
    let r = _mm256_add_epi32(e, o);
    proof {
        reveal_with_fuel(pow2_spec, 33);
        lemma2_to64();
        lemma2_to64_rest();
        let p = 0x1_0000_0000int;
        assert forall|j: int| 0 <= j < 8 implies #[trigger] uq(r, j) == (uq(n, j) * uq(m, j)) / p by {
            let i = j / 2;
            assert(0 <= i < 4);
            lemma_halves(n, i);
            lemma_halves(m, i);
            lemma_from64(n1, i);
            lemma_from64(m1, i);
            lemma_from64(e, i);
            lemma_from64(o, i);
            lemma_from64(pe, i);
            lemma_from64(po, i);
            assert(u64x4(n1)[i] as int == u64x4(n)[i] as int / p);
            assert(u64x4(m1)[i] as int == u64x4(m)[i] as int / p);
            let a0 = uq(n, 2 * i);
            let a1 = uq(n, 2 * i + 1);
            let b0 = uq(m, 2 * i);
            let b1 = uq(m, 2 * i + 1);
            lemma_fundamental_div_mod_converse(a0 + p * a1, p, a1, a0);
            lemma_fundamental_div_mod_converse(b0 + p * b1, p, b1, b0);
            assert(uq(n1, 2 * i) == a1) by {
                lemma_small_mod(a1 as nat, p as nat);
            }
            assert(uq(m1, 2 * i) == b1) by {
                lemma_small_mod(b1 as nat, p as nat);
            }
            assert(0 <= a0 * b0 < p * p) by (nonlinear_arith)
                requires
                    0 <= a0 < p,
                    0 <= b0 < p,
            ;
            assert(0 <= a1 * b1 < p * p) by (nonlinear_arith)
                requires
                    0 <= a1 < p,
                    0 <= b1 < p,
            ;
            assert(u64x4(pe)[i] as int == a0 * b0);
            assert(u64x4(po)[i] as int == a1 * b1);
            let he = (a0 * b0) / p;
            let ho = (a1 * b1) / p;
            lemma_div_pos_is_pos(a0 * b0, p);
            lemma_div_pos_is_pos(a1 * b1, p);
            lemma_div_is_ordered(a0 * b0, p * p - 1, p);
            lemma_div_is_ordered(a1 * b1, p * p - 1, p);
            assert((p * p - 1) / p == p - 1) by {
                lemma_fundamental_div_mod_converse(p * p - 1, p, p - 1, p - 1);
            }
            assert(u64x4(e)[i] as int == he);
            assert(uq(e, 2 * i) == he) by {
                lemma_small_mod(he as nat, p as nat);
            }
            assert(uq(e, 2 * i + 1) == 0) by {
                lemma_basic_div(he, p);
            }
            assert(u64x4(o1)[i] as int == ho);
            assert(u64x4(o)[i] as int == (ho * p) % (p * p));
            assert(0 <= ho * p < p * p) by (nonlinear_arith)
                requires
                    0 <= ho < p,
            ;
            lemma_small_mod((ho * p) as nat, (p * p) as nat);
            assert(uq(o, 2 * i) == 0) by {
                lemma_mod_multiple(ho, p);
            }
            assert(uq(o, 2 * i + 1) == ho) by {
                lemma_div_multiples_vanish(ho, p);
            }
            if j == 2 * i {
                lemma_small_mod(he as nat, p as nat);
            } else {
                assert(j == 2 * i + 1);
                lemma_small_mod(ho as nat, p as nat);
            }
        }
    }
    r
}

proof fn lemma_mod_multiple(a: int, p: int)
    requires
        p > 0,
    ensures
        (a * p) % p == 0,
{
    lemma_mod_multiples_basic(a, p);
}

proof fn lemma_div_multiples_vanish(a: int, p: int)
    requires
        p > 0,
    ensures
        (a * p) / p == a,
{
    lemma_div_multiples_vanish_fancy(a, 0, p);
    assert(a * p == p * a + 0) by (nonlinear_arith);
}

proof fn lemma_basic_div(a: int, p: int)
    requires
        0 <= a < p,
    ensures
        a / p == 0,
{
    lemma_basic_div_specific_divisor(p);
}

proof fn lemma_basic_div_specific_divisor(p: int)
    requires
        p > 0,
    ensures
        forall|a: int| 0 <= a < p ==> #[trigger] (a / p) == 0,
{
    assert forall|a: int| 0 <= a < p implies #[trigger] (a / p) == 0 by {
        lemma_fundamental_div_mod_converse(a, p, 0, a);
    }
}

/// The quantizers of a table as the vector code takes them: half of each
/// divisor, and its reciprocal.
pub open spec fn qv_ok(q: Seq<u8>, h: Seq<u32>, m: Seq<u32>) -> bool {
    &&& q.len() == 64
    &&& h.len() == 64
    &&& m.len() == 64
    &&& forall|i: int|
        0 <= i < 64 ==> 1 <= #[trigger] q[i] && h[i] as int == 4 * q[i] && m[i] as int == (0x1_0000_0000 + 8 * q[i] - 1) / (8
            * q[i] as int)
}

/// Eight coefficients, row `v` of `t`, divided as `quant` divides them.
#[inline(always)]
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn qrow(t: &[u32; 64], h: &[u32; 64], m: &[u32; 64], q: &[u8; 64], v: usize) -> (r: __m256i)
    requires
        avx2(),
        v < 8,
        qv_ok(q@, h@, m@),
        forall|i: int| 0 <= i < 64 ==> -0x10_0000 <= #[trigger] s32(t[i]) <= 0x10_0000,
    ensures
        forall|u: int| 0 <= u < 8 ==> #[trigger] lv(r, u) == qdiv(s32(t[8 * v + u]), q[8 * v + u] as int),
{
    let o = load256_u32(t, 8 * v);
    let hv = load256_u32(h, 8 * v);
    let mv = load256_u32(m, 8 * v);
    let ghost x = Seq::new(8, |u: int| s32(t[8 * v + u]));
    let ghost neg = Seq::new(8, |u: int| x[u] < 0);
    proof {
        assert forall|u: int| 0 <= u < 8 implies -0x10_0000 <= #[trigger] lv(o, u) <= 0x10_0000 && lv(o, u) == x[u] by {
            assert(u32x8(o)[u] == t[8 * v + u]);
        }
    }
    let g = signs(o);
    proof {
        assert forall|u: int| 0 <= u < 8 implies #[trigger] uq(o, u) == (x[u] + 0x1_0000_0000) % 0x1_0000_0000 by {
            let y = uq(o, u);
            if y < 0x8000_0000 {
                lemma_mod_multiples_vanish(1, y, 0x1_0000_0000);
                lemma_small_mod(y as nat, 0x1_0000_0000);
            } else {
                lemma_small_mod(y as nat, 0x1_0000_0000);
            }
        }
    }
    let a = by_sign(o, g, Ghost(neg), Ghost(x));
    let ghost ab = Seq::new(8, |u: int| if x[u] < 0 { -x[u] } else { x[u] });
    proof {
        assert forall|u: int| 0 <= u < 8 implies #[trigger] uq(a, u) == ab[u] by {
            lemma_mod_multiples_vanish(1, ab[u], 0x1_0000_0000);
            lemma_small_mod(ab[u] as nat, 0x1_0000_0000);
        }
    }
    let n = _mm256_add_epi32(a, hv);
    proof {
        assert forall|u: int| 0 <= u < 8 implies #[trigger] uq(n, u) == ab[u] + 4 * q[8 * v + u] && uq(mv, u) == m[8 * v + u] by {
            assert(uq(a, u) == ab[u]);
            assert(x[u] == s32(t[8 * v + u]));
            assert(u32x8(hv)[u] == h[8 * v + u]);
            assert(u32x8(mv)[u] == m[8 * v + u]);
            assert(q[8 * v + u] <= 255);
            lemma_small_mod((ab[u] + 4 * q[8 * v + u]) as nat, 0x1_0000_0000);
        }
    }
    let p = mulhi32(n, mv);
    let ghost dv = Seq::new(8, |u: int| (ab[u] + 4 * q[8 * v + u]) / (8 * q[8 * v + u] as int));
    proof {
        assert forall|u: int| 0 <= u < 8 implies #[trigger] uq(p, u) == dv[u] && 0 <= dv[u] < 0x4_0000 by {
            let qq = q[8 * v + u] as int;
            assert(1 <= qq <= 255);
            lemma_recip(ab[u] + 4 * qq, 8 * qq, m[8 * v + u] as int);
            lemma_div_pos_is_pos(ab[u] + 4 * qq, 8 * qq);
            lemma_div_is_ordered_by_denominator(ab[u] + 4 * qq, 8, 8 * qq);
            lemma_div_is_ordered(ab[u] + 4 * qq, 0x20_0000, 8);
        }
        assert forall|u: int| 0 <= u < 8 implies #[trigger] uq(p, u) == (dv[u] + 0x1_0000_0000) % 0x1_0000_0000 by {
            lemma_mod_multiples_vanish(1, dv[u], 0x1_0000_0000);
            lemma_small_mod(dv[u] as nat, 0x1_0000_0000);
        }
    }
    let r = by_sign(p, g, Ghost(neg), Ghost(dv));
    proof {
        assert forall|u: int| 0 <= u < 8 implies #[trigger] lv(r, u) == qdiv(s32(t[8 * v + u]), q[8 * v + u] as int) by {
            let w = if neg[u] { -dv[u] } else { dv[u] };
            assert(uq(p, u) == dv[u] && 0 <= dv[u] < 0x4_0000);
            assert(x[u] == s32(t[8 * v + u]));
            assert(uq(r, u) == (w + 0x1_0000_0000) % 0x1_0000_0000);
            lemma_mod_multiples_vanish(1, w, 0x1_0000_0000);
            if w >= 0 {
                lemma_small_mod(w as nat, 0x1_0000_0000);
            } else {
                lemma_small_mod((w + 0x1_0000_0000) as nat, 0x1_0000_0000);
            }
            assert(8 * (q[8 * v + u] as int) / 2 == 4 * q[8 * v + u]);
        }
    }
    r
}

/// The 64 coefficients of a block (two's-complement lanes) divided as
/// `quant` divides them, before the clamp.
#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "avx2"))]
pub fn qdiv_block(t: &[u32; 64], h: &[u32; 64], m: &[u32; 64], q: &[u8; 64]) -> (r: [u32; 64])
    requires
        avx2(),
        qv_ok(q@, h@, m@),
        forall|i: int| 0 <= i < 64 ==> -0x10_0000 <= #[trigger] s32(t[i]) <= 0x10_0000,
    ensures
        forall|i: int| 0 <= i < 64 ==> #[trigger] s32(r[i]) == qdiv(s32(t[i]), q[i] as int),
        forall|i: int| 0 <= i < 64 ==> -0x4_0000 <= #[trigger] s32(r[i]) <= 0x4_0000,
{
    let mut r = [0u32; 64];
    let mut v: usize = 0;
    while v < 8
        invariant
            avx2(),
            v <= 8,
            qv_ok(q@, h@, m@),
            forall|i: int| 0 <= i < 64 ==> -0x10_0000 <= #[trigger] s32(t[i]) <= 0x10_0000,
            forall|i: int| 0 <= i < 8 * v ==> #[trigger] s32(r[i]) == qdiv(s32(t[i]), q[i] as int),
        decreases 8 - v,
    {
        let o = qrow(t, h, m, q, v);
        let ghost r0 = r@;
        store256_u32(&mut r, 8 * v, o);
        proof {
            assert forall|i: int| 0 <= i < 8 * (v + 1) implies #[trigger] s32(r[i]) == qdiv(s32(t[i]), q[i] as int) by {
                if i < 8 * v {
                    assert(r[i] == r0[i]);
                } else {
                    assert(r[i] == u32x8(o)[i - 8 * v]);
                    assert(lv(o, i - 8 * v) == qdiv(s32(t[8 * v + (i - 8 * v)]), q[8 * v + (i - 8 * v)] as int));
                }
            }
        }
        v = v + 1;
    }
    proof {
        assert forall|i: int| 0 <= i < 64 implies -0x4_0000 <= #[trigger] s32(r[i]) <= 0x4_0000 by {
            lemma_qdiv_bound(s32(t[i]), q[i] as int);
        }
    }
    r
}

proof fn lemma_qdiv_bound(t: int, q: int)
    requires
        -0x10_0000 <= t <= 0x10_0000,
        1 <= q <= 255,
    ensures
        -0x4_0000 <= qdiv(t, q) <= 0x4_0000,
{
    let a = if t < 0 { -t } else { t };
    lemma_div_pos_is_pos(a + 4 * q, 8 * q);
    lemma_div_is_ordered_by_denominator(a + 4 * q, 8, 8 * q);
    lemma_div_is_ordered(a + 4 * q, 0x20_0000, 8);
    assert(8 * q / 2 == 4 * q);
}

/// A 16-bit lane, signed.
pub open spec fn hv(v: __m256i, j: int) -> int {
    s16(u16x16(v)[j])
}

/// The clamp `quant` ends with: to -1024..1023, and -1023 for every
/// coefficient but the DC (`dc`).
pub open spec fn clampq(x: int, dc: bool) -> int {
    let lo = if dc {
        -1024
    } else {
        -1023
    };
    if x < lo {
        lo
    } else if x > 1023 {
        1023
    } else {
        x
    }
}

proof fn lemma_sat_shift(x: int)
    requires
        -0x4_0000 <= x <= 0x4_0000,
    ensures
        sat_s16(32 * x) / 32 == clampq(x, true),
{
    if 32 * x < -0x8000 {
        assert(-0x8000int / 32 == -1024);
    } else if 32 * x > 0x7fff {
        assert(0x7fffint / 32 == 1023);
    } else {
        lemma_div_multiples_vanish(x, 32);
        assert(x * 32 == 32 * x);
    }
}

/// The lanes of two rows, in order.
pub open spec fn two(a: __m256i, b: __m256i) -> Seq<int> {
    Seq::new(16, |j: int| if j < 8 { lv(a, j) } else { lv(b, j - 8) })
}

/// Times 32.
#[inline(always)]
fn times32(a: __m256i) -> (r: __m256i)
    requires
        avx2(),
        bnd(a, 0x4_0000),
    ensures
        forall|m: int| 0 <= m < 8 ==> #[trigger] s32(u32x8(r)[m]) == 32 * lv(a, m),
{
    let r = _mm256_slli_epi32::<5>(a);
    proof {
        reveal_with_fuel(pow2_spec, 6);
        assert forall|m: int| 0 <= m < 8 implies #[trigger] s32(u32x8(r)[m]) == 32 * lv(a, m) by {
            assert(-0x4_0000 <= lv(a, m) <= 0x4_0000);
            lemma_wrap32(u32x8(a)[m], 32);
        }
    }
    r
}

/// The 16-bit lanes of a permutation of 32-bit lanes.
proof fn lemma_perm16(p: __m256i, pm: __m256i, idx: __m256i)
    requires
        u32x8(pm) == permvar32(u32x8(p), u32x8(idx)),
        forall|l: int| 0 <= l < 8 ==> #[trigger] u32x8(idx)[l] < 8,
    ensures
        forall|j: int| 0 <= j < 16 ==> #[trigger] u16x16(pm)[j] == u16x16(p)[2 * (u32x8(idx)[j / 2] as int) + j % 2],
{
    lemma_u16s_of_u32s(b256(p));
    lemma_u16s_of_u32s(b256(pm));
    assert forall|j: int| 0 <= j < 16 implies #[trigger] u16x16(pm)[j] == u16x16(p)[2 * (u32x8(idx)[j / 2] as int) + j % 2] by {
        let l = j / 2;
        let src = u32x8(idx)[l] as int;
        assert(u32x8(pm)[l] == u32x8(p)[src]);
        assert(u16x16(pm)[2 * l] == (u32x8(pm)[l] & 0xffff) as u16);
        assert(u16x16(p)[2 * src] == (u32x8(p)[src] & 0xffff) as u16);
        assert(u16x16(pm)[2 * l + 1] == (u32x8(pm)[l] >> 16u32) as u16);
        assert(u16x16(p)[2 * src + 1] == (u32x8(p)[src] >> 16u32) as u16);
    }
}

/// The two rows times 32, saturated to 16 bits, in order.
#[inline(always)]
#[verifier::spinoff_prover]
fn packed(a: __m256i, b: __m256i) -> (pm: __m256i)
    requires
        avx2(),
        bnd(a, 0x4_0000),
        bnd(b, 0x4_0000),
    ensures
        forall|j: int| 0 <= j < 16 ==> #[trigger] s16(u16x16(pm)[j]) == sat_s16(32 * two(a, b)[j]),
{
    let a5 = times32(a);
    let b5 = times32(b);
    let p = _mm256_packs_epi32(a5, b5);
    let idx = _mm256_setr_epi32(0, 1, 4, 5, 2, 3, 6, 7);
    let pm = _mm256_permutevar8x32_epi32(p, idx);
    proof {
        lemma_perm16(p, pm, idx);
        assert forall|j: int| 0 <= j < 16 implies #[trigger] s16(u16x16(pm)[j]) == sat_s16(32 * two(a, b)[j]) by {
            let src = u32x8(idx)[j / 2] as int;
            let sj = 2 * src + j % 2;
            assert(u16x16(pm)[j] == u16x16(p)[sj]);
            let w = sat_s16(if sj % 8 < 4 { s32(u32x8(a5)[(sj / 8) * 4 + sj % 8]) } else { s32(u32x8(b5)[(sj / 8) * 4 + sj % 8 - 4]) });
            assert(u16x16(p)[sj] == (w % 0x10000) as u16);
            lemma_s16_of(w);
        }
    }
    pm
}

/// Lanes divided by 32, rounding down: the saturated values clamped.
#[inline(always)]
fn halve(pm: __m256i, Ghost(xs): Ghost<Seq<int>>) -> (sh: __m256i)
    requires
        avx2(),
        xs.len() == 16,
        forall|j: int| 0 <= j < 16 ==> -0x4_0000 <= #[trigger] xs[j] <= 0x4_0000,
        forall|j: int| 0 <= j < 16 ==> #[trigger] s16(u16x16(pm)[j]) == sat_s16(32 * xs[j]),
    ensures
        forall|j: int| 0 <= j < 16 ==> #[trigger] hv(sh, j) == clampq(xs[j], true),
{
    let sh = _mm256_srai_epi16::<5>(pm);
    proof {
        reveal_with_fuel(pow2_spec, 6);
        assert forall|j: int| 0 <= j < 16 implies #[trigger] hv(sh, j) == clampq(xs[j], true) by {
            lemma_sat_shift(xs[j]);
            let w = sat_s16(32 * xs[j]);
            assert(s16(u16x16(pm)[j]) == w);
            assert(u16x16(sh)[j] == ((w / 32) % 0x10000) as u16);
            lemma_s16_of(w / 32);
        }
    }
    sh
}

/// -1024 raised to -1023 in every lane but the DC (`dc`, lane 0).
#[inline(always)]
fn fix_ac(sh: __m256i, dc: bool, Ghost(xs): Ghost<Seq<int>>) -> (r: __m256i)
    requires
        avx2(),
        xs.len() == 16,
        forall|j: int| 0 <= j < 16 ==> #[trigger] hv(sh, j) == clampq(xs[j], true),
    ensures
        forall|j: int| 0 <= j < 16 ==> #[trigger] hv(r, j) == clampq(xs[j], dc && j == 0),
{
    let c = dc_const(dc);
    let e = _mm256_cmpeq_epi16(sh, c);
    let r = _mm256_sub_epi16(sh, e);
    proof {
        assert forall|j: int| 0 <= j < 16 implies #[trigger] hv(r, j) == clampq(xs[j], dc && j == 0) by {
            let z = clampq(xs[j], true);
            assert(hv(sh, j) == z);
            let cj = u16x16(c)[j];
            let zu = u16x16(sh)[j];
            if z == -1024 && !(dc && j == 0) {
                assert(zu == 0xfc00u16);
                assert(u16x16(e)[j] == 0xffffu16);
                assert(u16x16(r)[j] == ((0xfc00int - 0xffff + 0x10000) % 0x10000) as u16);
            } else {
                assert(zu != cj);
                assert(u16x16(e)[j] == 0u16);
                assert(u16x16(r)[j] == ((zu - 0 + 0x10000) % 0x10000) as u16);
                lemma_small_mod(zu as nat, 0x10000);
                lemma_mod_multiples_vanish(1, zu as int, 0x10000);
            }
        }
    }
    r
}

/// Rows `2 w` and `2 w + 1` of a block of divided coefficients, clamped,
/// as sixteen 16-bit lanes in order.
#[inline(always)]
fn clamp_pair(a: __m256i, b: __m256i, dc: bool) -> (r: __m256i)
    requires
        avx2(),
        bnd(a, 0x4_0000),
        bnd(b, 0x4_0000),
    ensures
        forall|j: int| 0 <= j < 8 ==> #[trigger] hv(r, j) == clampq(lv(a, j), dc && j == 0),
        forall|j: int| 8 <= j < 16 ==> #[trigger] hv(r, j) == clampq(lv(b, j - 8), false),
{
    let ghost xs = two(a, b);
    let pm = packed(a, b);
    let sh = halve(pm, Ghost(xs));
    let r = fix_ac(sh, dc, Ghost(xs));
    proof {
        assert forall|j: int| 0 <= j < 8 implies #[trigger] hv(r, j) == clampq(lv(a, j), dc && j == 0) by {
            assert(xs[j] == lv(a, j));
        }
        assert forall|j: int| 8 <= j < 16 implies #[trigger] hv(r, j) == clampq(lv(b, j - 8), false) by {
            assert(xs[j] == lv(b, j - 8));
        }
    }
    r
}

/// -1024 in every 16-bit lane, but for 0x4000 in lane 0 with `dc`.
#[inline(always)]
fn dc_const(dc: bool) -> (c: __m256i)
    requires
        avx2(),
    ensures
        forall|j: int| 0 <= j < 16 ==> #[trigger] u16x16(c)[j] == if dc && j == 0 { 0x4000u16 } else { 0xfc00u16 },
{
    let c = if dc {
        _mm256_setr_epi32(-67092480, -67044352, -67044352, -67044352, -67044352, -67044352, -67044352, -67044352)
    } else {
        _mm256_set1_epi32(-67044352)
    };
    proof {
        lemma_u16s_of_u32s(b256(c));
        assert((0xfc00_4000u32 & 0xffff) as u16 == 0x4000u16 && (0xfc00_4000u32 >> 16u32) as u16 == 0xfc00u16
            && (0xfc00_fc00u32 & 0xffff) as u16 == 0xfc00u16 && (0xfc00_fc00u32 >> 16u32) as u16 == 0xfc00u16) by (bit_vector);
        assert forall|j: int| 0 <= j < 16 implies #[trigger] u16x16(c)[j] == if dc && j == 0 { 0x4000u16 } else { 0xfc00u16 } by {
            let l = j / 2;
            assert(u16x16(c)[2 * l] == (u32x8(c)[l] & 0xffff) as u16);
            assert(u16x16(c)[2 * l + 1] == (u32x8(c)[l] >> 16u32) as u16);
            assert(u32x8(c)[l] == if dc && l == 0 { 0xfc00_4000u32 } else { 0xfc00_fc00u32 });
        }
    }
    c
}

/// A signed value in 16 bits, stored and read back.
proof fn lemma_s16_of(w: int)
    requires
        -0x8000 <= w <= 0x7fff,
    ensures
        s16((w % 0x10000) as u16) == w,
{
    if w >= 0 {
        lemma_small_mod(w as nat, 0x10000);
    } else {
        lemma_mod_multiples_vanish(1, w, 0x10000);
        lemma_small_mod((w + 0x10000) as nat, 0x10000);
    }
}

/// A lane times a small power of two, read back signed.
proof fn lemma_wrap32(u: u32, k: int)
    requires
        k == 32,
        -0x4_0000 <= s32(u) <= 0x4_0000,
    ensures
        s32(((u as nat * 32) % 0x1_0000_0000) as u32) == 32 * s32(u),
{
    let x = s32(u);
    let p = 0x1_0000_0000int;
    if u < 0x8000_0000 {
        lemma_small_mod((u as nat * 32) as nat, p as nat);
    } else {
        assert(u as int == x + p);
        assert(u as int * 32 == 32 * x + 32 * p);
        lemma_mod_multiples_vanish(32, 32 * x, p);
        lemma_mod_multiples_vanish(1, 32 * x, p);
        lemma_small_mod((32 * x + p) as nat, p as nat);
        assert((u as int * 32) % p == 32 * x + p) by {
            assert(32 * p + 32 * x == p * 32 + 32 * x);
        }
    }
}

/// A block's coefficients quantized (`quant`), from the divided ones.
#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "avx2"))]
pub fn clamp_block_v(d: &[u32; 64]) -> (r: [i16; 64])
    requires
        avx2(),
        forall|i: int| 0 <= i < 64 ==> -0x4_0000 <= #[trigger] s32(d[i]) <= 0x4_0000,
    ensures
        forall|i: int| 0 <= i < 64 ==> #[trigger] r[i] as int == clampq(s32(d[i]), i == 0),
{
    let mut r = [0i16; 64];
    let mut w: usize = 0;
    while w < 4
        invariant
            avx2(),
            w <= 4,
            forall|i: int| 0 <= i < 64 ==> -0x4_0000 <= #[trigger] s32(d[i]) <= 0x4_0000,
            forall|i: int| 0 <= i < 16 * w ==> #[trigger] r[i] as int == clampq(s32(d[i]), i == 0),
        decreases 4 - w,
    {
        let a = load256_u32(d, 16 * w);
        let b = load256_u32(d, 16 * w + 8);
        proof {
            assert forall|m: int| 0 <= m < 8 implies -0x4_0000 <= #[trigger] lv(a, m) <= 0x4_0000 && lv(a, m) == s32(d[16 * w + m]) by {
                assert(u32x8(a)[m] == d[16 * w + m]);
            }
            assert forall|m: int| 0 <= m < 8 implies -0x4_0000 <= #[trigger] lv(b, m) <= 0x4_0000 && lv(b, m) == s32(d[16 * w + 8 + m]) by {
                assert(u32x8(b)[m] == d[16 * w + 8 + m]);
            }
        }
        let o = clamp_pair(a, b, w == 0);
        let ghost r0 = r@;
        store256_i16(&mut r, 16 * w, o);
        proof {
            assert forall|i: int| 0 <= i < 16 * (w + 1) implies #[trigger] r[i] as int == clampq(s32(d[i]), i == 0) by {
                if i < 16 * w {
                    assert(r[i] == r0[i]);
                } else {
                    let j = i - 16 * w;
                    assert(r[i] == u16x16(o)[j] as i16);
                    assert(-0x8000 <= hv(o, j) <= 0x7fff);
                    if j < 8 {
                        assert(lv(a, j) == s32(d[16 * w + j]));
                        assert(hv(o, j) == clampq(lv(a, j), w == 0 && j == 0));
                    } else {
                        assert(lv(b, j - 8) == s32(d[16 * w + 8 + (j - 8)]));
                        assert(hv(o, j) == clampq(lv(b, j - 8), false));
                    }
                    let ou = u16x16(o)[j];
                    assert((ou as i16) as int == if ou >= 0x8000 { ou - 0x1_0000 } else { ou as int }) by (bit_vector);
                }
            }
        }
        w = w + 1;
    }
    r
}

} // verus!

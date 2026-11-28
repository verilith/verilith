//! The encoder's forward DCT on AVX2, proven equal to `enc_spec::fdct`.
//!
//! Each pass runs the scalar pass (`enc_spec::fdct_1d`, libjpeg's
//! `jpeg_fdct_islow`) on eight rows or columns at once, one per 32-bit
//! lane, with the same operations in the same order: 32-bit adds,
//! subtracts and multiplies by constants (`vpmulld`), and descaling by an
//! add and an arithmetic shift. Every intermediate value fits in 32 bits
//! (bounded below), so each lane computes exactly what the scalar code
//! does. The block is transposed before each pass.
use crate::enc_spec::*;
#[cfg(verus_only)]
use crate::encode::pblock;
#[cfg(verus_only)]
use crate::idct_avx2::{lemma_perm_u32, pick4};
use crate::idct_avx2::tr4;
use crate::spec::*;
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

// ---------------------------------------------------------------------------
// Lanes as signed values
// ---------------------------------------------------------------------------
/// 32-bit lane `m` of `v`, signed.
pub open spec fn lv(v: __m256i, m: int) -> int {
    s32(u32x8(v)[m])
}

/// Every lane of `v` is at most `b` in magnitude.
pub open spec fn bnd(v: __m256i, b: int) -> bool {
    forall|m: int| 0 <= m < 8 ==> -b <= #[trigger] lv(v, m) <= b
}

pub spec const M32: int = 0x1_0000_0000;

/// A value congruent to `v` modulo 2^32, read back as a signed lane.
proof fn lemma_wrap(v: int, k: int)
    requires
        -0x8000_0000 <= v < 0x8000_0000,
    ensures
        0 <= (v + k * M32) % M32 < M32,
        s32(((v + k * M32) % M32) as u32) == v,
{
    lemma_mod_multiples_vanish(k, v, M32);
    assert((k * M32 + v) == (v + k * M32));
    if v >= 0 {
        lemma_small_mod(v as nat, M32 as nat);
    } else {
        lemma_fundamental_div_mod_converse(v, M32, -1, v + M32);
    }
}

proof fn lemma_s32_split(x: u32)
    ensures
        x as int == s32(x) + (if x < 0x8000_0000 { 0int } else { 1int }) * M32,
        -0x8000_0000 <= s32(x) < 0x8000_0000,
{
}

proof fn lemma_add(x: u32, y: u32)
    requires
        -0x8000_0000 <= s32(x) + s32(y) < 0x8000_0000,
    ensures
        s32(((x + y) % M32) as u32) == s32(x) + s32(y),
{
    lemma_s32_split(x);
    lemma_s32_split(y);
    let a: int = if x < 0x8000_0000 { 0 } else { 1 };
    let b: int = if y < 0x8000_0000 { 0 } else { 1 };
    assert(x + y == s32(x) + s32(y) + (a + b) * M32);
    lemma_wrap(s32(x) + s32(y), a + b);
}

proof fn lemma_sub(x: u32, y: u32)
    requires
        -0x8000_0000 <= s32(x) - s32(y) < 0x8000_0000,
    ensures
        s32(((x - y + M32) % M32) as u32) == s32(x) - s32(y),
{
    lemma_s32_split(x);
    lemma_s32_split(y);
    let a: int = if x < 0x8000_0000 { 0 } else { 1 };
    let b: int = if y < 0x8000_0000 { 0 } else { 1 };
    assert(x - y + M32 == s32(x) - s32(y) + (a - b + 1) * M32);
    lemma_wrap(s32(x) - s32(y), a - b + 1);
}

proof fn lemma_mul(x: u32, y: u32)
    requires
        -0x8000_0000 <= s32(x) * s32(y) < 0x8000_0000,
    ensures
        s32(((x * y) % M32) as u32) == s32(x) * s32(y),
{
    lemma_s32_split(x);
    lemma_s32_split(y);
    let a: int = if x < 0x8000_0000 { 0 } else { 1 };
    let b: int = if y < 0x8000_0000 { 0 } else { 1 };
    let (sx, sy) = (s32(x), s32(y));
    let k = a * sy + b * sx + a * b * M32;
    assert(x * y == sx * sy + k * M32) by (nonlinear_arith)
        requires
            x as int == sx + a * M32,
            y as int == sy + b * M32,
            k == a * sy + b * sx + a * b * M32,
    ;
    lemma_wrap(sx * sy, k);
}

// ---------------------------------------------------------------------------
// The operations, lane by lane
// ---------------------------------------------------------------------------
#[inline(always)]
fn vadd(a: __m256i, b: __m256i, Ghost(ba): Ghost<int>, Ghost(bb): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        bnd(a, ba),
        bnd(b, bb),
        ba + bb < 0x8000_0000,
    ensures
        bnd(r, ba + bb),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(r, m) == lv(a, m) + lv(b, m),
{
    let r = _mm256_add_epi32(a, b);
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] lv(r, m) == lv(a, m) + lv(b, m) by {
            assert(lv(a, m) <= ba && lv(b, m) <= bb && -ba <= lv(a, m) && -bb <= lv(b, m));
            lemma_add(u32x8(a)[m], u32x8(b)[m]);
        }
    }
    r
}

#[inline(always)]
fn vsub(a: __m256i, b: __m256i, Ghost(ba): Ghost<int>, Ghost(bb): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        bnd(a, ba),
        bnd(b, bb),
        ba + bb < 0x8000_0000,
    ensures
        bnd(r, ba + bb),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(r, m) == lv(a, m) - lv(b, m),
{
    let r = _mm256_sub_epi32(a, b);
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] lv(r, m) == lv(a, m) - lv(b, m) by {
            assert(lv(a, m) <= ba && lv(b, m) <= bb && -ba <= lv(a, m) && -bb <= lv(b, m));
            lemma_sub(u32x8(a)[m], u32x8(b)[m]);
        }
    }
    r
}

/// Times the constant `c`.
#[inline(always)]
fn vmul(a: __m256i, c: i32, Ghost(ba): Ghost<int>, Ghost(bc): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        bnd(a, ba),
        0 <= ba,
        bc == (if c < 0 { -c } else { c as int }) * ba,
        bc < 0x8000_0000,
    ensures
        bnd(r, bc),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(r, m) == lv(a, m) * c,
{
    let k = _mm256_set1_epi32(c);
    let r = _mm256_mullo_epi32(a, k);
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] lv(r, m) == lv(a, m) * c && -bc <= lv(r, m) <= bc by {
            let x = lv(a, m);
            assert(-ba <= x <= ba);
            assert(s32(u32x8(k)[m]) == c);
            let ac: int = if c < 0 { -c } else { c as int };
            assert(-bc <= x * c <= bc) by (nonlinear_arith)
                requires
                    -ba <= x <= ba,
                    ac == (if c < 0 { -c } else { c as int }),
                    bc == ac * ba,
            ;
            lemma_mul(u32x8(a)[m], u32x8(k)[m]);
        }
    }
    r
}

/// The floor of `c - ba` over `d` is at least `-(ba / d) - 1`.
proof fn lemma_floor_lo(ba: int, c: int, d: int)
    requires
        0 <= ba,
        0 <= c,
        0 < d,
    ensures
        (-ba + c) / d >= -(ba / d) - 1,
{
    let q = ba / d;
    let r = ba % d;
    lemma_fundamental_div_mod(ba, d);
    lemma_mod_pos_bound(ba, d);
    assert(-ba + c >= d * (-(q + 1))) by (nonlinear_arith)
        requires
            ba == d * q + r,
            r < d,
            c >= 0,
    ;
    lemma_div_is_ordered(d * (-(q + 1)), -ba + c, d);
    lemma_div_multiples_vanish(-(q + 1), d);
}

/// `descale(x, 11)`: add 2^10, shift right by 11.
#[inline(always)]
fn vds11(a: __m256i, Ghost(ba): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        bnd(a, ba),
        0 <= ba < 0x7000_0000,
    ensures
        bnd(r, ba / 2048 + 1),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(r, m) == descale(lv(a, m), 11),
{
    let k = _mm256_set1_epi32(1024);
    let s = _mm256_add_epi32(a, k);
    let r = _mm256_srai_epi32::<11>(s);
    proof {
        reveal_with_fuel(pow2_spec, 12);
        lemma2_to64();
        assert forall|m: int| 0 <= m < 8 implies #[trigger] lv(r, m) == descale(lv(a, m), 11) && -(ba / 2048 + 1)
            <= lv(r, m) <= ba / 2048 + 1 by {
            let x = lv(a, m);
            assert(-ba <= x <= ba);
            assert(s32(u32x8(k)[m]) == 1024);
            lemma_add(u32x8(a)[m], u32x8(k)[m]);
            let y = x + 1024;
            assert(s32(u32x8(s)[m]) == y);
            lemma_div_is_ordered(y, ba + 1024, 2048);
            lemma_div_is_ordered(-ba + 1024, y, 2048);
            assert((ba + 1024) / 2048 <= ba / 2048 + 1);
            lemma_floor_lo(ba, 1024, 2048);
            lemma_wrap(y / 2048, 0);
        }
    }
    r
}

/// `descale(x, 15)`.
#[inline(always)]
fn vds15(a: __m256i, Ghost(ba): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        bnd(a, ba),
        0 <= ba < 0x7000_0000,
    ensures
        bnd(r, ba / 32768 + 1),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(r, m) == descale(lv(a, m), 15),
{
    let k = _mm256_set1_epi32(16384);
    let s = _mm256_add_epi32(a, k);
    let r = _mm256_srai_epi32::<15>(s);
    proof {
        reveal_with_fuel(pow2_spec, 16);
        lemma2_to64();
        assert forall|m: int| 0 <= m < 8 implies #[trigger] lv(r, m) == descale(lv(a, m), 15) && -(ba / 32768 + 1)
            <= lv(r, m) <= ba / 32768 + 1 by {
            let x = lv(a, m);
            assert(-ba <= x <= ba);
            assert(s32(u32x8(k)[m]) == 16384);
            lemma_add(u32x8(a)[m], u32x8(k)[m]);
            let y = x + 16384;
            lemma_div_is_ordered(y, ba + 16384, 32768);
            lemma_div_is_ordered(-ba + 16384, y, 32768);
            assert((ba + 16384) / 32768 <= ba / 32768 + 1);
            lemma_floor_lo(ba, 16384, 32768);
            lemma_wrap(y / 32768, 0);
        }
    }
    r
}

/// `descale(x, 2)`.
#[inline(always)]
fn vds2(a: __m256i, Ghost(ba): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        bnd(a, ba),
        0 <= ba < 0x7000_0000,
    ensures
        bnd(r, ba / 4 + 1),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(r, m) == descale(lv(a, m), 2),
{
    let k = _mm256_set1_epi32(2);
    let s = _mm256_add_epi32(a, k);
    let r = _mm256_srai_epi32::<2>(s);
    proof {
        reveal_with_fuel(pow2_spec, 3);
        lemma2_to64();
        assert forall|m: int| 0 <= m < 8 implies #[trigger] lv(r, m) == descale(lv(a, m), 2) && -(ba / 4 + 1) <= lv(r,
            m) <= ba / 4 + 1 by {
            let x = lv(a, m);
            assert(-ba <= x <= ba);
            assert(s32(u32x8(k)[m]) == 2);
            lemma_add(u32x8(a)[m], u32x8(k)[m]);
            let y = x + 2;
            lemma_div_is_ordered(y, ba + 2, 4);
            lemma_div_is_ordered(-ba + 2, y, 4);
            assert((ba + 2) / 4 <= ba / 4 + 1);
            lemma_floor_lo(ba, 2, 4);
            lemma_wrap(y / 4, 0);
        }
    }
    r
}

// ---------------------------------------------------------------------------
// One pass
// ---------------------------------------------------------------------------
/// Lane `m` of eight vectors, as a sequence.
pub open spec fn col8(x0: __m256i, x1: __m256i, x2: __m256i, x3: __m256i, x4: __m256i, x5: __m256i, x6: __m256i, x7: __m256i, m: int) -> Seq<int> {
    seq![lv(x0, m), lv(x1, m), lv(x2, m), lv(x3, m), lv(x4, m), lv(x5, m), lv(x6, m), lv(x7, m)]
}

/// Output `k` of a pass, in lane `m`.
pub open spec fn pout(o: __m256i, x0: __m256i, x1: __m256i, x2: __m256i, x3: __m256i, x4: __m256i, x5: __m256i, x6: __m256i, x7: __m256i, first: bool, k: int) -> bool {
    forall|m: int| 0 <= m < 8 ==> #[trigger] lv(o, m) == fdct_1d(col8(x0, x1, x2, x3, x4, x5, x6, x7, m), first)[k]
}

/// The even outputs (0, 2, 4, 6) of a pass, from its sums `a0..a3`
/// (`tmp0..tmp3`).
pub open spec fn pev(a0: int, a1: int, a2: int, a3: int, first: bool) -> Seq<int> {
    let tmp10 = a0 + a3;
    let tmp13 = a0 - a3;
    let tmp11 = a1 + a2;
    let tmp12 = a1 - a2;
    let sh: nat = if first { 11 } else { 15 };
    let o0 = if first { 4 * (tmp10 + tmp11) } else { descale(tmp10 + tmp11, 2) };
    let o4 = if first { 4 * (tmp10 - tmp11) } else { descale(tmp10 - tmp11, 2) };
    let z1 = (tmp12 + tmp13) * 4433;
    let o2 = descale(z1 + tmp13 * 6270, sh);
    let o6 = descale(z1 + tmp12 * (-15137), sh);
    seq![o0, o2, o4, o6]
}

/// The odd outputs (1, 3, 5, 7) of a pass, from its differences
/// `a4..a7` (`tmp4..tmp7`).
pub open spec fn pod(tmp4: int, tmp5: int, tmp6: int, tmp7: int, first: bool) -> Seq<int> {
    let sh: nat = if first { 11 } else { 15 };
    let z1 = tmp4 + tmp7;
    let z2 = tmp5 + tmp6;
    let z3 = tmp4 + tmp6;
    let z4 = tmp5 + tmp7;
    let z5 = (z3 + z4) * 9633;
    let t4 = tmp4 * 2446;
    let t5 = tmp5 * 16819;
    let t6 = tmp6 * 25172;
    let t7 = tmp7 * 12299;
    let z1 = z1 * (-7373);
    let z2 = z2 * (-20995);
    let z3 = z3 * (-16069) + z5;
    let z4 = z4 * (-3196) + z5;
    let o7 = descale(t4 + z1 + z3, sh);
    let o5 = descale(t5 + z2 + z4, sh);
    let o3 = descale(t6 + z2 + z3, sh);
    let o1 = descale(t7 + z1 + z4, sh);
    seq![o1, o3, o5, o7]
}

/// `fdct_1d` split into its even and odd halves.
proof fn lemma_fdct_split(d: Seq<int>, first: bool)
    requires
        d.len() == 8,
    ensures
        ({
            let e = pev(d[0] + d[7], d[1] + d[6], d[2] + d[5], d[3] + d[4], first);
            let o = pod(d[3] - d[4], d[2] - d[5], d[1] - d[6], d[0] - d[7], first);
            &&& fdct_1d(d, first)[0] == e[0]
            &&& fdct_1d(d, first)[2] == e[1]
            &&& fdct_1d(d, first)[4] == e[2]
            &&& fdct_1d(d, first)[6] == e[3]
            &&& fdct_1d(d, first)[1] == o[0]
            &&& fdct_1d(d, first)[3] == o[1]
            &&& fdct_1d(d, first)[5] == o[2]
            &&& fdct_1d(d, first)[7] == o[3]
        }),
{
    reveal(fdct_1d);
}

/// The butterflies at the start of a pass.
#[inline(always)]
fn vbfly(x0: __m256i, x1: __m256i, x2: __m256i, x3: __m256i, x4: __m256i, x5: __m256i, x6: __m256i, x7: __m256i, Ghost(b): Ghost<int>) -> (t: (__m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i))
    requires
        avx2(),
        0 <= b <= 4096,
        bnd(x0, b) && bnd(x1, b) && bnd(x2, b) && bnd(x3, b),
        bnd(x4, b) && bnd(x5, b) && bnd(x6, b) && bnd(x7, b),
    ensures
        bnd(t.0, 2 * b) && bnd(t.1, 2 * b) && bnd(t.2, 2 * b) && bnd(t.3, 2 * b),
        bnd(t.4, 2 * b) && bnd(t.5, 2 * b) && bnd(t.6, 2 * b) && bnd(t.7, 2 * b),
        forall|m: int| 0 <= m < 8 ==> {
            &&& #[trigger] lv(t.0, m) == lv(x0, m) + lv(x7, m)
            &&& lv(t.1, m) == lv(x1, m) + lv(x6, m)
            &&& lv(t.2, m) == lv(x2, m) + lv(x5, m)
            &&& lv(t.3, m) == lv(x3, m) + lv(x4, m)
            &&& lv(t.4, m) == lv(x3, m) - lv(x4, m)
            &&& lv(t.5, m) == lv(x2, m) - lv(x5, m)
            &&& lv(t.6, m) == lv(x1, m) - lv(x6, m)
            &&& lv(t.7, m) == lv(x0, m) - lv(x7, m)
        },
{
    let tmp0 = vadd(x0, x7, Ghost(b), Ghost(b));
    let tmp7 = vsub(x0, x7, Ghost(b), Ghost(b));
    let tmp1 = vadd(x1, x6, Ghost(b), Ghost(b));
    let tmp6 = vsub(x1, x6, Ghost(b), Ghost(b));
    let tmp2 = vadd(x2, x5, Ghost(b), Ghost(b));
    let tmp5 = vsub(x2, x5, Ghost(b), Ghost(b));
    let tmp3 = vadd(x3, x4, Ghost(b), Ghost(b));
    let tmp4 = vsub(x3, x4, Ghost(b), Ghost(b));
    (tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7)
}

/// The even half of a pass, inputs at most `2 * b`.
#[inline(always)]
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
fn veven(tmp0: __m256i, tmp1: __m256i, tmp2: __m256i, tmp3: __m256i, first: bool, Ghost(b): Ghost<int>) -> (o: (__m256i, __m256i, __m256i, __m256i))
    requires
        avx2(),
        b == if first { 128int } else { 4096int },
        bnd(tmp0, 2 * b) && bnd(tmp1, 2 * b) && bnd(tmp2, 2 * b) && bnd(tmp3, 2 * b),
    ensures
        forall|m: int| #![trigger lv(o.0, m)] #![trigger lv(o.1, m)] #![trigger lv(o.2, m)] #![trigger lv(o.3, m)] 0 <= m < 8 ==> {
            let e = pev(lv(tmp0, m), lv(tmp1, m), lv(tmp2, m), lv(tmp3, m), first);
            &&& lv(o.0, m) == e[0]
            &&& lv(o.1, m) == e[1]
            &&& lv(o.2, m) == e[2]
            &&& lv(o.3, m) == e[3]
        },
        !first ==> bnd(o.0, 0x10_0000) && bnd(o.1, 0x10_0000) && bnd(o.2, 0x10_0000) && bnd(o.3, 0x10_0000),
{
    let ghost b2 = 2 * b;
    let tmp10 = vadd(tmp0, tmp3, Ghost(b2), Ghost(b2));
    let tmp13 = vsub(tmp0, tmp3, Ghost(b2), Ghost(b2));
    let tmp11 = vadd(tmp1, tmp2, Ghost(b2), Ghost(b2));
    let tmp12 = vsub(tmp1, tmp2, Ghost(b2), Ghost(b2));
    let ghost b4 = 4 * b;
    let s0 = vadd(tmp10, tmp11, Ghost(b4), Ghost(b4));
    let s4 = vsub(tmp10, tmp11, Ghost(b4), Ghost(b4));
    let o0;
    let o4;
    if first {
        o0 = vmul(s0, 4, Ghost(8 * b), Ghost(32 * b));
        o4 = vmul(s4, 4, Ghost(8 * b), Ghost(32 * b));
    } else {
        o0 = vds2(s0, Ghost(8 * b));
        o4 = vds2(s4, Ghost(8 * b));
    }
    let s1213 = vadd(tmp12, tmp13, Ghost(b4), Ghost(b4));
    let z1 = vmul(s1213, 4433, Ghost(8 * b), Ghost(4433 * 8 * b));
    let m13 = vmul(tmp13, 6270, Ghost(b4), Ghost(6270 * b4));
    let m12 = vmul(tmp12, -15137, Ghost(b4), Ghost(15137 * b4));
    let p2 = vadd(z1, m13, Ghost(4433 * 8 * b), Ghost(6270 * b4));
    let p6 = vadd(z1, m12, Ghost(4433 * 8 * b), Ghost(15137 * b4));
    let ghost bp2 = 4433 * 8 * b + 6270 * b4;
    let ghost bp6 = 4433 * 8 * b + 15137 * b4;
    let o2;
    let o6;
    if first {
        o2 = vds11(p2, Ghost(bp2));
        o6 = vds11(p6, Ghost(bp6));
    } else {
        o2 = vds15(p2, Ghost(bp2));
        o6 = vds15(p6, Ghost(bp6));
    }
    proof {
        assert forall|m: int| 0 <= m < 8 implies {
            let e = pev(lv(tmp0, m), lv(tmp1, m), lv(tmp2, m), lv(tmp3, m), first);
            &&& #[trigger] lv(o0, m) == e[0]
            &&& lv(o2, m) == e[1]
            &&& lv(o4, m) == e[2]
            &&& lv(o6, m) == e[3]
        } by {
            assert(lv(z1, m) == (lv(tmp12, m) + lv(tmp13, m)) * 4433);
            if first {
                assert(lv(o0, m) == 4 * (lv(tmp10, m) + lv(tmp11, m)));
                assert(lv(o4, m) == 4 * (lv(tmp10, m) - lv(tmp11, m)));
            }
        }
    }
    (o0, o2, o4, o6)
}

/// The odd half of a pass, inputs at most `2 * b`.
#[inline(always)]
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
fn vodd(tmp4: __m256i, tmp5: __m256i, tmp6: __m256i, tmp7: __m256i, first: bool, Ghost(b): Ghost<int>) -> (o: (__m256i, __m256i, __m256i, __m256i))
    requires
        avx2(),
        b == if first { 128int } else { 4096int },
        bnd(tmp4, 2 * b) && bnd(tmp5, 2 * b) && bnd(tmp6, 2 * b) && bnd(tmp7, 2 * b),
    ensures
        forall|m: int| #![trigger lv(o.0, m)] #![trigger lv(o.1, m)] #![trigger lv(o.2, m)] #![trigger lv(o.3, m)] 0 <= m < 8 ==> {
            let e = pod(lv(tmp4, m), lv(tmp5, m), lv(tmp6, m), lv(tmp7, m), first);
            &&& lv(o.0, m) == e[0]
            &&& lv(o.1, m) == e[1]
            &&& lv(o.2, m) == e[2]
            &&& lv(o.3, m) == e[3]
        },
        !first ==> bnd(o.0, 0x10_0000) && bnd(o.1, 0x10_0000) && bnd(o.2, 0x10_0000) && bnd(o.3, 0x10_0000),
{
    let ghost b2 = 2 * b;
    let ghost b4 = 4 * b;
    let za = vadd(tmp4, tmp7, Ghost(b2), Ghost(b2));
    let zb = vadd(tmp5, tmp6, Ghost(b2), Ghost(b2));
    let zc = vadd(tmp4, tmp6, Ghost(b2), Ghost(b2));
    let zd = vadd(tmp5, tmp7, Ghost(b2), Ghost(b2));
    let zcd = vadd(zc, zd, Ghost(b4), Ghost(b4));
    let z5 = vmul(zcd, 9633, Ghost(8 * b), Ghost(9633 * 8 * b));
    let t4 = vmul(tmp4, 2446, Ghost(b2), Ghost(2446 * b2));
    let t5 = vmul(tmp5, 16819, Ghost(b2), Ghost(16819 * b2));
    let t6 = vmul(tmp6, 25172, Ghost(b2), Ghost(25172 * b2));
    let t7 = vmul(tmp7, 12299, Ghost(b2), Ghost(12299 * b2));
    let y1 = vmul(za, -7373, Ghost(b4), Ghost(7373 * b4));
    let y2 = vmul(zb, -20995, Ghost(b4), Ghost(20995 * b4));
    let y3m = vmul(zc, -16069, Ghost(b4), Ghost(16069 * b4));
    let y4m = vmul(zd, -3196, Ghost(b4), Ghost(3196 * b4));
    let y3 = vadd(y3m, z5, Ghost(16069 * b4), Ghost(9633 * 8 * b));
    let y4 = vadd(y4m, z5, Ghost(3196 * b4), Ghost(9633 * 8 * b));
    let ghost by3 = 16069 * b4 + 9633 * 8 * b;
    let ghost by4 = 3196 * b4 + 9633 * 8 * b;
    let q7a = vadd(t4, y1, Ghost(2446 * b2), Ghost(7373 * b4));
    let q7 = vadd(q7a, y3, Ghost(2446 * b2 + 7373 * b4), Ghost(by3));
    let q5a = vadd(t5, y2, Ghost(16819 * b2), Ghost(20995 * b4));
    let q5 = vadd(q5a, y4, Ghost(16819 * b2 + 20995 * b4), Ghost(by4));
    let q3a = vadd(t6, y2, Ghost(25172 * b2), Ghost(20995 * b4));
    let q3 = vadd(q3a, y3, Ghost(25172 * b2 + 20995 * b4), Ghost(by3));
    let q1a = vadd(t7, y1, Ghost(12299 * b2), Ghost(7373 * b4));
    let q1 = vadd(q1a, y4, Ghost(12299 * b2 + 7373 * b4), Ghost(by4));
    let ghost bq7 = 2446 * b2 + 7373 * b4 + by3;
    let ghost bq5 = 16819 * b2 + 20995 * b4 + by4;
    let ghost bq3 = 25172 * b2 + 20995 * b4 + by3;
    let ghost bq1 = 12299 * b2 + 7373 * b4 + by4;
    let (o1, o3, o5, o7);
    if first {
        o7 = vds11(q7, Ghost(bq7));
        o5 = vds11(q5, Ghost(bq5));
        o3 = vds11(q3, Ghost(bq3));
        o1 = vds11(q1, Ghost(bq1));
    } else {
        o7 = vds15(q7, Ghost(bq7));
        o5 = vds15(q5, Ghost(bq5));
        o3 = vds15(q3, Ghost(bq3));
        o1 = vds15(q1, Ghost(bq1));
    }
    proof {
        assert forall|m: int| 0 <= m < 8 implies {
            let e = pod(lv(tmp4, m), lv(tmp5, m), lv(tmp6, m), lv(tmp7, m), first);
            &&& #[trigger] lv(o1, m) == e[0]
            &&& lv(o3, m) == e[1]
            &&& lv(o5, m) == e[2]
            &&& lv(o7, m) == e[3]
        } by {
            assert(lv(z5, m) == (lv(zc, m) + lv(zd, m)) * 9633);
            assert(lv(y3, m) == lv(zc, m) * (-16069) + lv(z5, m));
            assert(lv(y4, m) == lv(zd, m) * (-3196) + lv(z5, m));
        }
    }
    (o1, o3, o5, o7)
}

/// The pass over eight vectors, inputs at most 128 for the first and
/// 4096 for the second.
#[inline(always)]
#[verifier::spinoff_prover]
fn vpass(x0: __m256i, x1: __m256i, x2: __m256i, x3: __m256i, x4: __m256i, x5: __m256i, x6: __m256i, x7: __m256i, first: bool) -> (o: (__m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i))
    requires
        avx2(),
        bnd(x0, if first { 128 } else { 4096 }),
        bnd(x1, if first { 128 } else { 4096 }),
        bnd(x2, if first { 128 } else { 4096 }),
        bnd(x3, if first { 128 } else { 4096 }),
        bnd(x4, if first { 128 } else { 4096 }),
        bnd(x5, if first { 128 } else { 4096 }),
        bnd(x6, if first { 128 } else { 4096 }),
        bnd(x7, if first { 128 } else { 4096 }),
    ensures
        pout(o.0, x0, x1, x2, x3, x4, x5, x6, x7, first, 0),
        pout(o.1, x0, x1, x2, x3, x4, x5, x6, x7, first, 1),
        pout(o.2, x0, x1, x2, x3, x4, x5, x6, x7, first, 2),
        pout(o.3, x0, x1, x2, x3, x4, x5, x6, x7, first, 3),
        pout(o.4, x0, x1, x2, x3, x4, x5, x6, x7, first, 4),
        pout(o.5, x0, x1, x2, x3, x4, x5, x6, x7, first, 5),
        pout(o.6, x0, x1, x2, x3, x4, x5, x6, x7, first, 6),
        pout(o.7, x0, x1, x2, x3, x4, x5, x6, x7, first, 7),
        !first ==> bnd(o.0, 0x10_0000) && bnd(o.1, 0x10_0000) && bnd(o.2, 0x10_0000) && bnd(o.3, 0x10_0000) && bnd(
            o.4,
            0x10_0000,
        ) && bnd(o.5, 0x10_0000) && bnd(o.6, 0x10_0000) && bnd(o.7, 0x10_0000),
{
    let ghost b: int = if first { 128 } else { 4096 };
    let (t0, t1, t2, t3, t4, t5, t6, t7) = vbfly(x0, x1, x2, x3, x4, x5, x6, x7, Ghost(b));
    let (o0, o2, o4, o6) = veven(t0, t1, t2, t3, first, Ghost(b));
    let (o1, o3, o5, o7) = vodd(t4, t5, t6, t7, first, Ghost(b));
    proof {
        assert forall|m: int|
            #![trigger lv(o0, m)]
            #![trigger lv(o1, m)]
            #![trigger lv(o2, m)]
            #![trigger lv(o3, m)]
            #![trigger lv(o4, m)]
            #![trigger lv(o5, m)]
            #![trigger lv(o6, m)]
            #![trigger lv(o7, m)]
            0 <= m < 8 implies {
            &&& lv(o0, m) == fdct_1d(col8(x0, x1, x2, x3, x4, x5, x6, x7, m), first)[0]
            &&& lv(o1, m) == fdct_1d(col8(x0, x1, x2, x3, x4, x5, x6, x7, m), first)[1]
            &&& lv(o2, m) == fdct_1d(col8(x0, x1, x2, x3, x4, x5, x6, x7, m), first)[2]
            &&& lv(o3, m) == fdct_1d(col8(x0, x1, x2, x3, x4, x5, x6, x7, m), first)[3]
            &&& lv(o4, m) == fdct_1d(col8(x0, x1, x2, x3, x4, x5, x6, x7, m), first)[4]
            &&& lv(o5, m) == fdct_1d(col8(x0, x1, x2, x3, x4, x5, x6, x7, m), first)[5]
            &&& lv(o6, m) == fdct_1d(col8(x0, x1, x2, x3, x4, x5, x6, x7, m), first)[6]
            &&& lv(o7, m) == fdct_1d(col8(x0, x1, x2, x3, x4, x5, x6, x7, m), first)[7]
        } by {
            let d = col8(x0, x1, x2, x3, x4, x5, x6, x7, m);
            assert(d[0] == lv(x0, m) && d[1] == lv(x1, m) && d[2] == lv(x2, m) && d[3] == lv(x3, m));
            assert(d[4] == lv(x4, m) && d[5] == lv(x5, m) && d[6] == lv(x6, m) && d[7] == lv(x7, m));
            assert(lv(t0, m) == d[0] + d[7]);
            lemma_fdct_split(d, first);
        }
    }
    (o0, o1, o2, o3, o4, o5, o6, o7)
}

// ---------------------------------------------------------------------------
// The first pass's output bounds
// ---------------------------------------------------------------------------
/// The first pass maps inputs of at most 128 to at most 4096 (outputs 0
/// and 4) or 3785.
pub proof fn lemma_pass1_bound(d: Seq<int>)
    requires
        d.len() == 8,
        forall|j: int| 0 <= j < 8 ==> -128 <= #[trigger] d[j] <= 128,
    ensures
        -4096 <= fdct_1d(d, true)[0] <= 4096,
        -4096 <= fdct_1d(d, true)[4] <= 4096,
        -3785 <= fdct_1d(d, true)[1] <= 3785,
        -3785 <= fdct_1d(d, true)[2] <= 3785,
        -3785 <= fdct_1d(d, true)[3] <= 3785,
        -3785 <= fdct_1d(d, true)[5] <= 3785,
        -3785 <= fdct_1d(d, true)[6] <= 3785,
        -3785 <= fdct_1d(d, true)[7] <= 3785,
{
    reveal(fdct_1d);
    lemma2_to64();
    let (d0, d1, d2, d3, d4, d5, d6, d7) = (d[0], d[1], d[2], d[3], d[4], d[5], d[6], d[7]);
    assert(-128 <= d0 <= 128 && -128 <= d1 <= 128 && -128 <= d2 <= 128 && -128 <= d3 <= 128);
    assert(-128 <= d4 <= 128 && -128 <= d5 <= 128 && -128 <= d6 <= 128 && -128 <= d7 <= 128);
    let tmp0 = d0 + d7;
    let tmp7 = d0 - d7;
    let tmp1 = d1 + d6;
    let tmp6 = d1 - d6;
    let tmp2 = d2 + d5;
    let tmp5 = d2 - d5;
    let tmp3 = d3 + d4;
    let tmp4 = d3 - d4;
    let tmp10 = tmp0 + tmp3;
    let tmp13 = tmp0 - tmp3;
    let tmp11 = tmp1 + tmp2;
    let tmp12 = tmp1 - tmp2;
    let z1 = (tmp12 + tmp13) * 4433;
    let p2 = z1 + tmp13 * 6270;
    let p6 = z1 + tmp12 * (-15137);
    let za = tmp4 + tmp7;
    let zb = tmp5 + tmp6;
    let zc = tmp4 + tmp6;
    let zd = tmp5 + tmp7;
    let z5 = (zc + zd) * 9633;
    let y3 = zc * (-16069) + z5;
    let y4 = zd * (-3196) + z5;
    let q7 = tmp4 * 2446 + za * (-7373) + y3;
    let q5 = tmp5 * 16819 + zb * (-20995) + y4;
    let q3 = tmp6 * 25172 + zb * (-20995) + y3;
    let q1 = tmp7 * 12299 + za * (-7373) + y4;
    assert(-7750144 <= p2 <= 7750144);
    assert(-7750144 <= p6 <= 7750144);
    assert(-7601408 <= q7 <= 7601408);
    assert(-7601408 <= q5 <= 7601408);
    assert(-7601408 <= q3 <= 7601408);
    assert(-7601408 <= q1 <= 7601408);
    lemma_ds11_bound(p2);
    lemma_ds11_bound(p6);
    lemma_ds11_bound(q7);
    lemma_ds11_bound(q5);
    lemma_ds11_bound(q3);
    lemma_ds11_bound(q1);
}

proof fn lemma_ds11_bound(x: int)
    requires
        -7750144 <= x <= 7750144,
    ensures
        -3785 <= descale(x, 11) <= 3785,
{
    lemma2_to64();
    lemma_div_is_ordered(x + 1024, 7750144int + 1024, 2048);
    lemma_div_is_ordered(-7750144int + 1024, x + 1024, 2048);
}

// ---------------------------------------------------------------------------
// Transposing
// ---------------------------------------------------------------------------
/// Vector `j` of the result holds lane `j` of each input, input `m` in
/// lane `m`.
#[inline(always)]
#[verifier::spinoff_prover]
fn tr8x(x0: __m256i, x1: __m256i, x2: __m256i, x3: __m256i, x4: __m256i, x5: __m256i, x6: __m256i, x7: __m256i) -> (t: (__m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i))
    requires
        avx2(),
    ensures
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t.0, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 0),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t.1, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 1),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t.2, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 2),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t.3, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 3),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t.4, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 4),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t.5, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 5),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t.6, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 6),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t.7, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 7),
{
    let (a0, a1, a2, a3) = tr4(x0, x1, x2, x3);
    let (b0, b1, b2, b3) = tr4(x4, x5, x6, x7);
    let t0 = _mm256_permute2x128_si256::<0x20>(a0, b0);
    let t1 = _mm256_permute2x128_si256::<0x20>(a1, b1);
    let t2 = _mm256_permute2x128_si256::<0x20>(a2, b2);
    let t3 = _mm256_permute2x128_si256::<0x20>(a3, b3);
    let t4 = _mm256_permute2x128_si256::<0x31>(a0, b0);
    let t5 = _mm256_permute2x128_si256::<0x31>(a1, b1);
    let t6 = _mm256_permute2x128_si256::<0x31>(a2, b2);
    let t7 = _mm256_permute2x128_si256::<0x31>(a3, b3);
    proof {
        lemma_perm_u32(a0, b0, t0, 0x20);
        lemma_perm_u32(a1, b1, t1, 0x20);
        lemma_perm_u32(a2, b2, t2, 0x20);
        lemma_perm_u32(a3, b3, t3, 0x20);
        lemma_perm_u32(a0, b0, t4, 0x31);
        lemma_perm_u32(a1, b1, t5, 0x31);
        lemma_perm_u32(a2, b2, t6, 0x31);
        lemma_perm_u32(a3, b3, t7, 0x31);
        assert forall|m: int| 0 <= m < 8 implies {
            &&& #[trigger] lv(t0, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 0)
            &&& lv(t1, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 1)
            &&& lv(t2, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 2)
            &&& lv(t3, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 3)
            &&& lv(t4, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 4)
            &&& lv(t5, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 5)
            &&& lv(t6, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 6)
            &&& lv(t7, m) == lv(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m), 7)
        } by {
            if m < 4 {
                assert(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m) == pick4(x0, x1, x2, x3, m));
            } else {
                assert(pick8x(x0, x1, x2, x3, x4, x5, x6, x7, m) == pick4(x4, x5, x6, x7, m - 4));
            }
        }
    }
    (t0, t1, t2, t3, t4, t5, t6, t7)
}

pub open spec fn pick8x(x0: __m256i, x1: __m256i, x2: __m256i, x3: __m256i, x4: __m256i, x5: __m256i, x6: __m256i, x7: __m256i, i: int) -> __m256i {
    if i < 4 {
        pick4(x0, x1, x2, x3, i)
    } else {
        pick4(x4, x5, x6, x7, i - 4)
    }
}


// ---------------------------------------------------------------------------
// A block
// ---------------------------------------------------------------------------
/// Row `r` of block (`bx`, `by`), less 128, one sample per lane.
#[inline(always)]
fn load_row(pl: &Vec<Vec<u8>>, bx: usize, by: usize, r: usize) -> (x: __m256i)
    requires
        avx2(),
        r < 8,
        8 * by + 8 <= pl@.len(),
        forall|y: int| 8 * by <= y < 8 * by + 8 ==> 8 * bx + 8 <= (#[trigger] pl@[y])@.len(),
        bx < 0x1000_0000,
        by < 0x1000_0000,
    ensures
        forall|j: int| 0 <= j < 8 ==> #[trigger] lv(x, j) == pblock(pl@, bx as int, by as int)[8 * r + j],
        bnd(x, 128),
{
    let row = &pl[8 * by + r];
    let v = loadl64_u8(row.as_slice(), 8 * bx);
    let w = _mm256_cvtepu8_epi32(v);
    let k = _mm256_set1_epi32(128);
    let x = _mm256_sub_epi32(w, k);
    proof {
        assert forall|j: int| 0 <= j < 8 implies #[trigger] lv(x, j) == pblock(pl@, bx as int, by as int)[8 * r + j]
            && -128 <= lv(x, j) <= 128 by {
            assert(u32x8(w)[j] == b128(v)[j] as u32);
            assert(b128(v)[j] == row@[8 * bx + j]);
            assert(s32(u32x8(w)[j]) == row@[8 * bx + j] as int);
            assert(s32(u32x8(k)[j]) == 128);
            lemma_sub(u32x8(w)[j], u32x8(k)[j]);
            assert((8 * r + j) / 8 == r as int && (8 * r + j) % 8 == j);
        }
    }
    x
}

/// The `i32` with the bits of `x`.
#[inline(always)]
fn i64_of_lane(x: u32) -> (r: i64)
    ensures
        r as int == s32(x),
{
    if x < 0x8000_0000 {
        x as i64
    } else {
        x as i64 - 0x1_0000_0000
    }
}

/// The forward DCT of block (`bx`, `by`) of a plane, as `fdct_x` computes
/// it from the block's samples.
#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "avx2"))]
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub fn fdct_block(pl: &Vec<Vec<u8>>, bx: usize, by: usize) -> (t: [i64; 64])
    requires
        avx2(),
        8 * by + 8 <= pl@.len(),
        forall|y: int| 8 * by <= y < 8 * by + 8 ==> 8 * bx + 8 <= (#[trigger] pl@[y])@.len(),
        bx < 0x1000_0000,
        by < 0x1000_0000,
    ensures
        forall|i: int| 0 <= i < 64 ==> #[trigger] t[i] as int == fdct(pblock(pl@, bx as int, by as int))[i],
        forall|i: int| 0 <= i < 64 ==> -(1i64 << 20) <= #[trigger] t[i] <= (1i64 << 20),
{
    let ghost s = pblock(pl@, bx as int, by as int);
    let ghost rows = fdct_rows(s);
    let l0 = load_row(pl, bx, by, 0);
    let l1 = load_row(pl, bx, by, 1);
    let l2 = load_row(pl, bx, by, 2);
    let l3 = load_row(pl, bx, by, 3);
    let l4 = load_row(pl, bx, by, 4);
    let l5 = load_row(pl, bx, by, 5);
    let l6 = load_row(pl, bx, by, 6);
    let l7 = load_row(pl, bx, by, 7);
    let (t0, t1, t2, t3, t4, t5, t6, t7) = tr8x(l0, l1, l2, l3, l4, l5, l6, l7);
    proof {
        lemma_tr_rows(l0, l1, l2, l3, l4, l5, l6, l7, t0, t1, t2, t3, t4, t5, t6, t7, s);
    }
    let (p0, p1, p2, p3, p4, p5, p6, p7) = vpass(t0, t1, t2, t3, t4, t5, t6, t7, true);
    proof {
        lemma_rows_out(t0, t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6, p7, s);
    }
    let (q0, q1, q2, q3, q4, q5, q6, q7) = tr8x(p0, p1, p2, p3, p4, p5, p6, p7);
    proof {
        lemma_tr_cols(p0, p1, p2, p3, p4, p5, p6, p7, q0, q1, q2, q3, q4, q5, q6, q7, rows);
    }
    let (o0, o1, o2, o3, o4, o5, o6, o7) = vpass(q0, q1, q2, q3, q4, q5, q6, q7, false);
    proof {
        lemma_out(q0, q1, q2, q3, q4, q5, q6, q7, rows, s);
    }
    let mut t = [0i64; 64];
    emit(&mut t, 0, o0);
    emit(&mut t, 1, o1);
    emit(&mut t, 2, o2);
    emit(&mut t, 3, o3);
    emit(&mut t, 4, o4);
    emit(&mut t, 5, o5);
    emit(&mut t, 6, o6);
    emit(&mut t, 7, o7);
    proof {
        lemma_final(t, o0, o1, o2, o3, o4, o5, o6, o7, q0, q1, q2, q3, q4, q5, q6, q7, s);
    }
    t
}

/// The emitted rows are `fdct`'s.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_final(t: [i64; 64], o0: __m256i, o1: __m256i, o2: __m256i, o3: __m256i, o4: __m256i, o5: __m256i, o6: __m256i, o7: __m256i, q0: __m256i, q1: __m256i, q2: __m256i, q3: __m256i, q4: __m256i, q5: __m256i, q6: __m256i, q7: __m256i, s: Seq<int>)
    requires
        forall|u: int| 0 <= u < 8 ==> #[trigger] t[u] as int == lv(o0, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] t[8 + u] as int == lv(o1, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] t[16 + u] as int == lv(o2, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] t[24 + u] as int == lv(o3, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] t[32 + u] as int == lv(o4, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] t[40 + u] as int == lv(o5, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] t[48 + u] as int == lv(o6, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] t[56 + u] as int == lv(o7, u),
        pout(o0, q0, q1, q2, q3, q4, q5, q6, q7, false, 0),
        pout(o1, q0, q1, q2, q3, q4, q5, q6, q7, false, 1),
        pout(o2, q0, q1, q2, q3, q4, q5, q6, q7, false, 2),
        pout(o3, q0, q1, q2, q3, q4, q5, q6, q7, false, 3),
        pout(o4, q0, q1, q2, q3, q4, q5, q6, q7, false, 4),
        pout(o5, q0, q1, q2, q3, q4, q5, q6, q7, false, 5),
        pout(o6, q0, q1, q2, q3, q4, q5, q6, q7, false, 6),
        pout(o7, q0, q1, q2, q3, q4, q5, q6, q7, false, 7),
        bnd(o0, 0x10_0000) && bnd(o1, 0x10_0000) && bnd(o2, 0x10_0000) && bnd(o3, 0x10_0000),
        bnd(o4, 0x10_0000) && bnd(o5, 0x10_0000) && bnd(o6, 0x10_0000) && bnd(o7, 0x10_0000),
        forall|v: int, u: int| 0 <= v < 8 && 0 <= u < 8 ==> #[trigger] fdct_1d(col8(q0, q1, q2, q3, q4, q5, q6, q7, u), false)[v] == fdct(s)[8 * v + u],
    ensures
        forall|i: int| 0 <= i < 64 ==> #[trigger] t[i] as int == fdct(s)[i],
        forall|i: int| 0 <= i < 64 ==> -(1i64 << 20) <= #[trigger] t[i] <= (1i64 << 20),
{
    assert((1i64 << 20) == 0x10_0000) by (bit_vector);
    assert forall|i: int| 0 <= i < 64 implies #[trigger] t[i] as int == fdct(s)[i] && -0x10_0000 <= t[i] <= 0x10_0000 by {
        let v = i / 8;
        let u = i % 8;
        assert(i == 8 * v + u);
        assert(fdct_1d(col8(q0, q1, q2, q3, q4, q5, q6, q7, u), false)[v] == fdct(s)[8 * v + u]);
        if v == 0 {
            assert(t[u] as int == lv(o0, u));
        } else if v == 1 {
            assert(t[8 + u] as int == lv(o1, u));
        } else if v == 2 {
            assert(t[16 + u] as int == lv(o2, u));
        } else if v == 3 {
            assert(t[24 + u] as int == lv(o3, u));
        } else if v == 4 {
            assert(t[32 + u] as int == lv(o4, u));
        } else if v == 5 {
            assert(t[40 + u] as int == lv(o5, u));
        } else if v == 6 {
            assert(t[48 + u] as int == lv(o6, u));
        } else {
            assert(t[56 + u] as int == lv(o7, u));
        }
    }
}

/// The forward DCT of block (`bx`, `by`) of a plane, as `fdct_x` computes
/// it from the block's samples.
#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "avx2"))]
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub fn fdct_block32(pl: &Vec<Vec<u8>>, bx: usize, by: usize) -> (t: [u32; 64])
    requires
        avx2(),
        8 * by + 8 <= pl@.len(),
        forall|y: int| 8 * by <= y < 8 * by + 8 ==> 8 * bx + 8 <= (#[trigger] pl@[y])@.len(),
        bx < 0x1000_0000,
        by < 0x1000_0000,
    ensures
        forall|i: int| 0 <= i < 64 ==> #[trigger] s32(t[i]) == fdct(pblock(pl@, bx as int, by as int))[i],
        forall|i: int| 0 <= i < 64 ==> -0x10_0000 <= #[trigger] s32(t[i]) <= 0x10_0000,
{
    let ghost s = pblock(pl@, bx as int, by as int);
    let ghost rows = fdct_rows(s);
    let l0 = load_row(pl, bx, by, 0);
    let l1 = load_row(pl, bx, by, 1);
    let l2 = load_row(pl, bx, by, 2);
    let l3 = load_row(pl, bx, by, 3);
    let l4 = load_row(pl, bx, by, 4);
    let l5 = load_row(pl, bx, by, 5);
    let l6 = load_row(pl, bx, by, 6);
    let l7 = load_row(pl, bx, by, 7);
    let (t0, t1, t2, t3, t4, t5, t6, t7) = tr8x(l0, l1, l2, l3, l4, l5, l6, l7);
    proof {
        lemma_tr_rows(l0, l1, l2, l3, l4, l5, l6, l7, t0, t1, t2, t3, t4, t5, t6, t7, s);
    }
    let (p0, p1, p2, p3, p4, p5, p6, p7) = vpass(t0, t1, t2, t3, t4, t5, t6, t7, true);
    proof {
        lemma_rows_out(t0, t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6, p7, s);
    }
    let (q0, q1, q2, q3, q4, q5, q6, q7) = tr8x(p0, p1, p2, p3, p4, p5, p6, p7);
    proof {
        lemma_tr_cols(p0, p1, p2, p3, p4, p5, p6, p7, q0, q1, q2, q3, q4, q5, q6, q7, rows);
    }
    let (o0, o1, o2, o3, o4, o5, o6, o7) = vpass(q0, q1, q2, q3, q4, q5, q6, q7, false);
    proof {
        lemma_out(q0, q1, q2, q3, q4, q5, q6, q7, rows, s);
    }
    let mut t = [0u32; 64];
    emit32(&mut t, 0, o0);
    emit32(&mut t, 1, o1);
    emit32(&mut t, 2, o2);
    emit32(&mut t, 3, o3);
    emit32(&mut t, 4, o4);
    emit32(&mut t, 5, o5);
    emit32(&mut t, 6, o6);
    emit32(&mut t, 7, o7);
    proof {
        lemma_final32(t, o0, o1, o2, o3, o4, o5, o6, o7, q0, q1, q2, q3, q4, q5, q6, q7, s);
    }
    t
}

/// The emitted rows are `fdct`'s.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_final32(t: [u32; 64], o0: __m256i, o1: __m256i, o2: __m256i, o3: __m256i, o4: __m256i, o5: __m256i, o6: __m256i, o7: __m256i, q0: __m256i, q1: __m256i, q2: __m256i, q3: __m256i, q4: __m256i, q5: __m256i, q6: __m256i, q7: __m256i, s: Seq<int>)
    requires
        forall|u: int| 0 <= u < 8 ==> #[trigger] s32(t[u]) == lv(o0, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] s32(t[8 + u]) == lv(o1, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] s32(t[16 + u]) == lv(o2, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] s32(t[24 + u]) == lv(o3, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] s32(t[32 + u]) == lv(o4, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] s32(t[40 + u]) == lv(o5, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] s32(t[48 + u]) == lv(o6, u),
        forall|u: int| 0 <= u < 8 ==> #[trigger] s32(t[56 + u]) == lv(o7, u),
        pout(o0, q0, q1, q2, q3, q4, q5, q6, q7, false, 0),
        pout(o1, q0, q1, q2, q3, q4, q5, q6, q7, false, 1),
        pout(o2, q0, q1, q2, q3, q4, q5, q6, q7, false, 2),
        pout(o3, q0, q1, q2, q3, q4, q5, q6, q7, false, 3),
        pout(o4, q0, q1, q2, q3, q4, q5, q6, q7, false, 4),
        pout(o5, q0, q1, q2, q3, q4, q5, q6, q7, false, 5),
        pout(o6, q0, q1, q2, q3, q4, q5, q6, q7, false, 6),
        pout(o7, q0, q1, q2, q3, q4, q5, q6, q7, false, 7),
        bnd(o0, 0x10_0000) && bnd(o1, 0x10_0000) && bnd(o2, 0x10_0000) && bnd(o3, 0x10_0000),
        bnd(o4, 0x10_0000) && bnd(o5, 0x10_0000) && bnd(o6, 0x10_0000) && bnd(o7, 0x10_0000),
        forall|v: int, u: int| 0 <= v < 8 && 0 <= u < 8 ==> #[trigger] fdct_1d(col8(q0, q1, q2, q3, q4, q5, q6, q7, u), false)[v] == fdct(s)[8 * v + u],
    ensures
        forall|i: int| 0 <= i < 64 ==> #[trigger] s32(t[i]) == fdct(s)[i],
        forall|i: int| 0 <= i < 64 ==> -0x10_0000 <= #[trigger] s32(t[i]) <= 0x10_0000,
{
    assert forall|i: int| 0 <= i < 64 implies #[trigger] s32(t[i]) == fdct(s)[i] && -0x10_0000 <= s32(t[i]) <= 0x10_0000 by {
        let v = i / 8;
        let u = i % 8;
        assert(i == 8 * v + u);
        assert(fdct_1d(col8(q0, q1, q2, q3, q4, q5, q6, q7, u), false)[v] == fdct(s)[8 * v + u]);
        if v == 0 {
            assert(s32(t[u]) == lv(o0, u));
        } else if v == 1 {
            assert(s32(t[8 + u]) == lv(o1, u));
        } else if v == 2 {
            assert(s32(t[16 + u]) == lv(o2, u));
        } else if v == 3 {
            assert(s32(t[24 + u]) == lv(o3, u));
        } else if v == 4 {
            assert(s32(t[32 + u]) == lv(o4, u));
        } else if v == 5 {
            assert(s32(t[40 + u]) == lv(o5, u));
        } else if v == 6 {
            assert(s32(t[48 + u]) == lv(o6, u));
        } else {
            assert(s32(t[56 + u]) == lv(o7, u));
        }
    }
}

/// Lanes `0..8` of `o` as row `v` of `t`, as they are.
#[inline(always)]
fn emit32(t: &mut [u32; 64], v: usize, o: __m256i)
    requires
        avx2(),
        v < 8,
    ensures
        forall|u: int| 0 <= u < 8 ==> #[trigger] s32(final(t)[8 * v + u]) == lv(o, u),
        forall|i: int| 0 <= i < 64 && (i < 8 * v || i >= 8 * v + 8) ==> #[trigger] final(t)[i] == old(t)[i],
{
    store256_u32(t, 8 * v, o);
    proof {
        assert forall|u: int| 0 <= u < 8 implies #[trigger] s32(t[8 * v + u]) == lv(o, u) by {
            assert(t[8 * v + u] == u32x8(o)[u]);
        }
    }
}

/// Lanes `0..8` of `o` as row `v` of `t`.
#[inline(always)]
fn emit(t: &mut [i64; 64], v: usize, o: __m256i)
    requires
        avx2(),
        v < 8,
    ensures
        forall|u: int| 0 <= u < 8 ==> #[trigger] final(t)[8 * v + u] as int == lv(o, u),
        forall|i: int| 0 <= i < 64 && (i < 8 * v || i >= 8 * v + 8) ==> #[trigger] final(t)[i] == old(t)[i],
{
    let mut b = [0u32; 8];
    store256_u32(&mut b, 0, o);
    proof {
        assert(b@ =~= u32x8(o));
    }
    let mut u: usize = 0;
    while u < 8
        invariant
            v < 8,
            u <= 8,
            b@ == u32x8(o),
            forall|k: int| 0 <= k < u ==> #[trigger] t[8 * v + k] as int == lv(o, k),
            forall|i: int| 0 <= i < 64 && (i < 8 * v || i >= 8 * v + 8) ==> #[trigger] t[i] == old(t)[i],
        decreases 8 - u,
    {
        t[8 * v + u] = i64_of_lane(b[u]);
        u = u + 1;
    }
}

/// After the first transpose, lane `m` of vector `j` is sample (`m`, `j`).
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
proof fn lemma_tr_rows(l0: __m256i, l1: __m256i, l2: __m256i, l3: __m256i, l4: __m256i, l5: __m256i, l6: __m256i, l7: __m256i, t0: __m256i, t1: __m256i, t2: __m256i, t3: __m256i, t4: __m256i, t5: __m256i, t6: __m256i, t7: __m256i, s: Seq<int>)
    requires
        forall|j: int| 0 <= j < 8 ==> #[trigger] lv(l0, j) == s[j],
        forall|j: int| 0 <= j < 8 ==> #[trigger] lv(l1, j) == s[8 + j],
        forall|j: int| 0 <= j < 8 ==> #[trigger] lv(l2, j) == s[16 + j],
        forall|j: int| 0 <= j < 8 ==> #[trigger] lv(l3, j) == s[24 + j],
        forall|j: int| 0 <= j < 8 ==> #[trigger] lv(l4, j) == s[32 + j],
        forall|j: int| 0 <= j < 8 ==> #[trigger] lv(l5, j) == s[40 + j],
        forall|j: int| 0 <= j < 8 ==> #[trigger] lv(l6, j) == s[48 + j],
        forall|j: int| 0 <= j < 8 ==> #[trigger] lv(l7, j) == s[56 + j],
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t0, m) == lv(pick8x(l0, l1, l2, l3, l4, l5, l6, l7, m), 0),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t1, m) == lv(pick8x(l0, l1, l2, l3, l4, l5, l6, l7, m), 1),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t2, m) == lv(pick8x(l0, l1, l2, l3, l4, l5, l6, l7, m), 2),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t3, m) == lv(pick8x(l0, l1, l2, l3, l4, l5, l6, l7, m), 3),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t4, m) == lv(pick8x(l0, l1, l2, l3, l4, l5, l6, l7, m), 4),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t5, m) == lv(pick8x(l0, l1, l2, l3, l4, l5, l6, l7, m), 5),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t6, m) == lv(pick8x(l0, l1, l2, l3, l4, l5, l6, l7, m), 6),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(t7, m) == lv(pick8x(l0, l1, l2, l3, l4, l5, l6, l7, m), 7),
        bnd(l0, 128) && bnd(l1, 128) && bnd(l2, 128) && bnd(l3, 128) && bnd(l4, 128) && bnd(l5, 128) && bnd(l6, 128) && bnd(l7, 128),
    ensures
        forall|m: int| 0 <= m < 8 ==> #[trigger] col8(t0, t1, t2, t3, t4, t5, t6, t7, m) == Seq::new(8, |j: int| s[8 * m + j]),
        bnd(t0, 128) && bnd(t1, 128) && bnd(t2, 128) && bnd(t3, 128) && bnd(t4, 128) && bnd(t5, 128) && bnd(t6, 128) && bnd(t7, 128),
{
    assert forall|m: int| 0 <= m < 8 implies #[trigger] col8(t0, t1, t2, t3, t4, t5, t6, t7, m) =~= Seq::new(8, |j: int| s[8 * m + j]) && -128 <= lv(t0, m) <= 128 && -128 <= lv(t1, m) <= 128 && -128 <= lv(t2, m) <= 128 && -128 <= lv(t3, m) <= 128 && -128 <= lv(t4, m) <= 128 && -128 <= lv(t5, m) <= 128 && -128 <= lv(t6, m) <= 128 && -128 <= lv(t7, m) <= 128 by {
        let l = pick8x(l0, l1, l2, l3, l4, l5, l6, l7, m);
        assert(forall|j: int| 0 <= j < 8 ==> #[trigger] lv(l, j) == s[8 * m + j] && -128 <= lv(l, j) <= 128) by {
            if m == 0 {} else if m == 1 {} else if m == 2 {} else if m == 3 {} else if m == 4 {} else if m == 5 {} else if m == 6 {} else {}
        }
        assert(lv(l, 0) == s[8 * m] && lv(l, 1) == s[8 * m + 1] && lv(l, 2) == s[8 * m + 2] && lv(l, 3) == s[8 * m + 3]);
        assert(lv(l, 4) == s[8 * m + 4] && lv(l, 5) == s[8 * m + 5] && lv(l, 6) == s[8 * m + 6] && lv(l, 7) == s[8 * m + 7]);
        assert(-128 <= lv(l, 0) <= 128 && -128 <= lv(l, 1) <= 128 && -128 <= lv(l, 2) <= 128 && -128 <= lv(l, 3) <= 128);
        assert(-128 <= lv(l, 4) <= 128 && -128 <= lv(l, 5) <= 128 && -128 <= lv(l, 6) <= 128 && -128 <= lv(l, 7) <= 128);
    }
}

/// After the first pass, lane `m` of vector `k` is the first pass's output
/// `k` of row `m`.
proof fn lemma_rows_out(t0: __m256i, t1: __m256i, t2: __m256i, t3: __m256i, t4: __m256i, t5: __m256i, t6: __m256i, t7: __m256i, p0: __m256i, p1: __m256i, p2: __m256i, p3: __m256i, p4: __m256i, p5: __m256i, p6: __m256i, p7: __m256i, s: Seq<int>)
    requires
        s.len() == 64,
        forall|i: int| 0 <= i < 64 ==> -128 <= #[trigger] s[i] <= 128,
        forall|m: int| 0 <= m < 8 ==> #[trigger] col8(t0, t1, t2, t3, t4, t5, t6, t7, m) == Seq::new(8, |j: int| s[8 * m + j]),
        pout(p0, t0, t1, t2, t3, t4, t5, t6, t7, true, 0),
        pout(p1, t0, t1, t2, t3, t4, t5, t6, t7, true, 1),
        pout(p2, t0, t1, t2, t3, t4, t5, t6, t7, true, 2),
        pout(p3, t0, t1, t2, t3, t4, t5, t6, t7, true, 3),
        pout(p4, t0, t1, t2, t3, t4, t5, t6, t7, true, 4),
        pout(p5, t0, t1, t2, t3, t4, t5, t6, t7, true, 5),
        pout(p6, t0, t1, t2, t3, t4, t5, t6, t7, true, 6),
        pout(p7, t0, t1, t2, t3, t4, t5, t6, t7, true, 7),
    ensures
        forall|m: int| #![trigger lv(p0, m)] #![trigger lv(p1, m)] #![trigger lv(p2, m)] #![trigger lv(p3, m)] #![trigger lv(p4, m)] #![trigger lv(p5, m)] #![trigger lv(p6, m)] #![trigger lv(p7, m)] 0 <= m < 8 ==> lv(p0, m) == fdct_rows(s)[8 * m] && lv(p1, m) == fdct_rows(s)[8 * m + 1]
            && lv(p2, m) == fdct_rows(s)[8 * m + 2] && lv(p3, m) == fdct_rows(s)[8 * m + 3] && lv(p4, m) == fdct_rows(s)[8 * m + 4]
            && lv(p5, m) == fdct_rows(s)[8 * m + 5] && lv(p6, m) == fdct_rows(s)[8 * m + 6] && lv(p7, m) == fdct_rows(s)[8 * m + 7],
        bnd(p0, 4096) && bnd(p1, 4096) && bnd(p2, 4096) && bnd(p3, 4096) && bnd(p4, 4096) && bnd(p5, 4096) && bnd(p6, 4096) && bnd(p7, 4096),
{
    assert forall|m: int| #![trigger lv(p0, m)] #![trigger lv(p1, m)] #![trigger lv(p2, m)] #![trigger lv(p3, m)] #![trigger lv(p4, m)] #![trigger lv(p5, m)] #![trigger lv(p6, m)] #![trigger lv(p7, m)] 0 <= m < 8 implies lv(p0, m) == fdct_rows(s)[8 * m] && lv(p1, m) == fdct_rows(s)[8 * m + 1]
        && lv(p2, m) == fdct_rows(s)[8 * m + 2] && lv(p3, m) == fdct_rows(s)[8 * m + 3] && lv(p4, m) == fdct_rows(s)[8 * m + 4]
        && lv(p5, m) == fdct_rows(s)[8 * m + 5] && lv(p6, m) == fdct_rows(s)[8 * m + 6] && lv(p7, m) == fdct_rows(s)[8 * m + 7]
        && -4096 <= lv(p0, m) <= 4096 && -4096 <= lv(p1, m) <= 4096 && -4096 <= lv(p2, m) <= 4096 && -4096 <= lv(p3, m) <= 4096
        && -4096 <= lv(p4, m) <= 4096 && -4096 <= lv(p5, m) <= 4096 && -4096 <= lv(p6, m) <= 4096 && -4096 <= lv(p7, m) <= 4096 by {
        let d = Seq::new(8, |j: int| s[8 * m + j]);
        assert(col8(t0, t1, t2, t3, t4, t5, t6, t7, m) == d);
        lemma_pass1_bound(d);
        assert forall|k: int| 0 <= k < 8 implies #[trigger] fdct_rows(s)[8 * m + k] == fdct_1d(d, true)[k] by {
            assert((8 * m + k) / 8 == m && (8 * m + k) % 8 == k);
            assert(Seq::new(8, |j: int| s[8 * ((8 * m + k) / 8) + j]) =~= d);
        }
        assert(fdct_rows(s)[8 * m] == fdct_1d(d, true)[0]);
        assert(fdct_rows(s)[8 * m + 1] == fdct_1d(d, true)[1]);
        assert(fdct_rows(s)[8 * m + 2] == fdct_1d(d, true)[2]);
        assert(fdct_rows(s)[8 * m + 3] == fdct_1d(d, true)[3]);
        assert(fdct_rows(s)[8 * m + 4] == fdct_1d(d, true)[4]);
        assert(fdct_rows(s)[8 * m + 5] == fdct_1d(d, true)[5]);
        assert(fdct_rows(s)[8 * m + 6] == fdct_1d(d, true)[6]);
        assert(fdct_rows(s)[8 * m + 7] == fdct_1d(d, true)[7]);
    }
}

/// After the second transpose, lane `u` of vector `j` is the first pass's
/// output `u` of row `j`.
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
proof fn lemma_tr_cols(p0: __m256i, p1: __m256i, p2: __m256i, p3: __m256i, p4: __m256i, p5: __m256i, p6: __m256i, p7: __m256i, q0: __m256i, q1: __m256i, q2: __m256i, q3: __m256i, q4: __m256i, q5: __m256i, q6: __m256i, q7: __m256i, rows: Seq<int>)
    requires
        forall|m: int| #![trigger lv(p0, m)] #![trigger lv(p1, m)] #![trigger lv(p2, m)] #![trigger lv(p3, m)] #![trigger lv(p4, m)] #![trigger lv(p5, m)] #![trigger lv(p6, m)] #![trigger lv(p7, m)] 0 <= m < 8 ==> lv(p0, m) == rows[8 * m] && lv(p1, m) == rows[8 * m + 1]
            && lv(p2, m) == rows[8 * m + 2] && lv(p3, m) == rows[8 * m + 3] && lv(p4, m) == rows[8 * m + 4]
            && lv(p5, m) == rows[8 * m + 5] && lv(p6, m) == rows[8 * m + 6] && lv(p7, m) == rows[8 * m + 7],
        bnd(p0, 4096) && bnd(p1, 4096) && bnd(p2, 4096) && bnd(p3, 4096) && bnd(p4, 4096) && bnd(p5, 4096) && bnd(p6, 4096) && bnd(p7, 4096),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(q0, m) == lv(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, m), 0),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(q1, m) == lv(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, m), 1),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(q2, m) == lv(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, m), 2),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(q3, m) == lv(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, m), 3),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(q4, m) == lv(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, m), 4),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(q5, m) == lv(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, m), 5),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(q6, m) == lv(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, m), 6),
        forall|m: int| 0 <= m < 8 ==> #[trigger] lv(q7, m) == lv(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, m), 7),
    ensures
        forall|u: int| 0 <= u < 8 ==> #[trigger] col8(q0, q1, q2, q3, q4, q5, q6, q7, u) == Seq::new(8, |j: int| rows[8 * j + u]),
        bnd(q0, 4096) && bnd(q1, 4096) && bnd(q2, 4096) && bnd(q3, 4096) && bnd(q4, 4096) && bnd(q5, 4096) && bnd(q6, 4096) && bnd(q7, 4096),
{
    assert(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, 0) == p0);
    lemma_col_u(p0, q0, q1, q2, q3, q4, q5, q6, q7, rows, 0);
    assert(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, 1) == p1);
    lemma_col_u(p1, q0, q1, q2, q3, q4, q5, q6, q7, rows, 1);
    assert(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, 2) == p2);
    lemma_col_u(p2, q0, q1, q2, q3, q4, q5, q6, q7, rows, 2);
    assert(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, 3) == p3);
    lemma_col_u(p3, q0, q1, q2, q3, q4, q5, q6, q7, rows, 3);
    assert(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, 4) == p4);
    lemma_col_u(p4, q0, q1, q2, q3, q4, q5, q6, q7, rows, 4);
    assert(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, 5) == p5);
    lemma_col_u(p5, q0, q1, q2, q3, q4, q5, q6, q7, rows, 5);
    assert(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, 6) == p6);
    lemma_col_u(p6, q0, q1, q2, q3, q4, q5, q6, q7, rows, 6);
    assert(pick8x(p0, p1, p2, p3, p4, p5, p6, p7, 7) == p7);
    lemma_col_u(p7, q0, q1, q2, q3, q4, q5, q6, q7, rows, 7);
    assert forall|u: int| 0 <= u < 8 implies #[trigger] col8(q0, q1, q2, q3, q4, q5, q6, q7, u) == Seq::new(8, |j: int| rows[8 * j + u])
        && -4096 <= lv(q0, u) <= 4096 && -4096 <= lv(q1, u) <= 4096 && -4096 <= lv(q2, u) <= 4096 && -4096 <= lv(q3, u) <= 4096
        && -4096 <= lv(q4, u) <= 4096 && -4096 <= lv(q5, u) <= 4096 && -4096 <= lv(q6, u) <= 4096 && -4096 <= lv(q7, u) <= 4096 by {
        if u == 0 {} else if u == 1 {} else if u == 2 {} else if u == 3 {} else if u == 4 {} else if u == 5 {} else if u == 6 {} else {}
    }
}

/// Column `u` after the second transpose, from vector `p`, the first
/// pass's output `u`.
proof fn lemma_col_u(p: __m256i, q0: __m256i, q1: __m256i, q2: __m256i, q3: __m256i, q4: __m256i, q5: __m256i, q6: __m256i, q7: __m256i, rows: Seq<int>, u: int)
    requires
        forall|j: int| 0 <= j < 8 ==> #[trigger] lv(p, j) == rows[8 * j + u] && -4096 <= lv(p, j) <= 4096,
        lv(q0, u) == lv(p, 0) && lv(q1, u) == lv(p, 1) && lv(q2, u) == lv(p, 2) && lv(q3, u) == lv(p, 3),
        lv(q4, u) == lv(p, 4) && lv(q5, u) == lv(p, 5) && lv(q6, u) == lv(p, 6) && lv(q7, u) == lv(p, 7),
    ensures
        col8(q0, q1, q2, q3, q4, q5, q6, q7, u) == Seq::new(8, |j: int| rows[8 * j + u]),
        -4096 <= lv(q0, u) <= 4096 && -4096 <= lv(q1, u) <= 4096 && -4096 <= lv(q2, u) <= 4096 && -4096 <= lv(q3, u) <= 4096,
        -4096 <= lv(q4, u) <= 4096 && -4096 <= lv(q5, u) <= 4096 && -4096 <= lv(q6, u) <= 4096 && -4096 <= lv(q7, u) <= 4096,
{
    assert(lv(p, 0) == rows[u] && lv(p, 1) == rows[8 + u] && lv(p, 2) == rows[16 + u] && lv(p, 3) == rows[24 + u]);
    assert(lv(p, 4) == rows[32 + u] && lv(p, 5) == rows[40 + u] && lv(p, 6) == rows[48 + u] && lv(p, 7) == rows[56 + u]);
    assert(col8(q0, q1, q2, q3, q4, q5, q6, q7, u) =~= Seq::new(8, |j: int| rows[8 * j + u]));
}

/// The second pass's inputs are `fdct`'s.
proof fn lemma_out(q0: __m256i, q1: __m256i, q2: __m256i, q3: __m256i, q4: __m256i, q5: __m256i, q6: __m256i, q7: __m256i, rows: Seq<int>, s: Seq<int>)
    requires
        rows == fdct_rows(s),
        forall|u: int| 0 <= u < 8 ==> #[trigger] col8(q0, q1, q2, q3, q4, q5, q6, q7, u) == Seq::new(8, |j: int| rows[8 * j + u]),
    ensures
        forall|v: int, u: int| 0 <= v < 8 && 0 <= u < 8 ==> #[trigger] fdct_1d(col8(q0, q1, q2, q3, q4, q5, q6, q7, u), false)[v] == fdct(s)[8 * v + u],
{
    reveal(fdct);
    assert forall|v: int, u: int| 0 <= v < 8 && 0 <= u < 8 implies #[trigger] fdct_1d(col8(q0, q1, q2, q3, q4, q5, q6, q7, u), false)[v] == fdct(s)[8 * v + u] by {
        let i = 8 * v + u;
        assert(i / 8 == v && i % 8 == u);
        assert(Seq::new(8, |j: int| rows[8 * j + i % 8]) =~= Seq::new(8, |j: int| rows[8 * j + u]));
    }
}

} // verus!

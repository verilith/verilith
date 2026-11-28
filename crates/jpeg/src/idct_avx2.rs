//! The inverse DCT on AVX2 over 16-bit rows, for the blocks `idct16_neon`
//! takes (the sum of the dequantized magnitudes at most `tot_max`), with
//! all eight columns of a pass in one vector, as libjpeg-turbo's AVX2 code
//! does it.
//!
//! A row of eight 16-bit values is spread over a 256-bit vector as
//! [c0 c1 c2 c3 * * * * | c4 c5 c6 c7 * * * *] (`xs`): interleaving two
//! such rows (`vpunpcklwd`) puts the pair for column m in 32-bit lane m,
//! and one `vpmaddwd` multiplies both by their constants and adds them.
//! The first pass's results are shifted in 32-bit lanes and transposed;
//! a signed pack of a transposed vector with itself (`vpackssdw`) gives the
//! spread layout again for the second pass, whose results are packed to
//! bytes, reordered within each 128-bit half and stored row by row.
//!
//! The dequantization is checked rather than bounded: the high half of
//! each signed product (`vpmulhw`) must be the sign of the low half, so
//! that the low half is the product.
use crate::idct::*;
use crate::idct16::*;
use crate::idct_neon::*;
use crate::num::*;
use crate::spec::*;
use verilith_simd::arch::*;
use verilith_simd::cpu::*;
#[cfg(verus_only)]
use verilith_simd::lanes::*;
use verilith_simd::mem::*;
#[cfg(verus_only)]
use verilith_simd::ops::*;
#[cfg(verus_only)]
use verilith_simd::x86::{half128, perm2x128};
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::cpu::group_cpu};

// ---------------------------------------------------------------------------
// Lanes
// ---------------------------------------------------------------------------

/// 16-bit lane `i` of a vector, read as signed.
pub open spec fn h16(v: __m256i, i: int) -> int {
    s16(u16x16(v)[i])
}

/// 32-bit lane `i` of a vector.
pub open spec fn w32(v: __m256i, i: int) -> int {
    u32x8(v)[i] as int
}

/// The 16-bit lane that holds column `m` of a spread row.
pub open spec fn sp(m: int) -> int {
    if m < 4 {
        m
    } else {
        m + 4
    }
}

/// `v` holds the eight values of `t`, exactly, spread.
pub open spec fn xs(v: __m256i, t: Seq<int>) -> bool {
    t.len() == 8 && forall|m: int| 0 <= m < 8 ==> #[trigger] h16(v, sp(m)) == t[m]
}

/// 32-bit lane `m` of `v` is output `k` of a pass over column `m` of the
/// inputs, modulo 2^32.
pub open spec fn py(v: __m256i, t0: Seq<int>, t1: Seq<int>, t2: Seq<int>, t3: Seq<int>, t4: Seq<int>, t5: Seq<int>, t6: Seq<int>, t7: Seq<int>, k: int) -> bool {
    forall|m: int| 0 <= m < 8 ==> cong(#[trigger] w32(v, m), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, m))[k])
}

/// 32-bit lane `m` of `v` is the first pass's result at column `j`, row
/// `m`, exactly.
pub open spec fn wt(v: __m256i, dq: Seq<int>, j: int) -> bool {
    forall|m: int| 0 <= m < 8 ==> s32(#[trigger] u32x8(v)[m]) == idct_col(dq, j, m)
}

/// The sum of the eight 32-bit lanes.
pub open spec fn vs8(v: __m256i) -> int {
    w32(v, 0) + w32(v, 1) + w32(v, 2) + w32(v, 3) + w32(v, 4) + w32(v, 5) + w32(v, 6) + w32(v, 7)
}

/// The `i32` with the bits of `x`.
#[inline(always)]
fn i32_of_u32(x: u32) -> (r: i32)
    ensures
        u32_of_i32(r) == x,
{
    if x < 0x8000_0000 {
        x as i32
    } else {
        ((x - 0x8000_0000) as i32) - 0x7fff_ffff - 1
    }
}

/// A 16-bit lane in terms of the 32-bit lane that holds it.
proof fn lemma_u16_in_u32(b: Seq<u8>, k: int)
    requires
        b.len() % 4 == 0,
        0 <= k < b.len() / 2,
    ensures
        u16s(b)[k] == if k % 2 == 0 {
            (u32s(b)[k / 2] & 0xffff) as u16
        } else {
            (u32s(b)[k / 2] >> 16u32) as u16
        },
{
    lemma_u16s_of_u32s(b);
    let w = k / 2;
    if k % 2 == 0 {
        assert(k == 2 * w);
        assert(u16s(b)[2 * w] == (u32s(b)[w] & 0xffff) as u16);
    } else {
        assert(k == 2 * w + 1);
        assert(u16s(b)[2 * w] == (u32s(b)[w] & 0xffff) as u16);
        assert(u16s(b)[2 * w + 1] == (u32s(b)[w] >> 16u32) as u16);
    }
}

proof fn lemma_add16e(x: u16, y: u16, r: u16)
    requires
        r as int == (x + y) % 0x10000,
        -32768 <= s16(x) + s16(y) <= 32767,
    ensures
        s16(r) == s16(x) + s16(y),
{
}

// ---------------------------------------------------------------------------
// One pass
// ---------------------------------------------------------------------------

/// Every even 16-bit lane of `k` is `ca` and every odd one `cb`.
pub open spec fn kpr(k: __m256i, ca: int, cb: int) -> bool {
    forall|i: int| 0 <= i < 16 ==> #[trigger] h16(k, i) == if i % 2 == 0 {
        ca
    } else {
        cb
    }
}

/// The pair of constants (`c0`, `c1`) in each two 16-bit lanes.
#[inline(always)]
fn kp(c0: i16, c1: i16) -> (k: __m256i)
    requires
        avx2(),
    ensures
        kpr(k, c0 as int, c1 as int),
{
    let x = (c0 as u16 as u32) | ((c1 as u16 as u32) << 16u32);
    let k = _mm256_set1_epi32(i32_of_u32(x));
    proof {
        assert((x & 0xffff) as u16 == c0 as u16 && (x >> 16u32) as u16 == c1 as u16) by (bit_vector)
            requires
                x == (c0 as u16 as u32) | ((c1 as u16 as u32) << 16u32),
        ;
        assert forall|i: int| 0 <= i < 16 implies #[trigger] h16(k, i) == if i % 2 == 0 {
            c0 as int
        } else {
            c1 as int
        } by {
            lemma_u16_in_u32(b256(k), i);
            assert(u32x8(k)[i / 2] == x);
            if i % 2 == 0 {
                lemma_s16_cast(c0, u16x16(k)[i]);
            } else {
                lemma_s16_cast(c1, u16x16(k)[i]);
            }
        }
    }
    k
}

/// Column `m` of `a` and of `b`, times `ca` and `cb` and added, in 32-bit
/// lane `m`: the rows interleaved, then one pairwise multiply-add.
#[inline(always)]
fn dx(a: __m256i, b: __m256i, k: __m256i, Ghost(ca): Ghost<int>, Ghost(cb): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        kpr(k, ca, cb),
    ensures
        forall|m: int| 0 <= m < 8 ==> rdot(#[trigger] w32(r, m), h16(a, sp(m)), ca, h16(b, sp(m)), cb),
{
    reveal(rdot);
    let z = _mm256_unpacklo_epi16(a, b);
    let r = _mm256_madd_epi16(z, k);
    proof {
        assert forall|m: int| 0 <= m < 8 implies rdot(#[trigger] w32(r, m), h16(a, sp(m)), ca, h16(b, sp(m)), cb) by {
            if m < 4 {
                assert((2 * m) % 2 == 0 && (2 * m) / 8 == 0 && ((2 * m) % 8) / 2 == m);
                assert((2 * m + 1) % 2 == 1 && (2 * m + 1) / 8 == 0 && ((2 * m + 1) % 8) / 2 == m);
            } else {
                assert((2 * m) % 2 == 0 && (2 * m) / 8 == 1 && ((2 * m) % 8) / 2 == m - 4);
                assert((2 * m + 1) % 2 == 1 && (2 * m + 1) / 8 == 1 && ((2 * m + 1) % 8) / 2 == m - 4);
            }
            assert(u16x16(z)[2 * m] == u16x16(a)[sp(m)] && u16x16(z)[2 * m + 1] == u16x16(b)[sp(m)]);
            assert(h16(k, 2 * m) == ca && h16(k, 2 * m + 1) == cb);
        }
    }
    r
}

#[inline(always)]
fn ad(a: __m256i, b: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        forall|m: int| 0 <= m < 8 ==> radd(#[trigger] w32(r, m), w32(a, m), w32(b, m)),
{
    reveal(radd);
    _mm256_add_epi32(a, b)
}

#[inline(always)]
fn sb(a: __m256i, b: __m256i) -> (r: __m256i)
    requires
        avx2(),
    ensures
        forall|m: int| 0 <= m < 8 ==> rsub(#[trigger] w32(r, m), w32(a, m), w32(b, m)),
{
    reveal(rsub);
    _mm256_sub_epi32(a, b)
}

/// The sum of two spread rows whose sums fit 16 bits: exact.
#[inline(always)]
fn addy(a: __m256i, b: __m256i, Ghost(ta): Ghost<Seq<int>>, Ghost(tb): Ghost<Seq<int>>) -> (r: __m256i)
    requires
        avx2(),
        xs(a, ta),
        xs(b, tb),
        forall|m: int| 0 <= m < 8 ==> -0x8000 <= (#[trigger] ta[m]) + tb[m] < 0x8000,
    ensures
        xs(r, vsum(ta, tb)),
{
    let r = _mm256_add_epi16(a, b);
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] h16(r, sp(m)) == vsum(ta, tb)[m] by {
            assert(h16(a, sp(m)) == ta[m] && h16(b, sp(m)) == tb[m]);
            assert(-0x8000 <= ta[m] + tb[m] < 0x8000);
            lemma_add16e(u16x16(a)[sp(m)], u16x16(b)[sp(m)], u16x16(r)[sp(m)]);
        }
    }
    r
}

// BEGIN generated by scripts/gen_idct_avx2.py
/// One pass over eight rows in the spread layout: 32-bit lane `m` of
/// result `k` is output `k` of the pass over column `m`, modulo 2^32.
#[inline(always)]
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
fn pass8(x0: __m256i, x1: __m256i, x2: __m256i, x3: __m256i, x4: __m256i, x5: __m256i, x6: __m256i, x7: __m256i, Ghost(t0): Ghost<Seq<int>>, Ghost(t1): Ghost<Seq<int>>, Ghost(t2): Ghost<Seq<int>>, Ghost(t3): Ghost<Seq<int>>, Ghost(t4): Ghost<Seq<int>>, Ghost(t5): Ghost<Seq<int>>, Ghost(t6): Ghost<Seq<int>>, Ghost(t7): Ghost<Seq<int>>) -> (r: (__m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i))
    requires
        avx2(),
        xs(x0, t0),
        xs(x1, t1),
        xs(x2, t2),
        xs(x3, t3),
        xs(x4, t4),
        xs(x5, t5),
        xs(x6, t6),
        xs(x7, t7),
        forall|m: int| 0 <= m < 8 ==> -0x8000 <= (#[trigger] t7[m]) + t3[m] < 0x8000,
        forall|m: int| 0 <= m < 8 ==> -0x8000 <= (#[trigger] t5[m]) + t1[m] < 0x8000,
    ensures
        py(r.0, t0, t1, t2, t3, t4, t5, t6, t7, 0),
        py(r.1, t0, t1, t2, t3, t4, t5, t6, t7, 1),
        py(r.2, t0, t1, t2, t3, t4, t5, t6, t7, 2),
        py(r.3, t0, t1, t2, t3, t4, t5, t6, t7, 3),
        py(r.4, t0, t1, t2, t3, t4, t5, t6, t7, 4),
        py(r.5, t0, t1, t2, t3, t4, t5, t6, t7, 5),
        py(r.6, t0, t1, t2, t3, t4, t5, t6, t7, 6),
        py(r.7, t0, t1, t2, t3, t4, t5, t6, t7, 7),
{
    hide(idct_1d);
    hide(cong);
    hide(w32);
    let pz3 = addy(x7, x3, Ghost(t7), Ghost(t3));
    let pz4 = addy(x5, x1, Ghost(t5), Ghost(t1));
    let v1 = dx(x2, x6, kp(10703, 4433), Ghost(10703), Ghost(4433));
    let v2 = dx(x2, x6, kp(4433, -10704), Ghost(4433), Ghost(-10704));
    let v3 = dx(x0, x4, kp(8192, 8192), Ghost(8192), Ghost(8192));
    let v4 = dx(x0, x4, kp(8192, -8192), Ghost(8192), Ghost(-8192));
    let v5 = ad(v3, v1);
    let v6 = sb(v3, v1);
    let v7 = ad(v4, v2);
    let v8 = sb(v4, v2);
    let v9 = dx(pz3, pz4, kp(-6436, 9633), Ghost(-6436), Ghost(9633));
    let v10 = dx(pz3, pz4, kp(9633, 6437), Ghost(9633), Ghost(6437));
    let v11 = dx(x7, x1, kp(-4927, -7373), Ghost(-4927), Ghost(-7373));
    let v12 = dx(x7, x1, kp(-7373, 4926), Ghost(-7373), Ghost(4926));
    let v13 = dx(x5, x3, kp(-4176, -20995), Ghost(-4176), Ghost(-20995));
    let v14 = dx(x5, x3, kp(-20995, 4177), Ghost(-20995), Ghost(4177));
    let v15 = ad(v11, v9);
    let v16 = ad(v13, v10);
    let v17 = ad(v14, v9);
    let v18 = ad(v12, v10);
    let v19 = ad(v5, v18);
    let v20 = ad(v7, v17);
    let v21 = ad(v8, v16);
    let v22 = ad(v6, v15);
    let v23 = sb(v6, v15);
    let v24 = sb(v8, v16);
    let v25 = sb(v7, v17);
    let v26 = sb(v5, v18);
    proof {
        assert forall|m: int| 0 <= m < 8 implies cong(#[trigger] w32(v19, m), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, m))[0]) by {
            assert(vsum(t7, t3)[m] == t7[m] + t3[m] && vsum(t5, t1)[m] == t5[m] + t1[m]);
            lemma_vd16_lane(t0[m], t1[m], t2[m], t3[m], t4[m], t5[m], t6[m], t7[m], w32(v1, m), w32(v2, m), w32(v3, m), w32(v4, m), w32(v5, m), w32(v6, m), w32(v7, m), w32(v8, m), w32(v9, m), w32(v10, m), w32(v11, m), w32(v12, m), w32(v13, m), w32(v14, m), w32(v15, m), w32(v16, m), w32(v17, m), w32(v18, m), w32(v19, m), w32(v20, m), w32(v21, m), w32(v22, m), w32(v23, m), w32(v24, m), w32(v25, m), w32(v26, m));
        }
        assert forall|m: int| 0 <= m < 8 implies cong(#[trigger] w32(v20, m), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, m))[1]) by {
            assert(vsum(t7, t3)[m] == t7[m] + t3[m] && vsum(t5, t1)[m] == t5[m] + t1[m]);
            lemma_vd16_lane(t0[m], t1[m], t2[m], t3[m], t4[m], t5[m], t6[m], t7[m], w32(v1, m), w32(v2, m), w32(v3, m), w32(v4, m), w32(v5, m), w32(v6, m), w32(v7, m), w32(v8, m), w32(v9, m), w32(v10, m), w32(v11, m), w32(v12, m), w32(v13, m), w32(v14, m), w32(v15, m), w32(v16, m), w32(v17, m), w32(v18, m), w32(v19, m), w32(v20, m), w32(v21, m), w32(v22, m), w32(v23, m), w32(v24, m), w32(v25, m), w32(v26, m));
        }
        assert forall|m: int| 0 <= m < 8 implies cong(#[trigger] w32(v21, m), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, m))[2]) by {
            assert(vsum(t7, t3)[m] == t7[m] + t3[m] && vsum(t5, t1)[m] == t5[m] + t1[m]);
            lemma_vd16_lane(t0[m], t1[m], t2[m], t3[m], t4[m], t5[m], t6[m], t7[m], w32(v1, m), w32(v2, m), w32(v3, m), w32(v4, m), w32(v5, m), w32(v6, m), w32(v7, m), w32(v8, m), w32(v9, m), w32(v10, m), w32(v11, m), w32(v12, m), w32(v13, m), w32(v14, m), w32(v15, m), w32(v16, m), w32(v17, m), w32(v18, m), w32(v19, m), w32(v20, m), w32(v21, m), w32(v22, m), w32(v23, m), w32(v24, m), w32(v25, m), w32(v26, m));
        }
        assert forall|m: int| 0 <= m < 8 implies cong(#[trigger] w32(v22, m), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, m))[3]) by {
            assert(vsum(t7, t3)[m] == t7[m] + t3[m] && vsum(t5, t1)[m] == t5[m] + t1[m]);
            lemma_vd16_lane(t0[m], t1[m], t2[m], t3[m], t4[m], t5[m], t6[m], t7[m], w32(v1, m), w32(v2, m), w32(v3, m), w32(v4, m), w32(v5, m), w32(v6, m), w32(v7, m), w32(v8, m), w32(v9, m), w32(v10, m), w32(v11, m), w32(v12, m), w32(v13, m), w32(v14, m), w32(v15, m), w32(v16, m), w32(v17, m), w32(v18, m), w32(v19, m), w32(v20, m), w32(v21, m), w32(v22, m), w32(v23, m), w32(v24, m), w32(v25, m), w32(v26, m));
        }
        assert forall|m: int| 0 <= m < 8 implies cong(#[trigger] w32(v23, m), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, m))[4]) by {
            assert(vsum(t7, t3)[m] == t7[m] + t3[m] && vsum(t5, t1)[m] == t5[m] + t1[m]);
            lemma_vd16_lane(t0[m], t1[m], t2[m], t3[m], t4[m], t5[m], t6[m], t7[m], w32(v1, m), w32(v2, m), w32(v3, m), w32(v4, m), w32(v5, m), w32(v6, m), w32(v7, m), w32(v8, m), w32(v9, m), w32(v10, m), w32(v11, m), w32(v12, m), w32(v13, m), w32(v14, m), w32(v15, m), w32(v16, m), w32(v17, m), w32(v18, m), w32(v19, m), w32(v20, m), w32(v21, m), w32(v22, m), w32(v23, m), w32(v24, m), w32(v25, m), w32(v26, m));
        }
        assert forall|m: int| 0 <= m < 8 implies cong(#[trigger] w32(v24, m), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, m))[5]) by {
            assert(vsum(t7, t3)[m] == t7[m] + t3[m] && vsum(t5, t1)[m] == t5[m] + t1[m]);
            lemma_vd16_lane(t0[m], t1[m], t2[m], t3[m], t4[m], t5[m], t6[m], t7[m], w32(v1, m), w32(v2, m), w32(v3, m), w32(v4, m), w32(v5, m), w32(v6, m), w32(v7, m), w32(v8, m), w32(v9, m), w32(v10, m), w32(v11, m), w32(v12, m), w32(v13, m), w32(v14, m), w32(v15, m), w32(v16, m), w32(v17, m), w32(v18, m), w32(v19, m), w32(v20, m), w32(v21, m), w32(v22, m), w32(v23, m), w32(v24, m), w32(v25, m), w32(v26, m));
        }
        assert forall|m: int| 0 <= m < 8 implies cong(#[trigger] w32(v25, m), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, m))[6]) by {
            assert(vsum(t7, t3)[m] == t7[m] + t3[m] && vsum(t5, t1)[m] == t5[m] + t1[m]);
            lemma_vd16_lane(t0[m], t1[m], t2[m], t3[m], t4[m], t5[m], t6[m], t7[m], w32(v1, m), w32(v2, m), w32(v3, m), w32(v4, m), w32(v5, m), w32(v6, m), w32(v7, m), w32(v8, m), w32(v9, m), w32(v10, m), w32(v11, m), w32(v12, m), w32(v13, m), w32(v14, m), w32(v15, m), w32(v16, m), w32(v17, m), w32(v18, m), w32(v19, m), w32(v20, m), w32(v21, m), w32(v22, m), w32(v23, m), w32(v24, m), w32(v25, m), w32(v26, m));
        }
        assert forall|m: int| 0 <= m < 8 implies cong(#[trigger] w32(v26, m), idct_1d(col(t0, t1, t2, t3, t4, t5, t6, t7, m))[7]) by {
            assert(vsum(t7, t3)[m] == t7[m] + t3[m] && vsum(t5, t1)[m] == t5[m] + t1[m]);
            lemma_vd16_lane(t0[m], t1[m], t2[m], t3[m], t4[m], t5[m], t6[m], t7[m], w32(v1, m), w32(v2, m), w32(v3, m), w32(v4, m), w32(v5, m), w32(v6, m), w32(v7, m), w32(v8, m), w32(v9, m), w32(v10, m), w32(v11, m), w32(v12, m), w32(v13, m), w32(v14, m), w32(v15, m), w32(v16, m), w32(v17, m), w32(v18, m), w32(v19, m), w32(v20, m), w32(v21, m), w32(v22, m), w32(v23, m), w32(v24, m), w32(v25, m), w32(v26, m));
        }
    }
    (v19, v20, v21, v22, v23, v24, v25, v26)
}
// END generated

// ---------------------------------------------------------------------------
// Dequantization, checked
// ---------------------------------------------------------------------------

/// The low half of a product of two 16-bit values whose high half is the
/// sign of the low half is the product.
proof fn lemma_deq_lane(c: u16, q: u16, l: u16, s: u16, h: u16)
    requires
        l as int == (c as int * q as int) % 0x10000,
        s as int == (s16(l) / 0x8000) % 0x10000,
        h as int == ((s16(c) * s16(q)) / 0x10000) % 0x10000,
        h == s,
    ensures
        s16(l) == s16(c) * s16(q),
{
    let sc = s16(c);
    let sq = s16(q);
    let p = sc * sq;
    let ec: int = if c < 0x8000 { 0 } else { 1 };
    let eq: int = if q < 0x8000 { 0 } else { 1 };
    assert(c as int == sc + 0x10000 * ec);
    assert(q as int == sq + 0x10000 * eq);
    assert(-0x4000_0000 <= p <= 0x4000_0000) by (nonlinear_arith)
        requires
            -0x8000 <= sc < 0x8000,
            -0x8000 <= sq < 0x8000,
            p == sc * sq,
    ;
    let kk = ec * sq + eq * sc + 0x10000 * ec * eq;
    assert(c as int * q as int == p + 0x10000 * kk) by (nonlinear_arith)
        requires
            c as int == sc + 0x10000 * ec,
            q as int == sq + 0x10000 * eq,
            p == sc * sq,
            kk == ec * sq + eq * sc + 0x10000 * ec * eq,
    ;
    lemma_mod_multiples_vanish(kk, p, 0x10000);
    assert(l as int == p % 0x10000);
    let d = p / 0x10000;
    lemma_fundamental_div_mod(p, 0x10000);
    assert(p == 0x10000 * d + p % 0x10000);
    assert(-0x4001 <= d <= 0x4000);
    if s16(l) >= 0 {
        assert(s16(l) / 0x8000 == 0);
        assert(s == 0);
        assert(d % 0x10000 == 0);
        assert(d == 0);
    } else {
        assert(s16(l) / 0x8000 == -1);
        assert(s == 0xffff);
        assert(d % 0x10000 == 0xffff);
        assert(d == -1);
    }
}

/// A lane times its sign (the sign doubled, plus one) is its magnitude.
proof fn lemma_abs_lane(l: u16, s: u16, g: u16)
    requires
        s as int == (s16(l) / 0x8000) % 0x10000,
        g as int == ((s as int + s as int) % 0x10000 + 1) % 0x10000,
    ensures
        s16(l) * s16(g) == iabs(s16(l)),
{
    if s16(l) >= 0 {
        assert(s16(l) / 0x8000 == 0);
        assert(g == 1);
        assert(s16(g) == 1);
        assert(s16(l) * 1 == s16(l));
    } else {
        assert(s16(l) / 0x8000 == -1);
        assert(g == 0xffff);
        assert(s16(g) == -1);
        assert(s16(l) * -1 == -s16(l));
    }
}

/// Byte `b` of `x ^ y` is zero only where the bytes are equal.
proof fn lemma_xor_zero(x: u8, y: u8)
    requires
        x ^ y == 0,
    ensures
        x == y,
{
    assert(x ^ y == 0 ==> x == y) by (bit_vector);
}

/// Where `e` is all zero bits, `l` holds 16 dequantized values, from
/// `16 * j` on, and `m` the pairwise sums of their magnitudes.
pub open spec fn deq_ok(l: __m256i, e: __m256i, m: __m256i, a: Seq<i16>, o: int, qs: Seq<u16>, j: int) -> bool {
    (forall|b: int| 0 <= b < 32 ==> #[trigger] b256(e)[b] == 0u8) ==> {
        &&& forall|i: int| 0 <= i < 16 ==> #[trigger] h16(l, i) == dequant(a, o, qs)[16 * j + i]
        &&& forall|i: int|
            0 <= i < 8 ==> #[trigger] w32(m, i) == iabs(dequant(a, o, qs)[16 * j + 2 * i]) + iabs(
                dequant(a, o, qs)[16 * j + 2 * i + 1],
            ) && w32(m, i) <= 0x10000
    }
}

/// `deqv`'s check, lane by lane.
proof fn lemma_deqv(c: __m256i, q: __m256i, l: __m256i, s: __m256i, mh: __m256i, e: __m256i, g: __m256i, m: __m256i, a: Seq<i16>, o: int, qs: Seq<u16>, j: int)
    requires
        0 <= o,
        o + 64 <= a.len(),
        qs.len() == 64,
        0 <= j < 4,
        u16x16(c) == a.subrange(o + 16 * j, o + 16 * j + 16).map_values(|x: i16| x as u16),
        u16x16(q) == qs.subrange(16 * j, 16 * j + 16),
        u16x16(l) == mullo16(u16x16(c), u16x16(q)),
        u16x16(s) == srai16(u16x16(l), 15),
        u16x16(mh) == mulhi_s16(u16x16(c), u16x16(q)),
        b256(e) == xor8(b256(mh), b256(s)),
        u16x16(g) == add16(add16(u16x16(s), u16x16(s)), splat16(1u16, 16)),
        u32x8(m) == madd16(u16x16(l), u16x16(g)),
    ensures
        deq_ok(l, e, m, a, o, qs, j),
{
    if !(forall|b: int| 0 <= b < 32 ==> #[trigger] b256(e)[b] == 0u8) {
        return;
    }
    reveal_with_fuel(pow2_spec, 16);
    let dq = dequant(a, o, qs);
    assert forall|b: int| 0 <= b < 32 implies #[trigger] b256(mh)[b] == b256(s)[b] by {
        assert(b256(e)[b] == 0u8);
        lemma_xor_zero(b256(mh)[b], b256(s)[b]);
    }
    assert(b256(mh) =~= b256(s));
    assert forall|i: int| 0 <= i < 16 implies #[trigger] h16(l, i) == dq[16 * j + i] by {
        let ci = u16x16(c)[i];
        let qi = u16x16(q)[i];
        lemma_s16_cast(a[o + 16 * j + i], ci);
        assert(qi == qs[16 * j + i]);
        lemma_deq_lane(ci, qi, u16x16(l)[i], u16x16(s)[i], u16x16(mh)[i]);
    }
    assert forall|i: int|
        0 <= i < 8 implies #[trigger] w32(m, i) == iabs(dq[16 * j + 2 * i]) + iabs(dq[16 * j + 2 * i + 1]) && w32(m, i) <= 0x10000 by {
        assert(h16(l, 2 * i) == dq[16 * j + 2 * i]);
        assert(h16(l, 2 * i + 1) == dq[16 * j + 2 * i + 1]);
        lemma_abs_lane(u16x16(l)[2 * i], u16x16(s)[2 * i], u16x16(g)[2 * i]);
        lemma_abs_lane(u16x16(l)[2 * i + 1], u16x16(s)[2 * i + 1], u16x16(g)[2 * i + 1]);
        let v = iabs(dq[16 * j + 2 * i]) + iabs(dq[16 * j + 2 * i + 1]);
        assert(0 <= v <= 0x10000);
    }
}

/// Sixteen coefficients times their quantizers, with the check: where `e`
/// is all zero bits, the low halves are the dequantized values and the
/// pairwise sums of their magnitudes are in `g`'s lanes.
#[inline(always)]
fn deqv(c: __m256i, a: &[i16], o: usize, qs: &[u16], j: usize) -> (r: (__m256i, __m256i, __m256i))
    requires
        avx2(),
        o + 64 <= a@.len(),
        qs@.len() == 64,
        j < 4,
        u16x16(c) == a@.subrange(o + 16 * j, o + 16 * j + 16).map_values(|x: i16| x as u16),
    ensures
        deq_ok(r.0, r.1, r.2, a@, o as int, qs@, j as int),
{
    let q = load256_u16(qs, 16 * j);
    let l = _mm256_mullo_epi16(c, q);
    let s = _mm256_srai_epi16::<15>(l);
    let mh = _mm256_mulhi_epi16(c, q);
    let e = _mm256_xor_si256(mh, s);
    let g = _mm256_add_epi16(_mm256_add_epi16(s, s), _mm256_set1_epi16(1));
    let m = _mm256_madd_epi16(l, g);
    proof {
        lemma_deqv(c, q, l, s, mh, e, g, m, a@, o as int, qs@, j as int);
    }
    (l, e, m)
}

proof fn lemma_add32e(x: u32, y: u32, r: u32)
    requires
        r == ((x + y) % 0x1_0000_0000) as u32,
        x + y <= 0x1000_0000,
    ensures
        r == x + y,
{
}

/// The sum of the 32 lanes of four vectors of small lanes.
#[inline(always)]
fn hsum(m0: __m256i, m1: __m256i, m2: __m256i, m3: __m256i) -> (t: u32)
    requires
        avx2(),
        forall|i: int|
            0 <= i < 8 ==> #[trigger] w32(m0, i) <= 0x10000 && w32(m1, i) <= 0x10000 && w32(m2, i) <= 0x10000 && w32(m3, i)
                <= 0x10000,
    ensures
        t as int == vs8(m0) + vs8(m1) + vs8(m2) + vs8(m3),
{
    hide(vs8);
    let m01 = _mm256_add_epi32(m0, m1);
    let m23 = _mm256_add_epi32(m2, m3);
    let m = _mm256_add_epi32(m01, m23);
    let mut b = [0u32; 8];
    store256_u32(&mut b, 0, m);
    proof {
        assert forall|i: int| 0 <= i < 8 implies #[trigger] w32(m, i) == w32(m0, i) + w32(m1, i) + w32(m2, i) + w32(m3, i) by {
            assert(w32(m0, i) <= 0x10000 && w32(m1, i) <= 0x10000 && w32(m2, i) <= 0x10000 && w32(m3, i) <= 0x10000);
            lemma_add32e(u32x8(m0)[i], u32x8(m1)[i], u32x8(m01)[i]);
            lemma_add32e(u32x8(m2)[i], u32x8(m3)[i], u32x8(m23)[i]);
            lemma_add32e(u32x8(m01)[i], u32x8(m23)[i], u32x8(m)[i]);
        }
        assert(w32(m, 0) + w32(m, 1) + w32(m, 2) + w32(m, 3) + w32(m, 4) + w32(m, 5) + w32(m, 6) + w32(m, 7) == vs8(m0) + vs8(m1) + vs8(m2) + vs8(m3)) by {
            reveal(vs8);
        }
        assert(b@ =~= u32x8(m));
        assert(w32(m, 0) <= 0x4_0000 && w32(m, 1) <= 0x4_0000 && w32(m, 2) <= 0x4_0000 && w32(m, 3) <= 0x4_0000);
        assert(w32(m, 4) <= 0x4_0000 && w32(m, 5) <= 0x4_0000 && w32(m, 6) <= 0x4_0000 && w32(m, 7) <= 0x4_0000);
    }
    b[0] + b[1] + b[2] + b[3] + b[4] + b[5] + b[6] + b[7]
}

/// The four vectors' sums are the block's sum of magnitudes.
proof fn lemma_atot_link(dq: Seq<int>, g0: __m256i, g1: __m256i, g2: __m256i, g3: __m256i)
    requires
        dq.len() == 64,
        forall|i: int| 0 <= i < 8 ==> #[trigger] w32(g0, i) == iabs(dq[2 * i]) + iabs(dq[2 * i + 1]),
        forall|i: int| 0 <= i < 8 ==> #[trigger] w32(g1, i) == iabs(dq[16 + 2 * i]) + iabs(dq[16 + 2 * i + 1]),
        forall|i: int| 0 <= i < 8 ==> #[trigger] w32(g2, i) == iabs(dq[32 + 2 * i]) + iabs(dq[32 + 2 * i + 1]),
        forall|i: int| 0 <= i < 8 ==> #[trigger] w32(g3, i) == iabs(dq[48 + 2 * i]) + iabs(dq[48 + 2 * i + 1]),
    ensures
        vs8(g0) + vs8(g1) + vs8(g2) + vs8(g3) == atot(dq),
{
    reveal(atot);
    reveal(acol);
}

// ---------------------------------------------------------------------------
// The first pass
// ---------------------------------------------------------------------------

/// Row `2 * j` (`hi` false) or `2 * j + 1` of `l`'s two rows, spread.
#[inline(always)]
fn spread(l: __m256i, hi: bool) -> (x: __m256i)
    requires
        avx2(),
    ensures
        forall|m: int| 0 <= m < 8 ==> #[trigger] u16x16(x)[sp(m)] == u16x16(l)[(if hi { 8int } else { 0int }) + m],
{
    let idx = if hi {
        _mm256_setr_epi32(4, 5, 4, 5, 6, 7, 6, 7)
    } else {
        _mm256_setr_epi32(0, 1, 0, 1, 2, 3, 2, 3)
    };
    let x = _mm256_permutevar8x32_epi32(l, idx);
    proof {
        let base: int = if hi { 8 } else { 0 };
        if hi {
            assert(u32x8(idx) =~= seq![4u32, 5, 4, 5, 6, 7, 6, 7]);
        } else {
            assert(u32x8(idx) =~= seq![0u32, 1, 0, 1, 2, 3, 2, 3]);
        }
        assert forall|m: int| 0 <= m < 8 implies #[trigger] u16x16(x)[sp(m)] == u16x16(l)[base + m] by {
            lemma_u16_in_u32(b256(x), sp(m));
            lemma_u16_in_u32(b256(l), base + m);
            assert(sp(m) % 2 == (base + m) % 2);
            assert((u32x8(idx)[sp(m) / 2] % 8) as int == (base + m) / 2);
            assert(u32x8(x)[sp(m) / 2] == u32x8(l)[(base + m) / 2]);
        }
    }
    x
}

/// The first pass's shift of one lane: exact, because the pass was and
/// the result is small.
proof fn lemma_nar32(u: u32, g: int, a: u32, n: u32)
    requires
        cong(u as int, g),
        -0x7000_0000 <= g <= 0x7000_0000,
        a as int == (u as int + 1024) % 0x1_0000_0000,
        n as int == (s32(a) / 2048) % 0x1_0000_0000,
    ensures
        s32(n) == descale(g, 11),
{
    vstd::arithmetic::power2::lemma2_to64();
    let k = (u - g) / 0x1_0000_0000;
    assert(u - g == 0x1_0000_0000 * k);
    assert(-2 <= k <= 2);
    assert(a as int == g + 1024 || a as int == g + 1024 + 0x1_0000_0000);
    assert(s32(a) == g + 1024);
    assert(descale(g, 11) == (g + 1024) / 2048);
}

/// Output `k` of the first pass, shifted: row `k` of each column of the
/// workspace.
#[inline(always)]
fn nar1(v: __m256i, Ghost(dq): Ghost<Seq<int>>, Ghost(k): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        dq.len() == 64,
        atot(dq) <= tot_max(),
        0 <= k < 8,
        py(v, dr(dq, 0), dr(dq, 1), dr(dq, 2), dr(dq, 3), dr(dq, 4), dr(dq, 5), dr(dq, 6), dr(dq, 7), k),
    ensures
        wn(r, dq, k),
{
    let a = _mm256_add_epi32(v, _mm256_set1_epi32(1024));
    let r = _mm256_srai_epi32::<11>(a);
    proof {
        reveal_with_fuel(pow2_spec, 12);
        assert forall|m: int| 0 <= m < 8 implies s32(#[trigger] u32x8(r)[m]) == idct_col(dq, m, k) by {
            lemma_acol_le(dq, m);
            lemma_ws_bound(dq, m, k);
            lemma_dcol(dq, m);
            let g = idct_1d(dcol(dq, m))[k];
            assert(cong(w32(v, m), g));
            lemma_nar32(u32x8(v)[m], g, u32x8(a)[m], u32x8(r)[m]);
        }
    }
    r
}

/// The 32-bit lanes of a selection of 128-bit halves.
proof fn lemma_perm_u32(p: __m256i, q: __m256i, r: __m256i, imm: int)
    requires
        imm == 0x20 || imm == 0x31,
        b256(r) == perm2x128(b256(p), b256(q), imm),
    ensures
        forall|n: int|
            0 <= n < 8 ==> #[trigger] u32x8(r)[n] == if n < 4 {
                u32x8(p)[n + if imm == 0x31 { 4int } else { 0int }]
            } else {
                u32x8(q)[n - 4 + if imm == 0x31 { 4int } else { 0int }]
            },
{
    let off: int = if imm == 0x31 { 16 } else { 0 };
    assert(b256(r) =~= b256(p).subrange(off, off + 16) + b256(q).subrange(off, off + 16));
    assert forall|n: int|
        0 <= n < 8 implies #[trigger] u32x8(r)[n] == if n < 4 {
            u32x8(p)[n + if imm == 0x31 { 4int } else { 0int }]
        } else {
            u32x8(q)[n - 4 + if imm == 0x31 { 4int } else { 0int }]
        } by {
        let b = b256(r);
        if n < 4 {
            assert(b[4 * n] == b256(p)[off + 4 * n] && b[4 * n + 1] == b256(p)[off + 4 * n + 1]);
            assert(b[4 * n + 2] == b256(p)[off + 4 * n + 2] && b[4 * n + 3] == b256(p)[off + 4 * n + 3]);
            assert(4 * (n + off / 4) == off + 4 * n);
        } else {
            assert(b[4 * n] == b256(q)[off + 4 * n - 16] && b[4 * n + 1] == b256(q)[off + 4 * n - 15]);
            assert(b[4 * n + 2] == b256(q)[off + 4 * n - 14] && b[4 * n + 3] == b256(q)[off + 4 * n - 13]);
            assert(4 * (n - 4 + off / 4) == off + 4 * n - 16);
        }
    }
}

/// Transposes four rows of 32-bit lanes within each 128-bit half.
#[inline(always)]
fn tr4(a: __m256i, b: __m256i, c: __m256i, d: __m256i) -> (r: (__m256i, __m256i, __m256i, __m256i))
    requires
        avx2(),
    ensures
        forall|n: int| 0 <= n < 4 ==> #[trigger] u32x8(r.0)[n] == u32x8(pick4(a, b, c, d, n))[0],
        forall|n: int| 4 <= n < 8 ==> #[trigger] u32x8(r.0)[n] == u32x8(pick4(a, b, c, d, n - 4))[4],
        forall|n: int| 0 <= n < 4 ==> #[trigger] u32x8(r.1)[n] == u32x8(pick4(a, b, c, d, n))[1],
        forall|n: int| 4 <= n < 8 ==> #[trigger] u32x8(r.1)[n] == u32x8(pick4(a, b, c, d, n - 4))[5],
        forall|n: int| 0 <= n < 4 ==> #[trigger] u32x8(r.2)[n] == u32x8(pick4(a, b, c, d, n))[2],
        forall|n: int| 4 <= n < 8 ==> #[trigger] u32x8(r.2)[n] == u32x8(pick4(a, b, c, d, n - 4))[6],
        forall|n: int| 0 <= n < 4 ==> #[trigger] u32x8(r.3)[n] == u32x8(pick4(a, b, c, d, n))[3],
        forall|n: int| 4 <= n < 8 ==> #[trigger] u32x8(r.3)[n] == u32x8(pick4(a, b, c, d, n - 4))[7],
{
    let ac0 = _mm256_unpacklo_epi32(a, c);
    let ac1 = _mm256_unpackhi_epi32(a, c);
    let bd0 = _mm256_unpacklo_epi32(b, d);
    let bd1 = _mm256_unpackhi_epi32(b, d);
    let r0 = _mm256_unpacklo_epi32(ac0, bd0);
    let r1 = _mm256_unpackhi_epi32(ac0, bd0);
    let r2 = _mm256_unpacklo_epi32(ac1, bd1);
    let r3 = _mm256_unpackhi_epi32(ac1, bd1);
    proof {
        assert forall|n: int| 0 <= n < 4 implies #[trigger] u32x8(r0)[n] == u32x8(pick4(a, b, c, d, n))[0] by {
            if n == 0 {
            } else if n == 1 {
            } else if n == 2 {
            } else if n == 3 {
            }
        }
        assert forall|n: int| 4 <= n < 8 implies #[trigger] u32x8(r0)[n] == u32x8(pick4(a, b, c, d, n - 4))[4] by {
            if n == 4 {
            } else if n == 5 {
            } else if n == 6 {
            } else if n == 7 {
            }
        }
        assert forall|n: int| 0 <= n < 4 implies #[trigger] u32x8(r1)[n] == u32x8(pick4(a, b, c, d, n))[1] by {
            if n == 0 {
            } else if n == 1 {
            } else if n == 2 {
            } else if n == 3 {
            }
        }
        assert forall|n: int| 4 <= n < 8 implies #[trigger] u32x8(r1)[n] == u32x8(pick4(a, b, c, d, n - 4))[5] by {
            if n == 4 {
            } else if n == 5 {
            } else if n == 6 {
            } else if n == 7 {
            }
        }
        assert forall|n: int| 0 <= n < 4 implies #[trigger] u32x8(r2)[n] == u32x8(pick4(a, b, c, d, n))[2] by {
            if n == 0 {
            } else if n == 1 {
            } else if n == 2 {
            } else if n == 3 {
            }
        }
        assert forall|n: int| 4 <= n < 8 implies #[trigger] u32x8(r2)[n] == u32x8(pick4(a, b, c, d, n - 4))[6] by {
            if n == 4 {
            } else if n == 5 {
            } else if n == 6 {
            } else if n == 7 {
            }
        }
        assert forall|n: int| 0 <= n < 4 implies #[trigger] u32x8(r3)[n] == u32x8(pick4(a, b, c, d, n))[3] by {
            if n == 0 {
            } else if n == 1 {
            } else if n == 2 {
            } else if n == 3 {
            }
        }
        assert forall|n: int| 4 <= n < 8 implies #[trigger] u32x8(r3)[n] == u32x8(pick4(a, b, c, d, n - 4))[7] by {
            if n == 4 {
            } else if n == 5 {
            } else if n == 6 {
            } else if n == 7 {
            }
        }
    }
    (r0, r1, r2, r3)
}

/// One of four vectors.
pub open spec fn pick4(a: __m256i, b: __m256i, c: __m256i, d: __m256i, i: int) -> __m256i {
    if i == 0 {
        a
    } else if i == 1 {
        b
    } else if i == 2 {
        c
    } else {
        d
    }
}

/// Lane `y` of `w_m` is the first pass's result at column `m`, row `y`.
pub open spec fn wn(v: __m256i, dq: Seq<int>, y: int) -> bool {
    forall|m: int| 0 <= m < 8 ==> s32(#[trigger] u32x8(v)[m]) == idct_col(dq, m, y)
}

/// One of eight vectors.
pub open spec fn pick8(w0: __m256i, w1: __m256i, w2: __m256i, w3: __m256i, w4: __m256i, w5: __m256i, w6: __m256i, w7: __m256i, i: int) -> __m256i {
    if i < 4 {
        pick4(w0, w1, w2, w3, i)
    } else {
        pick4(w4, w5, w6, w7, i - 4)
    }
}

/// The first pass's eight results, transposed: vector `y` holds row `y` of
/// the workspace, column `m` in 32-bit lane `m`.
#[inline(always)]
#[verifier::spinoff_prover]
fn tr8(w0: __m256i, w1: __m256i, w2: __m256i, w3: __m256i, w4: __m256i, w5: __m256i, w6: __m256i, w7: __m256i, Ghost(dq): Ghost<Seq<int>>) -> (t: (__m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i))
    requires
        avx2(),
        wn(w0, dq, 0),
        wn(w1, dq, 1),
        wn(w2, dq, 2),
        wn(w3, dq, 3),
        wn(w4, dq, 4),
        wn(w5, dq, 5),
        wn(w6, dq, 6),
        wn(w7, dq, 7),
    ensures
        wt(t.0, dq, 0),
        wt(t.1, dq, 1),
        wt(t.2, dq, 2),
        wt(t.3, dq, 3),
        wt(t.4, dq, 4),
        wt(t.5, dq, 5),
        wt(t.6, dq, 6),
        wt(t.7, dq, 7),
{
    let (p0, p1, p2, p3) = tr4(w0, w1, w2, w3);
    let (q0, q1, q2, q3) = tr4(w4, w5, w6, w7);
    let t0 = _mm256_permute2x128_si256::<0x20>(p0, q0);
    let t1 = _mm256_permute2x128_si256::<0x20>(p1, q1);
    let t2 = _mm256_permute2x128_si256::<0x20>(p2, q2);
    let t3 = _mm256_permute2x128_si256::<0x20>(p3, q3);
    let t4 = _mm256_permute2x128_si256::<0x31>(p0, q0);
    let t5 = _mm256_permute2x128_si256::<0x31>(p1, q1);
    let t6 = _mm256_permute2x128_si256::<0x31>(p2, q2);
    let t7 = _mm256_permute2x128_si256::<0x31>(p3, q3);
    proof {
        lemma_perm_u32(p0, q0, t0, 0x20);
        assert(u32x8(t0)[0] == u32x8(w0)[0]);
        assert(s32(u32x8(w0)[0]) == idct_col(dq, 0, 0));
        assert(u32x8(t0)[1] == u32x8(w1)[0]);
        assert(s32(u32x8(w1)[0]) == idct_col(dq, 0, 1));
        assert(u32x8(t0)[2] == u32x8(w2)[0]);
        assert(s32(u32x8(w2)[0]) == idct_col(dq, 0, 2));
        assert(u32x8(t0)[3] == u32x8(w3)[0]);
        assert(s32(u32x8(w3)[0]) == idct_col(dq, 0, 3));
        assert(u32x8(t0)[4] == u32x8(w4)[0]);
        assert(s32(u32x8(w4)[0]) == idct_col(dq, 0, 4));
        assert(u32x8(t0)[5] == u32x8(w5)[0]);
        assert(s32(u32x8(w5)[0]) == idct_col(dq, 0, 5));
        assert(u32x8(t0)[6] == u32x8(w6)[0]);
        assert(s32(u32x8(w6)[0]) == idct_col(dq, 0, 6));
        assert(u32x8(t0)[7] == u32x8(w7)[0]);
        assert(s32(u32x8(w7)[0]) == idct_col(dq, 0, 7));
        assert forall|m: int| 0 <= m < 8 implies s32(#[trigger] u32x8(t0)[m]) == idct_col(dq, 0, m) by {
            if m == 0 {
            } else if m == 1 {
            } else if m == 2 {
            } else if m == 3 {
            } else if m == 4 {
            } else if m == 5 {
            } else if m == 6 {
            } else if m == 7 {
            }
        }
        lemma_perm_u32(p1, q1, t1, 0x20);
        assert(u32x8(t1)[0] == u32x8(w0)[1]);
        assert(s32(u32x8(w0)[1]) == idct_col(dq, 1, 0));
        assert(u32x8(t1)[1] == u32x8(w1)[1]);
        assert(s32(u32x8(w1)[1]) == idct_col(dq, 1, 1));
        assert(u32x8(t1)[2] == u32x8(w2)[1]);
        assert(s32(u32x8(w2)[1]) == idct_col(dq, 1, 2));
        assert(u32x8(t1)[3] == u32x8(w3)[1]);
        assert(s32(u32x8(w3)[1]) == idct_col(dq, 1, 3));
        assert(u32x8(t1)[4] == u32x8(w4)[1]);
        assert(s32(u32x8(w4)[1]) == idct_col(dq, 1, 4));
        assert(u32x8(t1)[5] == u32x8(w5)[1]);
        assert(s32(u32x8(w5)[1]) == idct_col(dq, 1, 5));
        assert(u32x8(t1)[6] == u32x8(w6)[1]);
        assert(s32(u32x8(w6)[1]) == idct_col(dq, 1, 6));
        assert(u32x8(t1)[7] == u32x8(w7)[1]);
        assert(s32(u32x8(w7)[1]) == idct_col(dq, 1, 7));
        assert forall|m: int| 0 <= m < 8 implies s32(#[trigger] u32x8(t1)[m]) == idct_col(dq, 1, m) by {
            if m == 0 {
            } else if m == 1 {
            } else if m == 2 {
            } else if m == 3 {
            } else if m == 4 {
            } else if m == 5 {
            } else if m == 6 {
            } else if m == 7 {
            }
        }
        lemma_perm_u32(p2, q2, t2, 0x20);
        assert(u32x8(t2)[0] == u32x8(w0)[2]);
        assert(s32(u32x8(w0)[2]) == idct_col(dq, 2, 0));
        assert(u32x8(t2)[1] == u32x8(w1)[2]);
        assert(s32(u32x8(w1)[2]) == idct_col(dq, 2, 1));
        assert(u32x8(t2)[2] == u32x8(w2)[2]);
        assert(s32(u32x8(w2)[2]) == idct_col(dq, 2, 2));
        assert(u32x8(t2)[3] == u32x8(w3)[2]);
        assert(s32(u32x8(w3)[2]) == idct_col(dq, 2, 3));
        assert(u32x8(t2)[4] == u32x8(w4)[2]);
        assert(s32(u32x8(w4)[2]) == idct_col(dq, 2, 4));
        assert(u32x8(t2)[5] == u32x8(w5)[2]);
        assert(s32(u32x8(w5)[2]) == idct_col(dq, 2, 5));
        assert(u32x8(t2)[6] == u32x8(w6)[2]);
        assert(s32(u32x8(w6)[2]) == idct_col(dq, 2, 6));
        assert(u32x8(t2)[7] == u32x8(w7)[2]);
        assert(s32(u32x8(w7)[2]) == idct_col(dq, 2, 7));
        assert forall|m: int| 0 <= m < 8 implies s32(#[trigger] u32x8(t2)[m]) == idct_col(dq, 2, m) by {
            if m == 0 {
            } else if m == 1 {
            } else if m == 2 {
            } else if m == 3 {
            } else if m == 4 {
            } else if m == 5 {
            } else if m == 6 {
            } else if m == 7 {
            }
        }
        lemma_perm_u32(p3, q3, t3, 0x20);
        assert(u32x8(t3)[0] == u32x8(w0)[3]);
        assert(s32(u32x8(w0)[3]) == idct_col(dq, 3, 0));
        assert(u32x8(t3)[1] == u32x8(w1)[3]);
        assert(s32(u32x8(w1)[3]) == idct_col(dq, 3, 1));
        assert(u32x8(t3)[2] == u32x8(w2)[3]);
        assert(s32(u32x8(w2)[3]) == idct_col(dq, 3, 2));
        assert(u32x8(t3)[3] == u32x8(w3)[3]);
        assert(s32(u32x8(w3)[3]) == idct_col(dq, 3, 3));
        assert(u32x8(t3)[4] == u32x8(w4)[3]);
        assert(s32(u32x8(w4)[3]) == idct_col(dq, 3, 4));
        assert(u32x8(t3)[5] == u32x8(w5)[3]);
        assert(s32(u32x8(w5)[3]) == idct_col(dq, 3, 5));
        assert(u32x8(t3)[6] == u32x8(w6)[3]);
        assert(s32(u32x8(w6)[3]) == idct_col(dq, 3, 6));
        assert(u32x8(t3)[7] == u32x8(w7)[3]);
        assert(s32(u32x8(w7)[3]) == idct_col(dq, 3, 7));
        assert forall|m: int| 0 <= m < 8 implies s32(#[trigger] u32x8(t3)[m]) == idct_col(dq, 3, m) by {
            if m == 0 {
            } else if m == 1 {
            } else if m == 2 {
            } else if m == 3 {
            } else if m == 4 {
            } else if m == 5 {
            } else if m == 6 {
            } else if m == 7 {
            }
        }
        lemma_perm_u32(p0, q0, t4, 0x31);
        assert(u32x8(t4)[0] == u32x8(w0)[4]);
        assert(s32(u32x8(w0)[4]) == idct_col(dq, 4, 0));
        assert(u32x8(t4)[1] == u32x8(w1)[4]);
        assert(s32(u32x8(w1)[4]) == idct_col(dq, 4, 1));
        assert(u32x8(t4)[2] == u32x8(w2)[4]);
        assert(s32(u32x8(w2)[4]) == idct_col(dq, 4, 2));
        assert(u32x8(t4)[3] == u32x8(w3)[4]);
        assert(s32(u32x8(w3)[4]) == idct_col(dq, 4, 3));
        assert(u32x8(t4)[4] == u32x8(w4)[4]);
        assert(s32(u32x8(w4)[4]) == idct_col(dq, 4, 4));
        assert(u32x8(t4)[5] == u32x8(w5)[4]);
        assert(s32(u32x8(w5)[4]) == idct_col(dq, 4, 5));
        assert(u32x8(t4)[6] == u32x8(w6)[4]);
        assert(s32(u32x8(w6)[4]) == idct_col(dq, 4, 6));
        assert(u32x8(t4)[7] == u32x8(w7)[4]);
        assert(s32(u32x8(w7)[4]) == idct_col(dq, 4, 7));
        assert forall|m: int| 0 <= m < 8 implies s32(#[trigger] u32x8(t4)[m]) == idct_col(dq, 4, m) by {
            if m == 0 {
            } else if m == 1 {
            } else if m == 2 {
            } else if m == 3 {
            } else if m == 4 {
            } else if m == 5 {
            } else if m == 6 {
            } else if m == 7 {
            }
        }
        lemma_perm_u32(p1, q1, t5, 0x31);
        assert(u32x8(t5)[0] == u32x8(w0)[5]);
        assert(s32(u32x8(w0)[5]) == idct_col(dq, 5, 0));
        assert(u32x8(t5)[1] == u32x8(w1)[5]);
        assert(s32(u32x8(w1)[5]) == idct_col(dq, 5, 1));
        assert(u32x8(t5)[2] == u32x8(w2)[5]);
        assert(s32(u32x8(w2)[5]) == idct_col(dq, 5, 2));
        assert(u32x8(t5)[3] == u32x8(w3)[5]);
        assert(s32(u32x8(w3)[5]) == idct_col(dq, 5, 3));
        assert(u32x8(t5)[4] == u32x8(w4)[5]);
        assert(s32(u32x8(w4)[5]) == idct_col(dq, 5, 4));
        assert(u32x8(t5)[5] == u32x8(w5)[5]);
        assert(s32(u32x8(w5)[5]) == idct_col(dq, 5, 5));
        assert(u32x8(t5)[6] == u32x8(w6)[5]);
        assert(s32(u32x8(w6)[5]) == idct_col(dq, 5, 6));
        assert(u32x8(t5)[7] == u32x8(w7)[5]);
        assert(s32(u32x8(w7)[5]) == idct_col(dq, 5, 7));
        assert forall|m: int| 0 <= m < 8 implies s32(#[trigger] u32x8(t5)[m]) == idct_col(dq, 5, m) by {
            if m == 0 {
            } else if m == 1 {
            } else if m == 2 {
            } else if m == 3 {
            } else if m == 4 {
            } else if m == 5 {
            } else if m == 6 {
            } else if m == 7 {
            }
        }
        lemma_perm_u32(p2, q2, t6, 0x31);
        assert(u32x8(t6)[0] == u32x8(w0)[6]);
        assert(s32(u32x8(w0)[6]) == idct_col(dq, 6, 0));
        assert(u32x8(t6)[1] == u32x8(w1)[6]);
        assert(s32(u32x8(w1)[6]) == idct_col(dq, 6, 1));
        assert(u32x8(t6)[2] == u32x8(w2)[6]);
        assert(s32(u32x8(w2)[6]) == idct_col(dq, 6, 2));
        assert(u32x8(t6)[3] == u32x8(w3)[6]);
        assert(s32(u32x8(w3)[6]) == idct_col(dq, 6, 3));
        assert(u32x8(t6)[4] == u32x8(w4)[6]);
        assert(s32(u32x8(w4)[6]) == idct_col(dq, 6, 4));
        assert(u32x8(t6)[5] == u32x8(w5)[6]);
        assert(s32(u32x8(w5)[6]) == idct_col(dq, 6, 5));
        assert(u32x8(t6)[6] == u32x8(w6)[6]);
        assert(s32(u32x8(w6)[6]) == idct_col(dq, 6, 6));
        assert(u32x8(t6)[7] == u32x8(w7)[6]);
        assert(s32(u32x8(w7)[6]) == idct_col(dq, 6, 7));
        assert forall|m: int| 0 <= m < 8 implies s32(#[trigger] u32x8(t6)[m]) == idct_col(dq, 6, m) by {
            if m == 0 {
            } else if m == 1 {
            } else if m == 2 {
            } else if m == 3 {
            } else if m == 4 {
            } else if m == 5 {
            } else if m == 6 {
            } else if m == 7 {
            }
        }
        lemma_perm_u32(p3, q3, t7, 0x31);
        assert(u32x8(t7)[0] == u32x8(w0)[7]);
        assert(s32(u32x8(w0)[7]) == idct_col(dq, 7, 0));
        assert(u32x8(t7)[1] == u32x8(w1)[7]);
        assert(s32(u32x8(w1)[7]) == idct_col(dq, 7, 1));
        assert(u32x8(t7)[2] == u32x8(w2)[7]);
        assert(s32(u32x8(w2)[7]) == idct_col(dq, 7, 2));
        assert(u32x8(t7)[3] == u32x8(w3)[7]);
        assert(s32(u32x8(w3)[7]) == idct_col(dq, 7, 3));
        assert(u32x8(t7)[4] == u32x8(w4)[7]);
        assert(s32(u32x8(w4)[7]) == idct_col(dq, 7, 4));
        assert(u32x8(t7)[5] == u32x8(w5)[7]);
        assert(s32(u32x8(w5)[7]) == idct_col(dq, 7, 5));
        assert(u32x8(t7)[6] == u32x8(w6)[7]);
        assert(s32(u32x8(w6)[7]) == idct_col(dq, 7, 6));
        assert(u32x8(t7)[7] == u32x8(w7)[7]);
        assert(s32(u32x8(w7)[7]) == idct_col(dq, 7, 7));
        assert forall|m: int| 0 <= m < 8 implies s32(#[trigger] u32x8(t7)[m]) == idct_col(dq, 7, m) by {
            if m == 0 {
            } else if m == 1 {
            } else if m == 2 {
            } else if m == 3 {
            } else if m == 4 {
            } else if m == 5 {
            } else if m == 6 {
            } else if m == 7 {
            }
        }
    }
    (t0, t1, t2, t3, t4, t5, t6, t7)
}

/// Row `r` of the block, spread, from the vector of rows `2 * (r / 2)`
/// and `2 * (r / 2) + 1`.
proof fn lemma_xs_row(x: __m256i, l: __m256i, dq: Seq<int>, r: int)
    requires
        dq.len() == 64,
        0 <= r < 8,
        forall|m: int| 0 <= m < 8 ==> #[trigger] u16x16(x)[sp(m)] == u16x16(l)[(if r % 2 == 1 { 8int } else { 0int }) + m],
        forall|i: int| 0 <= i < 16 ==> #[trigger] h16(l, i) == dq[16 * (r / 2) + i],
    ensures
        xs(x, dr(dq, r)),
{
    assert forall|m: int| 0 <= m < 8 implies #[trigger] h16(x, sp(m)) == dr(dq, r)[m] by {
        let b: int = if r % 2 == 1 { 8 } else { 0 };
        assert(h16(l, b + m) == dq[16 * (r / 2) + b + m]);
        assert(16 * (r / 2) + b == 8 * r);
    }
}

/// The first pass: the block's rows in, its workspace's rows out.
#[inline(always)]
#[verifier::spinoff_prover]
fn pass1(l0: __m256i, l1: __m256i, l2: __m256i, l3: __m256i, Ghost(dq): Ghost<Seq<int>>) -> (t: (__m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i))
    requires
        avx2(),
        dq.len() == 64,
        atot(dq) <= tot_max(),
        forall|i: int| 0 <= i < 16 ==> #[trigger] h16(l0, i) == dq[i],
        forall|i: int| 0 <= i < 16 ==> #[trigger] h16(l1, i) == dq[16 + i],
        forall|i: int| 0 <= i < 16 ==> #[trigger] h16(l2, i) == dq[32 + i],
        forall|i: int| 0 <= i < 16 ==> #[trigger] h16(l3, i) == dq[48 + i],
    ensures
        wt(t.0, dq, 0),
        wt(t.1, dq, 1),
        wt(t.2, dq, 2),
        wt(t.3, dq, 3),
        wt(t.4, dq, 4),
        wt(t.5, dq, 5),
        wt(t.6, dq, 6),
        wt(t.7, dq, 7),
{
    hide(idct_1d);
    hide(idct_col);
    hide(atot);
    let x0 = spread(l0, false);
    let x1 = spread(l0, true);
    let x2 = spread(l1, false);
    let x3 = spread(l1, true);
    let x4 = spread(l2, false);
    let x5 = spread(l2, true);
    let x6 = spread(l3, false);
    let x7 = spread(l3, true);
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] h16(l0, i) == dq[16 * (0int / 2) + i] by {
            assert(h16(l0, i) == dq[0 + i]);
        }
        lemma_xs_row(x0, l0, dq, 0);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] h16(l0, i) == dq[16 * (1int / 2) + i] by {
            assert(h16(l0, i) == dq[0 + i]);
        }
        lemma_xs_row(x1, l0, dq, 1);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] h16(l1, i) == dq[16 * (2int / 2) + i] by {
            assert(h16(l1, i) == dq[16 + i]);
        }
        lemma_xs_row(x2, l1, dq, 2);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] h16(l1, i) == dq[16 * (3int / 2) + i] by {
            assert(h16(l1, i) == dq[16 + i]);
        }
        lemma_xs_row(x3, l1, dq, 3);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] h16(l2, i) == dq[16 * (4int / 2) + i] by {
            assert(h16(l2, i) == dq[32 + i]);
        }
        lemma_xs_row(x4, l2, dq, 4);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] h16(l2, i) == dq[16 * (5int / 2) + i] by {
            assert(h16(l2, i) == dq[32 + i]);
        }
        lemma_xs_row(x5, l2, dq, 5);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] h16(l3, i) == dq[16 * (6int / 2) + i] by {
            assert(h16(l3, i) == dq[48 + i]);
        }
        lemma_xs_row(x6, l3, dq, 6);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] h16(l3, i) == dq[16 * (7int / 2) + i] by {
            assert(h16(l3, i) == dq[48 + i]);
        }
        lemma_xs_row(x7, l3, dq, 7);
        assert forall|m: int| 0 <= m < 8 implies -0x8000 <= (#[trigger] dr(dq, 7)[m]) + dr(dq, 3)[m] < 0x8000 by {
            lemma_acol_le(dq, m);
            reveal(atot);
            assert(dr(dq, 7)[m] == dq[56 + m] && dr(dq, 3)[m] == dq[24 + m]);
        }
        assert forall|m: int| 0 <= m < 8 implies -0x8000 <= (#[trigger] dr(dq, 5)[m]) + dr(dq, 1)[m] < 0x8000 by {
            lemma_acol_le(dq, m);
            reveal(atot);
            assert(dr(dq, 5)[m] == dq[40 + m] && dr(dq, 1)[m] == dq[8 + m]);
        }
    }
    let r = pass8(x0, x1, x2, x3, x4, x5, x6, x7, Ghost(dr(dq, 0)), Ghost(dr(dq, 1)), Ghost(dr(dq, 2)), Ghost(dr(dq, 3)), Ghost(dr(dq, 4)), Ghost(dr(dq, 5)), Ghost(dr(dq, 6)), Ghost(dr(dq, 7)));
    let w0 = nar1(r.0, Ghost(dq), Ghost(0int));
    let w1 = nar1(r.1, Ghost(dq), Ghost(1int));
    let w2 = nar1(r.2, Ghost(dq), Ghost(2int));
    let w3 = nar1(r.3, Ghost(dq), Ghost(3int));
    let w4 = nar1(r.4, Ghost(dq), Ghost(4int));
    let w5 = nar1(r.5, Ghost(dq), Ghost(5int));
    let w6 = nar1(r.6, Ghost(dq), Ghost(6int));
    let w7 = nar1(r.7, Ghost(dq), Ghost(7int));
    tr8(w0, w1, w2, w3, w4, w5, w6, w7, Ghost(dq))
}

// ---------------------------------------------------------------------------
// The second pass
// ---------------------------------------------------------------------------

/// A row of the workspace from its 32-bit lanes, spread: the signed pack
/// of the vector with itself.
#[inline(always)]
fn spr(t: __m256i, Ghost(row): Ghost<Seq<int>>) -> (x: __m256i)
    requires
        avx2(),
        row.len() == 8,
        forall|m: int| 0 <= m < 8 ==> s32(#[trigger] u32x8(t)[m]) == row[m] && -0x8000 <= row[m] < 0x8000,
    ensures
        xs(x, row),
{
    let x = _mm256_packs_epi32(t, t);
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] h16(x, sp(m)) == row[m] by {
            let i = sp(m);
            assert(i % 8 < 4 && (i / 8) * 4 + i % 8 == m);
            assert(s32(u32x8(t)[m]) == row[m]);
        }
    }
    x
}

/// A spread row plus 16 in every lane.
#[inline(always)]
fn addk(x: __m256i, Ghost(row): Ghost<Seq<int>>) -> (y: __m256i)
    requires
        avx2(),
        xs(x, row),
        forall|m: int| 0 <= m < 8 ==> -0x8000 <= #[trigger] row[m] < 0x8000 - 16,
    ensures
        xs(y, sh16(row)),
{
    let y = _mm256_add_epi16(x, _mm256_set1_epi16(16));
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] h16(y, sp(m)) == sh16(row)[m] by {
            assert(h16(x, sp(m)) == row[m]);
            lemma_add16e(u16x16(x)[sp(m)], 16u16, u16x16(y)[sp(m)]);
        }
    }
    y
}

/// The second pass's exact result at row `y`, column `x`, shifted.
pub open spec fn dd(dq: Seq<int>, y: int, x: int) -> int {
    descale(idct_1d(rowv(dq, y))[x], 18)
}

/// 32-bit lane `m` of `v` is the shifted result at row `m`, column `k`.
pub open spec fn fin(v: __m256i, dq: Seq<int>, k: int) -> bool {
    forall|m: int| 0 <= m < 8 ==> s32(#[trigger] u32x8(v)[m]) == dd(dq, m, k) && -512 <= dd(dq, m, k) <= 511
}

/// The second pass's shift of one lane, with the rounding already in the
/// sum: exact.
proof fn lemma_fin32(u: u32, g: int, n: u32)
    requires
        cong(u as int, g + 131072),
        -0x800_0000 <= g + 131072 < 0x800_0000,
        n as int == (s32(u) / 0x4_0000) % 0x1_0000_0000,
    ensures
        s32(n) == descale(g, 18),
        -512 <= descale(g, 18) <= 511,
{
    vstd::arithmetic::power2::lemma2_to64();
    let v = g + 131072;
    let k = (u - v) / 0x1_0000_0000;
    assert(u - v == 0x1_0000_0000 * k);
    assert(s32(u) == v);
    assert(descale(g, 18) == v / 0x4_0000);
}

/// Output `k` of the second pass, shifted.
#[inline(always)]
fn fin1(u: __m256i, Ghost(dq): Ghost<Seq<int>>, Ghost(k): Ghost<int>) -> (s: __m256i)
    requires
        avx2(),
        dq.len() == 64,
        atot(dq) <= tot_max(),
        0 <= k < 8,
        py(u, sh16(wsc(dq, 0)), wsc(dq, 1), wsc(dq, 2), wsc(dq, 3), wsc(dq, 4), wsc(dq, 5), wsc(dq, 6), wsc(dq, 7), k),
    ensures
        fin(s, dq, k),
{
    hide(idct_1d);
    hide(idct_col);
    hide(atot);
    let s = _mm256_srai_epi32::<18>(u);
    proof {
        reveal_with_fuel(pow2_spec, 19);
        assert forall|m: int| 0 <= m < 8 implies s32(#[trigger] u32x8(s)[m]) == dd(dq, m, k) && -512 <= dd(dq, m, k) <= 511 by {
            let c = col(sh16(wsc(dq, 0)), wsc(dq, 1), wsc(dq, 2), wsc(dq, 3), wsc(dq, 4), wsc(dq, 5), wsc(dq, 6), wsc(dq, 7), m);
            assert(c =~= seq![idct_col(dq, 0, m) + 16, idct_col(dq, 1, m), idct_col(dq, 2, m), idct_col(dq, 3, m), idct_col(dq, 4, m), idct_col(dq, 5, m), idct_col(dq, 6, m), idct_col(dq, 7, m)]);
            assert(rowv(dq, m) =~= seq![idct_col(dq, 0, m), idct_col(dq, 1, m), idct_col(dq, 2, m), idct_col(dq, 3, m), idct_col(dq, 4, m), idct_col(dq, 5, m), idct_col(dq, 6, m), idct_col(dq, 7, m)]);
            assert(cong(w32(u, m), idct_1d(c)[k]));
            lemma_pass_shift16(idct_col(dq, 0, m), idct_col(dq, 1, m), idct_col(dq, 2, m), idct_col(dq, 3, m), idct_col(dq, 4, m), idct_col(dq, 5, m), idct_col(dq, 6, m), idct_col(dq, 7, m));
            lemma_ex_bound(dq, m, k);
            lemma_fin32(u32x8(u)[m], idct_1d(rowv(dq, m))[k], u32x8(s)[m]);
        }
    }
    s
}

/// The second pass: rows of the workspace in, samples' values out.
#[inline(always)]
#[verifier::spinoff_prover]
fn pass2(t0: __m256i, t1: __m256i, t2: __m256i, t3: __m256i, t4: __m256i, t5: __m256i, t6: __m256i, t7: __m256i, Ghost(dq): Ghost<Seq<int>>) -> (s: (__m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i, __m256i))
    requires
        avx2(),
        dq.len() == 64,
        atot(dq) <= tot_max(),
        wt(t0, dq, 0),
        wt(t1, dq, 1),
        wt(t2, dq, 2),
        wt(t3, dq, 3),
        wt(t4, dq, 4),
        wt(t5, dq, 5),
        wt(t6, dq, 6),
        wt(t7, dq, 7),
    ensures
        fin(s.0, dq, 0),
        fin(s.1, dq, 1),
        fin(s.2, dq, 2),
        fin(s.3, dq, 3),
        fin(s.4, dq, 4),
        fin(s.5, dq, 5),
        fin(s.6, dq, 6),
        fin(s.7, dq, 7),
{
    hide(idct_1d);
    hide(idct_col);
    hide(atot);
    proof {
        lemma_wsmall(dq);
    }
    let x0 = spr(t0, Ghost(wsc(dq, 0)));
    let x1 = spr(t1, Ghost(wsc(dq, 1)));
    let x2 = spr(t2, Ghost(wsc(dq, 2)));
    let x3 = spr(t3, Ghost(wsc(dq, 3)));
    let x4 = spr(t4, Ghost(wsc(dq, 4)));
    let x5 = spr(t5, Ghost(wsc(dq, 5)));
    let x6 = spr(t6, Ghost(wsc(dq, 6)));
    let x7 = spr(t7, Ghost(wsc(dq, 7)));
    let y0 = addk(x0, Ghost(wsc(dq, 0)));
    proof {
        assert forall|m: int| 0 <= m < 8 implies -0x8000 <= (#[trigger] wsc(dq, 7)[m]) + wsc(dq, 3)[m] < 0x8000 by {
            assert(-11764 <= idct_col(dq, 7, m) <= 11764 && -11764 <= idct_col(dq, 3, m) <= 11764);
        }
        assert forall|m: int| 0 <= m < 8 implies -0x8000 <= (#[trigger] wsc(dq, 5)[m]) + wsc(dq, 1)[m] < 0x8000 by {
            assert(-11764 <= idct_col(dq, 5, m) <= 11764 && -11764 <= idct_col(dq, 1, m) <= 11764);
        }
    }
    let u = pass8(y0, x1, x2, x3, x4, x5, x6, x7, Ghost(sh16(wsc(dq, 0))), Ghost(wsc(dq, 1)), Ghost(wsc(dq, 2)), Ghost(wsc(dq, 3)), Ghost(wsc(dq, 4)), Ghost(wsc(dq, 5)), Ghost(wsc(dq, 6)), Ghost(wsc(dq, 7)));
    let s0 = fin1(u.0, Ghost(dq), Ghost(0int));
    let s1 = fin1(u.1, Ghost(dq), Ghost(1int));
    let s2 = fin1(u.2, Ghost(dq), Ghost(2int));
    let s3 = fin1(u.3, Ghost(dq), Ghost(3int));
    let s4 = fin1(u.4, Ghost(dq), Ghost(4int));
    let s5 = fin1(u.5, Ghost(dq), Ghost(5int));
    let s6 = fin1(u.6, Ghost(dq), Ghost(6int));
    let s7 = fin1(u.7, Ghost(dq), Ghost(7int));
    (s0, s1, s2, s3, s4, s5, s6, s7)
}

// ---------------------------------------------------------------------------
// Samples and stores
// ---------------------------------------------------------------------------

/// A sample from its shifted value: saturated to a signed byte and the
/// sign bit flipped, the range limit, since the value is inside the ten
/// bits the limit reads.
proof fn lemma_fin_byte(d: int, a: u16, b: u8, z: u8)
    requires
        -512 <= d <= 511,
        s16(a) == d,
        b as int == sat_s8(s16(a)) % 256,
        z == b ^ 128u8,
    ensures
        z == range_limit(d),
{
    assert(z == (if b < 128 {
        b + 128
    } else {
        b - 128
    }) as u8) by (bit_vector)
        requires
            z == b ^ 128u8,
    ;
}

/// The sample is the range limit of the shifted value.
proof fn lemma_idct_dd(dq: Seq<int>, y: int, x: int)
    ensures
        idct(dq, y, x) == range_limit(dd(dq, y, x)),
{
    assert(rowv(dq, y) =~= Seq::new(8, |j: int| idct_col(dq, j, y)));
}

pub open spec fn sel4i(a: int, b: int, c: int, d: int, i: int) -> int {
    if i == 0 {
        a
    } else if i == 1 {
        b
    } else if i == 2 {
        c
    } else {
        d
    }
}

/// Two outputs packed to 16 bits: lane `i` is row `4 * (i / 8) + i % 4` of
/// column `ka` (`i % 8 < 4`) or `kb`.
#[inline(always)]
fn pk32(sa: __m256i, sb: __m256i, Ghost(dq): Ghost<Seq<int>>, Ghost(ka): Ghost<int>, Ghost(kb): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        fin(sa, dq, ka),
        fin(sb, dq, kb),
    ensures
        forall|i: int|
            0 <= i < 16 ==> #[trigger] h16(r, i) == dd(dq, 4 * (i / 8) + i % 4, if i % 8 < 4 { ka } else { kb }) && -512 <= dd(
                dq,
                4 * (i / 8) + i % 4,
                if i % 8 < 4 { ka } else { kb },
            ) <= 511,
{
    hide(dd);
    let r = _mm256_packs_epi32(sa, sb);
    proof {
        assert forall|i: int|
            0 <= i < 16 implies #[trigger] h16(r, i) == dd(dq, 4 * (i / 8) + i % 4, if i % 8 < 4 { ka } else { kb }) && -512
                <= dd(dq, 4 * (i / 8) + i % 4, if i % 8 < 4 { ka } else { kb }) <= 511 by {
            let m = 4 * (i / 8) + i % 4;
            assert(0 <= m < 8);
            if i % 8 < 4 {
                assert((i / 8) * 4 + i % 8 == m);
                assert(s32(u32x8(sa)[m]) == dd(dq, m, ka) && -512 <= dd(dq, m, ka) <= 511);
                assert(u16x16(r)[i] == (sat_s16(s32(u32x8(sa)[m])) % 0x10000) as u16);
                assert(h16(r, i) == dd(dq, m, ka));
            } else {
                assert((i / 8) * 4 + i % 8 - 4 == m);
                assert(s32(u32x8(sb)[m]) == dd(dq, m, kb) && -512 <= dd(dq, m, kb) <= 511);
                assert(u16x16(r)[i] == (sat_s16(s32(u32x8(sb)[m])) % 0x10000) as u16);
                assert(h16(r, i) == dd(dq, m, kb));
            }
        }
    }
    r
}

/// Four outputs packed to bytes, the sign bit flipped: byte `i` is the
/// sample at row `4 * (i / 16) + i % 4` of column `ka`, `kb`, `kc` or
/// `kd` by `(i % 16) / 4`.
#[inline(always)]
fn pk16(a: __m256i, b: __m256i, Ghost(dq): Ghost<Seq<int>>, Ghost(ka): Ghost<int>, Ghost(kb): Ghost<int>, Ghost(kc): Ghost<int>, Ghost(kd): Ghost<int>) -> (r: __m256i)
    requires
        avx2(),
        forall|i: int|
            0 <= i < 16 ==> #[trigger] h16(a, i) == dd(dq, 4 * (i / 8) + i % 4, if i % 8 < 4 { ka } else { kb }) && -512 <= dd(
                dq,
                4 * (i / 8) + i % 4,
                if i % 8 < 4 { ka } else { kb },
            ) <= 511,
        forall|i: int|
            0 <= i < 16 ==> #[trigger] h16(b, i) == dd(dq, 4 * (i / 8) + i % 4, if i % 8 < 4 { kc } else { kd }) && -512 <= dd(
                dq,
                4 * (i / 8) + i % 4,
                if i % 8 < 4 { kc } else { kd },
            ) <= 511,
    ensures
        forall|i: int| 0 <= i < 32 ==> #[trigger] b256(r)[i] == idct(dq, 4 * (i / 16) + i % 4, sel4i(ka, kb, kc, kd, (i % 16) / 4)),
{
    hide(dd);
    hide(idct);
    let p = _mm256_packs_epi16(a, b);
    let r = _mm256_xor_si256(p, _mm256_set1_epi8(-128));
    proof {
        assert forall|i: int| 0 <= i < 32 implies #[trigger] b256(r)[i] == idct(dq, 4 * (i / 16) + i % 4, sel4i(ka, kb, kc, kd, (i % 16) / 4)) by {
            let y = 4 * (i / 16) + i % 4;
            let x = sel4i(ka, kb, kc, kd, (i % 16) / 4);
            lemma_idct_dd(dq, y, x);
            if i % 16 < 8 {
                let j = (i / 16) * 8 + i % 16;
                assert(0 <= j < 16 && j / 8 == i / 16 && j % 8 == i % 16 && j % 4 == i % 4);
                assert(4 * (j / 8) + j % 4 == y);
                assert((if j % 8 < 4 { ka } else { kb }) == x);
                assert(h16(a, j) == dd(dq, 4 * (j / 8) + j % 4, if j % 8 < 4 { ka } else { kb }));
                assert(h16(a, j) == dd(dq, y, x) && -512 <= dd(dq, y, x) <= 511);
                lemma_fin_byte(dd(dq, y, x), u16x16(a)[j], b256(p)[i], b256(r)[i]);
            } else {
                let j = (i / 16) * 8 + i % 16 - 8;
                assert(0 <= j < 16 && j / 8 == i / 16 && j % 8 == i % 16 - 8 && j % 4 == i % 4);
                assert(4 * (j / 8) + j % 4 == y);
                assert((if j % 8 < 4 { kc } else { kd }) == x);
                assert(h16(b, j) == dd(dq, 4 * (j / 8) + j % 4, if j % 8 < 4 { kc } else { kd }));
                assert(h16(b, j) == dd(dq, y, x) && -512 <= dd(dq, y, x) <= 511);
                lemma_fin_byte(dd(dq, y, x), u16x16(b)[j], b256(p)[i], b256(r)[i]);
            }
        }
    }
    r
}

/// The even and odd columns' samples, reordered within each half and
/// interleaved: `lo` holds rows 0, 1 | 4, 5 and `hi` rows 2, 3 | 6, 7.
#[inline(always)]
#[verifier::spinoff_prover]
fn rows(e: __m256i, d: __m256i, Ghost(dq): Ghost<Seq<int>>) -> (r: (__m256i, __m256i))
    requires
        avx2(),
        forall|i: int| 0 <= i < 32 ==> #[trigger] b256(e)[i] == idct(dq, 4 * (i / 16) + i % 4, 2 * ((i % 16) / 4)),
        forall|i: int| 0 <= i < 32 ==> #[trigger] b256(d)[i] == idct(dq, 4 * (i / 16) + i % 4, 2 * ((i % 16) / 4) + 1),
    ensures
        forall|i: int| 0 <= i < 32 ==> #[trigger] b256(r.0)[i] == idct(dq, 4 * (i / 16) + (i % 16) / 8, i % 8),
        forall|i: int| 0 <= i < 32 ==> #[trigger] b256(r.1)[i] == idct(dq, 4 * (i / 16) + (i % 16) / 8 + 2, i % 8),
{
    hide(idct);
    // To byte 4 * y + e of each half from byte 4 * e + y.
    let sh = _mm256_setr_epi8(0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15);
    let es = _mm256_shuffle_epi8(e, sh);
    let ds = _mm256_shuffle_epi8(d, sh);
    let lo = _mm256_unpacklo_epi8(es, ds);
    let hi = _mm256_unpackhi_epi8(es, ds);
    proof {
        assert(b256(sh) =~= seq![0u8, 4u8, 8u8, 12u8, 1u8, 5u8, 9u8, 13u8, 2u8, 6u8, 10u8, 14u8, 3u8, 7u8, 11u8, 15u8, 0u8, 4u8, 8u8, 12u8, 1u8, 5u8, 9u8, 13u8, 2u8, 6u8, 10u8, 14u8, 3u8, 7u8, 11u8, 15u8]);
        assert forall|i: int| 0 <= i < 32 implies #[trigger] b256(lo)[i] == idct(dq, 4 * (i / 16) + (i % 16) / 8, i % 8) by {
            if i == 0 {
                assert(b256(lo)[0] == b256(es)[0]);
                assert(b256(es)[0] == b256(e)[0]);
            } else if i == 1 {
                assert(b256(lo)[1] == b256(ds)[0]);
                assert(b256(ds)[0] == b256(d)[0]);
            } else if i == 2 {
                assert(b256(lo)[2] == b256(es)[1]);
                assert(b256(es)[1] == b256(e)[4]);
            } else if i == 3 {
                assert(b256(lo)[3] == b256(ds)[1]);
                assert(b256(ds)[1] == b256(d)[4]);
            } else if i == 4 {
                assert(b256(lo)[4] == b256(es)[2]);
                assert(b256(es)[2] == b256(e)[8]);
            } else if i == 5 {
                assert(b256(lo)[5] == b256(ds)[2]);
                assert(b256(ds)[2] == b256(d)[8]);
            } else if i == 6 {
                assert(b256(lo)[6] == b256(es)[3]);
                assert(b256(es)[3] == b256(e)[12]);
            } else if i == 7 {
                assert(b256(lo)[7] == b256(ds)[3]);
                assert(b256(ds)[3] == b256(d)[12]);
            } else if i == 8 {
                assert(b256(lo)[8] == b256(es)[4]);
                assert(b256(es)[4] == b256(e)[1]);
            } else if i == 9 {
                assert(b256(lo)[9] == b256(ds)[4]);
                assert(b256(ds)[4] == b256(d)[1]);
            } else if i == 10 {
                assert(b256(lo)[10] == b256(es)[5]);
                assert(b256(es)[5] == b256(e)[5]);
            } else if i == 11 {
                assert(b256(lo)[11] == b256(ds)[5]);
                assert(b256(ds)[5] == b256(d)[5]);
            } else if i == 12 {
                assert(b256(lo)[12] == b256(es)[6]);
                assert(b256(es)[6] == b256(e)[9]);
            } else if i == 13 {
                assert(b256(lo)[13] == b256(ds)[6]);
                assert(b256(ds)[6] == b256(d)[9]);
            } else if i == 14 {
                assert(b256(lo)[14] == b256(es)[7]);
                assert(b256(es)[7] == b256(e)[13]);
            } else if i == 15 {
                assert(b256(lo)[15] == b256(ds)[7]);
                assert(b256(ds)[7] == b256(d)[13]);
            } else if i == 16 {
                assert(b256(lo)[16] == b256(es)[16]);
                assert(b256(es)[16] == b256(e)[16]);
            } else if i == 17 {
                assert(b256(lo)[17] == b256(ds)[16]);
                assert(b256(ds)[16] == b256(d)[16]);
            } else if i == 18 {
                assert(b256(lo)[18] == b256(es)[17]);
                assert(b256(es)[17] == b256(e)[20]);
            } else if i == 19 {
                assert(b256(lo)[19] == b256(ds)[17]);
                assert(b256(ds)[17] == b256(d)[20]);
            } else if i == 20 {
                assert(b256(lo)[20] == b256(es)[18]);
                assert(b256(es)[18] == b256(e)[24]);
            } else if i == 21 {
                assert(b256(lo)[21] == b256(ds)[18]);
                assert(b256(ds)[18] == b256(d)[24]);
            } else if i == 22 {
                assert(b256(lo)[22] == b256(es)[19]);
                assert(b256(es)[19] == b256(e)[28]);
            } else if i == 23 {
                assert(b256(lo)[23] == b256(ds)[19]);
                assert(b256(ds)[19] == b256(d)[28]);
            } else if i == 24 {
                assert(b256(lo)[24] == b256(es)[20]);
                assert(b256(es)[20] == b256(e)[17]);
            } else if i == 25 {
                assert(b256(lo)[25] == b256(ds)[20]);
                assert(b256(ds)[20] == b256(d)[17]);
            } else if i == 26 {
                assert(b256(lo)[26] == b256(es)[21]);
                assert(b256(es)[21] == b256(e)[21]);
            } else if i == 27 {
                assert(b256(lo)[27] == b256(ds)[21]);
                assert(b256(ds)[21] == b256(d)[21]);
            } else if i == 28 {
                assert(b256(lo)[28] == b256(es)[22]);
                assert(b256(es)[22] == b256(e)[25]);
            } else if i == 29 {
                assert(b256(lo)[29] == b256(ds)[22]);
                assert(b256(ds)[22] == b256(d)[25]);
            } else if i == 30 {
                assert(b256(lo)[30] == b256(es)[23]);
                assert(b256(es)[23] == b256(e)[29]);
            } else if i == 31 {
                assert(b256(lo)[31] == b256(ds)[23]);
                assert(b256(ds)[23] == b256(d)[29]);
            }
        }
        assert forall|i: int| 0 <= i < 32 implies #[trigger] b256(hi)[i] == idct(dq, 4 * (i / 16) + (i % 16) / 8 + 2, i % 8) by {
            if i == 0 {
                assert(b256(hi)[0] == b256(es)[8]);
                assert(b256(es)[8] == b256(e)[2]);
            } else if i == 1 {
                assert(b256(hi)[1] == b256(ds)[8]);
                assert(b256(ds)[8] == b256(d)[2]);
            } else if i == 2 {
                assert(b256(hi)[2] == b256(es)[9]);
                assert(b256(es)[9] == b256(e)[6]);
            } else if i == 3 {
                assert(b256(hi)[3] == b256(ds)[9]);
                assert(b256(ds)[9] == b256(d)[6]);
            } else if i == 4 {
                assert(b256(hi)[4] == b256(es)[10]);
                assert(b256(es)[10] == b256(e)[10]);
            } else if i == 5 {
                assert(b256(hi)[5] == b256(ds)[10]);
                assert(b256(ds)[10] == b256(d)[10]);
            } else if i == 6 {
                assert(b256(hi)[6] == b256(es)[11]);
                assert(b256(es)[11] == b256(e)[14]);
            } else if i == 7 {
                assert(b256(hi)[7] == b256(ds)[11]);
                assert(b256(ds)[11] == b256(d)[14]);
            } else if i == 8 {
                assert(b256(hi)[8] == b256(es)[12]);
                assert(b256(es)[12] == b256(e)[3]);
            } else if i == 9 {
                assert(b256(hi)[9] == b256(ds)[12]);
                assert(b256(ds)[12] == b256(d)[3]);
            } else if i == 10 {
                assert(b256(hi)[10] == b256(es)[13]);
                assert(b256(es)[13] == b256(e)[7]);
            } else if i == 11 {
                assert(b256(hi)[11] == b256(ds)[13]);
                assert(b256(ds)[13] == b256(d)[7]);
            } else if i == 12 {
                assert(b256(hi)[12] == b256(es)[14]);
                assert(b256(es)[14] == b256(e)[11]);
            } else if i == 13 {
                assert(b256(hi)[13] == b256(ds)[14]);
                assert(b256(ds)[14] == b256(d)[11]);
            } else if i == 14 {
                assert(b256(hi)[14] == b256(es)[15]);
                assert(b256(es)[15] == b256(e)[15]);
            } else if i == 15 {
                assert(b256(hi)[15] == b256(ds)[15]);
                assert(b256(ds)[15] == b256(d)[15]);
            } else if i == 16 {
                assert(b256(hi)[16] == b256(es)[24]);
                assert(b256(es)[24] == b256(e)[18]);
            } else if i == 17 {
                assert(b256(hi)[17] == b256(ds)[24]);
                assert(b256(ds)[24] == b256(d)[18]);
            } else if i == 18 {
                assert(b256(hi)[18] == b256(es)[25]);
                assert(b256(es)[25] == b256(e)[22]);
            } else if i == 19 {
                assert(b256(hi)[19] == b256(ds)[25]);
                assert(b256(ds)[25] == b256(d)[22]);
            } else if i == 20 {
                assert(b256(hi)[20] == b256(es)[26]);
                assert(b256(es)[26] == b256(e)[26]);
            } else if i == 21 {
                assert(b256(hi)[21] == b256(ds)[26]);
                assert(b256(ds)[26] == b256(d)[26]);
            } else if i == 22 {
                assert(b256(hi)[22] == b256(es)[27]);
                assert(b256(es)[27] == b256(e)[30]);
            } else if i == 23 {
                assert(b256(hi)[23] == b256(ds)[27]);
                assert(b256(ds)[27] == b256(d)[30]);
            } else if i == 24 {
                assert(b256(hi)[24] == b256(es)[28]);
                assert(b256(es)[28] == b256(e)[19]);
            } else if i == 25 {
                assert(b256(hi)[25] == b256(ds)[28]);
                assert(b256(ds)[28] == b256(d)[19]);
            } else if i == 26 {
                assert(b256(hi)[26] == b256(es)[29]);
                assert(b256(es)[29] == b256(e)[23]);
            } else if i == 27 {
                assert(b256(hi)[27] == b256(ds)[29]);
                assert(b256(ds)[29] == b256(d)[23]);
            } else if i == 28 {
                assert(b256(hi)[28] == b256(es)[30]);
                assert(b256(es)[30] == b256(e)[27]);
            } else if i == 29 {
                assert(b256(hi)[29] == b256(ds)[30]);
                assert(b256(ds)[30] == b256(d)[27]);
            } else if i == 30 {
                assert(b256(hi)[30] == b256(es)[31]);
                assert(b256(es)[31] == b256(e)[31]);
            } else if i == 31 {
                assert(b256(hi)[31] == b256(ds)[31]);
                assert(b256(ds)[31] == b256(d)[31]);
            }
        }
    }
    (lo, hi)
}

/// Stores the low 8 bytes of `v` as row `y` of the block.
#[inline(always)]
fn row_st(out: &mut [u8], v: __m128i, base: usize, stride: usize, y: usize, Ghost(row0): Ghost<int>, Ghost(col0): Ghost<int>, Ghost(blk): Ghost<Seq<u8>>, Ghost(o0): Ghost<Seq<u8>>)
    requires
        y < 8,
        0 <= row0,
        0 <= col0,
        col0 + 8 <= stride,
        base == row0 * stride + col0,
        (row0 + 8) * stride <= old(out)@.len(),
        old(out)@.len() == o0.len(),
        blk.len() == 64,
        forall|x: int| 0 <= x < 8 ==> #[trigger] b128(v)[x] == blk[8 * y + x],
        forall|j: int|
            0 <= j < o0.len() ==> (#[trigger] old(out)@[j]) == if in_rows(j, stride as int, row0, col0, y as int) {
                blk[8 * (j / (stride as int) - row0) + (j % (stride as int) - col0)]
            } else {
                o0[j]
            },
    ensures
        final(out)@.len() == o0.len(),
        forall|j: int|
            0 <= j < o0.len() ==> (#[trigger] final(out)@[j]) == if in_rows(j, stride as int, row0, col0, y + 1) {
                blk[8 * (j / (stride as int) - row0) + (j % (stride as int) - col0)]
            } else {
                o0[j]
            },
{
    let ghost st = stride as int;
    let n = out.len();
    assert(0 <= y * stride && (row0 + y) * stride + stride <= (row0 + 8) * stride && (row0 + y) * stride == row0 * stride + y
        * stride) by (nonlinear_arith)
        requires
            y < 8,
            stride >= 0,
            row0 >= 0,
    ;
    let i = base + y * stride;
    let ghost prev = out@;
    storel64_u8(out, i, v);
    proof {
        assert((row0 + y) * st == st * (row0 + y)) by (nonlinear_arith);
        assert forall|j: int| 0 <= j < o0.len() implies (#[trigger] out@[j]) == if in_rows(j, st, row0, col0, y + 1) {
            blk[8 * (j / st - row0) + (j % st - col0)]
        } else {
            o0[j]
        } by {
            lemma_fundamental_div_mod(j, st);
            if i <= j < i + 8 {
                lemma_fundamental_div_mod_converse(j, st, row0 + y, col0 + (j - i));
                assert(out@[j] == b128(v).subrange(0, 8)[j - i]);
                assert(b128(v)[j - i] == blk[8 * y + (j - i)]);
            } else {
                assert(out@[j] == prev[j]);
            }
        }
    }
}

/// The two vectors of rows stored as the 8 by 8 block at row `row0`,
/// column `col0` of a plane with rows of `stride`.
#[inline(always)]
// The default budget is too small for z3's Arm build here; x86 needs less.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn st8(out: &mut [u8], lo: __m256i, hi: __m256i, row0: usize, col0: usize, stride: usize, Ghost(blk): Ghost<Seq<u8>>)
    requires
        avx2(),
        col0 + 8 <= stride,
        (row0 + 8) * stride <= old(out)@.len(),
        blk.len() == 64,
        forall|i: int| 0 <= i < 32 ==> #[trigger] b256(lo)[i] == blk[8 * (4 * (i / 16) + (i % 16) / 8) + i % 8],
        forall|i: int| 0 <= i < 32 ==> #[trigger] b256(hi)[i] == blk[8 * (4 * (i / 16) + (i % 16) / 8 + 2) + i % 8],
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|j: int|
            0 <= j < final(out)@.len() ==> (#[trigger] final(out)@[j]) == if in_rows(j, stride as int, row0 as int, col0 as int, 8) {
                blk[8 * (j / (stride as int) - row0) + (j % (stride as int) - col0)]
            } else {
                old(out)@[j]
            },
{
    let ghost o0 = out@;
    let n = out.len();
    assert(0 <= row0 * stride && row0 * stride + 8 * stride == (row0 + 8) * stride) by (nonlinear_arith)
        requires
            row0 >= 0,
            stride >= 0,
    ;
    let base = row0 * stride + col0;
    let r01 = _mm256_castsi256_si128(lo);
    let r45 = _mm256_extracti128_si256::<1>(lo);
    let r23 = _mm256_castsi256_si128(hi);
    let r67 = _mm256_extracti128_si256::<1>(hi);
    let r1 = _mm_srli_si128::<8>(r01);
    let r3 = _mm_srli_si128::<8>(r23);
    let r5 = _mm_srli_si128::<8>(r45);
    let r7 = _mm_srli_si128::<8>(r67);
    let ghost r = row0 as int;
    let ghost c = col0 as int;
    proof {
        assert forall|x: int| 0 <= x < 8 implies #[trigger] b128(r01)[x] == blk[0 + x] by {
            assert(b256(lo)[0 + x] == blk[0 + x]);
        }
        assert forall|x: int| 0 <= x < 8 implies #[trigger] b128(r1)[x] == blk[8 + x] by {
            assert(b256(lo)[8 + x] == blk[8 + x]);
        }
        assert forall|x: int| 0 <= x < 8 implies #[trigger] b128(r23)[x] == blk[16 + x] by {
            assert(b256(hi)[0 + x] == blk[16 + x]);
        }
        assert forall|x: int| 0 <= x < 8 implies #[trigger] b128(r3)[x] == blk[24 + x] by {
            assert(b256(hi)[8 + x] == blk[24 + x]);
        }
        assert forall|x: int| 0 <= x < 8 implies #[trigger] b128(r45)[x] == blk[32 + x] by {
            assert(b256(lo)[16 + x] == blk[32 + x]);
        }
        assert forall|x: int| 0 <= x < 8 implies #[trigger] b128(r5)[x] == blk[40 + x] by {
            assert(b256(lo)[24 + x] == blk[40 + x]);
        }
        assert forall|x: int| 0 <= x < 8 implies #[trigger] b128(r67)[x] == blk[48 + x] by {
            assert(b256(hi)[16 + x] == blk[48 + x]);
        }
        assert forall|x: int| 0 <= x < 8 implies #[trigger] b128(r7)[x] == blk[56 + x] by {
            assert(b256(hi)[24 + x] == blk[56 + x]);
        }
        assert forall|j: int| 0 <= j < o0.len() implies (#[trigger] out@[j]) == if in_rows(j, stride as int, r, c, 0) {
            blk[8 * (j / (stride as int) - r) + (j % (stride as int) - c)]
        } else {
            o0[j]
        } by {}
    }
    row_st(out, r01, base, stride, 0, Ghost(r), Ghost(c), Ghost(blk), Ghost(o0));
    row_st(out, r1, base, stride, 1, Ghost(r), Ghost(c), Ghost(blk), Ghost(o0));
    row_st(out, r23, base, stride, 2, Ghost(r), Ghost(c), Ghost(blk), Ghost(o0));
    row_st(out, r3, base, stride, 3, Ghost(r), Ghost(c), Ghost(blk), Ghost(o0));
    row_st(out, r45, base, stride, 4, Ghost(r), Ghost(c), Ghost(blk), Ghost(o0));
    row_st(out, r5, base, stride, 5, Ghost(r), Ghost(c), Ghost(blk), Ghost(o0));
    row_st(out, r67, base, stride, 6, Ghost(r), Ghost(c), Ghost(blk), Ghost(o0));
    row_st(out, r7, base, stride, 7, Ghost(r), Ghost(c), Ghost(blk), Ghost(o0));
}

/// Bytes of four vectors OR-ed are all zero only if each is.
proof fn lemma_or4_zero(a: u8, b: u8, c: u8, d: u8)
    requires
        ((a | b) | (c | d)) & ((a | b) | (c | d)) == 0,
    ensures
        a == 0 && b == 0 && c == 0 && d == 0,
{
    assert(((a | b) | (c | d)) & ((a | b) | (c | d)) == 0 ==> a == 0 && b == 0 && c == 0 && d == 0) by (bit_vector);
}

/// The checks: 1 for a block with only its DC coefficient, 2 for one too
/// large for 16-bit rows, else 0 and its dequantized rows, two to a
/// vector.
#[inline(always)]
#[verifier::spinoff_prover]
fn front(a: &[i16], o: usize, qs: &[u16]) -> (r: (u8, __m256i, __m256i, __m256i, __m256i))
    requires
        avx2(),
        o + 64 <= a@.len(),
        qs@.len() == 64,
    ensures
        r.0 == 0 ==> {
            &&& atot(dequant(a@, o as int, qs@)) <= tot_max()
            &&& forall|i: int| 0 <= i < 16 ==> #[trigger] h16(r.1, i) == dequant(a@, o as int, qs@)[i]
            &&& forall|i: int| 0 <= i < 16 ==> #[trigger] h16(r.2, i) == dequant(a@, o as int, qs@)[16 + i]
            &&& forall|i: int| 0 <= i < 16 ==> #[trigger] h16(r.3, i) == dequant(a@, o as int, qs@)[32 + i]
            &&& forall|i: int| 0 <= i < 16 ==> #[trigger] h16(r.4, i) == dequant(a@, o as int, qs@)[48 + i]
        },
{
    hide(dequant);
    hide(acol);
    hide(atot);
    let n = a.len();
    let ghost dq = dequant(a@, o as int, qs@);
    proof {
        reveal(dequant);
        assert(dq.len() == 64);
    }
    let c0 = load256_i16(a, o);
    let c1 = load256_i16(a, o + 16);
    let c2 = load256_i16(a, o + 32);
    let c3 = load256_i16(a, o + 48);
    // Every coefficient but the DC zero: the caller's DC-only path.
    let nodc = _mm256_setr_epi32(-65536, -1, -1, -1, -1, -1, -1, -1);
    let ac = _mm256_or_si256(_mm256_or_si256(_mm256_and_si256(c0, nodc), c1), _mm256_or_si256(c2, c3));
    if _mm256_testz_si256(ac, ac) == 1 {
        return (1, c0, c0, c0, c0);
    }
    let (l0, e0, g0) = deqv(c0, a, o, qs, 0);
    let (l1, e1, g1) = deqv(c1, a, o, qs, 1);
    let (l2, e2, g2) = deqv(c2, a, o, qs, 2);
    let (l3, e3, g3) = deqv(c3, a, o, qs, 3);
    let e01 = _mm256_or_si256(e0, e1);
    let e23 = _mm256_or_si256(e2, e3);
    let e = _mm256_or_si256(e01, e23);
    if _mm256_testz_si256(e, e) == 0 {
        return (2, c0, c0, c0, c0);
    }
    proof {
        assert forall|b: int| 0 <= b < 32 implies #[trigger] b256(e0)[b] == 0u8 by {
            assert(and8(b256(e), b256(e))[b] == 0u8);
            lemma_or4_zero(b256(e0)[b], b256(e1)[b], b256(e2)[b], b256(e3)[b]);
        }
        assert forall|b: int| 0 <= b < 32 implies #[trigger] b256(e1)[b] == 0u8 by {
            assert(and8(b256(e), b256(e))[b] == 0u8);
            lemma_or4_zero(b256(e0)[b], b256(e1)[b], b256(e2)[b], b256(e3)[b]);
        }
        assert forall|b: int| 0 <= b < 32 implies #[trigger] b256(e2)[b] == 0u8 by {
            assert(and8(b256(e), b256(e))[b] == 0u8);
            lemma_or4_zero(b256(e0)[b], b256(e1)[b], b256(e2)[b], b256(e3)[b]);
        }
        assert forall|b: int| 0 <= b < 32 implies #[trigger] b256(e3)[b] == 0u8 by {
            assert(and8(b256(e), b256(e))[b] == 0u8);
            lemma_or4_zero(b256(e0)[b], b256(e1)[b], b256(e2)[b], b256(e3)[b]);
        }
        assert(deq_ok(l0, e0, g0, a@, o as int, qs@, 0));
        assert(deq_ok(l1, e1, g1, a@, o as int, qs@, 1));
        assert(deq_ok(l2, e2, g2, a@, o as int, qs@, 2));
        assert(deq_ok(l3, e3, g3, a@, o as int, qs@, 3));
    }
    let t = hsum(g0, g1, g2, g3);
    if t > 2120 {
        return (2, c0, c0, c0, c0);
    }
    proof {
        lemma_atot_link(dq, g0, g1, g2, g3);
    }
    (0, l0, l1, l2, l3)
}

/// Both passes and the stores, for a block that passed the checks.
#[inline(always)]
#[verifier::spinoff_prover]
fn back(l0: __m256i, l1: __m256i, l2: __m256i, l3: __m256i, out: &mut [u8], row0: usize, col0: usize, stride: usize, Ghost(dq): Ghost<Seq<int>>) -> (blk: Ghost<Seq<u8>>)
    requires
        avx2(),
        dq.len() == 64,
        atot(dq) <= tot_max(),
        col0 + 8 <= stride,
        (row0 + 8) * stride <= old(out)@.len(),
        forall|i: int| 0 <= i < 16 ==> #[trigger] h16(l0, i) == dq[i],
        forall|i: int| 0 <= i < 16 ==> #[trigger] h16(l1, i) == dq[16 + i],
        forall|i: int| 0 <= i < 16 ==> #[trigger] h16(l2, i) == dq[32 + i],
        forall|i: int| 0 <= i < 16 ==> #[trigger] h16(l3, i) == dq[48 + i],
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
    hide(acol);
    hide(atot);
    let w = pass1(l0, l1, l2, l3, Ghost(dq));
    let s = pass2(w.0, w.1, w.2, w.3, w.4, w.5, w.6, w.7, Ghost(dq));
    let a02 = pk32(s.0, s.2, Ghost(dq), Ghost(0), Ghost(2));
    let a46 = pk32(s.4, s.6, Ghost(dq), Ghost(4), Ghost(6));
    let a13 = pk32(s.1, s.3, Ghost(dq), Ghost(1), Ghost(3));
    let a57 = pk32(s.5, s.7, Ghost(dq), Ghost(5), Ghost(7));
    let ev = pk16(a02, a46, Ghost(dq), Ghost(0), Ghost(2), Ghost(4), Ghost(6));
    let od = pk16(a13, a57, Ghost(dq), Ghost(1), Ghost(3), Ghost(5), Ghost(7));
    proof {
        assert forall|i: int| 0 <= i < 32 implies #[trigger] b256(ev)[i] == idct(dq, 4 * (i / 16) + i % 4, 2 * ((i % 16) / 4)) by {
            let c = (i % 16) / 4;
            assert(sel4i(0, 2, 4, 6, c) == 2 * c);
        }
        assert forall|i: int| 0 <= i < 32 implies #[trigger] b256(od)[i] == idct(dq, 4 * (i / 16) + i % 4, 2 * ((i % 16) / 4) + 1) by {
            let c = (i % 16) / 4;
            assert(sel4i(1, 3, 5, 7, c) == 2 * c + 1);
        }
    }
    let (lo, hi) = rows(ev, od, Ghost(dq));
    let ghost blk = Seq::new(64, |k: int| idct(dq, k / 8, k % 8));
    proof {
        assert forall|i: int| 0 <= i < 32 implies #[trigger] b256(lo)[i] == blk[8 * (4 * (i / 16) + (i % 16) / 8) + i % 8] by {
            let k = 8 * (4 * (i / 16) + (i % 16) / 8) + i % 8;
            assert(0 <= k < 64 && k / 8 == 4 * (i / 16) + (i % 16) / 8 && k % 8 == i % 8);
        }
        assert forall|i: int| 0 <= i < 32 implies #[trigger] b256(hi)[i] == blk[8 * (4 * (i / 16) + (i % 16) / 8 + 2) + i % 8] by {
            let k = 8 * (4 * (i / 16) + (i % 16) / 8 + 2) + i % 8;
            assert(0 <= k < 64 && k / 8 == 4 * (i / 16) + (i % 16) / 8 + 2 && k % 8 == i % 8);
        }
    }
    st8(out, lo, hi, row0, col0, stride, Ghost(blk));
    Ghost(blk)
}

/// The inverse DCT of the block at `o` of `a` with the quantizers `q`,
/// stored at row `row0`, column `col0` of `out`: 0 when it did that, 1
/// when the block has only its DC coefficient, 2 when the block is too
/// large for 16-bit rows (`out` unchanged for 1 and 2).
#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "avx2"))]
pub fn idct_avx2(a: &[i16], o: usize, q: &[u16; 64], out: &mut [u8], row0: usize, col0: usize, stride: usize) -> (r: (u8, Ghost<Seq<u8>>))
    requires
        avx2(),
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
    hide(acol);
    hide(atot);
    let qs: &[u16] = q;
    let ghost dq = dequant(a@, o as int, q@);
    proof {
        reveal(dequant);
        assert(dq.len() == 64);
        assert(qs@ == q@);
    }
    let (f, l0, l1, l2, l3) = front(a, o, qs);
    if f != 0 {
        return (f, Ghost(Seq::empty()));
    }
    let blk = back(l0, l1, l2, l3, out, row0, col0, stride, Ghost(dq));
    (0, blk)
}

} // verus!

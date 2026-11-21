//! The inverse predictor transform, a run of same-mode pixels at a time,
//! with AVX2/SSE kernels; verified against `spec::unpredict`.
//!
//! Within a row (past its first pixel) the pixels of one block share a mode.
//! For such a run, `pstep` says what the decoder must store at each pixel,
//! in terms of pixels already final: its left neighbour (in the run or just
//! before it) and three pixels of the row above. The kernels establish
//! `pstep` over a run; `lemma_unpredict_run` turns that into the spec's
//! `unpredict` prefix.
use crate::pixels::*;
use verilith_core::prims::*;
#[cfg(verus_only)]
use crate::undo::{lemma_shr, lemma_sub_bound};
use crate::pxops::*;
use crate::vpx::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use crate::vlemmas::*;
use verilith_simd::arch::*;
use verilith_simd::cpu::*;
#[cfg(verus_only)]
use verilith_simd::lanes::*;
use verilith_simd::mem::*;
use verilith_simd::neon::*;
#[cfg(verus_only)]
use verilith_simd::ops::*;
#[cfg(verus_only)]
use verilith_simd::patterns::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::cpu::group_cpu, verilith_simd::neon::group_neon};

/// Pixel `j` holds its residual plus mode `m`'s prediction from the final
/// pixels around it.
pub open spec fn pstep(px: Seq<u32>, src: Seq<u32>, w: int, m: nat, j: int) -> bool {
    px[j] == add_px(src[j], predict_mode(m, px[j - 1], px[j - w], px[j - w + 1], px[j - w - 1]))
}

/// The geometry of a run: inside one row, past its first pixel, not the
/// first row.
pub open spec fn run_geom(len: nat, w: int, row: int, i0: int, i1: int) -> bool {
    &&& 2 <= w
    &&& w <= row
    &&& row + 1 <= i0 <= i1 <= row + w
    &&& row + w <= len
}

/// The modes that read only the row above.
pub open spec fn vertical(m: nat) -> bool {
    m == 0 || m == 2 || m == 3 || m == 4 || m == 8 || m == 9 || m >= 14
}

proof fn lemma_vertical_ignores_l(m: nat, l1: u32, l2: u32, t: u32, tr: u32, tl: u32)
    requires
        vertical(m),
    ensures
        predict_mode(m, l1, t, tr, tl) == predict_mode(m, l2, t, tr, tl),
{
}

/// Mode `m`'s prediction for the eight pixels at `j..j + 8` (all of which
/// read only the row above).
#[inline(always)]
fn vert_pred8(px: &[u32], j: usize, w: usize, m: u32) -> (r: __m256i)
    requires
        avx2(),
        vertical(m as nat),
        m < 16,
        2 <= w,
        w + 1 <= j,
        j + 8 <= px@.len(),
    ensures
        forall|k: int|
            0 <= k < 8 ==> #[trigger] u32x8(r)[k] == predict_mode(
                m as nat,
                px@[j + k - 1],
                px@[j + k - w],
                px@[j + k - w + 1],
                px@[j + k - w - 1],
            ),
{
    if m == 2 {
        load256_u32(px, j - w)
    } else if m == 3 {
        load256_u32(px, j - w + 1)
    } else if m == 4 {
        load256_u32(px, j - w - 1)
    } else if m == 8 || m == 9 {
        let a = if m == 8 {
            load256_u32(px, j - w - 1)
        } else {
            load256_u32(px, j - w + 1)
        };
        let t = load256_u32(px, j - w);
        let ones = _mm256_set1_epi8(1);
        let r = _mm256_sub_epi8(_mm256_avg_epu8(a, t), _mm256_and_si256(_mm256_xor_si256(a, t), ones));
        proof {
            lemma_avgf_px(b256(a), b256(t), b256(ones), b256(r));
            assert forall|k: int| 0 <= k < 8 implies #[trigger] u32x8(r)[k] == predict_mode(
                m as nat,
                px@[j + k - 1],
                px@[j + k - w],
                px@[j + k - w + 1],
                px@[j + k - w - 1],
            ) by {
                assert(u32x8(t)[k] == px@[j + k - w]);
                if m == 8 {
                    assert(u32x8(a)[k] == px@[j + k - w - 1]);
                } else {
                    assert(u32x8(a)[k] == px@[j + k - w + 1]);
                    lemma_avg2_comm(u32x8(a)[k], u32x8(t)[k]);
                }
            }
        }
        r
    } else {
        _mm256_set1_epi32(i32_of_u32(0xff00_0000))
    }
}

proof fn lemma_avg2_comm(x: u32, y: u32)
    ensures
        avg2(x, y) == avg2(y, x),
{
}

/// Stores into `j..j + k` keep `pstep` at the pixels before `j`.
proof fn lemma_pstep_frame(old: Seq<u32>, new: Seq<u32>, src: Seq<u32>, w: int, m: nat, i0: int, j: int)
    requires
        old.len() == new.len(),
        2 <= w,
        w + 1 <= i0,
        forall|q: int| 0 <= q < j ==> #[trigger] new[q] == old[q],
        forall|q: int| i0 <= q < j ==> #[trigger] pstep(old, src, w, m, q),
    ensures
        forall|q: int| i0 <= q < j ==> #[trigger] pstep(new, src, w, m, q),
{
    assert forall|q: int| i0 <= q < j implies #[trigger] pstep(new, src, w, m, q) by {
        assert(pstep(old, src, w, m, q));
        assert(new[q] == old[q]);
        assert(new[q - 1] == old[q - 1]);
        assert(new[q - w] == old[q - w]);
        assert(new[q - w + 1] == old[q - w + 1]);
        assert(new[q - w - 1] == old[q - w - 1]);
    }
}

/// A run in one of the vertical modes, eight pixels at a time.
#[inline(always)]
fn run_vertical(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize, m: u32)
    requires
        avx2(),
        vertical(m as nat),
        m < 16,
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, m as nat, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    let ghost src = px@;
    let mut j = i0;
    while i1 - j >= 8
        invariant
            avx2(),
            vertical(m as nat),
            m < 16,
            run_geom(src.len(), w as int, row as int, i0 as int, i1 as int),
            i0 <= j <= i1,
            px@.len() == src.len(),
            forall|q: int| i0 <= q < j ==> #[trigger] pstep(px@, src, w as int, m as nat, q),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let p = vert_pred8(px.as_slice(), j, w, m);
        let s = load256_u32(px.as_slice(), j);
        let o = _mm256_add_epi8(s, p);
        let ghost before = px@;
        proof {
            lemma_add8_px(b256(s), b256(p));
        }
        store256_u32(px.as_mut_slice(), j, o);
        proof {
            lemma_pstep_frame(before, px@, src, w as int, m as nat, i0 as int, j as int);
            assert forall|q: int| j <= q < j + 8 implies #[trigger] pstep(px@, src, w as int, m as nat, q) by {
                let k = q - j;
                assert(px@[q] == u32x8(o)[k]);
                assert(u32x8(o)[k] == add_px(u32x8(s)[k], u32x8(p)[k]));
                assert(u32x8(p)[k] == predict_mode(m as nat, before[j + k - 1], before[j + k - w], before[j + k - w + 1], before[j + k - w - 1]));
                assert(u32x8(s)[k] == src[q]);
                assert(px@[q - w] == before[q - w]);
                assert(px@[q - w + 1] == before[q - w + 1]);
                assert(px@[q - w - 1] == before[q - w - 1]);
                lemma_vertical_ignores_l(m as nat, px@[q - 1], before[j + k - 1], px@[q - w], px@[q - w + 1], px@[q - w - 1]);
            }
        }
        j = j + 8;
    }
    let ghost mid = px@;
    run_scalar(px, j, i1, row, w, m);
    proof {
        lemma_pstep_frame(mid, px@, src, w as int, m as nat, i0 as int, j as int);
        assert forall|q: int| j <= q < i1 implies #[trigger] pstep(px@, src, w as int, m as nat, q) by {
            assert(pstep(px@, mid, w as int, m as nat, q));
            assert(mid[q] == src[q]);
        }
    }
}

/// A run in any mode, one pixel at a time.
fn run_scalar(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize, m: u32)
    requires
        m < 16,
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, m as nat, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    let ghost src = px@;
    if i0 == i1 {
        return;
    }
    let mut l = get32(px.as_slice(), i0 - 1);
    let mut j = i0;
    while j < i1
        invariant
            m < 16,
            run_geom(src.len(), w as int, row as int, i0 as int, i1 as int),
            i0 <= j <= i1,
            px@.len() == src.len(),
            l == px@[j - 1],
            forall|q: int| i0 <= q < j ==> #[trigger] pstep(px@, src, w as int, m as nat, q),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = px.as_slice();
        let c = add_px_exec(get32(s, j), predict_mode_exec(m, l, get32(s, j - w), get32(s, j - w + 1), get32(s, j - w - 1)));
        let ghost before = px@;
        set32(px.as_mut_slice(), j, c);
        proof {
            lemma_pstep_frame(before, px@, src, w as int, m as nat, i0 as int, j as int);
            assert(before[j as int] == src[j as int]);
            assert(pstep(px@, src, w as int, m as nat, j as int));
        }
        l = c;
        j = j + 1;
    }
}

/// Four pixels of a left-predicted run: the in-vector prefix sum.
proof fn lemma_left4(s: Seq<u8>, a: Seq<u8>, b: Seq<u8>, pv: Seq<u8>, r: Seq<u8>, l: u32)
    requires
        s.len() == 16 && pv.len() == 16,
        a == add8(s, bslli_lanes(s, 4)),
        b == add8(a, bslli_lanes(a, 8)),
        u32s(pv) == splat32(l, 4),
        r == add8(b, pv),
    ensures
        u32s(r)[0] == add_px(u32s(s)[0], l),
        u32s(r)[1] == add_px(u32s(s)[1], u32s(r)[0]),
        u32s(r)[2] == add_px(u32s(s)[2], u32s(r)[1]),
        u32s(r)[3] == add_px(u32s(s)[3], u32s(r)[2]),
{
    lemma_bslli_u32s(s, 1);
    assert(4 * 1 == 4);
    lemma_add8_px(s, bslli_lanes(s, 4));
    lemma_bslli_u32s(a, 2);
    assert(4 * 2 == 8);
    lemma_add8_px(a, bslli_lanes(a, 8));
    lemma_add8_px(b, pv);
    let (s0, s1, s2, s3) = (u32s(s)[0], u32s(s)[1], u32s(s)[2], u32s(s)[3]);
    let us = u32s(bslli_lanes(s, 4));
    assert(us[0] == 0 && us[1] == s0 && us[2] == s1 && us[3] == s2);
    let ua = u32s(a);
    assert(ua[0] == add_px(s0, 0) && ua[1] == add_px(s1, s0) && ua[2] == add_px(s2, s1) && ua[3] == add_px(s3, s2));
    lemma_add_px_zero(s0);
    let ub = u32s(bslli_lanes(a, 8));
    assert(ub[0] == 0 && ub[1] == 0 && ub[2] == ua[0] && ub[3] == ua[1]);
    let bb = u32s(b);
    lemma_add_px_zero(ua[0]);
    lemma_add_px_zero(ua[1]);
    assert(bb[0] == s0 && bb[1] == add_px(s1, s0) && bb[2] == add_px(add_px(s2, s1), s0) && bb[3] == add_px(
        add_px(s3, s2),
        add_px(s1, s0),
    ));
    let r0 = add_px(s0, l);
    assert(u32s(r)[0] == r0);
    // r1
    lemma_add_px_assoc(s1, s0, l);
    let r1 = add_px(s1, r0);
    assert(u32s(r)[1] == r1);
    // r2
    lemma_add_px_assoc(add_px(s2, s1), s0, l);
    lemma_add_px_assoc(s2, s1, r0);
    let r2 = add_px(s2, r1);
    assert(u32s(r)[2] == r2);
    // r3
    lemma_add_px_assoc(add_px(s3, s2), add_px(s1, s0), l);
    lemma_add_px_assoc(s3, s2, r1);
    assert(u32s(r)[3] == add_px(s3, r2));
}

/// Pixels `i0..i1` each add their residual to the final pixel on their
/// left; four at a time.
#[verifier::rlimit(30)]
#[inline(always)]
fn run_left(px: &mut Vec<u32>, i0: usize, i1: usize)
    requires
        avx2(),
        1 <= i0 <= i1 <= old(px)@.len(),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] final(px)@[j] == add_px(old(px)@[j], final(px)@[j - 1]),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    hide(add_px);
    hide(add8);
    hide(bslli_lanes);
    hide(shuffle32_lanes);
    let ghost src = px@;
    let l0 = get32(px.as_slice(), i0 - 1);
    let mut prev = _mm_set1_epi32(i32_of_u32(l0));
    let mut j = i0;
    while i1 - j >= 4
        invariant
            avx2(),
            1 <= i0 <= j <= i1 <= src.len(),
            px@.len() == src.len(),
            u32x4(prev) == splat32(px@[j - 1], 4),
            forall|q: int| i0 <= q < j ==> #[trigger] px@[q] == add_px(src[q], px@[q - 1]),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = load128_u32(px.as_slice(), j);
        let a = _mm_add_epi8(s, _mm_slli_si128::<4>(s));
        let b = _mm_add_epi8(a, _mm_slli_si128::<8>(a));
        let r = _mm_add_epi8(b, prev);
        let ghost before = px@;
        proof {
            lemma_left4(b128(s), b128(a), b128(b), b128(prev), b128(r), before[j - 1]);
        }
        store128_u32(px.as_mut_slice(), j, r);
        prev = _mm_shuffle_epi32::<0xff>(r);
        proof {
            lemma_shuffle32_splat3(u32x4(r));
            let ur = u32x4(r);
            let us = u32x4(s);
            assert(px@[j as int] == ur[0] && px@[j + 1] == ur[1] && px@[j + 2] == ur[2] && px@[j + 3] == ur[3]);
            assert(us[0] == src[j as int] && us[1] == src[j + 1] && us[2] == src[j + 2] && us[3] == src[j + 3]);
            assert(px@[j - 1] == before[j - 1]);
            assert(u32x4(prev) =~= splat32(px@[j + 3], 4));
            assert(px@[j + 0] == add_px(src[j + 0], px@[j + 0 - 1]));
            assert(px@[j + 1] == add_px(src[j + 1], px@[j + 1 - 1]));
            assert(px@[j + 2] == add_px(src[j + 2], px@[j + 2 - 1]));
            assert(px@[j + 3] == add_px(src[j + 3], px@[j + 3 - 1]));
            assert forall|q: int| i0 <= q < j + 4 implies #[trigger] px@[q] == add_px(src[q], px@[q - 1]) by {
                if q < j {
                    assert(px@[q] == before[q] && px@[q - 1] == before[q - 1]);
                }
            }
        }
        j = j + 4;
    }
    while j < i1
        invariant
            1 <= i0 <= j <= i1 <= src.len(),
            px@.len() == src.len(),
            forall|q: int| i0 <= q < j ==> #[trigger] px@[q] == add_px(src[q], px@[q - 1]),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = px.as_slice();
        let c = add_px_exec(get32(s, j), get32(s, j - 1));
        let ghost before = px@;
        set32(px.as_mut_slice(), j, c);
        assert forall|q: int| i0 <= q < j + 1 implies #[trigger] px@[q] == add_px(src[q], px@[q - 1]) by {
            if q < j {
                assert(px@[q] == before[q] && px@[q - 1] == before[q - 1]);
            }
        }
        j = j + 1;
    }
}

/// A run in mode `m`.
#[inline(always)]
fn run_mode(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize, m: u32)
    requires
        avx2(),
        m < 16,
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, m as nat, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    if m == 0 || m == 2 || m == 3 || m == 4 || m == 8 || m == 9 || m >= 14 {
        run_vertical(px, i0, i1, row, w, m);
    } else if m == 1 {
        let ghost src = px@;
        run_left(px, i0, i1);
        assert forall|j: int| i0 <= j < i1 implies #[trigger] pstep(px@, src, w as int, m as nat, j) by {
        }
    } else if m == 5 {
        run_m5(px, i0, i1, row, w);
    } else if m == 6 {
        run_m6(px, i0, i1, row, w);
    } else if m == 7 {
        run_m7(px, i0, i1, row, w);
    } else if m == 10 {
        run_m10(px, i0, i1, row, w);
    } else if m == 11 {
        run_m11(px, i0, i1, row, w);
    } else if m == 12 {
        run_m12(px, i0, i1, row, w);
    } else {
        run_m13(px, i0, i1, row, w);
    }
}

/// The block's mode for pixel `j` (not in the first row or column).
pub open spec fn mode_at(j: nat, w: nat, bits: nat, data: Seq<u32>) -> nat {
    green(data[(((j / w) / pow2(bits)) * subsample(w, bits) + (j % w) / pow2(bits)) as int]) as nat % 16
}

/// A run satisfying `pstep` extends the `unpredict` prefix over it.
proof fn lemma_unpredict_run(src: Seq<u32>, px: Seq<u32>, w: nat, bits: nat, data: Seq<u32>, i0: nat, i1: nat, m: nat)
    requires
        2 <= w,
        i0 <= i1 <= px.len(),
        px.subrange(0, i0 as int) == unpredict(src, w, bits, data, i0),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(px, src, w as int, m, j),
        forall|j: nat|
            i0 <= j < i1 ==> #[trigger] (j % w) >= 1 && j / w >= 1 && mode_at(j, w, bits, data) == m,
    ensures
        px.subrange(0, i1 as int) == unpredict(src, w, bits, data, i1),
    decreases i1 - i0,
{
    if i0 < i1 {
        let o = unpredict(src, w, bits, data, i0);
        assert(i0 % w >= 1 && i0 / w >= 1 && mode_at(i0, w, bits, data) == m);
        assert(i0 >= w + 1) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i0 as int, w as int);
            assert(i0 >= w * (i0 / w) + 1);
            assert(w * (i0 / w) >= w) by (nonlinear_arith)
                requires
                    i0 / w >= 1,
                    w >= 2,
            ;
        }
        assert(o == px.subrange(0, i0 as int));
        assert(predict(o, i0, w, bits, data) == predict_mode(m, px[i0 - 1], px[i0 - w], px[i0 - w + 1], px[i0 - w - 1]));
        assert(pstep(px, src, w as int, m, i0 as int));
        assert(unpredict(src, w, bits, data, i0 + 1) == o.push(add_px(src[i0 as int], predict(o, i0, w, bits, data))));
        assert(px.subrange(0, i0 + 1 as int) =~= o.push(px[i0 as int]));
        lemma_unpredict_run(src, px, w, bits, data, i0 + 1, i1, m);
    }
}

/// One more pixel of the `unpredict` prefix.
proof fn lemma_unpredict_step(src: Seq<u32>, px: Seq<u32>, w: nat, bits: nat, data: Seq<u32>, i: nat)
    requires
        i < px.len(),
        px.subrange(0, i as int) == unpredict(src, w, bits, data, i),
        px[i as int] == add_px(src[i as int], predict(px.subrange(0, i as int), i, w, bits, data)),
    ensures
        px.subrange(0, i + 1 as int) == unpredict(src, w, bits, data, i + 1),
{
    assert(px.subrange(0, i + 1 as int) =~= px.subrange(0, i as int).push(px[i as int]));
}

/// The first row (past pixel 0) is predicted from the left.
proof fn lemma_unpredict_row0(src: Seq<u32>, px: Seq<u32>, w: nat, bits: nat, data: Seq<u32>, i0: nat, i1: nat)
    requires
        1 <= i0 <= i1 <= w,
        i1 <= px.len(),
        px.subrange(0, i0 as int) == unpredict(src, w, bits, data, i0),
        forall|j: int| i0 <= j < i1 ==> #[trigger] px[j] == add_px(src[j], px[j - 1]),
    ensures
        px.subrange(0, i1 as int) == unpredict(src, w, bits, data, i1),
    decreases i1 - i0,
{
    if i0 < i1 {
        assert(i0 / w == 0) by {
            vstd::arithmetic::div_mod::lemma_basic_div(i0 as int, w as int);
        }
        assert(px[i0 as int] == add_px(src[i0 as int], px[i0 - 1]));
        lemma_unpredict_step(src, px, w, bits, data, i0);
        lemma_unpredict_row0(src, px, w, bits, data, i0 + 1, i1);
    }
}

/// Undoes the predictor transform, a run of one mode at a time.
#[verifier::rlimit(40)]
#[inline(always)]
fn unpredict_runs<const FAST: bool>(px: &mut Vec<u32>, w: usize, h: usize, bits: u32, data: &Vec<u32>)
    requires
        FAST ==> avx2(),
        1 <= w <= 16384,
        1 <= h <= 16384,
        old(px)@.len() == w * h,
        2 <= bits <= 9,
        data@.len() == subsample(w as nat, bits as nat) * subsample(h as nat, bits as nat),
    ensures
        final(px)@ == unpredict(old(px)@, w as nat, bits as nat, data@, old(px)@.len()),
{
    hide(add_px);
    hide(predict_mode);
    let ghost src = px@;
    let ghost (wn, bn, dn) = (w as nat, bits as nat, data@);
    proof {
        assert(w * h <= 16384 * 16384) by (nonlinear_arith)
            requires
                w <= 16384,
                h <= 16384,
        ;
        assert(w * h >= 1) by (nonlinear_arith)
            requires
                w >= 1,
                h >= 1,
        ;
        lemma_pow2_pos(bits as nat);
        lemma2_to64();
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(bits as nat, 10);
    }
    let n = w * h;
    // Pixel 0 predicts black.
    let c0 = add_px_exec(get32(px.as_slice(), 0), 0xff00_0000);
    set32(px.as_mut_slice(), 0, c0);
    proof {
        assert(px@.subrange(0, 0) =~= unpredict(src, wn, bn, dn, 0));
        lemma_unpredict_step(src, px@, wn, bn, dn, 0);
    }
    // The rest of the first row predicts from the left.
    proof {
        assert(w <= w * h) by (nonlinear_arith)
            requires
                h >= 1,
        ;
    }
    let ghost before = px@;
    if FAST {
        // SAFETY: FAST only when the CPU has AVX2.
        unsafe { run_left(px, 1, w) };
    } else {
        run_left_swar(px, 1, w);
    }
    proof {
        assert(px@.subrange(0, 1) =~= before.subrange(0, 1));
        assert forall|j: int| 1 <= j < w implies #[trigger] px@[j] == add_px(src[j], px@[j - 1]) by {
            assert(before[j] == src[j]);
        }
        lemma_unpredict_row0(src, px@, wn, bn, dn, 1, wn);
    }
    let sw = subsample_exec(w, bits);
    let bw: usize = 1usize << bits;
    proof {
        assert(bw as nat == pow2(bits as nat)) by {
            vstd::bits::lemma_usize_shl_is_mul(1, bits as usize);
        }
        lemma_sub_bound(h as nat, bits as nat, 0);
        assert(data@.len() <= w * h) by (nonlinear_arith)
            requires
                data@.len() == sw * subsample(h as nat, bits as nat),
                sw <= w,
                subsample(h as nat, bits as nat) <= h,
        ;
        if bits > 2 {
            lemma_pow2_strictly_increases(2, bits as nat);
        }
    }
    let mut y: usize = 1;
    while y < h
        invariant
            FAST ==> avx2(),
            1 <= w <= 16384,
            1 <= h <= 16384,
            2 <= bits <= 9,
            n == w * h,
            n <= 16384 * 16384,
            px@.len() == n,
            src.len() == n,
            (wn, bn, dn) == (w as nat, bits as nat, data@),
            sw == subsample(w as nat, bits as nat),
            1 <= sw,
            forall|x: nat| x < w ==> #[trigger] (x / pow2(bits as nat)) < sw,
            bw as nat == pow2(bits as nat),
            4 <= bw <= 512,
            sw <= w,
            data@.len() <= n,
            data@.len() == sw * subsample(h as nat, bits as nat),
            1 <= y <= h,
            px@.subrange(0, y * w) == unpredict(src, wn, bn, dn, (y * w) as nat),
            forall|j: int| y * w <= j < n ==> #[trigger] px@[j] == src[j],
        decreases h - y,
    {
        proof {
            assert(y * w + w <= n) by (nonlinear_arith)
                requires
                    y < h,
                    n == w * h,
            ;
            assert(y * w >= w) by (nonlinear_arith)
                requires
                    y >= 1,
            ;
        }
        let row = y * w;
        // The first pixel of a row predicts from above.
        let c = add_px_exec(get32(px.as_slice(), row), get32(px.as_slice(), row - w));
        let ghost pre = px@;
        set32(px.as_mut_slice(), row, c);
        proof {
            assert(px@.subrange(0, row as int) =~= pre.subrange(0, row as int));
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(row as int, w as int, y as int, 0);
            assert(predict(px@.subrange(0, row as int), row as nat, wn, bn, dn) == px@[row - w]);
            lemma_unpredict_step(src, px@, wn, bn, dn, row as nat);
        }
        if w >= 2 {
            proof {
                lemma_shr(y, bits);
                lemma_sub_bound(h as nat, bits as nat, y as nat);
            }
            let by = y >> bits;
            proof {
                assert(by * sw + sw <= data@.len()) by (nonlinear_arith)
                    requires
                        by < subsample(h as nat, bits as nat),
                        data@.len() == sw * subsample(h as nat, bits as nat),
                ;
            }
            let brow = by * sw;
            let mut x0: usize = 1;
            let mut bx: usize = 0;
            while x0 < w
                invariant
                    FAST ==> avx2(),
                    2 <= w <= 16384,
                    2 <= bits <= 9,
                    px@.len() == n,
                    src.len() == n,
                    (wn, bn, dn) == (w as nat, bits as nat, data@),
                    sw == subsample(w as nat, bits as nat),
                    forall|x: nat| x < w ==> #[trigger] (x / pow2(bits as nat)) < sw,
                    bw as nat == pow2(bits as nat),
                    4 <= bw <= 512,
                    sw <= w,
                    data@.len() <= n,
                    n <= 16384 * 16384,
                    row == y * w,
                    w <= row,
                    row + w <= n,
                    1 <= y < h,
                    by as nat == y as nat / pow2(bits as nat),
                    brow == by * sw,
                    brow + sw <= data@.len(),
                    1 <= x0 <= w,
                    x0 < w ==> bx * bw <= x0 < (bx + 1) * bw,
                    x0 < w ==> bx < sw,
                    px@.subrange(0, row + x0) == unpredict(src, wn, bn, dn, (row + x0) as nat),
                    forall|j: int| row + x0 <= j < n ==> #[trigger] px@[j] == src[j],
                decreases w - x0,
            {
                proof {
                    assert((bx + 1) * bw <= 16384 * 512) by (nonlinear_arith)
                        requires
                            bx < sw,
                            sw <= 16384,
                            bw <= 512,
                    ;
                }
                let bend = (bx + 1) * bw;
                let x1 = if bend < w {
                    bend
                } else {
                    w
                };
                let d = data[brow + bx];
                let m = (d >> 8) & 0xf;
                proof {
                    assert((d >> 8u32) & 0xfu32 == ((d >> 8u32) & 0xffu32) % 16) by (bit_vector);
                }
                let ghost pre = px@;
                if FAST {
                    // SAFETY: FAST only when the CPU has AVX2.
                    unsafe { run_mode(px, row + x0, row + x1, row, w, m) };
                } else {
                    run_mode_swar(px, row + x0, row + x1, row, w, m);
                }
                proof {
                    assert forall|j: int| row + x0 <= j < row + x1 implies #[trigger] pstep(px@, src, w as int, m as nat, j) by {
                        assert(pstep(px@, pre, w as int, m as nat, j));
                        assert(pre[j] == src[j]);
                    }
                    assert forall|j: nat| row + x0 <= j < row + x1 implies #[trigger] (j % wn) >= 1 && j / wn >= 1
                        && mode_at(j, wn, bn, dn) == m as nat by {
                        let x = j - row;
                        assert(x0 <= x < x1);
                        assert(x1 <= bend);
                        assert(bx * bw <= x < bx * bw + bw) by (nonlinear_arith)
                            requires
                                bx * bw <= x0 <= x,
                                x < bend,
                                bend == (bx + 1) * bw,
                        ;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j as int, w as int, y as int, x);
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, bw as int, bx as int, x - bx * bw);
                    }
                    assert(px@.subrange(0, row + x0) =~= pre.subrange(0, row + x0));
                    lemma_unpredict_run(src, px@, wn, bn, dn, (row + x0) as nat, (row + x1) as nat, m as nat);
                    if x1 < w {
                        assert(x1 == (bx + 1) * bw);
                        assert(bx + 1 < sw) by {
                            assert(x1 as nat / pow2(bits as nat) < sw);
                            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x1 as int, bw as int, (bx + 1) as int, 0);
                        }
                        assert((bx + 1) * bw <= x1 < (bx + 2) * bw) by (nonlinear_arith)
                            requires
                                x1 == (bx + 1) * bw,
                                bw >= 1,
                        ;
                    }
                }
                x0 = x1;
                bx = bx + 1;
            }
        }
        y = y + 1;
        proof {
            assert(row + w == y * w) by (nonlinear_arith)
                requires
                    row == (y - 1) * w,
            ;
        }
    }
    proof {
        assert(h * w == n) by (nonlinear_arith)
            requires
                n == w * h,
        ;
        assert(px@.subrange(0, n as int) =~= px@);
    }
}

/// Undoes the predictor transform, a run of one mode at a time, with AVX2.
#[inline(always)]
pub fn unpredict_avx2_body(px: &mut Vec<u32>, w: usize, h: usize, bits: u32, data: &Vec<u32>)
    requires
        avx2(),
        1 <= w <= 16384,
        1 <= h <= 16384,
        old(px)@.len() == w * h,
        2 <= bits <= 9,
        data@.len() == subsample(w as nat, bits as nat) * subsample(h as nat, bits as nat),
    ensures
        final(px)@ == unpredict(old(px)@, w as nat, bits as nat, data@, old(px)@.len()),
{
    unpredict_runs::<true>(px, w, h, bits, data)
}

/// Trusted: `unpredict_avx2_body` compiled with `avx2` enabled, through
/// `tf::unpredict_avx2`; the contract is `unpredict_avx2_body`'s, which is verified.
#[verifier::external_body]
pub fn unpredict_avx2(px: &mut Vec<u32>, w: usize, h: usize, bits: u32, data: &Vec<u32>)
    requires
        avx2(),
        1 <= w <= 16384,
        1 <= h <= 16384,
        old(px)@.len() == w * h,
        2 <= bits <= 9,
        data@.len() == subsample(w as nat, bits as nat) * subsample(h as nat, bits as nat),
    ensures
        final(px)@ == unpredict(old(px)@, w as nat, bits as nat, data@, old(px)@.len()),
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::unpredict_avx2(px, w, h, bits, data) };
    #[cfg(not(target_arch = "x86_64"))]
    return unpredict_avx2_body(px, w, h, bits, data);
}

/// Undoes the predictor transform, a run of one mode at a time, with no
/// vector unit: SWAR on the packed pixels (AArch64 and pre-AVX2 x86).
pub fn unpredict_swar(px: &mut Vec<u32>, w: usize, h: usize, bits: u32, data: &Vec<u32>)
    requires
        1 <= w <= 16384,
        1 <= h <= 16384,
        old(px)@.len() == w * h,
        2 <= bits <= 9,
        data@.len() == subsample(w as nat, bits as nat) * subsample(h as nat, bits as nat),
    ensures
        final(px)@ == unpredict(old(px)@, w as nat, bits as nat, data@, old(px)@.len()),
{
    unpredict_runs::<false>(px, w, h, bits, data)
}

/// `s` shifted up one pixel (four bytes), shifting in zeros.
#[inline(always)]
fn shl_px1_neon(s: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == bslli_lanes(n8(s), 4),
{
    let r = vextq_u8::<12>(vdupq_n_u8(0), s);
    assert(n8(r) =~= bslli_lanes(n8(s), 4));
    r
}

/// `s` shifted up two pixels (eight bytes), shifting in zeros.
#[inline(always)]
fn shl_px2_neon(s: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == bslli_lanes(n8(s), 8),
{
    let r = vextq_u8::<8>(vdupq_n_u8(0), s);
    assert(n8(r) =~= bslli_lanes(n8(s), 8));
    r
}

/// `run_left` with NEON: four pixels at a time, the in-vector prefix sum.
#[verifier::rlimit(30)]
fn run_left_neon(px: &mut Vec<u32>, i0: usize, i1: usize)
    requires
        neon(),
        1 <= i0 <= i1 <= old(px)@.len(),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] final(px)@[j] == add_px(old(px)@[j], final(px)@[j - 1]),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    hide(add_px);
    hide(add8);
    hide(bslli_lanes);
    let ghost src = px@;
    let l0 = get32(px.as_slice(), i0 - 1);
    let mut prev = vdupq_n_u32(l0);
    let mut j = i0;
    while i1 - j >= 4
        invariant
            neon(),
            1 <= i0 <= j <= i1 <= src.len(),
            px@.len() == src.len(),
            u32s(n8(prev)) == splat32(px@[j - 1], 4),
            forall|q: int| i0 <= q < j ==> #[trigger] px@[q] == add_px(src[q], px@[q - 1]),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = vld1q_u32_at(px.as_slice(), j);
        let a = vaddq_u8(s, shl_px1_neon(s));
        let b = vaddq_u8(a, shl_px2_neon(a));
        let r = vaddq_u8(b, prev);
        let ghost before = px@;
        proof {
            lemma_left4(n8(s), n8(a), n8(b), n8(prev), n8(r), before[j - 1]);
        }
        vst1q_u32_at(px.as_mut_slice(), j, r);
        prev = vdupq_laneq_u32_3(r);
        proof {
            let ur = u32s(n8(r));
            let us = u32s(n8(s));
            assert(px@[j as int] == ur[0] && px@[j + 1] == ur[1] && px@[j + 2] == ur[2] && px@[j + 3] == ur[3]);
            assert(us[0] == src[j as int] && us[1] == src[j + 1] && us[2] == src[j + 2] && us[3] == src[j + 3]);
            assert(px@[j - 1] == before[j - 1]);
            assert(u32s(n8(prev)) =~= splat32(px@[j + 3], 4));
            assert(px@[j + 0] == add_px(src[j + 0], px@[j + 0 - 1]));
            assert(px@[j + 1] == add_px(src[j + 1], px@[j + 1 - 1]));
            assert(px@[j + 2] == add_px(src[j + 2], px@[j + 2 - 1]));
            assert(px@[j + 3] == add_px(src[j + 3], px@[j + 3 - 1]));
            assert forall|q: int| i0 <= q < j + 4 implies #[trigger] px@[q] == add_px(src[q], px@[q - 1]) by {
                if q < j {
                    assert(px@[q] == before[q] && px@[q - 1] == before[q - 1]);
                }
            }
        }
        j = j + 4;
    }
    let ghost mid = px@;
    run_left_swar(px, j, i1);
    proof {
        assert forall|q: int| i0 <= q < i1 implies #[trigger] px@[q] == add_px(src[q], px@[q - 1]) by {
            if q < j {
                assert(px@[q] == mid[q] && px@[q - 1] == mid[q - 1]);
            } else {
                assert(mid[q] == src[q]);
            }
        }
    }
}

/// Mode `m`'s prediction for the four pixels at `j..j + 4` (all of which
/// read only the row above), with NEON.
fn vert_pred4_neon(px: &[u32], j: usize, w: usize, m: u32) -> (r: uint8x16_t)
    requires
        neon(),
        vertical(m as nat),
        m < 16,
        2 <= w,
        w + 1 <= j,
        j + 4 <= px@.len(),
    ensures
        forall|k: int|
            0 <= k < 4 ==> #[trigger] u32s(n8(r))[k] == predict_mode(
                m as nat,
                px@[j + k - 1],
                px@[j + k - w],
                px@[j + k - w + 1],
                px@[j + k - w - 1],
            ),
{
    if m == 2 {
        vld1q_u32_at(px, j - w)
    } else if m == 3 {
        vld1q_u32_at(px, j - w + 1)
    } else if m == 4 {
        vld1q_u32_at(px, j - w - 1)
    } else if m == 8 || m == 9 {
        let a = if m == 8 {
            vld1q_u32_at(px, j - w - 1)
        } else {
            vld1q_u32_at(px, j - w + 1)
        };
        let t = vld1q_u32_at(px, j - w);
        let r = vaddq_u8(vandq_u8(a, t), vshrq_n_u8::<1>(veorq_u8(a, t)));
        proof {
            lemma_avgh_px(n8(a), n8(t), n8(r));
            assert forall|k: int| 0 <= k < 4 implies #[trigger] u32s(n8(r))[k] == predict_mode(
                m as nat,
                px@[j + k - 1],
                px@[j + k - w],
                px@[j + k - w + 1],
                px@[j + k - w - 1],
            ) by {
                assert(u32s(n8(t))[k] == px@[j + k - w]);
                if m == 8 {
                    assert(u32s(n8(a))[k] == px@[j + k - w - 1]);
                } else {
                    assert(u32s(n8(a))[k] == px@[j + k - w + 1]);
                    lemma_avg2_comm(u32s(n8(a))[k], u32s(n8(t))[k]);
                }
            }
        }
        r
    } else {
        vdupq_n_u32(0xff00_0000)
    }
}

/// A run in one of the vertical modes, four pixels at a time with NEON.
fn run_vertical_neon(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize, m: u32)
    requires
        neon(),
        vertical(m as nat),
        m < 16,
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, m as nat, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    hide(add_px);
    let ghost src = px@;
    let mut j = i0;
    while i1 - j >= 4
        invariant
            neon(),
            vertical(m as nat),
            m < 16,
            run_geom(src.len(), w as int, row as int, i0 as int, i1 as int),
            i0 <= j <= i1,
            px@.len() == src.len(),
            forall|q: int| i0 <= q < j ==> #[trigger] pstep(px@, src, w as int, m as nat, q),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let p = vert_pred4_neon(px.as_slice(), j, w, m);
        let s = vld1q_u32_at(px.as_slice(), j);
        let o = vaddq_u8(s, p);
        let ghost before = px@;
        proof {
            lemma_add8_px(n8(s), n8(p));
        }
        vst1q_u32_at(px.as_mut_slice(), j, o);
        proof {
            lemma_pstep_frame(before, px@, src, w as int, m as nat, i0 as int, j as int);
            assert forall|q: int| j <= q < j + 4 implies #[trigger] pstep(px@, src, w as int, m as nat, q) by {
                let k = q - j;
                assert(px@[q] == u32s(n8(o))[k]);
                assert(u32s(n8(o))[k] == add_px(u32s(n8(s))[k], u32s(n8(p))[k]));
                assert(u32s(n8(p))[k] == predict_mode(m as nat, before[j + k - 1], before[j + k - w], before[j + k - w + 1], before[j + k - w - 1]));
                assert(u32s(n8(s))[k] == src[q]);
                assert(px@[q - w] == before[q - w]);
                assert(px@[q - w + 1] == before[q - w + 1]);
                assert(px@[q - w - 1] == before[q - w - 1]);
                lemma_vertical_ignores_l(m as nat, px@[q - 1], before[j + k - 1], px@[q - w], px@[q - w + 1], px@[q - w - 1]);
            }
        }
        j = j + 4;
    }
    let ghost mid = px@;
    run_vertical_swar(px, j, i1, row, w, m);
    proof {
        lemma_pstep_frame(mid, px@, src, w as int, m as nat, i0 as int, j as int);
        assert forall|q: int| j <= q < i1 implies #[trigger] pstep(px@, src, w as int, m as nat, q) by {
            assert(pstep(px@, mid, w as int, m as nat, q));
            assert(mid[q] == src[q]);
        }
    }
}

/// `run_left` without SSE: one pixel at a time, the left pixel in a
/// register.
fn run_left_swar(px: &mut Vec<u32>, i0: usize, i1: usize)
    requires
        1 <= i0 <= i1 <= old(px)@.len(),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] final(px)@[j] == add_px(old(px)@[j], final(px)@[j - 1]),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    let ghost src = px@;
    let mut l = get32(px.as_slice(), i0 - 1);
    let mut j = i0;
    while j < i1
        invariant
            1 <= i0 <= j <= i1 <= src.len(),
            px@.len() == src.len(),
            l == px@[j - 1],
            forall|q: int| i0 <= q < j ==> #[trigger] px@[q] == add_px(src[q], px@[q - 1]),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let c = add_px_swar(get32(px.as_slice(), j), l);
        let ghost before = px@;
        set32(px.as_mut_slice(), j, c);
        proof {
            assert forall|q: int| i0 <= q < j + 1 implies #[trigger] px@[q] == add_px(src[q], px@[q - 1]) by {
                if q < j {
                    assert(px@[q] == before[q] && px@[q - 1] == before[q - 1]);
                }
            }
        }
        l = c;
        j = j + 1;
    }
}

/// `run_mode` without SSE or AVX2.
fn run_mode_swar(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize, m: u32)
    requires
        m < 16,
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, m as nat, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    if m == 1 {
        let ghost src = px@;
        if has_neon() {
            run_left_neon(px, i0, i1);
        } else {
            run_left_swar(px, i0, i1);
        }
        assert forall|j: int| i0 <= j < i1 implies #[trigger] pstep(px@, src, w as int, m as nat, j) by {
        }
    } else if m == 5 {
        run_m5(px, i0, i1, row, w);
    } else if m == 6 {
        run_m6(px, i0, i1, row, w);
    } else if m == 7 {
        run_m7(px, i0, i1, row, w);
    } else if m == 10 {
        run_m10(px, i0, i1, row, w);
    } else if m == 11 {
        run_m11_swar(px, i0, i1, row, w);
    } else if m == 12 {
        run_m12(px, i0, i1, row, w);
    } else if m == 13 {
        run_m13(px, i0, i1, row, w);
    } else if has_neon() {
        run_vertical_neon(px, i0, i1, row, w, m);
    } else {
        run_vertical_swar(px, i0, i1, row, w, m);
    }
}

/// A run of a mode that ignores the left pixel (`vertical`), without SIMD:
/// the prediction from the row above, added a pixel at a time.
fn run_vertical_swar(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize, m: u32)
    requires
        m < 16,
        vertical(m as nat),
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, m as nat, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    hide(add_px);
    let ghost src = px@;
    let mut j = i0;
    while j < i1
        invariant
            m < 16,
            vertical(m as nat),
            run_geom(src.len(), w as int, row as int, i0 as int, i1 as int),
            i0 <= j <= i1,
            px@.len() == src.len(),
            forall|q: int| i0 <= q < j ==> #[trigger] pstep(px@, src, w as int, m as nat, q),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = px.as_slice();
        let t = get32(s, j - w);
        let tr = get32(s, j - w + 1);
        let tl = get32(s, j - w - 1);
        let p = if m == 2 {
            t
        } else if m == 3 {
            tr
        } else if m == 4 {
            tl
        } else if m == 8 {
            avg2_swar(tl, t)
        } else if m == 9 {
            avg2_swar(t, tr)
        } else {
            0xff00_0000u32
        };
        let c = add_px_swar(get32(s, j), p);
        let ghost before = px@;
        set32(px.as_mut_slice(), j, c);
        proof {
            lemma_pstep_frame(before, px@, src, w as int, m as nat, i0 as int, j as int);
            assert(before[j as int] == src[j as int]);
            assert(p == predict_mode(m as nat, before[j - 1], before[j - w], before[j - w + 1], before[j - w - 1]));
            assert(pstep(px@, src, w as int, m as nat, j as int));
        }
        j = j + 1;
    }
}

/// `run_m11` without SIMD: the select predictor's distances channel by
/// channel.
fn run_m11_swar(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize)
    requires
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, 11, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    hide(add_px);
    let ghost src = px@;
    if i0 == i1 {
        return;
    }
    let mut l = get32(px.as_slice(), i0 - 1);
    let mut j = i0;
    while j < i1
        invariant
            run_geom(src.len(), w as int, row as int, i0 as int, i1 as int),
            i0 <= j <= i1,
            px@.len() == src.len(),
            l == px@[j - 1],
            forall|q: int| i0 <= q < j ==> #[trigger] pstep(px@, src, w as int, 11, q),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = px.as_slice();
        let t = get32(s, j - w);
        let tl = get32(s, j - w - 1);
        let c = select_add_exec(get32(s, j), l, t, tl);
        let ghost before = px@;
        set32(px.as_mut_slice(), j, c);
        proof {
            lemma_pstep_frame(before, px@, src, w as int, 11, i0 as int, j as int);
            assert(before[j as int] == src[j as int]);
            assert(select(l, t, tl) == predict_mode(11, before[j - 1], before[j - w], before[j - w + 1], before[j - w - 1]));
            assert(pstep(px@, src, w as int, 11, j as int));
        }
        l = c;
        j = j + 1;
    }
}

/// A run in mode 5, one pixel at a time with the left pixel in a register.
fn run_m5(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize)
    requires
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, 5, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    hide(add_px);
    let ghost src = px@;
    if i0 == i1 {
        return;
    }
    let mut l = get32(px.as_slice(), i0 - 1);
    let mut j = i0;
    while j < i1
        invariant
            run_geom(src.len(), w as int, row as int, i0 as int, i1 as int),
            i0 <= j <= i1,
            px@.len() == src.len(),
            l == px@[j - 1],
            forall|q: int| i0 <= q < j ==> #[trigger] pstep(px@, src, w as int, 5, q),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = px.as_slice();
        let t = get32(s, j - w);
        let tr = get32(s, j - w + 1);
        let p = avg2_swar(avg2_swar(l, tr), t);
        let c = add_px_swar(get32(s, j), p);
        let ghost before = px@;
        set32(px.as_mut_slice(), j, c);
        proof {
            lemma_pstep_frame(before, px@, src, w as int, 5, i0 as int, j as int);
            assert(before[j as int] == src[j as int]);
            assert(p == predict_mode(5, before[j - 1], before[j - w], before[j - w + 1], before[j - w - 1]));
            assert(pstep(px@, src, w as int, 5, j as int));
        }
        l = c;
        j = j + 1;
    }
}

/// A run in mode 6, one pixel at a time with the left pixel in a register.
fn run_m6(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize)
    requires
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, 6, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    hide(add_px);
    let ghost src = px@;
    if i0 == i1 {
        return;
    }
    let mut l = get32(px.as_slice(), i0 - 1);
    let mut j = i0;
    while j < i1
        invariant
            run_geom(src.len(), w as int, row as int, i0 as int, i1 as int),
            i0 <= j <= i1,
            px@.len() == src.len(),
            l == px@[j - 1],
            forall|q: int| i0 <= q < j ==> #[trigger] pstep(px@, src, w as int, 6, q),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = px.as_slice();
        let tl = get32(s, j - w - 1);
        let p = avg2_swar(l, tl);
        let c = add_px_swar(get32(s, j), p);
        let ghost before = px@;
        set32(px.as_mut_slice(), j, c);
        proof {
            lemma_pstep_frame(before, px@, src, w as int, 6, i0 as int, j as int);
            assert(before[j as int] == src[j as int]);
            assert(p == predict_mode(6, before[j - 1], before[j - w], before[j - w + 1], before[j - w - 1]));
            assert(pstep(px@, src, w as int, 6, j as int));
        }
        l = c;
        j = j + 1;
    }
}

/// A run in mode 7, one pixel at a time with the left pixel in a register.
fn run_m7(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize)
    requires
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, 7, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    hide(add_px);
    let ghost src = px@;
    if i0 == i1 {
        return;
    }
    let mut l = get32(px.as_slice(), i0 - 1);
    let mut j = i0;
    while j < i1
        invariant
            run_geom(src.len(), w as int, row as int, i0 as int, i1 as int),
            i0 <= j <= i1,
            px@.len() == src.len(),
            l == px@[j - 1],
            forall|q: int| i0 <= q < j ==> #[trigger] pstep(px@, src, w as int, 7, q),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = px.as_slice();
        let t = get32(s, j - w);
        let p = avg2_swar(l, t);
        let c = add_px_swar(get32(s, j), p);
        let ghost before = px@;
        set32(px.as_mut_slice(), j, c);
        proof {
            lemma_pstep_frame(before, px@, src, w as int, 7, i0 as int, j as int);
            assert(before[j as int] == src[j as int]);
            assert(p == predict_mode(7, before[j - 1], before[j - w], before[j - w + 1], before[j - w - 1]));
            assert(pstep(px@, src, w as int, 7, j as int));
        }
        l = c;
        j = j + 1;
    }
}

/// A run in mode 10, one pixel at a time with the left pixel in a register.
fn run_m10(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize)
    requires
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, 10, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    hide(add_px);
    let ghost src = px@;
    if i0 == i1 {
        return;
    }
    let mut l = get32(px.as_slice(), i0 - 1);
    let mut j = i0;
    while j < i1
        invariant
            run_geom(src.len(), w as int, row as int, i0 as int, i1 as int),
            i0 <= j <= i1,
            px@.len() == src.len(),
            l == px@[j - 1],
            forall|q: int| i0 <= q < j ==> #[trigger] pstep(px@, src, w as int, 10, q),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = px.as_slice();
        let t = get32(s, j - w);
        let tr = get32(s, j - w + 1);
        let tl = get32(s, j - w - 1);
        let p = avg2_swar(avg2_swar(l, tl), avg2_swar(t, tr));
        let c = add_px_swar(get32(s, j), p);
        let ghost before = px@;
        set32(px.as_mut_slice(), j, c);
        proof {
            lemma_pstep_frame(before, px@, src, w as int, 10, i0 as int, j as int);
            assert(before[j as int] == src[j as int]);
            assert(p == predict_mode(10, before[j - 1], before[j - w], before[j - w + 1], before[j - w - 1]));
            assert(pstep(px@, src, w as int, 10, j as int));
        }
        l = c;
        j = j + 1;
    }
}

/// A run in mode 11, one pixel at a time with the left pixel in a register.
#[inline(always)]
fn run_m11(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize)
    requires
        avx2(),
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, 11, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    hide(add_px);
    let ghost src = px@;
    if i0 == i1 {
        return;
    }
    let mut l = get32(px.as_slice(), i0 - 1);
    let mut j = i0;
    while j < i1
        invariant
            avx2(),
            run_geom(src.len(), w as int, row as int, i0 as int, i1 as int),
            i0 <= j <= i1,
            px@.len() == src.len(),
            l == px@[j - 1],
            forall|q: int| i0 <= q < j ==> #[trigger] pstep(px@, src, w as int, 11, q),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = px.as_slice();
        let t = get32(s, j - w);
        let tl = get32(s, j - w - 1);
        let p = select_sad(l, t, tl);
        let c = add_px_swar(get32(s, j), p);
        let ghost before = px@;
        set32(px.as_mut_slice(), j, c);
        proof {
            lemma_pstep_frame(before, px@, src, w as int, 11, i0 as int, j as int);
            assert(before[j as int] == src[j as int]);
            assert(p == predict_mode(11, before[j - 1], before[j - w], before[j - w + 1], before[j - w - 1]));
            assert(pstep(px@, src, w as int, 11, j as int));
        }
        l = c;
        j = j + 1;
    }
}

/// A run in mode 12, one pixel at a time with the left pixel in a register.
fn run_m12(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize)
    requires
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, 12, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    hide(add_px);
    let ghost src = px@;
    if i0 == i1 {
        return;
    }
    let mut l = get32(px.as_slice(), i0 - 1);
    let mut j = i0;
    while j < i1
        invariant
            run_geom(src.len(), w as int, row as int, i0 as int, i1 as int),
            i0 <= j <= i1,
            px@.len() == src.len(),
            l == px@[j - 1],
            forall|q: int| i0 <= q < j ==> #[trigger] pstep(px@, src, w as int, 12, q),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = px.as_slice();
        let t = get32(s, j - w);
        let tl = get32(s, j - w - 1);
        let p = clamp_add_sub_full_exec(l, t, tl);
        let c = add_px_swar(get32(s, j), p);
        let ghost before = px@;
        set32(px.as_mut_slice(), j, c);
        proof {
            lemma_pstep_frame(before, px@, src, w as int, 12, i0 as int, j as int);
            assert(before[j as int] == src[j as int]);
            assert(p == predict_mode(12, before[j - 1], before[j - w], before[j - w + 1], before[j - w - 1]));
            assert(pstep(px@, src, w as int, 12, j as int));
        }
        l = c;
        j = j + 1;
    }
}

/// A run in mode 13, one pixel at a time with the left pixel in a register.
fn run_m13(px: &mut Vec<u32>, i0: usize, i1: usize, row: usize, w: usize)
    requires
        run_geom(old(px)@.len(), w as int, row as int, i0 as int, i1 as int),
    ensures
        final(px)@.len() == old(px)@.len(),
        forall|j: int| i0 <= j < i1 ==> #[trigger] pstep(final(px)@, old(px)@, w as int, 13, j),
        forall|j: int| 0 <= j < i0 || i1 <= j < old(px)@.len() ==> #[trigger] final(px)@[j] == old(px)@[j],
{
    hide(add_px);
    let ghost src = px@;
    if i0 == i1 {
        return;
    }
    let mut l = get32(px.as_slice(), i0 - 1);
    let mut j = i0;
    while j < i1
        invariant
            run_geom(src.len(), w as int, row as int, i0 as int, i1 as int),
            i0 <= j <= i1,
            px@.len() == src.len(),
            l == px@[j - 1],
            forall|q: int| i0 <= q < j ==> #[trigger] pstep(px@, src, w as int, 13, q),
            forall|q: int| 0 <= q < i0 || j <= q < src.len() ==> #[trigger] px@[q] == src[q],
        decreases i1 - j,
    {
        let s = px.as_slice();
        let t = get32(s, j - w);
        let tl = get32(s, j - w - 1);
        let p = clamp_add_sub_half_exec(avg2_swar(l, t), tl);
        let c = add_px_swar(get32(s, j), p);
        let ghost before = px@;
        set32(px.as_mut_slice(), j, c);
        proof {
            lemma_pstep_frame(before, px@, src, w as int, 13, i0 as int, j as int);
            assert(before[j as int] == src[j as int]);
            assert(p == predict_mode(13, before[j - 1], before[j - w], before[j - w + 1], before[j - w - 1]));
            assert(pstep(px@, src, w as int, 13, j as int));
        }
        l = c;
        j = j + 1;
    }
}

} // verus!

/// Trampolines that compile a verified `*_body` function with the target
/// features its kernel needs. Each is one call; `#[target_feature]` only
/// changes code generation. Verus rejects the attribute on verified code
/// (verus-lang/verus#3362), so it lives outside `verus!`.
#[cfg(target_arch = "x86_64")]
mod tf {
    #[allow(unused_imports)]
    use super::*;

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn unpredict_avx2(px: &mut Vec<u32>, w: usize, h: usize, bits: u32, data: &Vec<u32>) {
        unpredict_avx2_body(px, w, h, bits, data)
    }
}

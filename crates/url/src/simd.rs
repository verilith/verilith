//! 16-byte scans with SIMD: whether a block of input holds no byte that a
//! percent-encode scan has to stop at. SSE2 on x86-64, NEON on AArch64,
//! verified against vsimd's models of the instructions.
#![allow(unused_imports)]
use crate::encode::*;
use crate::spec::*;
use verilith_simd::lanes::*;
use verilith_simd::neon::*;
use verilith_simd::ops::*;
use vstd::prelude::*;

#[cfg(target_arch = "x86_64")]
use verilith_simd::arch::*;
#[cfg(target_arch = "x86_64")]
use verilith_simd::mem::load128_u8;

verus! {

/// A movemask of zero means no lane has its top bit set.
pub proof fn lemma_movemask_zero(a: Seq<u8>)
    requires
        movemask(a) == 0,
    ensures
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] < 128,
    decreases a.len(),
{
    if a.len() > 0 {
        let t = a.drop_first();
        assert(movemask(t) == 0);
        lemma_movemask_zero(t);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] < 128 by {
            if i > 0 {
                assert(a[i] == t[i - 1]);
            }
        }
    }
}

/// Seven lane masks, each 0 or 0xFF, OR to a byte below 0x80 only when all
/// are 0.
proof fn lemma_or7(a: u8, b: u8, c: u8, d: u8, e: u8, f: u8, g: u8)
    requires
        a == 0 || a == 0xFF,
        b == 0 || b == 0xFF,
        c == 0 || c == 0xFF,
        d == 0 || d == 0xFF,
        e == 0 || e == 0xFF,
        f == 0 || f == 0xFF,
        g == 0 || g == 0xFF,
        (((a | b) | (c | d)) | ((e | f) | g)) < 128,
    ensures
        a == 0 && b == 0 && c == 0 && d == 0 && e == 0 && f == 0 && g == 0,
{
    assert(((a == 0 || a == 0xFFu8) && (b == 0 || b == 0xFFu8) && (c == 0 || c == 0xFFu8) && (d == 0
        || d == 0xFFu8) && (e == 0 || e == 0xFFu8) && (f == 0 || f == 0xFFu8) && (g == 0 || g
        == 0xFFu8) && (((a | b) | (c | d)) | ((e | f) | g)) < 128u8) ==> (a == 0 && b == 0 && c == 0
        && d == 0 && e == 0 && f == 0 && g == 0)) by (bit_vector);
}

/// The two set-specific bytes besides `"`, `<` and `>`.
pub open spec fn extra(kind: u8) -> (u8, u8) {
    if kind == K_FRAG {
        (0x60, 0x60)
    } else {
        (0x23, 0x27)
    }
}

/// `maybe` for the query and fragment sets, as the lane tests compute it.
proof fn lemma_maybe_lanes(kind: u8, c: u8)
    requires
        kind == K_FRAG || kind == K_QUERY,
    ensures
        maybe(kind, c) == (c <= 0x20 || c >= 0x7F || c == 0x22 || c == 0x3C || c == 0x3E || c
            == extra(kind).0 || c == extra(kind).1),
{
}

/// No byte of `s[j..j + 16]` is `maybe(kind, _)` if this returns true.
#[cfg(target_arch = "x86_64")]
pub fn clean16_sse(s: &[u8], j: usize, kind: u8) -> (r: bool)
    requires
        j + 16 <= s@.len(),
        kind == K_FRAG || kind == K_QUERY,
    ensures
        r ==> forall|k: int| j <= k < j + 16 ==> !maybe(kind, #[trigger] s@[k]),
{
    let (x, y): (u8, u8) = if kind == K_FRAG { (0x60, 0x60) } else { (0x23, 0x27) };
    let v = load128_u8(s, j);
    // Signed v < 0x21: v <= 0x20 or v >= 0x80.
    let lo = _mm_cmpgt_epi8(_mm_set1_epi8(0x21), v);
    let del = _mm_cmpeq_epi8(v, _mm_set1_epi8(0x7F));
    let q = _mm_cmpeq_epi8(v, _mm_set1_epi8(0x22));
    let lt = _mm_cmpeq_epi8(v, _mm_set1_epi8(0x3C));
    let gt = _mm_cmpeq_epi8(v, _mm_set1_epi8(0x3E));
    let ex = _mm_cmpeq_epi8(v, _mm_set1_epi8(x as i8));
    let ey = _mm_cmpeq_epi8(v, _mm_set1_epi8(y as i8));
    let all = _mm_or_si128(
        _mm_or_si128(_mm_or_si128(lo, del), _mm_or_si128(q, lt)),
        _mm_or_si128(_mm_or_si128(gt, ex), ey),
    );
    let m = _mm_movemask_epi8(all);
    if m != 0 {
        return false;
    }
    proof {
        assert(movemask(b128(all)) == 0);
        lemma_movemask_zero(b128(all));
        assert forall|k: int| j <= k < j + 16 implies !maybe(kind, #[trigger] s@[k]) by {
            let i = k - j;
            let c = s@[k];
            assert(b128(v)[i] == c);
            assert(b128(all)[i] < 128);
            let (l1, l2, l3, l4, l5, l6, l7) = (b128(lo)[i], b128(del)[i], b128(q)[i], b128(lt)[i],
                b128(gt)[i], b128(ex)[i], b128(ey)[i]);
            assert(b128(all)[i] == (((l1 | l2) | (l3 | l4)) | ((l5 | l6) | l7)));
            lemma_or7(l1, l2, l3, l4, l5, l6, l7);
            assert(u8_of_i8(x as i8) == x);
            assert(u8_of_i8(y as i8) == y);
            assert(!(s8(0x21) > s8(c)));
            lemma_maybe_lanes(kind, c);
        }
    }
    true
}

/// `clean16_sse` with NEON.
#[inline(always)]
pub fn clean16_neon(s: &[u8], j: usize, kind: u8) -> (r: bool)
    requires
        neon(),
        j + 16 <= s@.len(),
        kind == K_FRAG || kind == K_QUERY,
    ensures
        r ==> forall|k: int| j <= k < j + 16 ==> !maybe(kind, #[trigger] s@[k]),
{
    let all = maybe_vec_neon(s, j, kind);
    let mx = vmaxvq_u8(all);
    if mx != 0 {
        return false;
    }
    proof {
        assert forall|k: int| j <= k < j + 16 implies !maybe(kind, #[trigger] s@[k]) by {
            let i = k - j;
            assert(n8(all)[i] <= mx);
            assert(maybe(kind, s@[j + i]) == maybe(kind, s@[k]));
        }
    }
    true
}

/// 0xFF at each byte of `s[j..j + 16]` that is `maybe(kind, _)`, 0
/// elsewhere.
#[inline(always)]
pub fn maybe_vec_neon(s: &[u8], j: usize, kind: u8) -> (r: uint8x16_t)
    requires
        neon(),
        j + 16 <= s@.len(),
        kind == K_FRAG || kind == K_QUERY,
    ensures
        verilith_simd::neon_mask::is_mask(n8(r)),
        forall|i: int| 0 <= i < 16 ==> ((n8(r)[i] == 0xFF) == maybe(kind, #[trigger] s@[j + i])),
{
    let (x, y): (u8, u8) = if kind == K_FRAG { (0x60, 0x60) } else { (0x23, 0x27) };
    let v = vld1q_u8_at(s, j);
    let z = vdupq_n_u8(0);
    // Saturating v - 0x20 is 0 for v <= 0x20; 0x7F - v is 0 for v >= 0x7F.
    let lo = vceqq_u8(vqsubq_u8(v, vdupq_n_u8(0x20)), z);
    let hi = vceqq_u8(vqsubq_u8(vdupq_n_u8(0x7F), v), z);
    let q = vceqq_u8(v, vdupq_n_u8(0x22));
    let lt = vceqq_u8(v, vdupq_n_u8(0x3C));
    let gt = vceqq_u8(v, vdupq_n_u8(0x3E));
    let ex = vceqq_u8(v, vdupq_n_u8(x));
    let ey = vceqq_u8(v, vdupq_n_u8(y));
    let all = vorrq_u8(vorrq_u8(vorrq_u8(lo, hi), vorrq_u8(q, lt)), vorrq_u8(vorrq_u8(gt, ex), ey));
    proof {
        assert forall|i: int| 0 <= i < 16 implies (n8(all)[i] == 0 || n8(all)[i] == 0xFF) && ((n8(all)[i] == 0xFF)
            == maybe(kind, #[trigger] s@[j + i])) by {
            let c = s@[j + i];
            assert(n8(v)[i] == c);
            let (l1, l2, l3, l4, l5, l6, l7) = (n8(lo)[i], n8(hi)[i], n8(q)[i], n8(lt)[i],
                n8(gt)[i], n8(ex)[i], n8(ey)[i]);
            assert(n8(all)[i] == (((l1 | l2) | (l3 | l4)) | ((l5 | l6) | l7)));
            lemma_or7_mask(l1, l2, l3, l4, l5, l6, l7);
            lemma_maybe_lanes(kind, c);
        }
        verilith_simd::neon::axiom_n8_len(all);
        assert forall|i: int| 0 <= i < n8(all).len() implies #[trigger] n8(all)[i] == 0 || n8(all)[i] == 0xFF by {
            let (l1, l2, l3, l4, l5, l6, l7) = (n8(lo)[i], n8(hi)[i], n8(q)[i], n8(lt)[i],
                n8(gt)[i], n8(ex)[i], n8(ey)[i]);
            assert(n8(all)[i] == (((l1 | l2) | (l3 | l4)) | ((l5 | l6) | l7)));
            lemma_or7_mask(l1, l2, l3, l4, l5, l6, l7);
        }
        assert(verilith_simd::neon_mask::is_mask(n8(all)));
    }
    all
}

/// Seven lane masks, each 0 or 0xFF, OR to a mask that is 0xFF exactly when
/// one of them is.
proof fn lemma_or7_mask(a: u8, b: u8, c: u8, d: u8, e: u8, f: u8, g: u8)
    requires
        a == 0 || a == 0xFF,
        b == 0 || b == 0xFF,
        c == 0 || c == 0xFF,
        d == 0 || d == 0xFF,
        e == 0 || e == 0xFF,
        f == 0 || f == 0xFF,
        g == 0 || g == 0xFF,
    ensures
        ({
            let o = ((a | b) | (c | d)) | ((e | f) | g);
            (o == 0 || o == 0xFF) && ((o == 0xFF) == (a == 0xFF || b == 0xFF || c == 0xFF || d == 0xFF || e
                == 0xFF || f == 0xFF || g == 0xFF))
        }),
{
    assert(((a == 0 || a == 0xFFu8) && (b == 0 || b == 0xFFu8) && (c == 0 || c == 0xFFu8) && (d == 0
        || d == 0xFFu8) && (e == 0 || e == 0xFFu8) && (f == 0 || f == 0xFFu8) && (g == 0 || g
        == 0xFFu8)) ==> ({
        let o = ((a | b) | (c | d)) | ((e | f) | g);
        (o == 0 || o == 0xFFu8) && ((o == 0xFFu8) == (a == 0xFFu8 || b == 0xFFu8 || c == 0xFFu8 || d == 0xFFu8
            || e == 0xFFu8 || f == 0xFFu8 || g == 0xFFu8))
    })) by (bit_vector);
}

/// `encode::maybe_mask16` with NEON: one compare chain and a movemask in
/// place of sixteen byte tests.
#[inline(always)]
pub fn maybe_mask16_neon(w: &[u8], kind: u8) -> (m: u32)
    requires
        neon(),
        w.len() == 16,
        kind == K_FRAG || kind == K_QUERY,
    ensures
        m < 0x10000,
        forall|j: u32| j < 16 ==> (((m >> j) & 1) == 1) == maybe(kind, #[trigger] w@[j as int]),
{
    let all = maybe_vec_neon(w, 0, kind);
    let m = verilith_simd::neon_mask::movemask16(all);
    proof {
        assert forall|j: u32| j < 16 implies (((m >> j) & 1) == 1) == maybe(kind, #[trigger] w@[j as int]) by {
            assert(w@[0 + j as int] == w@[j as int]);
        }
    }
    m
}

/// No byte of `s[j..j + 16]` is `maybe(kind, _)` if this returns true.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub fn clean16(s: &[u8], j: usize, kind: u8) -> (r: bool)
    requires
        j + 16 <= s@.len(),
        kind == K_FRAG || kind == K_QUERY,
    ensures
        r ==> forall|k: int| j <= k < j + 16 ==> !maybe(kind, #[trigger] s@[k]),
{
    // SAFETY: SSE2 is part of the x86-64 baseline.
    unsafe { clean16_sse(s, j, kind) }
}

/// No byte of `s[j..j + 16]` is `maybe(kind, _)` if this returns true.
#[cfg(not(target_arch = "x86_64"))]
#[inline(always)]
pub fn clean16(s: &[u8], j: usize, kind: u8) -> (r: bool)
    requires
        j + 16 <= s@.len(),
        kind == K_FRAG || kind == K_QUERY,
    ensures
        r ==> forall|k: int| j <= k < j + 16 ==> !maybe(kind, #[trigger] s@[k]),
{
    if has_neon() {
        clean16_neon(s, j, kind)
    } else {
        false
    }
}

/// Three lane masks, each 0 or 0xFF, OR to a byte below 0x80 only when all
/// are 0.
proof fn lemma_or3(a: u8, b: u8, c: u8)
    requires
        a == 0 || a == 0xFF,
        b == 0 || b == 0xFF,
        c == 0 || c == 0xFF,
        ((a | b) | c) < 128,
    ensures
        a == 0 && b == 0 && c == 0,
{
    assert(((a == 0 || a == 0xFFu8) && (b == 0 || b == 0xFFu8) && (c == 0 || c == 0xFFu8) && ((a
        | b) | c) < 128u8) ==> (a == 0 && b == 0 && c == 0)) by (bit_vector);
}

/// `s[j..j + 16]` has no tab or newline if this returns false.
#[cfg(target_arch = "x86_64")]
pub fn tab_nl16_sse(s: &[u8], j: usize) -> (r: bool)
    requires
        j + 16 <= s@.len(),
    ensures
        !r ==> forall|k: int| j <= k < j + 16 ==> !is_ascii_tab_or_newline(#[trigger] s@[k]),
{
    let v = load128_u8(s, j);
    let t = _mm_cmpeq_epi8(v, _mm_set1_epi8(0x09));
    let l = _mm_cmpeq_epi8(v, _mm_set1_epi8(0x0A));
    let c = _mm_cmpeq_epi8(v, _mm_set1_epi8(0x0D));
    let all = _mm_or_si128(_mm_or_si128(t, l), c);
    let m = _mm_movemask_epi8(all);
    if m != 0 {
        return true;
    }
    proof {
        assert(movemask(b128(all)) == 0);
        lemma_movemask_zero(b128(all));
        assert forall|k: int| j <= k < j + 16 implies !is_ascii_tab_or_newline(#[trigger] s@[k]) by {
            let i = k - j;
            assert(b128(v)[i] == s@[k]);
            assert(b128(all)[i] < 128);
            assert(b128(all)[i] == ((b128(t)[i] | b128(l)[i]) | b128(c)[i]));
            lemma_or3(b128(t)[i], b128(l)[i], b128(c)[i]);
        }
    }
    false
}

/// `tab_nl16_sse` with NEON.
#[inline(always)]
pub fn tab_nl16_neon(s: &[u8], j: usize) -> (r: bool)
    requires
        neon(),
        j + 16 <= s@.len(),
    ensures
        !r ==> forall|k: int| j <= k < j + 16 ==> !is_ascii_tab_or_newline(#[trigger] s@[k]),
{
    let v = vld1q_u8_at(s, j);
    let t = vceqq_u8(v, vdupq_n_u8(0x09));
    let l = vceqq_u8(v, vdupq_n_u8(0x0A));
    let c = vceqq_u8(v, vdupq_n_u8(0x0D));
    let all = vorrq_u8(vorrq_u8(t, l), c);
    let mx = vmaxvq_u8(all);
    if mx != 0 {
        return true;
    }
    proof {
        assert forall|k: int| j <= k < j + 16 implies !is_ascii_tab_or_newline(#[trigger] s@[k]) by {
            let i = k - j;
            assert(n8(v)[i] == s@[k]);
            assert(n8(all)[i] <= mx);
            assert(n8(all)[i] == ((n8(t)[i] | n8(l)[i]) | n8(c)[i]));
            lemma_or3(n8(t)[i], n8(l)[i], n8(c)[i]);
        }
    }
    false
}

/// `s[j..j + 16]` has no tab or newline if this returns false.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub fn tab_nl16(s: &[u8], j: usize) -> (r: bool)
    requires
        j + 16 <= s@.len(),
    ensures
        !r ==> forall|k: int| j <= k < j + 16 ==> !is_ascii_tab_or_newline(#[trigger] s@[k]),
{
    // SAFETY: SSE2 is part of the x86-64 baseline.
    unsafe { tab_nl16_sse(s, j) }
}

/// `s[j..j + 16]` has no tab or newline if this returns false.
#[cfg(not(target_arch = "x86_64"))]
#[inline(always)]
pub fn tab_nl16(s: &[u8], j: usize) -> (r: bool)
    requires
        j + 16 <= s@.len(),
    ensures
        !r ==> forall|k: int| j <= k < j + 16 ==> !is_ascii_tab_or_newline(#[trigger] s@[k]),
{
    if has_neon() {
        tab_nl16_neon(s, j)
    } else {
        true
    }
}

} // verus!

/// The SIMD scanners against byte-by-byte answers, at every offset of
/// buffers built from the bytes each one treats specially. On AArch64 this
/// runs the NEON kernels.
#[cfg(test)]
mod tests {
    use super::*;

    fn maybe_ref(kind: u8, c: u8) -> bool {
        c <= 0x20 || c >= 0x7F || c == 0x22 || c == 0x3C || c == 0x3E
            || if kind == K_FRAG { c == 0x60 } else { c == 0x23 || c == 0x27 }
    }

    #[test]
    fn scanners_match_bytewise() {
        let special = [0u8, 9, 10, 13, 0x1F, 0x20, 0x21, 0x22, 0x23, 0x26, 0x27, 0x28, 0x3B, 0x3C, 0x3D, 0x3E,
            0x5F, 0x60, 0x61, 0x7E, 0x7F, 0x80, 0xC3, 0xFF, b'a', b'/', b'%'];
        let mut x: u64 = 0x9E37_79B9_7F4A_7C15;
        for round in 0..20000 {
            let buf: Vec<u8> = (0..48)
                .map(|_| {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    if round % 3 == 0 { b'a' + (x % 26) as u8 } else { special[(x % special.len() as u64) as usize] }
                })
                .collect();
            for j in 0..=32 {
                for kind in [K_FRAG, K_QUERY] {
                    let w = &buf[j..j + 16];
                    let want: u32 = (0..16).filter(|&k| maybe_ref(kind, w[k])).fold(0, |m, k| m | 1 << k);
                    assert_eq!(maybe_mask16(w, kind), want, "mask kind {kind} at {j}");
                    if !tab_nl16(&buf, j) {
                        assert!(!w.iter().any(|&c| c == 9 || c == 10 || c == 13), "tab_nl16 at {j}");
                    }
                    if clean16(&buf, j, kind) {
                        assert_eq!(want, 0, "clean16 kind {kind} at {j}");
                    }
                }
            }
        }
    }
}

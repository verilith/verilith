//! AVX2 kernels for the runs of ASCII (or Latin-1) that most text is made
//! of: a test that 32 bytes or 32 UTF-16 units are ASCII, and the widening
//! and narrowing moves between 8- and 16-bit units. Each is proven with
//! vsimd's specifications of the intrinsics.
use super::spec::*;
use crate::simd::*;
use verilith_simd::arch::*;
use verilith_simd::cpu::*;
use verilith_simd::lanes::*;
use verilith_simd::mem::*;
use verilith_simd::ops::*;
#[cfg(verus_only)]
use verilith_simd::x86::{half128, perm2x128};
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::cpu::group_cpu};

/// `movemask` is zero exactly when no byte has its top bit set.
pub proof fn lemma_movemask_zero(b: Seq<u8>)
    ensures
        (movemask(b) == 0) <==> forall|k: int| 0 <= k < b.len() ==> #[trigger] b[k] < 128,
    decreases b.len(),
{
    if b.len() > 0 {
        let r = b.drop_first();
        lemma_movemask_zero(r);
        if forall|k: int| 0 <= k < b.len() ==> #[trigger] b[k] < 128 {
            assert forall|k: int| 0 <= k < r.len() implies #[trigger] r[k] < 128 by {
                assert(r[k] == b[k + 1]);
            }
        }
        if movemask(b) == 0 {
            assert forall|k: int| 0 <= k < b.len() implies #[trigger] b[k] < 128 by {
                if k > 0 {
                    assert(r[k - 1] == b[k]);
                }
            }
        }
    }
}

/// Whether the 32 bytes at `s[i..]` are ASCII.
#[inline(always)]
pub fn ascii32(s: &[u8], i: usize) -> (r: bool)
    requires
        avx2(),
        i + 32 <= s.len(),
    ensures
        r == ascii(s@, i as int, i + 32),
{
    let v = load256_u8(s, i);
    let m = _mm256_movemask_epi8(v);
    proof {
        lemma_movemask_zero(b256(v));
        assert(b256(v) == s@.subrange(i as int, i + 32));
        if ascii(s@, i as int, i + 32) {
            assert forall|k: int| 0 <= k < 32 implies #[trigger] b256(v)[k] < 128 by {
                assert(s@[i + k] < 0x80);
            }
        }
        if m == 0 {
            assert forall|k: int| i <= k < i + 32 implies #[trigger] s@[k] < 0x80 by {
                assert(b256(v)[k - i] < 128);
            }
        }
    }
    m == 0
}

/// Whether the 64 bytes at `s[i..]` are ASCII, in one test.
#[inline(always)]
pub fn ascii64(s: &[u8], i: usize) -> (r: bool)
    requires
        avx2(),
        i + 64 <= s.len(),
    ensures
        r ==> ascii(s@, i as int, i + 64),
{
    let a = load256_u8(s, i);
    let b = load256_u8(s, i + 32);
    let o = _mm256_or_si256(a, b);
    let m = _mm256_movemask_epi8(o);
    proof {
        lemma_movemask_zero(b256(o));
        if m == 0 {
            assert forall|k: int| i <= k < i + 64 implies #[trigger] s@[k] < 0x80 by {
                let l = if k < i + 32 { k - i } else { k - i - 32 };
                let (x, y) = (b256(a)[l], b256(b)[l]);
                assert(b256(o)[l] < 128);
                assert((x | y) < 128 ==> x < 128 && y < 128) by (bit_vector);
                if k < i + 32 {
                    assert(s@[k] == x);
                } else {
                    assert(s@[k] == y);
                }
            }
        }
    }
    m == 0
}

proof fn lemma_le16_zero(x: u8)
    ensures
        le16(x, 0) == x as u16,
{
    assert((x as u16) | ((0u8 as u16) << 8u16) == x as u16) by (bit_vector);
}

/// The bytes of the unpack-with-zero and `perm2x128` steps of `widen32`.
proof fn lemma_widen_lanes(vb: Seq<u8>, lb: Seq<u8>, hb: Seq<u8>, ab: Seq<u8>, bb: Seq<u8>)
    requires
        vb.len() == 32,
        lb == unpacklo8_lanes(vb, splat8(0u8, 32)),
        hb == unpackhi8_lanes(vb, splat8(0u8, 32)),
        ab == lb.subrange(0, 16) + hb.subrange(0, 16),
        bb == lb.subrange(16, 32) + hb.subrange(16, 32),
    ensures
        forall|k: int| 0 <= k < 16 ==> #[trigger] ab[2 * k] == vb[k] && ab[2 * k + 1] == 0,
        forall|k: int| 0 <= k < 16 ==> #[trigger] bb[2 * k] == vb[16 + k] && bb[2 * k + 1] == 0,
        u16s(ab) == Seq::new(16, |k: int| vb[k] as u16),
        u16s(bb) == Seq::new(16, |k: int| vb[16 + k] as u16),
{
    assert forall|k: int| 0 <= k < 16 implies #[trigger] ab[2 * k] == vb[k] && ab[2 * k + 1] == 0 by {
        if k < 8 {
            assert(ab[2 * k] == lb[2 * k]);
            assert(ab[2 * k + 1] == lb[2 * k + 1]);
            assert((2 * k) / 16 == 0 && (2 * k) % 16 == 2 * k);
            assert((2 * k + 1) % 2 == 1);
        } else {
            assert(ab[2 * k] == hb[2 * k - 16]);
            assert(ab[2 * k + 1] == hb[2 * k - 15]);
            assert((2 * k - 16) / 16 == 0 && (2 * k - 16) % 16 == 2 * k - 16);
            assert((2 * k - 15) % 2 == 1);
        }
    }
    assert forall|k: int| 0 <= k < 16 implies #[trigger] bb[2 * k] == vb[16 + k] && bb[2 * k + 1] == 0 by {
        if k < 8 {
            assert(bb[2 * k] == lb[16 + 2 * k]);
            assert(bb[2 * k + 1] == lb[17 + 2 * k]);
            assert((16 + 2 * k) / 16 == 1 && (16 + 2 * k) % 16 == 2 * k);
            assert((17 + 2 * k) % 2 == 1);
        } else {
            assert(bb[2 * k] == hb[2 * k]);
            assert(bb[2 * k + 1] == hb[2 * k + 1]);
            assert((2 * k) / 16 == 1 && (2 * k) % 16 == 2 * k - 16);
            assert((2 * k + 1) % 2 == 1);
        }
    }
    assert forall|k: int| 0 <= k < 16 implies #[trigger] u16s(ab)[k] == vb[k] as u16 by {
        lemma_le16_zero(vb[k]);
    }
    assert forall|k: int| 0 <= k < 16 implies #[trigger] u16s(bb)[k] == vb[16 + k] as u16 by {
        lemma_le16_zero(vb[16 + k]);
    }
    assert(u16s(ab) =~= Seq::new(16, |k: int| vb[k] as u16));
    assert(u16s(bb) =~= Seq::new(16, |k: int| vb[16 + k] as u16));
}

/// Writes the 32 bytes at `s[i..]`, widened to 16 bits, at `out[o..]`.
#[inline(always)]
pub fn widen32(s: &[u8], i: usize, out: &mut [u16], o: usize)
    requires
        avx2(),
        i + 32 <= s.len(),
        o + 32 <= old(out).len(),
    ensures
        final(out).len() == old(out).len(),
        forall|k: int|
            0 <= k < final(out).len() ==> #[trigger] final(out)@[k] == if o <= k < o + 32 {
                s@[i + k - o] as u16
            } else {
                old(out)@[k]
            },
{
    let v = load256_u8(s, i);
    let z = _mm256_setzero_si256();
    let lo = _mm256_unpacklo_epi8(v, z);
    let hi = _mm256_unpackhi_epi8(v, z);
    let a = _mm256_permute2x128_si256::<0x20>(lo, hi);
    let b = _mm256_permute2x128_si256::<0x31>(lo, hi);
    proof {
        let vb = b256(v);
        assert(vb == s@.subrange(i as int, i + 32));
        assert(b256(a) == b256(lo).subrange(0, 16) + b256(hi).subrange(0, 16));
        assert(b256(b) == b256(lo).subrange(16, 32) + b256(hi).subrange(16, 32));
        lemma_widen_lanes(vb, b256(lo), b256(hi), b256(a), b256(b));
    }
    let ghost before = out@;
    let ghost src = s@;
    store256_u16(out, o, a);
    let ghost mid = out@;
    store256_u16(out, o + 16, b);
    proof {
        assert forall|k: int| 0 <= k < out.len() implies #[trigger] out@[k] == if o <= k < o + 32 {
            src[i + k - o] as u16
        } else {
            before[k]
        } by {
            if o + 16 <= k < o + 32 {
                assert(out@[k] == u16x16(b)[k - o - 16]);
                assert(src[i + k - o] == b256(v)[16 + (k - o - 16)]);
            } else if o <= k < o + 16 {
                assert(out@[k] == mid[k]);
                assert(mid[k] == u16x16(a)[k - o]);
                assert(src[i + k - o] == b256(v)[k - o]);
            } else {
                assert(out@[k] == mid[k]);
            }
        }
    }
}

/// The 16-bit lanes of `perm2x128::<0x20>` and `<0x31>` of `x` and `y`.
proof fn lemma_u16s_halves(x: Seq<u8>, y: Seq<u8>, lo: Seq<u8>, hi: Seq<u8>)
    requires
        x.len() == 32 && y.len() == 32,
        lo == x.subrange(0, 16) + y.subrange(0, 16),
        hi == x.subrange(16, 32) + y.subrange(16, 32),
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] u16s(lo)[k] == u16s(x)[k] && u16s(hi)[k] == u16s(x)[k + 8],
        forall|k: int| 8 <= k < 16 ==> #[trigger] u16s(lo)[k] == u16s(y)[k - 8] && u16s(hi)[k] == u16s(y)[k],
{
    assert forall|k: int| 0 <= k < 8 implies #[trigger] u16s(lo)[k] == u16s(x)[k] && u16s(hi)[k] == u16s(x)[k + 8] by {
        assert(lo[2 * k] == x[2 * k] && lo[2 * k + 1] == x[2 * k + 1]);
        assert(hi[2 * k] == x[2 * (k + 8)] && hi[2 * k + 1] == x[2 * (k + 8) + 1]);
    }
    assert forall|k: int| 8 <= k < 16 implies #[trigger] u16s(lo)[k] == u16s(y)[k - 8] && u16s(hi)[k] == u16s(y)[k] by {
        assert(lo[2 * k] == y[2 * (k - 8)] && lo[2 * k + 1] == y[2 * (k - 8) + 1]);
        assert(hi[2 * k] == y[2 * k] && hi[2 * k + 1] == y[2 * k + 1]);
    }
}

/// Writes the 32 units at `s[i..]`, each below 0x100, as bytes at `out[o..]`.
#[inline(always)]
pub fn narrow32(s: &[u16], i: usize, out: &mut [u8], o: usize)
    requires
        avx2(),
        i + 32 <= s.len(),
        o + 32 <= old(out).len(),
        forall|k: int| i <= k < i + 32 ==> #[trigger] s@[k] <= 0xFF,
    ensures
        final(out).len() == old(out).len(),
        forall|k: int|
            0 <= k < final(out).len() ==> #[trigger] final(out)@[k] == if o <= k < o + 32 {
                s@[i + k - o] as u8
            } else {
                old(out)@[k]
            },
{
    let a = load256_u16(s, i);
    let b = load256_u16(s, i + 16);
    let x = _mm256_permute2x128_si256::<0x20>(a, b);
    let y = _mm256_permute2x128_si256::<0x31>(a, b);
    let p = _mm256_packus_epi16(x, y);
    proof {
        assert(b256(x) == b256(a).subrange(0, 16) + b256(b).subrange(0, 16));
        assert(b256(y) == b256(a).subrange(16, 32) + b256(b).subrange(16, 32));
        lemma_u16s_halves(b256(a), b256(b), b256(x), b256(y));
        assert forall|t: int| 0 <= t < 32 implies #[trigger] b256(p)[t] == s@[i + t] as u8 by {
            let u = s@[i + t];
            let w = if t < 8 {
                u16x16(x)[t]
            } else if t < 16 {
                u16x16(y)[t - 8]
            } else if t < 24 {
                u16x16(x)[t - 8]
            } else {
                u16x16(y)[t - 16]
            };
            assert(b256(p)[t] == sat_u8(s16(w)));
            if t < 16 {
                assert(w == u16x16(a)[t]);
                assert(u == u16x16(a)[t]);
            } else {
                assert(w == u16x16(b)[t - 16]);
                assert(u == u16x16(b)[t - 16]);
            }
            assert(u <= 0xFF);
        }
    }
    store256_u8(out, o, p);
}

/// Whether the 32 units at `s[i..]` are all below `lim` (0x80 or 0x100).
#[inline(always)]
pub fn below32(s: &[u16], i: usize, ascii_only: bool) -> (r: bool)
    requires
        avx2(),
        i + 32 <= s.len(),
    ensures
        r ==> forall|k: int| i <= k < i + 32 ==> #[trigger] s@[k] < (if ascii_only { 0x80u16 } else { 0x100u16 }),
{
    let a = load256_u16(s, i);
    let b = load256_u16(s, i + 16);
    let m = if ascii_only { _mm256_set1_epi16(-128) } else { _mm256_set1_epi16(-256) };
    let o = _mm256_or_si256(a, b);
    let e = _mm256_and_si256(o, m);
    let zero = _mm256_setzero_si256();
    let c = _mm256_cmpeq_epi8(e, zero);
    let mm = _mm256_movemask_epi8(c);
    proof {
        lemma_all_zero(b256(e), b256(zero), b256(c), mm);
        let mv: u16 = if ascii_only { 0xFF80u16 } else { 0xFF00u16 };
        assert(u16x16(m) == splat16(mv, 16));
        if mm == -1 {
            assert forall|k: int| i <= k < i + 32 implies #[trigger] s@[k] < (if ascii_only { 0x80u16 } else { 0x100u16 }) by {
                let l = if k < i + 16 { k - i } else { k - i - 16 };
                let src = if k < i + 16 { b256(a) } else { b256(b) };
                lemma_u16_lane_bytes(b256(m), l);
                lemma_u16_lane_bytes(src, l);
                let (m0, m1) = (b256(m)[2 * l], b256(m)[2 * l + 1]);
                let (o0, o1) = (b256(o)[2 * l], b256(o)[2 * l + 1]);
                let (a0, a1) = (b256(a)[2 * l], b256(a)[2 * l + 1]);
                let (b0, b1) = (b256(b)[2 * l], b256(b)[2 * l + 1]);
                assert(b256(e)[2 * l] == 0 && b256(e)[2 * l + 1] == 0);
                assert(byte16(0xFF80u16, 0) == 0x80 && byte16(0xFF80u16, 1) == 0xFF) by (bit_vector);
                assert(byte16(0xFF00u16, 0) == 0 && byte16(0xFF00u16, 1) == 0xFF) by (bit_vector);
                assert(u16x16(m)[l] == mv);
                assert(m1 == 0xFF);
                assert(ascii_only ==> m0 == 0x80);
                assert((o0 & m0) == 0 && (o1 & m1) == 0);
                assert(o0 == a0 | b0 && o1 == a1 | b1);
                assert((a1 | b1) & 0xFF == 0 ==> a1 == 0 && b1 == 0) by (bit_vector);
                assert(((a0 | b0) & 0x80) == 0 ==> a0 < 0x80 && b0 < 0x80) by (bit_vector);
                lemma_le16_value(a0, a1);
                lemma_le16_value(b0, b1);
                assert(u16x16(a)[l] == le16(a0, a1));
                assert(u16x16(b)[l] == le16(b0, b1));
                if k < i + 16 {
                    assert(s@[k] == u16x16(a)[l]);
                } else {
                    assert(s@[k] == u16x16(b)[l]);
                }
            }
        }
    }
    mm == -1
}

} // verus!

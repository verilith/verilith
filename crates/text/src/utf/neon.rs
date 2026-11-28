//! NEON versions of the AVX2 kernels in `avx2.rs`, with the same contracts
//! (32 bytes or units at a time), so the converters' proofs serve both.
//! Each is proven with vsimd's specifications of the NEON intrinsics.
use super::spec::*;
use verilith_simd::lanes::*;
use verilith_simd::neon::*;
use verilith_simd::ops::*;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::neon::group_neon};

/// No lane of an OR has its top bit unless one of its inputs does, and the
/// converse.
proof fn lemma_or_top(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>)
    requires
        a.len() == 16 && b.len() == 16,
        r == or8(a, b),
    ensures
        forall|l: int| 0 <= l < 16 ==> (#[trigger] r[l] < 0x80) == (a[l] < 0x80 && b[l] < 0x80),
{
    assert forall|l: int| 0 <= l < 16 implies (#[trigger] r[l] < 0x80) == (a[l] < 0x80 && b[l] < 0x80) by {
        let (x, y) = (a[l], b[l]);
        assert(((x | y) < 0x80) == (x < 0x80 && y < 0x80)) by (bit_vector);
    }
}

/// Whether the 32 bytes at `s[i..]` are ASCII.
#[inline(always)]
pub fn ascii32_neon(s: &[u8], i: usize) -> (r: bool)
    requires
        neon(),
        i + 32 <= s.len(),
    ensures
        r == ascii(s@, i as int, i + 32),
{
    let a = vld1q_u8_at(s, i);
    let b = vld1q_u8_at(s, i + 16);
    let o = vorrq_u8(a, b);
    let m = vmaxvq_u8(o);
    proof {
        lemma_or_top(n8(a), n8(b), n8(o));
        if m < 0x80 {
            assert forall|k: int| i <= k < i + 32 implies #[trigger] s@[k] < 0x80 by {
                let l = if k < i + 16 { k - i } else { k - i - 16 };
                assert(n8(o)[l] <= m);
                if k < i + 16 {
                    assert(n8(a)[l] == s@[k]);
                } else {
                    assert(n8(b)[l] == s@[k]);
                }
            }
        }
        if ascii(s@, i as int, i + 32) {
            let l = choose|l: int| 0 <= l < 16 && #[trigger] n8(o)[l] == m;
            assert(n8(a)[l] == s@[i + l] && n8(b)[l] == s@[i + 16 + l]);
        }
    }
    m < 0x80
}

/// Whether the 64 bytes at `s[i..]` are ASCII, in one test.
#[inline(always)]
pub fn ascii64_neon(s: &[u8], i: usize) -> (r: bool)
    requires
        neon(),
        i + 64 <= s.len(),
    ensures
        r ==> ascii(s@, i as int, i + 64),
{
    let a = vld1q_u8_at(s, i);
    let b = vld1q_u8_at(s, i + 16);
    let c = vld1q_u8_at(s, i + 32);
    let d = vld1q_u8_at(s, i + 48);
    let x = vorrq_u8(a, b);
    let y = vorrq_u8(c, d);
    let o = vorrq_u8(x, y);
    let m = vmaxvq_u8(o);
    proof {
        lemma_or_top(n8(a), n8(b), n8(x));
        lemma_or_top(n8(c), n8(d), n8(y));
        lemma_or_top(n8(x), n8(y), n8(o));
        if m < 0x80 {
            assert forall|k: int| i <= k < i + 64 implies #[trigger] s@[k] < 0x80 by {
                let q = (k - i) / 16;
                let l = (k - i) % 16;
                assert(n8(o)[l] <= m);
                if q == 0 {
                    assert(n8(a)[l] == s@[k]);
                } else if q == 1 {
                    assert(n8(b)[l] == s@[k]);
                } else if q == 2 {
                    assert(n8(c)[l] == s@[k]);
                } else {
                    assert(n8(d)[l] == s@[k]);
                }
            }
        }
    }
    m < 0x80
}

proof fn lemma_le16_zero_n(x: u8)
    ensures
        le16(x, 0) == x as u16,
{
    assert((x as u16) | ((0u8 as u16) << 8u16) == x as u16) by (bit_vector);
}

/// The 16-bit lanes of `zip1` and `zip2` with zero are the bytes, widened.
proof fn lemma_zip_zero(vb: Seq<u8>, lo: Seq<u8>, hi: Seq<u8>)
    requires
        vb.len() == 16,
        lo == unpacklo8_lanes(vb, splat8(0u8, 16)),
        hi == unpackhi8_lanes(vb, splat8(0u8, 16)),
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] u16s(lo)[k] == vb[k] as u16,
        forall|k: int| 0 <= k < 8 ==> #[trigger] u16s(hi)[k] == vb[8 + k] as u16,
{
    assert forall|k: int| 0 <= k < 8 implies #[trigger] u16s(lo)[k] == vb[k] as u16 by {
        assert((2 * k) / 16 == 0 && (2 * k) % 16 == 2 * k && (2 * k + 1) % 2 == 1);
        assert(lo[2 * k] == vb[k] && lo[2 * k + 1] == 0);
        lemma_le16_zero_n(vb[k]);
    }
    assert forall|k: int| 0 <= k < 8 implies #[trigger] u16s(hi)[k] == vb[8 + k] as u16 by {
        assert((2 * k) / 16 == 0 && (2 * k) % 16 == 2 * k && (2 * k + 1) % 2 == 1);
        assert(hi[2 * k] == vb[8 + k] && hi[2 * k + 1] == 0);
        lemma_le16_zero_n(vb[8 + k]);
    }
}

/// Writes the 16 bytes at `s[i..]`, widened to 16 bits, at `out[o..]`.
#[inline(always)]
fn widen16_neon(s: &[u8], i: usize, out: &mut [u16], o: usize)
    requires
        neon(),
        i + 16 <= s.len(),
        o + 16 <= old(out).len(),
    ensures
        final(out).len() == old(out).len(),
        forall|k: int|
            0 <= k < final(out).len() ==> #[trigger] final(out)@[k] == if o <= k < o + 16 {
                s@[i + k - o] as u16
            } else {
                old(out)@[k]
            },
{
    let v = vld1q_u8_at(s, i);
    let z = vdupq_n_u8(0);
    let lo = vzip1q_u8(v, z);
    let hi = vzip2q_u8(v, z);
    proof {
        lemma_zip_zero(n8(v), n8(lo), n8(hi));
    }
    let ghost before = out@;
    vst1q_u16_at(out, o, lo);
    let ghost mid = out@;
    vst1q_u16_at(out, o + 8, hi);
    proof {
        assert forall|k: int| 0 <= k < out.len() implies #[trigger] out@[k] == if o <= k < o + 16 {
            s@[i + k - o] as u16
        } else {
            before[k]
        } by {
            if o + 8 <= k < o + 16 {
                assert(out@[k] == u16s(n8(hi))[k - o - 8]);
                assert(s@[i + k - o] == n8(v)[8 + (k - o - 8)]);
            } else if o <= k < o + 8 {
                assert(out@[k] == mid[k]);
                assert(mid[k] == u16s(n8(lo))[k - o]);
                assert(s@[i + k - o] == n8(v)[k - o]);
            } else {
                assert(out@[k] == mid[k]);
            }
        }
    }
}

/// Writes the 32 bytes at `s[i..]`, widened to 16 bits, at `out[o..]`.
#[inline(always)]
pub fn widen32_neon(s: &[u8], i: usize, out: &mut [u16], o: usize)
    requires
        neon(),
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
    let ghost before = out@;
    widen16_neon(s, i, out, o);
    let ghost mid = out@;
    widen16_neon(s, i + 16, out, o + 16);
    proof {
        assert forall|k: int| 0 <= k < out.len() implies #[trigger] out@[k] == if o <= k < o + 32 {
            s@[i + k - o] as u16
        } else {
            before[k]
        } by {
            if !(o + 16 <= k < o + 32) {
                assert(out@[k] == mid[k]);
            }
        }
    }
}

/// The low byte of each 16-bit lane, for lanes below 0x100, is its value.
proof fn lemma_low_byte(b: Seq<u8>, k: int)
    requires
        b.len() == 16,
        0 <= k < 8,
        u16s(b)[k] <= 0xFF,
    ensures
        b[2 * k] == u16s(b)[k] as u8,
{
    lemma_u16_lane_bytes(b, k);
    let w = u16s(b)[k];
    assert(w <= 0xFF ==> byte16(w, 0) == w as u8) by (bit_vector);
}

/// Writes the 16 units at `s[i..]`, each below 0x100, as bytes at `out[o..]`.
#[inline(always)]
fn narrow16_neon(s: &[u16], i: usize, out: &mut [u8], o: usize)
    requires
        neon(),
        i + 16 <= s.len(),
        o + 16 <= old(out).len(),
        forall|k: int| i <= k < i + 16 ==> #[trigger] s@[k] <= 0xFF,
    ensures
        final(out).len() == old(out).len(),
        forall|k: int|
            0 <= k < final(out).len() ==> #[trigger] final(out)@[k] == if o <= k < o + 16 {
                s@[i + k - o] as u8
            } else {
                old(out)@[k]
            },
{
    let a = vld1q_u16_at(s, i);
    let b = vld1q_u16_at(s, i + 8);
    let p = vuzp1q_u8(a, b);
    proof {
        assert forall|t: int| 0 <= t < 16 implies #[trigger] n8(p)[t] == s@[i + t] as u8 by {
            if t < 8 {
                assert(n8(p)[t] == n8(a)[2 * t]);
                assert(u16s(n8(a))[t] == s@[i + t]);
                lemma_low_byte(n8(a), t);
            } else {
                assert(n8(p)[t] == n8(b)[2 * t - 16]);
                assert(u16s(n8(b))[t - 8] == s@[i + t]);
                lemma_low_byte(n8(b), t - 8);
            }
        }
    }
    let ghost before = out@;
    vst1q_u8_at(out, o, p);
    proof {
        assert forall|k: int| 0 <= k < out.len() implies #[trigger] out@[k] == if o <= k < o + 16 {
            s@[i + k - o] as u8
        } else {
            before[k]
        } by {
            if o <= k < o + 16 {
                assert(out@[k] == n8(p)[k - o]);
            }
        }
    }
}

/// Writes the 32 units at `s[i..]`, each below 0x100, as bytes at `out[o..]`.
#[inline(always)]
pub fn narrow32_neon(s: &[u16], i: usize, out: &mut [u8], o: usize)
    requires
        neon(),
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
    let ghost before = out@;
    narrow16_neon(s, i, out, o);
    let ghost mid = out@;
    narrow16_neon(s, i + 16, out, o + 16);
    proof {
        assert forall|k: int| 0 <= k < out.len() implies #[trigger] out@[k] == if o <= k < o + 32 {
            s@[i + k - o] as u8
        } else {
            before[k]
        } by {
            if !(o + 16 <= k < o + 32) {
                assert(out@[k] == mid[k]);
            }
        }
    }
}

/// `or8` is `|` on 16-bit lanes, and an OR is below a power of two only
/// when both sides are.
proof fn lemma_or16(x: Seq<u8>, y: Seq<u8>, r: Seq<u8>)
    requires
        x.len() == 16 && y.len() == 16,
        r == or8(x, y),
    ensures
        forall|k: int| 0 <= k < 8 ==> (#[trigger] u16s(r)[k] < 0x80u16 ==> u16s(x)[k] < 0x80u16 && u16s(y)[k] < 0x80u16),
        forall|k: int| 0 <= k < 8 ==> (#[trigger] u16s(r)[k] < 0x100u16 ==> u16s(x)[k] < 0x100u16 && u16s(y)[k] < 0x100u16),
{
    assert forall|k: int| 0 <= k < 8 implies (#[trigger] u16s(r)[k] < 0x80u16 ==> u16s(x)[k] < 0x80u16 && u16s(y)[k] < 0x80u16)
        && (u16s(r)[k] < 0x100u16 ==> u16s(x)[k] < 0x100u16 && u16s(y)[k] < 0x100u16) by {
        let (a0, a1, b0, b1) = (x[2 * k], x[2 * k + 1], y[2 * k], y[2 * k + 1]);
        assert(r[2 * k] == a0 | b0 && r[2 * k + 1] == a1 | b1);
        assert(le16(a0 | b0, a1 | b1) == le16(a0, a1) | le16(b0, b1)) by (bit_vector);
        let (u, v) = (le16(a0, a1), le16(b0, b1));
        assert((u | v) < 0x80u16 ==> u < 0x80u16 && v < 0x80u16) by (bit_vector);
        assert((u | v) < 0x100u16 ==> u < 0x100u16 && v < 0x100u16) by (bit_vector);
    }
}

/// A unit whose high byte, shifted right by 3, is not 0x1B is not a
/// surrogate.
proof fn lemma_sur_hi(b0: u8, b1: u8)
    requires
        (b1 as nat / pow2_spec(3)) as u8 != 0x1Bu8,
    ensures
        !(0xD800u16 <= le16(b0, b1) && le16(b0, b1) <= 0xDFFFu16),
{
    reveal_with_fuel(pow2_spec, 4);
    assert(pow2_spec(3) == 8);
    assert((b1 as nat / 8) as u8 == b1 / 8u8);
    assert(b1 / 8u8 == b1 >> 3u8) by (bit_vector);
    assert(b1 >> 3u8 != 0x1Bu8 ==> !(0xD800u16 <= ((b0 as u16) | ((b1 as u16) << 8u16)) && ((b0 as u16) | ((b1
        as u16) << 8u16)) <= 0xDFFFu16)) by (bit_vector);
}

/// Whether none of the 32 units at `s[i..]` is a surrogate: no unit's high
/// byte is 0xD8 to 0xDF, which is its top five bits being 0x1B.
#[inline(always)]
pub fn no_sur32_neon(s: &[u16], i: usize) -> (r: bool)
    requires
        neon(),
        i + 32 <= s.len(),
    ensures
        r ==> forall|k: int| i <= k < i + 32 ==> !(0xD800u16 <= #[trigger] s@[k] && s@[k] <= 0xDFFFu16),
{
    let odd_bytes: [u8; 16] = [0, 0xFF, 0, 0xFF, 0, 0xFF, 0, 0xFF, 0, 0xFF, 0, 0xFF, 0, 0xFF, 0, 0xFF];
    let odd = vld1q_u8_at(&odd_bytes, 0);
    let c = vdupq_n_u8(0x1B);
    let x0 = vld1q_u16_at(s, i);
    let x1 = vld1q_u16_at(s, i + 8);
    let x2 = vld1q_u16_at(s, i + 16);
    let x3 = vld1q_u16_at(s, i + 24);
    let e0 = vceqq_u8(vshrq_n_u8::<3>(x0), c);
    let e1 = vceqq_u8(vshrq_n_u8::<3>(x1), c);
    let e2 = vceqq_u8(vshrq_n_u8::<3>(x2), c);
    let e3 = vceqq_u8(vshrq_n_u8::<3>(x3), c);
    let o = vandq_u8(vorrq_u8(vorrq_u8(e0, e1), vorrq_u8(e2, e3)), odd);
    let m = vmaxvq_u8(o);
    proof {
        assert(odd_bytes@ =~= seq![0u8, 0xFFu8, 0u8, 0xFFu8, 0u8, 0xFFu8, 0u8, 0xFFu8, 0u8, 0xFFu8, 0u8, 0xFFu8, 0u8, 0xFFu8, 0u8, 0xFFu8]);
        if m == 0 {
            assert forall|k: int| i <= k < i + 32 implies !(0xD800u16 <= #[trigger] s@[k] && s@[k] <= 0xDFFFu16) by {
                let q = (k - i) / 8;
                let l = (k - i) % 8;
                let x = if q == 0 { x0 } else if q == 1 { x1 } else if q == 2 { x2 } else { x3 };
                let e = if q == 0 { e0 } else if q == 1 { e1 } else if q == 2 { e2 } else { e3 };
                assert(u16s(n8(x))[l] == s@[k]);
                let j = 2 * l + 1;
                assert(n8(odd)[j] == 0xFFu8);
                let (a0, a1, a2, a3) = (n8(e0)[j], n8(e1)[j], n8(e2)[j], n8(e3)[j]);
                assert(n8(o)[j] == ((a0 | a1) | (a2 | a3)) & 0xFFu8);
                assert(n8(o)[j] <= m);
                assert(((a0 | a1) | (a2 | a3)) & 0xFFu8 == 0 ==> a0 == 0 && a1 == 0 && a2 == 0 && a3 == 0) by (bit_vector);
                assert(n8(e)[j] == 0);
                assert(shr8(n8(x), 3)[j] != 0x1Bu8);
                lemma_sur_hi(n8(x)[2 * l], n8(x)[j]);
            }
        }
    }
    m == 0
}

/// Whether the 32 units at `s[i..]` are all below `lim` (0x80 or 0x100).
#[inline(always)]
pub fn below32_neon(s: &[u16], i: usize, ascii_only: bool) -> (r: bool)
    requires
        neon(),
        i + 32 <= s.len(),
    ensures
        r ==> forall|k: int| i <= k < i + 32 ==> #[trigger] s@[k] < (if ascii_only { 0x80u16 } else { 0x100u16 }),
{
    let a = vld1q_u16_at(s, i);
    let b = vld1q_u16_at(s, i + 8);
    let c = vld1q_u16_at(s, i + 16);
    let d = vld1q_u16_at(s, i + 24);
    let x = vorrq_u8(a, b);
    let y = vorrq_u8(c, d);
    let o = vorrq_u8(x, y);
    let m = vmaxvq_u16(o);
    let lim: u16 = if ascii_only { 0x80 } else { 0x100 };
    proof {
        lemma_or16(n8(a), n8(b), n8(x));
        lemma_or16(n8(c), n8(d), n8(y));
        lemma_or16(n8(x), n8(y), n8(o));
        if m < lim {
            assert forall|k: int| i <= k < i + 32 implies #[trigger] s@[k] < lim by {
                let q = (k - i) / 8;
                let l = (k - i) % 8;
                assert(u16s(n8(o))[l] <= m);
                if q == 0 {
                    assert(u16s(n8(a))[l] == s@[k]);
                } else if q == 1 {
                    assert(u16s(n8(b))[l] == s@[k]);
                } else if q == 2 {
                    assert(u16s(n8(c))[l] == s@[k]);
                } else {
                    assert(u16s(n8(d))[l] == s@[k]);
                }
            }
        }
    }
    m < lim
}

} // verus!

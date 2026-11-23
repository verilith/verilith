//! YUV 4:2:0 to ARGB, as libwebp 1.6.0's default RGB output does it: the
//! "fancy" upsampler (`UPSAMPLE_FUNC` in `src/dsp/upsampling.c`, driven by
//! `EmitFancyRGB` in `src/dec/io_dec.c`), and the 14-bit fixed-point
//! conversion of `src/dsp/yuv.h`.
use crate::pixels::Error;
use crate::vp8frame::*;
use crate::vp8spec::*;
use verilith_core::prims::*;
use verilith_simd::arch::*;
use verilith_simd::cpu::*;
use verilith_simd::lanes::*;
use verilith_simd::mem::*;
use verilith_simd::neon::*;
use verilith_simd::ops::*;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::neon::group_neon};

// ---------------------------------------------------------------------------
// What the routines below compute, in the terms of `vp8spec`
// ---------------------------------------------------------------------------

/// `s[0..len]` is the line of upsampled chroma `fancy_line(c, no, fo, len, ..)`.
pub open spec fn fancy_row(s: Seq<u8>, c: Seq<u8>, no: int, fo: int, len: int) -> bool {
    forall|x: int| 0 <= x < len ==> (#[trigger] s[x]) as int == fancy_line(c, no, fo, len, x)
}

/// The pair of bytes at `s[off + 2m..]`.
pub open spec fn pair2(s: Seq<u8>, off: int, m: int) -> (u8, u8) {
    (s[off + 2 * m], s[off + 2 * m + 1])
}

/// `s` is `s0` with the first `m` pairs of `s[off..off + 2n]` set to
/// `(e[p], o[p])`; nothing outside `s[off..off + 2n]` differs.
pub open spec fn interleaved(s0: Seq<u8>, s: Seq<u8>, e: Seq<u8>, o: Seq<u8>, off: int, m: int, n: int) -> bool {
    &&& s.len() == s0.len()
    &&& forall|p: int| 0 <= p < m ==> #[trigger] pair2(s, off, p) == (e[p], o[p])
    &&& forall|i: int| 0 <= i < s.len() && !(off <= i < off + 2 * n) ==> #[trigger] s[i] == s0[i]
}

/// The four bytes at `s[oo + 4p..]`.
pub open spec fn px4(s: Seq<u8>, oo: int, p: int) -> (u8, u8, u8, u8) {
    (s[oo + 4 * p], s[oo + 4 * p + 1], s[oo + 4 * p + 2], s[oo + 4 * p + 3])
}

/// `s` is `s0` with the first `m` four-byte pixels of `s[oo..oo + 4n]` set
/// to `(c0[p], c1[p], c2[p], c3[p])`; nothing outside that range differs.
pub open spec fn packed4(
    s0: Seq<u8>, s: Seq<u8>, c0: Seq<u8>, c1: Seq<u8>, c2: Seq<u8>, c3: Seq<u8>, oo: int, m: int, n: int,
) -> bool {
    &&& s.len() == s0.len()
    &&& forall|p: int| 0 <= p < m ==> #[trigger] px4(s, oo, p) == (c0[p], c1[p], c2[p], c3[p])
    &&& forall|i: int| 0 <= i < s.len() && !(oo <= i < oo + 4 * n) ==> #[trigger] s[i] == s0[i]
}

/// The bytes at offsets `pr`, `pg`, `pb` of the three-byte pixel `s[oo + 3p..]`.
pub open spec fn px3(s: Seq<u8>, oo: int, p: int, pr: int, pg: int, pb: int) -> (u8, u8, u8) {
    (s[oo + 3 * p + pr], s[oo + 3 * p + pg], s[oo + 3 * p + pb])
}

/// `s` is `s0` with the first `m` three-byte pixels of `s[oo..oo + 3n]`
/// set: byte `pr` to `sr[p]`, `pg` to `sg[p]`, `pb` to `sb[p]`.
pub open spec fn packed3(
    s0: Seq<u8>, s: Seq<u8>, sr: Seq<u8>, sg: Seq<u8>, sb: Seq<u8>, oo: int, m: int, n: int,
    pr: int, pg: int, pb: int,
) -> bool {
    &&& s.len() == s0.len()
    &&& forall|p: int| 0 <= p < m ==> #[trigger] px3(s, oo, p, pr, pg, pb) == (sr[p], sg[p], sb[p])
    &&& forall|i: int| 0 <= i < s.len() && !(oo <= i < oo + 3 * n) ==> #[trigger] s[i] == s0[i]
}

/// The upsampled chroma is a byte.
proof fn lemma_fancy_bounds(n0: int, n1: int, f0: int, f1: int)
    requires
        0 <= n0 <= 255, 0 <= n1 <= 255, 0 <= f0 <= 255, 0 <= f1 <= 255,
    ensures
        0 <= fancy_mid(n0, n1, f0, f1) <= 255,
        0 <= fancy_edge(n0, f0) <= 255,
{
}

/// One more pair, stored by bytes.
proof fn lemma_interleave1(s0: Seq<u8>, s1: Seq<u8>, s2: Seq<u8>, e: Seq<u8>, o: Seq<u8>, off: int, m: int, n: int)
    requires
        0 <= off, 0 <= m < n,
        off + 2 * n <= s0.len(),
        interleaved(s0, s1, e, o, off, m, n),
        s2 == s1.update(off + 2 * m, e[m]).update(off + 2 * m + 1, o[m]),
    ensures
        interleaved(s0, s2, e, o, off, m + 1, n),
{
    assert forall|p: int| 0 <= p < m + 1 implies #[trigger] pair2(s2, off, p) == (e[p], o[p]) by {
        if p < m {
            assert(pair2(s1, off, p) == (e[p], o[p]));
        }
    }
}

/// A byte unpack (`_mm_unpack{lo,hi}_epi8`, `vzip{1,2}q_u8`) by pairs.
proof fn lemma_unpack8(a: Seq<u8>, b: Seq<u8>)
    requires
        a.len() == 16, b.len() == 16,
    ensures
        unpacklo8_lanes(a, b).len() == 16,
        unpackhi8_lanes(a, b).len() == 16,
        forall|q: int| 0 <= q < 8 ==> #[trigger] pair2(unpacklo8_lanes(a, b), 0, q) == (a[q], b[q]),
        forall|q: int| 0 <= q < 8 ==> #[trigger] pair2(unpackhi8_lanes(a, b), 0, q) == (a[8 + q], b[8 + q]),
{
    assert forall|q: int| 0 <= q < 8 implies #[trigger] pair2(unpacklo8_lanes(a, b), 0, q) == (a[q], b[q]) by {
        assert(q == 0 || q == 1 || q == 2 || q == 3 || q == 4 || q == 5 || q == 6 || q == 7);
    }
    assert forall|q: int| 0 <= q < 8 implies #[trigger] pair2(unpackhi8_lanes(a, b), 0, q) == (a[8 + q], b[8 + q]) by {
        assert(q == 0 || q == 1 || q == 2 || q == 3 || q == 4 || q == 5 || q == 6 || q == 7);
    }
}

/// Sixteen more pairs, stored as the two unpacks of sixteen bytes of
/// each input.
proof fn lemma_interleave16(
    s0: Seq<u8>, s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>, e: Seq<u8>, o: Seq<u8>, off: int, m: int, n: int,
    a: Seq<u8>, b: Seq<u8>,
)
    requires
        0 <= off, 0 <= m, m + 16 <= n,
        n <= e.len(), n <= o.len(),
        off + 2 * n <= s0.len(),
        interleaved(s0, s1, e, o, off, m, n),
        a == e.subrange(m, m + 16),
        b == o.subrange(m, m + 16),
        s2 == s1.subrange(0, off + 2 * m) + unpacklo8_lanes(a, b) + s1.subrange(off + 2 * m + 16, s1.len() as int),
        s3 == s2.subrange(0, off + 2 * m + 16) + unpackhi8_lanes(a, b) + s2.subrange(
            off + 2 * m + 32,
            s2.len() as int,
        ),
    ensures
        interleaved(s0, s3, e, o, off, m + 16, n),
{
    let lo = unpacklo8_lanes(a, b);
    let hi = unpackhi8_lanes(a, b);
    lemma_unpack8(a, b);
    assert(s2.len() == s1.len());
    assert(s3.len() == s1.len());
    assert forall|p: int| 0 <= p < m + 16 implies #[trigger] pair2(s3, off, p) == (e[p], o[p]) by {
        let i = off + 2 * p;
        if p < m {
            assert(pair2(s1, off, p) == (e[p], o[p]));
            assert(s3[i] == s1[i] && s3[i + 1] == s1[i + 1]);
        } else if p < m + 8 {
            let q = p - m;
            assert(pair2(lo, 0, q) == (a[q], b[q]));
            assert(s3[i] == lo[2 * q] && s3[i + 1] == lo[2 * q + 1]);
        } else {
            let q = p - m - 8;
            assert(pair2(hi, 0, q) == (a[8 + q], b[8 + q]));
            assert(s3[i] == hi[2 * q] && s3[i + 1] == hi[2 * q + 1]);
        }
    }
    assert forall|i: int| 0 <= i < s3.len() && !(off <= i < off + 2 * n) implies #[trigger] s3[i] == s0[i] by {
        assert(s3[i] == s2[i]);
        assert(s2[i] == s1[i]);
    }
}

/// One more four-byte pixel, stored by bytes.
proof fn lemma_pack1(
    s0: Seq<u8>, s1: Seq<u8>, s2: Seq<u8>, c0: Seq<u8>, c1: Seq<u8>, c2: Seq<u8>, c3: Seq<u8>, oo: int, j: int,
    n: int,
)
    requires
        0 <= oo, 0 <= j < n,
        oo + 4 * n <= s0.len(),
        packed4(s0, s1, c0, c1, c2, c3, oo, j, n),
        s2 == s1.update(oo + 4 * j, c0[j]).update(oo + 4 * j + 1, c1[j]).update(oo + 4 * j + 2, c2[j]).update(
            oo + 4 * j + 3,
            c3[j],
        ),
    ensures
        packed4(s0, s2, c0, c1, c2, c3, oo, j + 1, n),
{
    assert forall|p: int| 0 <= p < j + 1 implies #[trigger] px4(s2, oo, p) == (c0[p], c1[p], c2[p], c3[p]) by {
        if p < j {
            assert(px4(s1, oo, p) == (c0[p], c1[p], c2[p], c3[p]));
        }
    }
}

/// Two rounds of byte unpacks interleave four vectors: the four results
/// hold pixels 0-3, 4-7, 8-11 and 12-15.
proof fn lemma_shuffle4(x0: Seq<u8>, x1: Seq<u8>, x2: Seq<u8>, x3: Seq<u8>)
    requires
        x0.len() == 16, x1.len() == 16, x2.len() == 16, x3.len() == 16,
    ensures
        ({
            let y0 = unpacklo8_lanes(x0, x2);
            let y1 = unpackhi8_lanes(x0, x2);
            let y2 = unpacklo8_lanes(x1, x3);
            let y3 = unpackhi8_lanes(x1, x3);
            &&& unpacklo8_lanes(y0, y2).len() == 16
            &&& unpackhi8_lanes(y0, y2).len() == 16
            &&& unpacklo8_lanes(y1, y3).len() == 16
            &&& unpackhi8_lanes(y1, y3).len() == 16
            &&& forall|r: int| 0 <= r < 4 ==> #[trigger] px4(unpacklo8_lanes(y0, y2), 0, r) == (x0[r], x1[r], x2[r], x3[r])
            &&& forall|r: int| 0 <= r < 4 ==> #[trigger] px4(unpackhi8_lanes(y0, y2), 0, r) == (x0[4 + r], x1[4 + r], x2[4 + r], x3[4 + r])
            &&& forall|r: int| 0 <= r < 4 ==> #[trigger] px4(unpacklo8_lanes(y1, y3), 0, r) == (x0[8 + r], x1[8 + r], x2[8 + r], x3[8 + r])
            &&& forall|r: int| 0 <= r < 4 ==> #[trigger] px4(unpackhi8_lanes(y1, y3), 0, r) == (x0[12 + r], x1[12 + r], x2[12 + r], x3[12 + r])
        }),
{
    let y0 = unpacklo8_lanes(x0, x2);
    let y1 = unpackhi8_lanes(x0, x2);
    let y2 = unpacklo8_lanes(x1, x3);
    let y3 = unpackhi8_lanes(x1, x3);
    lemma_unpack8(x0, x2);
    lemma_unpack8(x1, x3);
    lemma_unpack8(y0, y2);
    lemma_unpack8(y1, y3);
    let o0 = unpacklo8_lanes(y0, y2);
    let o1 = unpackhi8_lanes(y0, y2);
    let o2 = unpacklo8_lanes(y1, y3);
    let o3 = unpackhi8_lanes(y1, y3);
    assert forall|r: int| 0 <= r < 4 implies #[trigger] px4(o0, 0, r) == (x0[r], x1[r], x2[r], x3[r]) by {
        assert(pair2(o0, 0, 2 * r) == (y0[2 * r], y2[2 * r]));
        assert(pair2(o0, 0, 2 * r + 1) == (y0[2 * r + 1], y2[2 * r + 1]));
        assert(pair2(y0, 0, r) == (x0[r], x2[r]));
        assert(pair2(y2, 0, r) == (x1[r], x3[r]));
    }
    assert forall|r: int| 0 <= r < 4 implies #[trigger] px4(o1, 0, r) == (x0[4 + r], x1[4 + r], x2[4 + r], x3[4 + r]) by {
        assert(pair2(o1, 0, 2 * r) == (y0[8 + 2 * r], y2[8 + 2 * r]));
        assert(pair2(o1, 0, 2 * r + 1) == (y0[8 + 2 * r + 1], y2[8 + 2 * r + 1]));
        assert(pair2(y0, 0, 4 + r) == (x0[4 + r], x2[4 + r]));
        assert(pair2(y2, 0, 4 + r) == (x1[4 + r], x3[4 + r]));
    }
    assert forall|r: int| 0 <= r < 4 implies #[trigger] px4(o2, 0, r) == (x0[8 + r], x1[8 + r], x2[8 + r], x3[8 + r]) by {
        assert(pair2(o2, 0, 2 * r) == (y1[2 * r], y3[2 * r]));
        assert(pair2(o2, 0, 2 * r + 1) == (y1[2 * r + 1], y3[2 * r + 1]));
        assert(pair2(y1, 0, r) == (x0[8 + r], x2[8 + r]));
        assert(pair2(y3, 0, r) == (x1[8 + r], x3[8 + r]));
    }
    assert forall|r: int| 0 <= r < 4 implies #[trigger] px4(o3, 0, r) == (x0[12 + r], x1[12 + r], x2[12 + r], x3[12 + r]) by {
        assert(pair2(o3, 0, 2 * r) == (y1[8 + 2 * r], y3[8 + 2 * r]));
        assert(pair2(o3, 0, 2 * r + 1) == (y1[8 + 2 * r + 1], y3[8 + 2 * r + 1]));
        assert(pair2(y1, 0, 4 + r) == (x0[12 + r], x2[12 + r]));
        assert(pair2(y3, 0, 4 + r) == (x1[12 + r], x3[12 + r]));
    }
}

/// Four more four-byte pixels, stored as one vector that holds them.
proof fn lemma_pack4px(
    s0: Seq<u8>, s1: Seq<u8>, s2: Seq<u8>, c0: Seq<u8>, c1: Seq<u8>, c2: Seq<u8>, c3: Seq<u8>, oo: int, j: int,
    n: int, q: Seq<u8>,
)
    requires
        0 <= oo, 0 <= j, j + 4 <= n,
        oo + 4 * n <= s0.len(),
        packed4(s0, s1, c0, c1, c2, c3, oo, j, n),
        q.len() == 16,
        forall|r: int| 0 <= r < 4 ==> #[trigger] px4(q, 0, r) == (c0[j + r], c1[j + r], c2[j + r], c3[j + r]),
        s2 == s1.subrange(0, oo + 4 * j) + q + s1.subrange(oo + 4 * j + 16, s1.len() as int),
    ensures
        packed4(s0, s2, c0, c1, c2, c3, oo, j + 4, n),
{
    let o = oo + 4 * j;
    assert(s2.len() == s1.len());
    assert forall|p: int| 0 <= p < j + 4 implies #[trigger] px4(s2, oo, p) == (c0[p], c1[p], c2[p], c3[p]) by {
        let i = oo + 4 * p;
        if p < j {
            assert(px4(s1, oo, p) == (c0[p], c1[p], c2[p], c3[p]));
            assert(s2[i] == s1[i] && s2[i + 1] == s1[i + 1] && s2[i + 2] == s1[i + 2] && s2[i + 3] == s1[i + 3]);
        } else {
            let r = p - j;
            assert(px4(q, 0, r) == (c0[j + r], c1[j + r], c2[j + r], c3[j + r]));
            assert(s2[i] == q[4 * r] && s2[i + 1] == q[4 * r + 1] && s2[i + 2] == q[4 * r + 2] && s2[i + 3] == q[4 * r + 3]);
        }
    }
    assert forall|i: int| 0 <= i < s2.len() && !(oo <= i < oo + 4 * n) implies #[trigger] s2[i] == s0[i] by {
        assert(s2[i] == s1[i]);
    }
}

/// Sixteen more four-byte pixels, stored as the four results of
/// `lemma_shuffle4` on sixteen bytes of each channel.
proof fn lemma_pack16(
    s0: Seq<u8>, s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>, s4: Seq<u8>, s5: Seq<u8>,
    c0: Seq<u8>, c1: Seq<u8>, c2: Seq<u8>, c3: Seq<u8>, oo: int, j: int, n: int,
    x0: Seq<u8>, x1: Seq<u8>, x2: Seq<u8>, x3: Seq<u8>,
)
    requires
        0 <= oo, 0 <= j, j + 16 <= n,
        n <= c0.len(), n <= c1.len(), n <= c2.len(), n <= c3.len(),
        oo + 4 * n <= s0.len(),
        packed4(s0, s1, c0, c1, c2, c3, oo, j, n),
        x0 == c0.subrange(j, j + 16),
        x1 == c1.subrange(j, j + 16),
        x2 == c2.subrange(j, j + 16),
        x3 == c3.subrange(j, j + 16),
        ({
            let y0 = unpacklo8_lanes(x0, x2);
            let y1 = unpackhi8_lanes(x0, x2);
            let y2 = unpacklo8_lanes(x1, x3);
            let y3 = unpackhi8_lanes(x1, x3);
            let o = oo + 4 * j;
            let l = s1.len() as int;
            &&& s2 == s1.subrange(0, o) + unpacklo8_lanes(y0, y2) + s1.subrange(o + 16, l)
            &&& s3 == s2.subrange(0, o + 16) + unpackhi8_lanes(y0, y2) + s2.subrange(o + 32, l)
            &&& s4 == s3.subrange(0, o + 32) + unpacklo8_lanes(y1, y3) + s3.subrange(o + 48, l)
            &&& s5 == s4.subrange(0, o + 48) + unpackhi8_lanes(y1, y3) + s4.subrange(o + 64, l)
        }),
    ensures
        packed4(s0, s5, c0, c1, c2, c3, oo, j + 16, n),
{
    let y0 = unpacklo8_lanes(x0, x2);
    let y1 = unpackhi8_lanes(x0, x2);
    let y2 = unpacklo8_lanes(x1, x3);
    let y3 = unpackhi8_lanes(x1, x3);
    let o0 = unpacklo8_lanes(y0, y2);
    let o1 = unpackhi8_lanes(y0, y2);
    let o2 = unpacklo8_lanes(y1, y3);
    let o3 = unpackhi8_lanes(y1, y3);
    lemma_shuffle4(x0, x1, x2, x3);
    assert forall|r: int| 0 <= r < 4 implies #[trigger] px4(o0, 0, r) == (c0[j + r], c1[j + r], c2[j + r], c3[j + r]) by {
        assert(x0[r] == c0[j + r] && x1[r] == c1[j + r] && x2[r] == c2[j + r] && x3[r] == c3[j + r]);
    }
    lemma_pack4px(s0, s1, s2, c0, c1, c2, c3, oo, j, n, o0);
    assert forall|r: int| 0 <= r < 4 implies #[trigger] px4(o1, 0, r) == (c0[j + 4 + r], c1[j + 4 + r], c2[j + 4 + r], c3[j + 4 + r]) by {
        assert(x0[4 + r] == c0[j + 4 + r] && x1[4 + r] == c1[j + 4 + r] && x2[4 + r] == c2[j + 4 + r] && x3[4 + r] == c3[j + 4 + r]);
    }
    lemma_pack4px(s0, s2, s3, c0, c1, c2, c3, oo, j + 4, n, o1);
    assert forall|r: int| 0 <= r < 4 implies #[trigger] px4(o2, 0, r) == (c0[j + 8 + r], c1[j + 8 + r], c2[j + 8 + r], c3[j + 8 + r]) by {
        assert(x0[8 + r] == c0[j + 8 + r] && x1[8 + r] == c1[j + 8 + r] && x2[8 + r] == c2[j + 8 + r] && x3[8 + r] == c3[j + 8 + r]);
    }
    lemma_pack4px(s0, s3, s4, c0, c1, c2, c3, oo, j + 8, n, o2);
    assert forall|r: int| 0 <= r < 4 implies #[trigger] px4(o3, 0, r) == (c0[j + 12 + r], c1[j + 12 + r], c2[j + 12 + r], c3[j + 12 + r]) by {
        assert(x0[12 + r] == c0[j + 12 + r] && x1[12 + r] == c1[j + 12 + r] && x2[12 + r] == c2[j + 12 + r] && x3[12 + r] == c3[j + 12 + r]);
    }
    lemma_pack4px(s0, s4, s5, c0, c1, c2, c3, oo, j + 12, n, o3);
}

/// The byte unpacks of thirty-two bytes, by pairs: `lemma_unpack8` within
/// each sixteen-byte half.
proof fn lemma_unpack8x(a: Seq<u8>, b: Seq<u8>)
    requires
        a.len() == 32, b.len() == 32,
    ensures
        unpacklo8_lanes(a, b).len() == 32,
        unpackhi8_lanes(a, b).len() == 32,
        forall|m: int| 0 <= m < 16 ==> #[trigger] pair2(unpacklo8_lanes(a, b), 0, m)
            == (a[(m / 8) * 16 + m % 8], b[(m / 8) * 16 + m % 8]),
        forall|m: int| 0 <= m < 16 ==> #[trigger] pair2(unpackhi8_lanes(a, b), 0, m)
            == (a[(m / 8) * 16 + 8 + m % 8], b[(m / 8) * 16 + 8 + m % 8]),
{
    assert forall|m: int| 0 <= m < 16 implies #[trigger] pair2(unpacklo8_lanes(a, b), 0, m)
        == (a[(m / 8) * 16 + m % 8], b[(m / 8) * 16 + m % 8]) by {
        assert((2 * m) / 16 == m / 8 && ((2 * m) % 16) / 2 == m % 8);
        assert((2 * m + 1) / 16 == m / 8 && ((2 * m + 1) % 16) / 2 == m % 8);
    }
    assert forall|m: int| 0 <= m < 16 implies #[trigger] pair2(unpackhi8_lanes(a, b), 0, m)
        == (a[(m / 8) * 16 + 8 + m % 8], b[(m / 8) * 16 + 8 + m % 8]) by {
        assert((2 * m) / 16 == m / 8 && ((2 * m) % 16) / 2 == m % 8);
        assert((2 * m + 1) / 16 == m / 8 && ((2 * m + 1) % 16) / 2 == m % 8);
    }
}

/// A 16-bit unpack of thirty-two bytes (the low one for `h == 0`, the high
/// one for `h == 4`), by four-byte groups: two bytes of `a`, then two of `b`.
proof fn lemma_unpack16x(a: Seq<u8>, b: Seq<u8>, t: Seq<u8>, h: int)
    requires
        a.len() == 32, b.len() == 32, t.len() == 32,
        h == 0 || h == 4,
        h == 0 ==> u16s(t) == unpacklo16_lanes(u16s(a), u16s(b)),
        h == 4 ==> u16s(t) == unpackhi16_lanes(u16s(a), u16s(b)),
    ensures
        forall|q: int| 0 <= q < 8 ==> #[trigger] px4(t, 0, q) == ({
            let m = (q / 4) * 8 + h + q % 4;
            (a[2 * m], a[2 * m + 1], b[2 * m], b[2 * m + 1])
        }),
{
    assert forall|q: int| 0 <= q < 8 implies #[trigger] px4(t, 0, q) == ({
        let m = (q / 4) * 8 + h + q % 4;
        (a[2 * m], a[2 * m + 1], b[2 * m], b[2 * m + 1])
    }) by {
        let m = (q / 4) * 8 + h + q % 4;
        assert((2 * q) / 8 == q / 4 && ((2 * q) % 8) / 2 == q % 4 && (2 * q) % 2 == 0);
        assert((2 * q + 1) / 8 == q / 4 && ((2 * q + 1) % 8) / 2 == q % 4 && (2 * q + 1) % 2 == 1);
        assert(u16s(t)[2 * q] == u16s(a)[m]);
        assert(u16s(t)[2 * q + 1] == u16s(b)[m]);
        lemma_u16_lane_bytes(t, 2 * q);
        lemma_u16_lane_bytes(t, 2 * q + 1);
        lemma_u16_lane_bytes(a, m);
        lemma_u16_lane_bytes(b, m);
    }
}

/// `t` holds eight four-byte pixels of the channels `x0` to `x3`: four
/// from offset `h` of each sixteen-byte half.
pub open spec fn shuffled8(x0: Seq<u8>, x1: Seq<u8>, x2: Seq<u8>, x3: Seq<u8>, t: Seq<u8>, h: int) -> bool {
    forall|q: int| 0 <= q < 8 ==> #[trigger] px4(t, 0, q) == ({
        let s = (q / 4) * 16 + h + q % 4;
        (x0[s], x1[s], x2[s], x3[s])
    })
}

/// A round of byte unpacks (low for `h8 == 0`, high for `h8 == 8`) and one
/// of 16-bit unpacks (low for `h16 == 0`, high for `h16 == 4`) interleave
/// four 32-byte vectors within their halves.
proof fn lemma_shuffle8(
    x0: Seq<u8>, x1: Seq<u8>, x2: Seq<u8>, x3: Seq<u8>, p: Seq<u8>, r: Seq<u8>, t: Seq<u8>, h8: int, h16: int,
)
    requires
        x0.len() == 32, x1.len() == 32, x2.len() == 32, x3.len() == 32, t.len() == 32,
        h8 == 0 || h8 == 8,
        h16 == 0 || h16 == 4,
        h8 == 0 ==> p == unpacklo8_lanes(x0, x1) && r == unpacklo8_lanes(x2, x3),
        h8 == 8 ==> p == unpackhi8_lanes(x0, x1) && r == unpackhi8_lanes(x2, x3),
        h16 == 0 ==> u16s(t) == unpacklo16_lanes(u16s(p), u16s(r)),
        h16 == 4 ==> u16s(t) == unpackhi16_lanes(u16s(p), u16s(r)),
    ensures
        shuffled8(x0, x1, x2, x3, t, h8 + h16),
{
    lemma_unpack8x(x0, x1);
    lemma_unpack8x(x2, x3);
    lemma_unpack16x(p, r, t, h16);
    assert forall|q: int| 0 <= q < 8 implies #[trigger] px4(t, 0, q) == ({
        let s = (q / 4) * 16 + h8 + h16 + q % 4;
        (x0[s], x1[s], x2[s], x3[s])
    }) by {
        let m = (q / 4) * 8 + h16 + q % 4;
        let s = (q / 4) * 16 + h8 + h16 + q % 4;
        assert(m / 8 == q / 4 && m % 8 == h16 + q % 4);
        assert(px4(t, 0, q) == (p[2 * m], p[2 * m + 1], r[2 * m], r[2 * m + 1]));
        assert(pair2(p, 0, m) == (x0[s], x1[s]));
        assert(pair2(r, 0, m) == (x2[s], x3[s]));
    }
}

/// Eight more four-byte pixels, stored as one vector that holds them.
proof fn lemma_pack8px(
    s0: Seq<u8>, s1: Seq<u8>, s2: Seq<u8>, c0: Seq<u8>, c1: Seq<u8>, c2: Seq<u8>, c3: Seq<u8>, oo: int, j: int,
    n: int, q: Seq<u8>,
)
    requires
        0 <= oo, 0 <= j, j + 8 <= n,
        oo + 4 * n <= s0.len(),
        packed4(s0, s1, c0, c1, c2, c3, oo, j, n),
        q.len() == 32,
        forall|r: int| 0 <= r < 8 ==> #[trigger] px4(q, 0, r) == (c0[j + r], c1[j + r], c2[j + r], c3[j + r]),
        s2 == s1.subrange(0, oo + 4 * j) + q + s1.subrange(oo + 4 * j + 32, s1.len() as int),
    ensures
        packed4(s0, s2, c0, c1, c2, c3, oo, j + 8, n),
{
    assert(s2.len() == s1.len());
    assert forall|p: int| 0 <= p < j + 8 implies #[trigger] px4(s2, oo, p) == (c0[p], c1[p], c2[p], c3[p]) by {
        let i = oo + 4 * p;
        if p < j {
            assert(px4(s1, oo, p) == (c0[p], c1[p], c2[p], c3[p]));
            assert(s2[i] == s1[i] && s2[i + 1] == s1[i + 1] && s2[i + 2] == s1[i + 2] && s2[i + 3] == s1[i + 3]);
        } else {
            let r = p - j;
            assert(px4(q, 0, r) == (c0[j + r], c1[j + r], c2[j + r], c3[j + r]));
            assert(s2[i] == q[4 * r] && s2[i + 1] == q[4 * r + 1] && s2[i + 2] == q[4 * r + 2] && s2[i + 3] == q[4 * r + 3]);
        }
    }
    assert forall|i: int| 0 <= i < s2.len() && !(oo <= i < oo + 4 * n) implies #[trigger] s2[i] == s0[i] by {
        assert(s2[i] == s1[i]);
    }
}

/// Eight pixels from the low or the high halves (`k` 0 or 4) of two
/// vectors that each hold four per half.
proof fn lemma_halves8(
    x0: Seq<u8>, x1: Seq<u8>, x2: Seq<u8>, x3: Seq<u8>, ta: Seq<u8>, tb: Seq<u8>, h: int, k: int, q: Seq<u8>,
)
    requires
        ta.len() == 32, tb.len() == 32,
        h == 0 || h == 8,
        k == 0 || k == 4,
        shuffled8(x0, x1, x2, x3, ta, h),
        shuffled8(x0, x1, x2, x3, tb, h + 4),
        q == ta.subrange(4 * k, 4 * k + 16) + tb.subrange(4 * k, 4 * k + 16),
    ensures
        q.len() == 32,
        forall|r: int| 0 <= r < 8 ==> #[trigger] px4(q, 0, r)
            == (x0[4 * k + h + r], x1[4 * k + h + r], x2[4 * k + h + r], x3[4 * k + h + r]),
{
    assert forall|r: int| 0 <= r < 8 implies #[trigger] px4(q, 0, r)
        == (x0[4 * k + h + r], x1[4 * k + h + r], x2[4 * k + h + r], x3[4 * k + h + r]) by {
        if r < 4 {
            let s = ((k + r) / 4) * 16 + h + (k + r) % 4;
            assert(px4(ta, 0, k + r) == (x0[s], x1[s], x2[s], x3[s]));
            assert(q[4 * r] == ta[4 * (k + r)] && q[4 * r + 1] == ta[4 * (k + r) + 1]);
            assert(q[4 * r + 2] == ta[4 * (k + r) + 2] && q[4 * r + 3] == ta[4 * (k + r) + 3]);
        } else {
            let w = k + r - 4;
            let s = (w / 4) * 16 + h + 4 + w % 4;
            assert(px4(tb, 0, w) == (x0[s], x1[s], x2[s], x3[s]));
            assert(q[4 * r] == tb[4 * w] && q[4 * r + 1] == tb[4 * w + 1]);
            assert(q[4 * r + 2] == tb[4 * w + 2] && q[4 * r + 3] == tb[4 * w + 3]);
        }
    }
}

/// Thirty-two more four-byte pixels, stored as the halves of the four
/// results of `lemma_shuffle8` on thirty-two bytes of each channel.
proof fn lemma_pack32(
    s0: Seq<u8>, s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>, s4: Seq<u8>, s5: Seq<u8>,
    c0: Seq<u8>, c1: Seq<u8>, c2: Seq<u8>, c3: Seq<u8>, oo: int, j: int, n: int,
    x0: Seq<u8>, x1: Seq<u8>, x2: Seq<u8>, x3: Seq<u8>, t0: Seq<u8>, t1: Seq<u8>, t2: Seq<u8>, t3: Seq<u8>,
)
    requires
        0 <= oo, 0 <= j, j + 32 <= n,
        n <= c0.len(), n <= c1.len(), n <= c2.len(), n <= c3.len(),
        oo + 4 * n <= s0.len(),
        packed4(s0, s1, c0, c1, c2, c3, oo, j, n),
        x0 == c0.subrange(j, j + 32),
        x1 == c1.subrange(j, j + 32),
        x2 == c2.subrange(j, j + 32),
        x3 == c3.subrange(j, j + 32),
        t0.len() == 32, t1.len() == 32, t2.len() == 32, t3.len() == 32,
        shuffled8(x0, x1, x2, x3, t0, 0),
        shuffled8(x0, x1, x2, x3, t1, 4),
        shuffled8(x0, x1, x2, x3, t2, 8),
        shuffled8(x0, x1, x2, x3, t3, 12),
        ({
            let o = oo + 4 * j;
            let l = s1.len() as int;
            &&& s2 == s1.subrange(0, o) + (t0.subrange(0, 16) + t1.subrange(0, 16)) + s1.subrange(o + 32, l)
            &&& s3 == s2.subrange(0, o + 32) + (t2.subrange(0, 16) + t3.subrange(0, 16)) + s2.subrange(o + 64, l)
            &&& s4 == s3.subrange(0, o + 64) + (t0.subrange(16, 32) + t1.subrange(16, 32)) + s3.subrange(o + 96, l)
            &&& s5 == s4.subrange(0, o + 96) + (t2.subrange(16, 32) + t3.subrange(16, 32)) + s4.subrange(o + 128, l)
        }),
    ensures
        packed4(s0, s5, c0, c1, c2, c3, oo, j + 32, n),
{
    let o0 = t0.subrange(0, 16) + t1.subrange(0, 16);
    let o1 = t2.subrange(0, 16) + t3.subrange(0, 16);
    let o2 = t0.subrange(16, 32) + t1.subrange(16, 32);
    let o3 = t2.subrange(16, 32) + t3.subrange(16, 32);
    lemma_halves8(x0, x1, x2, x3, t0, t1, 0, 0, o0);
    lemma_halves8(x0, x1, x2, x3, t2, t3, 8, 0, o1);
    lemma_halves8(x0, x1, x2, x3, t0, t1, 0, 4, o2);
    lemma_halves8(x0, x1, x2, x3, t2, t3, 8, 4, o3);
    assert forall|r: int| 0 <= r < 8 implies #[trigger] px4(o0, 0, r) == (c0[j + r], c1[j + r], c2[j + r], c3[j + r]) by {
        assert(x0[r] == c0[j + r] && x1[r] == c1[j + r] && x2[r] == c2[j + r] && x3[r] == c3[j + r]);
    }
    lemma_pack8px(s0, s1, s2, c0, c1, c2, c3, oo, j, n, o0);
    assert forall|r: int| 0 <= r < 8 implies #[trigger] px4(o1, 0, r) == (c0[j + 8 + r], c1[j + 8 + r], c2[j + 8 + r], c3[j + 8 + r]) by {
        assert(x0[8 + r] == c0[j + 8 + r] && x1[8 + r] == c1[j + 8 + r] && x2[8 + r] == c2[j + 8 + r] && x3[8 + r] == c3[j + 8 + r]);
    }
    lemma_pack8px(s0, s2, s3, c0, c1, c2, c3, oo, j + 8, n, o1);
    assert forall|r: int| 0 <= r < 8 implies #[trigger] px4(o2, 0, r) == (c0[j + 16 + r], c1[j + 16 + r], c2[j + 16 + r], c3[j + 16 + r]) by {
        assert(x0[16 + r] == c0[j + 16 + r] && x1[16 + r] == c1[j + 16 + r] && x2[16 + r] == c2[j + 16 + r] && x3[16 + r] == c3[j + 16 + r]);
    }
    lemma_pack8px(s0, s3, s4, c0, c1, c2, c3, oo, j + 16, n, o2);
    assert forall|r: int| 0 <= r < 8 implies #[trigger] px4(o3, 0, r) == (c0[j + 24 + r], c1[j + 24 + r], c2[j + 24 + r], c3[j + 24 + r]) by {
        assert(x0[24 + r] == c0[j + 24 + r] && x1[24 + r] == c1[j + 24 + r] && x2[24 + r] == c2[j + 24 + r] && x3[24 + r] == c3[j + 24 + r]);
    }
    lemma_pack8px(s0, s4, s5, c0, c1, c2, c3, oo, j + 24, n, o3);
}

/// One more three-byte pixel, stored by bytes.
proof fn lemma_pack3(
    s0: Seq<u8>, s1: Seq<u8>, s2: Seq<u8>, sr: Seq<u8>, sg: Seq<u8>, sb: Seq<u8>, oo: int, j: int, n: int,
    pr: int, pg: int, pb: int,
)
    requires
        0 <= oo, 0 <= j < n,
        oo + 3 * n <= s0.len(),
        0 <= pr < 3, 0 <= pg < 3, 0 <= pb < 3,
        pr != pg, pg != pb, pr != pb,
        packed3(s0, s1, sr, sg, sb, oo, j, n, pr, pg, pb),
        s2 == s1.update(oo + 3 * j + pr, sr[j]).update(oo + 3 * j + pg, sg[j]).update(oo + 3 * j + pb, sb[j]),
    ensures
        packed3(s0, s2, sr, sg, sb, oo, j + 1, n, pr, pg, pb),
{
    assert forall|p: int| 0 <= p < j + 1 implies #[trigger] px3(s2, oo, p, pr, pg, pb) == (sr[p], sg[p], sb[p]) by {
        if p < j {
            assert(px3(s1, oo, p, pr, pg, pb) == (sr[p], sg[p], sb[p]));
        }
    }
}

/// `MultHi`, `v * c >> 8`, in 16-bit lanes: with `c = 256 * ch + cl`, it is
/// `v * ch + (v * cl >> 8)`, and both products fit 16 bits.
#[inline(always)]
fn mulhi(v: u8, c: u16) -> (r: u16)
    ensures
        r as int == (v as int * c as int) / 256,
{
    let ch = c / 256;
    let cl = c % 256;
    let v16 = v as u16;
    proof {
        assert(v16 * ch < 0x1_0000 && v16 * cl < 0x1_0000) by (nonlinear_arith)
            requires v16 < 256, ch < 256, cl < 256;
        assert(v * c == 256 * (v * ch) + v * cl) by (nonlinear_arith)
            requires c == 256 * ch + cl;
        assert((256 * (v * ch) + v * cl) / 256 == v * ch + (v * cl) / 256) by (nonlinear_arith)
            requires v * ch >= 0, v * cl >= 0;
        assert(v * ch + (v * cl) / 256 < 0x1_0000) by (nonlinear_arith)
            requires v < 256, ch < 256, cl < 256;
    }
    v16 * ch + (v16 * cl) / 256
}

/// A 16-bit lane, shifted down 6 bits and saturated to a byte.
#[inline(always)]
fn pack6(x: i16) -> (r: u32)
    ensures
        r < 256,
        r as int == yuv_clip8(x as int),
{
    let c = if x < 0 { 0 } else { x };
    let c = c / 64;
    (if c > 255 { 255 } else { c }) as u32
}

/// `VP8YuvToRgb` (`src/dsp/yuv.h`), packed as ARGB with alpha `a`, in the
/// 16-bit lanes of `ConvertYUV444ToRGB_SSE2`: the same values, since every
/// intermediate fits (the bounds below), and it vectorizes.
#[inline(always)]
pub fn yuv_to_argb(y: u8, u: u8, v: u8, a: u8) -> (c: u32)
    ensures
        c as int == argb_word(a as int, yuv_r(y as int, v as int), yuv_g(y as int, u as int, v as int), yuv_b(y as int, u as int)),
{
    let (r, g, b) = yuv_to_rgb(y, u, v);
    argb(a, r, g, b)
}

/// `a, r, g, b` packed as ARGB.
#[inline(always)]
fn argb(a: u8, r: u8, g: u8, b: u8) -> (c: u32)
    ensures
        c as int == argb_word(a as int, r as int, g as int, b as int),
{
    proof {
        assert(((a as u32) << 24u32) | ((r as u32) << 16u32) | ((g as u32) << 8u32) | (b as u32) == (a as u32)
            * 0x100_0000 + (r as u32) * 0x1_0000 + (g as u32) * 0x100 + (b as u32)) by (bit_vector);
    }
    ((a as u32) << 24u32) | ((r as u32) << 16u32) | ((g as u32) << 8u32) | (b as u32)
}

/// `VP8YuvToRgb`'s three channels.
#[inline(always)]
fn yuv_to_rgb(y: u8, u: u8, v: u8) -> (c: (u8, u8, u8))
    ensures
        c.0 as int == yuv_r(y as int, v as int),
        c.1 as int == yuv_g(y as int, u as int, v as int),
        c.2 as int == yuv_b(y as int, u as int),
{
    let y1 = mulhi(y, 19077);
    let r0 = mulhi(v, 26149);
    let g0 = mulhi(u, 6419);
    let g1 = mulhi(v, 13320);
    let b0 = mulhi(u, 33050);
    proof {
        assert(y1 <= 19002) by (nonlinear_arith)
            requires y1 as int == (y as int * 19077) / 256, y < 256;
        assert(r0 <= 26046) by (nonlinear_arith)
            requires r0 as int == (v as int * 26149) / 256, v < 256;
        assert(g0 <= 6393) by (nonlinear_arith)
            requires g0 as int == (u as int * 6419) / 256, u < 256;
        assert(g1 <= 13267) by (nonlinear_arith)
            requires g1 as int == (v as int * 13320) / 256, v < 256;
        assert(b0 <= 32921) by (nonlinear_arith)
            requires b0 as int == (u as int * 33050) / 256, u < 256;
    }
    let r = pack6((y1 as i16 - 14234) + r0 as i16);
    let g = pack6((y1 as i16 + 8708) - (g0 as i16 + g1 as i16));
    // Unsigned: `b1` can pass 32767. Saturating at 0, as `_mm_subs_epu16`.
    let b1 = y1 + b0;
    let b2 = if b1 < 17685 { 0 } else { b1 - 17685 };
    let b3 = b2 / 64;
    let b = if b3 > 255 { 255 } else { b3 };
    (r as u8, g as u8, b as u8)
}

/// One line of fancy-upsampled chroma, `s[0..len]`: from the nearer chroma
/// line at `no` (weight 3/4) and the farther one at `fo` (1/4),
/// horizontally likewise (`UPSAMPLE_FUNC`'s `LOAD_UV` arithmetic).
fn upsample_chroma(c: &[u8], no: usize, fo: usize, s: &mut [u8], len: usize)
    requires
        len >= 1,
        len <= old(s)@.len(),
        no + (len + 1) / 2 <= c@.len(),
        fo + (len + 1) / 2 <= c@.len(),
    ensures
        final(s)@.len() == old(s)@.len(),
        fancy_row(final(s)@, c@, no as int, fo as int, len as int),
{
    proof {
        assert(c@.len() == c.len());
        assert(s@.len() == s.len());
    }
    let n0 = get(c, no) as u32;
    let f0 = get(c, fo) as u32;
    proof {
        lemma_fancy_bounds(n0 as int, n0 as int, f0 as int, f0 as int);
    }
    set(s, 0, ((3 * n0 + f0 + 2) / 4) as u8);
    let last_pair = (len - 1) / 2;
    let mut x: usize = 1;
    while x <= last_pair
        invariant
            1 <= x <= last_pair + 1,
            last_pair == (len - 1) / 2,
            len >= 1,
            len <= s@.len(),
            no + (len + 1) / 2 <= c@.len(),
            fo + (len + 1) / 2 <= c@.len(),
            s@.len() == old(s)@.len(),
            c@.len() <= usize::MAX,
            s@.len() <= usize::MAX,
            forall|j: int|
                0 <= j < 2 * x - 1 ==> (#[trigger] s@[j]) as int == fancy_line(c@, no as int, fo as int, len as int, j),
        decreases last_pair + 1 - x,
    {
        let tl = get(c, no + x - 1) as u16;
        let l = get(c, fo + x - 1) as u16;
        let t = get(c, no + x) as u16;
        let cc = get(c, fo + x) as u16;
        let avg = tl + t + l + cc + 8;
        let d12 = (avg + 2 * (t + l)) / 8;
        let d03 = (avg + 2 * (tl + cc)) / 8;
        proof {
            lemma_fancy_bounds(tl as int, t as int, l as int, cc as int);
            lemma_fancy_bounds(t as int, tl as int, cc as int, l as int);
            assert((d12 + tl) / 2 == fancy_line(c@, no as int, fo as int, len as int, 2 * x - 1));
            assert((d03 + t) / 2 == fancy_line(c@, no as int, fo as int, len as int, 2 * x as int));
        }
        set(s, 2 * x - 1, ((d12 + tl) / 2) as u8);
        set(s, 2 * x, ((d03 + t) / 2) as u8);
        x = x + 1;
    }
    if len % 2 == 0 {
        let tl = get(c, no + last_pair) as u32;
        let l = get(c, fo + last_pair) as u32;
        proof {
            lemma_fancy_bounds(tl as int, tl as int, l as int, l as int);
            assert((3 * tl + l + 2) / 4 == fancy_line(c@, no as int, fo as int, len as int, len - 1));
        }
        set(s, len - 1, ((3 * tl + l + 2) / 4) as u8);
    }
}

/// Writes `s[off + 2m] = e[m]` and `s[off + 2m + 1] = o[m]` for `m < n`:
/// sixteen pairs at a time with a byte unpack (SSE2) or `zip1`/`zip2`
/// (NEON), the rest one by one.
fn interleave2(e: &[u8], o: &[u8], s: &mut [u8], off: usize, n: usize)
    requires
        n <= e@.len(), n <= o@.len(),
        off + 2 * n <= old(s)@.len(),
    ensures
        final(s)@.len() == old(s)@.len(),
        interleaved(old(s)@, final(s)@, e@, o@, off as int, n as int, n as int),
{
    proof {
        assert(s@.len() == s.len());
    }
    let ghost s0 = s@;
    let mut m: usize = 0;
    if cfg!(target_arch = "aarch64") && has_neon() {
        while n - m >= 16
            invariant
                neon(),
                m <= n,
                n <= e@.len(), n <= o@.len(),
                off + 2 * n <= s@.len(),
                s@.len() == old(s)@.len(),
                s@.len() <= usize::MAX,
                s0 == old(s)@,
                interleaved(s0, s@, e@, o@, off as int, m as int, n as int),
            decreases n - m,
        {
            proof {
                assert(off + 2 * m + 32 <= off + 2 * n);
            }
            let ghost s1 = s@;
            let a = vld1q_u8_at(e, m);
            let b = vld1q_u8_at(o, m);
            vst1q_u8_at(s, off + 2 * m, vzip1q_u8(a, b));
            let ghost s2 = s@;
            vst1q_u8_at(s, off + 2 * m + 16, vzip2q_u8(a, b));
            proof {
                lemma_interleave16(s0, s1, s2, s@, e@, o@, off as int, m as int, n as int, n8(a), n8(b));
            }
            m = m + 16;
        }
    } else {
        // SAFETY: SSE2 is part of x86-64 (and emulated elsewhere).
        m = unsafe { interleave2_sse2(e, o, s, off, n) };
    }
    while m < n
        invariant
            m <= n,
            n <= e@.len(), n <= o@.len(),
            off + 2 * n <= s@.len(),
            s@.len() == old(s)@.len(),
            s@.len() <= usize::MAX,
            s0 == old(s)@,
            interleaved(s0, s@, e@, o@, off as int, m as int, n as int),
        decreases n - m,
    {
        proof {
            assert(off + 2 * m + 2 <= off + 2 * n);
        }
        let ghost s1 = s@;
        set(s, off + 2 * m, get(e, m));
        set(s, off + 2 * m + 1, get(o, m));
        proof {
            lemma_interleave1(s0, s1, s@, e@, o@, off as int, m as int, n as int);
        }
        m = m + 1;
    }
}

/// `interleave2`'s SSE2 loop: the pairs `0..r`, a multiple of sixteen.
fn interleave2_sse2(e: &[u8], o: &[u8], s: &mut [u8], off: usize, n: usize) -> (r: usize)
    requires
        n <= e@.len(), n <= o@.len(),
        off + 2 * n <= old(s)@.len(),
    ensures
        r <= n,
        final(s)@.len() == old(s)@.len(),
        interleaved(old(s)@, final(s)@, e@, o@, off as int, r as int, n as int),
{
    proof {
        assert(s@.len() == s.len());
    }
    let ghost s0 = s@;
    let mut m: usize = 0;
    while n - m >= 16
        invariant
            m <= n,
            n <= e@.len(), n <= o@.len(),
            off + 2 * n <= s@.len(),
            s@.len() == old(s)@.len(),
            s@.len() <= usize::MAX,
            s0 == old(s)@,
            interleaved(s0, s@, e@, o@, off as int, m as int, n as int),
        decreases n - m,
    {
        proof {
            assert(off + 2 * m + 32 <= off + 2 * n);
        }
        let ghost s1 = s@;
        let a = load128_u8(e, m);
        let b = load128_u8(o, m);
        store128_u8(s, off + 2 * m, _mm_unpacklo_epi8(a, b));
        let ghost s2 = s@;
        store128_u8(s, off + 2 * m + 16, _mm_unpackhi_epi8(a, b));
        proof {
            lemma_interleave16(s0, s1, s2, s@, e@, o@, off as int, m as int, n as int, b128(a), b128(b));
        }
        m = m + 16;
    }
    m
}

/// Pair `p` of a line's interior: `e[p]` and `o[p]` are pixels `2p + 1`
/// and `2p + 2` of `fancy_line(c, no, fo, len, ..)`.
pub open spec fn half_ok(c: Seq<u8>, no: int, fo: int, len: int, e: Seq<u8>, o: Seq<u8>, p: int) -> bool {
    &&& e[p] as int == fancy_line(c, no, fo, len, 2 * p + 1)
    &&& o[p] as int == fancy_line(c, no, fo, len, 2 * p + 2)
}

proof fn lemma_half_step(
    c: Seq<u8>, no: int, fo: int, len: int, e: Seq<u8>, o: Seq<u8>, e2: Seq<u8>, o2: Seq<u8>, m: int, ev: u8,
    ov: u8,
)
    requires
        0 <= m < e.len(), m < o.len(),
        forall|p: int| 0 <= p < m ==> #[trigger] half_ok(c, no, fo, len, e, o, p),
        e2 == e.update(m, ev),
        o2 == o.update(m, ov),
        ev as int == fancy_line(c, no, fo, len, 2 * m + 1),
        ov as int == fancy_line(c, no, fo, len, 2 * m + 2),
    ensures
        forall|p: int| 0 <= p < m + 1 ==> #[trigger] half_ok(c, no, fo, len, e2, o2, p),
{
    assert forall|p: int| 0 <= p < m + 1 implies #[trigger] half_ok(c, no, fo, len, e2, o2, p) by {
        if p < m {
            assert(half_ok(c, no, fo, len, e, o, p));
        }
    }
}

/// A line put together: its interior pairs interleaved from `e` and `o`,
/// then the first pixel, and the last one of an even length.
proof fn lemma_line_from_pairs(
    c: Seq<u8>, no: int, fo: int, len: int, e: Seq<u8>, o: Seq<u8>, s0: Seq<u8>, s1: Seq<u8>, s2: Seq<u8>,
    first: u8, last: u8,
)
    requires
        1 <= len <= s0.len(),
        interleaved(s0, s1, e, o, 1, (len - 1) / 2, (len - 1) / 2),
        forall|p: int| 0 <= p < (len - 1) / 2 ==> #[trigger] half_ok(c, no, fo, len, e, o, p),
        first as int == fancy_line(c, no, fo, len, 0),
        len % 2 == 0 ==> last as int == fancy_line(c, no, fo, len, len - 1),
        s2 == if len % 2 == 0 {
            s1.update(0, first).update(len - 1, last)
        } else {
            s1.update(0, first)
        },
    ensures
        fancy_row(s2, c, no, fo, len),
{
    let np = (len - 1) / 2;
    assert forall|x: int| 0 <= x < len implies (#[trigger] s2[x]) as int == fancy_line(c, no, fo, len, x) by {
        if x == 0 {
        } else if x == len - 1 && len % 2 == 0 {
        } else {
            let p = (x - 1) / 2;
            assert(0 <= p < np);
            assert(half_ok(c, no, fo, len, e, o, p));
            assert(pair2(s1, 1, p) == (e[p], o[p]));
            assert(s2[x] == s1[x]);
            if x % 2 == 1 {
                assert(x == 1 + 2 * p);
            } else {
                assert(x == 1 + 2 * p + 1);
            }
        }
    }
}

/// The two diagonals of sixteen pairs, `(a + 3b + 3c + d) / 8` and
/// `(3a + b + c + 3d) / 8`, as `upsample_pair_neon` computes them: byte
/// averages, each corrected by the bit its rounding gained.
pub open spec fn ups_diag(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>, d: Seq<u8>) -> (Seq<u8>, Seq<u8>) {
    let one = splat8(1u8, 16);
    let s = avg_u8(a, d);
    let t = avg_u8(b, c);
    let st = xor8(s, t);
    let ad = xor8(a, d);
    let bc = xor8(b, c);
    let k = sub8(avg_u8(s, t), and8(or8(or8(ad, bc), st), one));
    (
        sub8(avg_u8(k, t), and8(or8(and8(bc, st), xor8(k, t)), one)),
        sub8(avg_u8(k, s), and8(or8(and8(ad, st), xor8(k, s)), one)),
    )
}

/// One byte of a rounded-up average and of a wrapping difference.
pub open spec fn avg1(x: u8, y: u8) -> u8 {
    ((x + y + 1) / 2) as u8
}

pub open spec fn sub1(x: u8, y: u8) -> u8 {
    ((x - y + 256) % 256) as u8
}

/// One byte of `ups_diag`.
pub open spec fn diag1(a: u8, b: u8, c: u8, d: u8) -> (u8, u8) {
    let s = avg1(a, d);
    let t = avg1(b, c);
    let st = s ^ t;
    let ad = a ^ d;
    let bc = b ^ c;
    let k = sub1(avg1(s, t), ((ad | bc) | st) & 1);
    (sub1(avg1(k, t), ((bc & st) | (k ^ t)) & 1), sub1(avg1(k, s), ((ad & st) | (k ^ s)) & 1))
}

/// The four averages taken with a byte of `ups_diag` are the upsampled
/// pixels of `fancy_mid`: `(9a + 3b + 3c + d + 8) / 16` and its three
/// reflections.
proof fn lemma_ups_byte(a: u8, b: u8, c: u8, d: u8)
    ensures
        ({
            let (d1, d2) = diag1(a, b, c, d);
            &&& avg1(a, d1) as int == fancy_mid(a as int, b as int, c as int, d as int)
            &&& avg1(b, d2) as int == fancy_mid(b as int, a as int, d as int, c as int)
            &&& avg1(c, d2) as int == fancy_mid(c as int, d as int, a as int, b as int)
            &&& avg1(d, d1) as int == fancy_mid(d as int, c as int, b as int, a as int)
        }),
{
    let s = ((a + d + 1) / 2) as u8;
    let t = ((b + c + 1) / 2) as u8;
    lemma_ups_k(a, b, c, d);
    lemma_ups_diag(a, b, c, d);
    lemma_ups_diag(b, a, d, c);
    assert(t ^ s == s ^ t) by (bit_vector);
    assert((b + a + d + c) / 4 == (a + b + c + d) / 4);
}

/// `avg_u8` and `sub8` byte by byte.
proof fn lemma_avg_lane(x: Seq<u8>, y: Seq<u8>, i: int)
    requires
        0 <= i < x.len(),
    ensures
        avg_u8(x, y)[i] == avg1(x[i], y[i]),
        sub8(x, y)[i] == sub1(x[i], y[i]),
{
}

/// Sixteen pairs at once: the odd and even pixels of the upper line
/// (`ta`, `tb`) and of the lower one (`ua`, `ub`).
proof fn lemma_ups16(
    a: Seq<u8>, b: Seq<u8>, c: Seq<u8>, d: Seq<u8>, ta: Seq<u8>, tb: Seq<u8>, ua: Seq<u8>, ub: Seq<u8>,
)
    requires
        a.len() == 16, b.len() == 16, c.len() == 16, d.len() == 16,
        ta == avg_u8(a, ups_diag(a, b, c, d).0),
        tb == avg_u8(b, ups_diag(a, b, c, d).1),
        ua == avg_u8(c, ups_diag(a, b, c, d).1),
        ub == avg_u8(d, ups_diag(a, b, c, d).0),
    ensures
        forall|i: int|
            0 <= i < 16 ==> (#[trigger] ta[i]) as int == fancy_mid(a[i] as int, b[i] as int, c[i] as int, d[i] as int),
        forall|i: int|
            0 <= i < 16 ==> (#[trigger] tb[i]) as int == fancy_mid(b[i] as int, a[i] as int, d[i] as int, c[i] as int),
        forall|i: int|
            0 <= i < 16 ==> (#[trigger] ua[i]) as int == fancy_mid(c[i] as int, d[i] as int, a[i] as int, b[i] as int),
        forall|i: int|
            0 <= i < 16 ==> (#[trigger] ub[i]) as int == fancy_mid(d[i] as int, c[i] as int, b[i] as int, a[i] as int),
{
    hide(fancy_mid);
    hide(avg1);
    hide(sub1);
    let (d1, d2) = ups_diag(a, b, c, d);
    assert forall|i: int| 0 <= i < 16 implies {
        &&& ta[i] as int == fancy_mid(a[i] as int, b[i] as int, c[i] as int, d[i] as int)
        &&& tb[i] as int == fancy_mid(b[i] as int, a[i] as int, d[i] as int, c[i] as int)
        &&& ua[i] as int == fancy_mid(c[i] as int, d[i] as int, a[i] as int, b[i] as int)
        &&& ub[i] as int == fancy_mid(d[i] as int, c[i] as int, b[i] as int, a[i] as int)
    } by {
        lemma_ups_byte(a[i], b[i], c[i], d[i]);
        let one = splat8(1u8, 16);
        let s = avg_u8(a, d);
        let t = avg_u8(b, c);
        let st = xor8(s, t);
        let ad = xor8(a, d);
        let bc = xor8(b, c);
        let e1 = and8(or8(or8(ad, bc), st), one);
        let k = sub8(avg_u8(s, t), e1);
        let e2 = and8(or8(and8(bc, st), xor8(k, t)), one);
        let e3 = and8(or8(and8(ad, st), xor8(k, s)), one);
        lemma_avg_lane(a, d, i);
        lemma_avg_lane(b, c, i);
        lemma_avg_lane(s, t, i);
        lemma_avg_lane(avg_u8(s, t), e1, i);
        assert(e1[i] == ((ad[i] | bc[i]) | st[i]) & 1);
        assert(k[i] == sub1(avg1(s[i], t[i]), e1[i]));
        lemma_avg_lane(k, t, i);
        lemma_avg_lane(avg_u8(k, t), e2, i);
        assert(e2[i] == ((bc[i] & st[i]) | (k[i] ^ t[i])) & 1);
        lemma_avg_lane(k, s, i);
        lemma_avg_lane(avg_u8(k, s), e3, i);
        assert(e3[i] == ((ad[i] & st[i]) | (k[i] ^ s[i])) & 1);
        assert(d1[i] == diag1(a[i], b[i], c[i], d[i]).0);
        assert(d2[i] == diag1(a[i], b[i], c[i], d[i]).1);
        lemma_avg_lane(a, d1, i);
        lemma_avg_lane(b, d2, i);
        lemma_avg_lane(c, d2, i);
        lemma_avg_lane(d, d1, i);
    }
}

/// `s[1..1 + 2m]` is the interior of the line `fancy_line(c, no, fo, len, ..)`.
pub open spec fn fancy_mid_row(s: Seq<u8>, c: Seq<u8>, no: int, fo: int, len: int, m: int) -> bool {
    forall|x: int| 1 <= x < 1 + 2 * m ==> (#[trigger] s[x]) as int == fancy_line(c, no, fo, len, x)
}

/// Sixteen pairs stored at pair `k` (at or before `m`, where the line is
/// done so far) as the two zips of their odd pixels `ta` and even pixels
/// `tb`: the line is done up to pair `k + 16`.
proof fn lemma_ups_store(
    c: Seq<u8>, no: int, fo: int, len: int, s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>, m: int, k: int,
    ta: Seq<u8>, tb: Seq<u8>, a: Seq<u8>, b: Seq<u8>, cc: Seq<u8>, d: Seq<u8>,
)
    requires
        0 <= k <= m, k + 16 <= (len - 1) / 2,
        len <= s1.len(),
        0 <= no, 0 <= fo,
        no + (len + 1) / 2 <= c.len(),
        fo + (len + 1) / 2 <= c.len(),
        fancy_mid_row(s1, c, no, fo, len, m),
        a == c.subrange(no + k, no + k + 16),
        b == c.subrange(no + k + 1, no + k + 17),
        cc == c.subrange(fo + k, fo + k + 16),
        d == c.subrange(fo + k + 1, fo + k + 17),
        ta.len() == 16, tb.len() == 16,
        forall|i: int|
            0 <= i < 16 ==> (#[trigger] ta[i]) as int == fancy_mid(a[i] as int, b[i] as int, cc[i] as int, d[i] as int),
        forall|i: int|
            0 <= i < 16 ==> (#[trigger] tb[i]) as int == fancy_mid(b[i] as int, a[i] as int, d[i] as int, cc[i] as int),
        s2 == s1.subrange(0, 1 + 2 * k) + unpacklo8_lanes(ta, tb) + s1.subrange(1 + 2 * k + 16, s1.len() as int),
        s3 == s2.subrange(0, 1 + 2 * k + 16) + unpackhi8_lanes(ta, tb) + s2.subrange(1 + 2 * k + 32, s2.len() as int),
    ensures
        s3.len() == s1.len(),
        fancy_mid_row(s3, c, no, fo, len, k + 16),
{
    hide(fancy_mid);
    let lo = unpacklo8_lanes(ta, tb);
    let hi = unpackhi8_lanes(ta, tb);
    lemma_unpack8(ta, tb);
    assert(s2.len() == s1.len());
    assert(s3.len() == s1.len());
    assert forall|x: int| 1 <= x < 1 + 2 * (k + 16) implies (#[trigger] s3[x]) as int == fancy_line(c, no, fo, len, x) by {
        if x < 1 + 2 * k {
            assert(s3[x] == s2[x]);
            assert(s2[x] == s1[x]);
        } else {
            let p = (x - 1) / 2;
            let i = p - k;
            assert(0 <= i < 16);
            assert(a[i] == c[no + p] && b[i] == c[no + p + 1] && cc[i] == c[fo + p] && d[i] == c[fo + p + 1]);
            if i < 8 {
                assert(pair2(lo, 0, i) == (ta[i], tb[i]));
                assert(s3[1 + 2 * p] == lo[2 * i] && s3[1 + 2 * p + 1] == lo[2 * i + 1]);
            } else {
                assert(pair2(hi, 0, i - 8) == (ta[8 + (i - 8)], tb[8 + (i - 8)]));
                assert(s3[1 + 2 * p] == hi[2 * (i - 8)] && s3[1 + 2 * p + 1] == hi[2 * (i - 8) + 1]);
            }
            if x % 2 == 1 {
                assert(x == 1 + 2 * p);
                assert(s3[x] == ta[i]);
            } else {
                assert(x == 1 + 2 * p + 1);
                assert(s3[x] == tb[i]);
            }
        }
    }
}

/// A line put together from its interior, the first pixel, and the last
/// one of an even length.
proof fn lemma_line_from_mid(c: Seq<u8>, no: int, fo: int, len: int, s1: Seq<u8>, s2: Seq<u8>, first: u8, last: u8)
    requires
        1 <= len <= s1.len(),
        fancy_mid_row(s1, c, no, fo, len, (len - 1) / 2),
        first as int == fancy_line(c, no, fo, len, 0),
        len % 2 == 0 ==> last as int == fancy_line(c, no, fo, len, len - 1),
        s2 == if len % 2 == 0 {
            s1.update(0, first).update(len - 1, last)
        } else {
            s1.update(0, first)
        },
    ensures
        fancy_row(s2, c, no, fo, len),
{
    assert forall|x: int| 0 <= x < len implies (#[trigger] s2[x]) as int == fancy_line(c, no, fo, len, x) by {
        if x == 0 {
        } else if x == len - 1 && len % 2 == 0 {
        } else {
            assert(s2[x] == s1[x]);
        }
    }
}

/// The interiors of the two lines of `upsample_chroma_pair`, pixels
/// `1..1 + 2 * ((len - 1) / 2)` of each, sixteen pairs at a time on NEON
/// (`UPSAMPLE_16PIXELS`): with `a b` the samples above a pair and `c d`
/// those below, the pair is `(9a + 3b + 3c + d + 8) / 16` and
/// `(3a + 9b + c + 3d + 8) / 16`, each the rounded average of a sample and
/// a diagonal, and the diagonals come from byte averages (`ups_diag`). The
/// last step starts sixteen pairs before the end, over pairs already done.
fn upsample_pair_neon(c: &[u8], a: usize, b: usize, st: &mut [u8], sb: &mut [u8], len: usize)
    requires
        neon(),
        (len - 1) / 2 >= 16,
        len <= old(st)@.len(), len <= old(sb)@.len(),
        a + (len + 1) / 2 <= c@.len(),
        b + (len + 1) / 2 <= c@.len(),
    ensures
        final(st)@.len() == old(st)@.len(),
        final(sb)@.len() == old(sb)@.len(),
        fancy_mid_row(final(st)@, c@, a as int, b as int, len as int, (len - 1) / 2),
        fancy_mid_row(final(sb)@, c@, b as int, a as int, len as int, (len - 1) / 2),
{
    hide(avg_u8);
    hide(sub8);
    hide(and8);
    hide(or8);
    hide(xor8);
    hide(unpacklo8_lanes);
    hide(unpackhi8_lanes);
    proof {
        assert(c@.len() == c.len());
        assert(st@.len() == st.len());
        assert(sb@.len() == sb.len());
    }
    let ghost (ai, bi, li) = (a as int, b as int, len as int);
    let np = (len - 1) / 2;
    let one = vdupq_n_u8(1);
    let mut m: usize = 0;
    while m < np
        invariant
            neon(),
            m <= np,
            np == (len - 1) / 2,
            np >= 16,
            len <= st@.len(), len <= sb@.len(),
            a + (len + 1) / 2 <= c@.len(),
            b + (len + 1) / 2 <= c@.len(),
            st@.len() == old(st)@.len(),
            sb@.len() == old(sb)@.len(),
            c@.len() <= usize::MAX,
            st@.len() <= usize::MAX,
            sb@.len() <= usize::MAX,
            ai == a, bi == b, li == len,
            n8(one) == splat8(1u8, 16),
            fancy_mid_row(st@, c@, ai, bi, li, m as int),
            fancy_mid_row(sb@, c@, bi, ai, li, m as int),
        decreases np - m,
    {
        let k = if np - m < 16 { np - 16 } else { m };
        proof {
            assert(k + 17 <= (len + 1) / 2);
            assert(1 + 2 * k + 32 <= len);
        }
        let va = vld1q_u8_at(c, a + k);
        let vb = vld1q_u8_at(c, a + k + 1);
        let vc = vld1q_u8_at(c, b + k);
        let vd = vld1q_u8_at(c, b + k + 1);
        let s = vrhaddq_u8(va, vd);
        let t = vrhaddq_u8(vb, vc);
        let x = veorq_u8(s, t);
        let ad = veorq_u8(va, vd);
        let bc = veorq_u8(vb, vc);
        let q = vsubq_u8(vrhaddq_u8(s, t), vandq_u8(vorrq_u8(vorrq_u8(ad, bc), x), one));
        let d1 = vsubq_u8(vrhaddq_u8(q, t), vandq_u8(vorrq_u8(vandq_u8(bc, x), veorq_u8(q, t)), one));
        let d2 = vsubq_u8(vrhaddq_u8(q, s), vandq_u8(vorrq_u8(vandq_u8(ad, x), veorq_u8(q, s)), one));
        let ta = vrhaddq_u8(va, d1);
        let tb = vrhaddq_u8(vb, d2);
        let ua = vrhaddq_u8(vc, d2);
        let ub = vrhaddq_u8(vd, d1);
        let ghost s1 = st@;
        let ghost t1 = sb@;
        let o = 1 + 2 * k;
        vst1q_u8_at(st, o, vzip1q_u8(ta, tb));
        let ghost s2 = st@;
        vst1q_u8_at(st, o + 16, vzip2q_u8(ta, tb));
        vst1q_u8_at(sb, o, vzip1q_u8(ua, ub));
        let ghost t2 = sb@;
        vst1q_u8_at(sb, o + 16, vzip2q_u8(ua, ub));
        proof {
            assert(n8(d1) == ups_diag(n8(va), n8(vb), n8(vc), n8(vd)).0);
            assert(n8(d2) == ups_diag(n8(va), n8(vb), n8(vc), n8(vd)).1);
            lemma_ups16(n8(va), n8(vb), n8(vc), n8(vd), n8(ta), n8(tb), n8(ua), n8(ub));
            lemma_ups_store(c@, ai, bi, li, s1, s2, st@, m as int, k as int, n8(ta), n8(tb), n8(va), n8(vb), n8(vc), n8(vd));
            lemma_ups_store(c@, bi, ai, li, t1, t2, sb@, m as int, k as int, n8(ua), n8(ub), n8(vc), n8(vd), n8(va), n8(vb));
        }
        m = k + 16;
    }
}

/// The fancy-upsampled chroma of the two output lines between chroma
/// lines `a` (above) and `b` (below), as `UpsampleRgbaLinePair` computes
/// them together: `st[0..len]` nearer `a`, `sb[0..len]` nearer `b`. Each
/// pair of output pixels shares its diagonal sums; the odd and even
/// pixels go to `e*`/`o*` and are interleaved after, so that each loop
/// stores contiguously. On NEON, lines of at least sixteen pairs are
/// written directly by `upsample_pair_neon`.
#[verifier::rlimit(40)]
fn upsample_chroma_pair(
    c: &[u8], a: usize, b: usize, st: &mut [u8], sb: &mut [u8],
    e0: &mut [u8], o0: &mut [u8], e1: &mut [u8], o1: &mut [u8], len: usize,
)
    requires
        len >= 1,
        len <= old(st)@.len(), len <= old(sb)@.len(),
        len <= old(e0)@.len(), len <= old(o0)@.len(), len <= old(e1)@.len(), len <= old(o1)@.len(),
        a + (len + 1) / 2 <= c@.len(),
        b + (len + 1) / 2 <= c@.len(),
    ensures
        final(st)@.len() == old(st)@.len(),
        final(sb)@.len() == old(sb)@.len(),
        final(e0)@.len() == old(e0)@.len(),
        final(o0)@.len() == old(o0)@.len(),
        final(e1)@.len() == old(e1)@.len(),
        final(o1)@.len() == old(o1)@.len(),
        fancy_row(final(st)@, c@, a as int, b as int, len as int),
        fancy_row(final(sb)@, c@, b as int, a as int, len as int),
{
    proof {
        assert(c@.len() == c.len());
        assert(st@.len() == st.len());
        assert(sb@.len() == sb.len());
    }
    let ghost (ai, bi, li) = (a as int, b as int, len as int);
    let np = (len - 1) / 2;
    let ghost st0 = st@;
    let ghost sb0 = sb@;
    // On NEON, straight into the lines (the first and last pixels follow).
    let fast = np >= 16 && (cfg!(target_arch = "aarch64") && has_neon());
    if fast {
        upsample_pair_neon(c, a, b, st, sb, len);
    }
    let ns = if fast { 0 } else { np };
    let mut m: usize = 0;
    while m < ns
        invariant
            m <= ns,
            ns <= np,
            np == (len - 1) / 2,
            len <= e0@.len(), len <= o0@.len(), len <= e1@.len(), len <= o1@.len(),
            a + (len + 1) / 2 <= c@.len(),
            b + (len + 1) / 2 <= c@.len(),
            e0@.len() == old(e0)@.len(),
            o0@.len() == old(o0)@.len(),
            e1@.len() == old(e1)@.len(),
            o1@.len() == old(o1)@.len(),
            c@.len() <= usize::MAX,
            ai == a, bi == b, li == len,
            forall|p: int| 0 <= p < m ==> #[trigger] half_ok(c@, ai, bi, li, e0@, o0@, p),
            forall|p: int| 0 <= p < m ==> #[trigger] half_ok(c@, bi, ai, li, e1@, o1@, p),
        decreases ns - m,
    {
        let tl = get(c, a + m) as u16;
        let t = get(c, a + m + 1) as u16;
        let l = get(c, b + m) as u16;
        let cc = get(c, b + m + 1) as u16;
        let avg = tl + t + l + cc + 8;
        let d12 = (avg + 2 * (t + l)) / 8;
        let d03 = (avg + 2 * (tl + cc)) / 8;
        let ghost (g0, h0, g1, h1) = (e0@, o0@, e1@, o1@);
        proof {
            lemma_fancy_bounds(tl as int, t as int, l as int, cc as int);
            lemma_fancy_bounds(t as int, tl as int, cc as int, l as int);
            lemma_fancy_bounds(l as int, cc as int, tl as int, t as int);
            lemma_fancy_bounds(cc as int, l as int, t as int, tl as int);
            assert((d12 + tl) / 2 == fancy_line(c@, ai, bi, li, 2 * m + 1));
            assert((d03 + t) / 2 == fancy_line(c@, ai, bi, li, 2 * m + 2));
            assert((d03 + l) / 2 == fancy_line(c@, bi, ai, li, 2 * m + 1));
            assert((d12 + cc) / 2 == fancy_line(c@, bi, ai, li, 2 * m + 2));
        }
        set(e0, m, ((d12 + tl) / 2) as u8);
        set(o0, m, ((d03 + t) / 2) as u8);
        set(e1, m, ((d03 + l) / 2) as u8);
        set(o1, m, ((d12 + cc) / 2) as u8);
        proof {
            lemma_half_step(c@, ai, bi, li, g0, h0, e0@, o0@, m as int, ((d12 + tl) / 2) as u8, ((d03 + t) / 2) as u8);
            lemma_half_step(c@, bi, ai, li, g1, h1, e1@, o1@, m as int, ((d03 + l) / 2) as u8, ((d12 + cc) / 2) as u8);
        }
        m = m + 1;
    }
    proof {
        assert(1 + 2 * np <= len);
    }
    if !fast {
        interleave2(e0, o0, st, 1, np);
        interleave2(e1, o1, sb, 1, np);
    }
    let ghost st1 = st@;
    let ghost sb1 = sb@;
    let ta = get(c, a) as u32;
    let tb = get(c, b) as u32;
    proof {
        lemma_fancy_bounds(ta as int, ta as int, tb as int, tb as int);
        lemma_fancy_bounds(tb as int, tb as int, ta as int, ta as int);
        assert((3 * ta + tb + 2) / 4 == fancy_line(c@, ai, bi, li, 0));
        assert((3 * tb + ta + 2) / 4 == fancy_line(c@, bi, ai, li, 0));
    }
    set(st, 0, ((3 * ta + tb + 2) / 4) as u8);
    set(sb, 0, ((3 * tb + ta + 2) / 4) as u8);
    let ghost mut lta = 0u8;
    let ghost mut ltb = 0u8;
    if len % 2 == 0 {
        let la = get(c, a + np) as u32;
        let lb = get(c, b + np) as u32;
        proof {
            lemma_fancy_bounds(la as int, la as int, lb as int, lb as int);
            lemma_fancy_bounds(lb as int, lb as int, la as int, la as int);
            assert((3 * la + lb + 2) / 4 == fancy_line(c@, ai, bi, li, li - 1));
            assert((3 * lb + la + 2) / 4 == fancy_line(c@, bi, ai, li, li - 1));
            lta = ((3 * la + lb + 2) / 4) as u8;
            ltb = ((3 * lb + la + 2) / 4) as u8;
        }
        set(st, len - 1, ((3 * la + lb + 2) / 4) as u8);
        set(sb, len - 1, ((3 * lb + la + 2) / 4) as u8);
    }
    proof {
        if fast {
            lemma_line_from_mid(c@, ai, bi, li, st1, st@, ((3 * ta + tb + 2) / 4) as u8, lta);
            lemma_line_from_mid(c@, bi, ai, li, sb1, sb@, ((3 * tb + ta + 2) / 4) as u8, ltb);
        } else {
            lemma_line_from_pairs(c@, ai, bi, li, e0@, o0@, st0, st1, st@, ((3 * ta + tb + 2) / 4) as u8, lta);
            lemma_line_from_pairs(c@, bi, ai, li, e1@, o1@, sb0, sb1, sb@, ((3 * tb + ta + 2) / 4) as u8, ltb);
        }
    }
}

// The pair of lines sixteen pairs at a time, with byte averages only
// (`UPSAMPLE_16PIXELS` of libwebp's `upsampling_sse2.c`).

/// `(a + b + c + d) / 4` from rounded-up byte averages: the average of
/// `s = (a + d + 1) / 2` and `t = (b + c + 1) / 2`, less one when any of
/// the three averages rounded up.
proof fn lemma_ups_k(a: u8, b: u8, c: u8, d: u8)
    ensures
        ({
            let s = ((a + d + 1) / 2) as u8;
            let t = ((b + c + 1) / 2) as u8;
            let k = ((((s + t + 1) / 2) as u8 - ((((a ^ d) | (b ^ c)) | (s ^ t)) & 1) + 256) % 256) as u8;
            k as int == (a + b + c + d) / 4
        }),
{
    assert(({
        let s = ((a + d + 1) / 2) as u8;
        let t = ((b + c + 1) / 2) as u8;
        let k = ((((s + t + 1) / 2) as u8 - ((((a ^ d) | (b ^ c)) | (s ^ t)) & 1) + 256) % 256) as u8;
        k as int == (a + b + c + d) / 4
    })) by (bit_vector);
}

/// A diagonal `(a + 3b + 3c + d) / 8` from `k = (a + b + c + d) / 4` and
/// `t = (b + c + 1) / 2`: their average, less one when it rounded up or
/// when `k` itself lost a half that `t` gained.
proof fn lemma_ups_diag(a: u8, b: u8, c: u8, d: u8)
    ensures
        ({
            let s = ((a + d + 1) / 2) as u8;
            let t = ((b + c + 1) / 2) as u8;
            let k = ((a + b + c + d) / 4) as u8;
            let m = ((((k + t + 1) / 2) as u8 - ((((b ^ c) & (s ^ t)) | (k ^ t)) & 1) + 256) % 256) as u8;
            m as int == (a + 3 * b + 3 * c + d) / 8
        }),
{
    assert(({
        let s = ((a + d + 1) / 2) as u8;
        let t = ((b + c + 1) / 2) as u8;
        let k = ((a + b + c + d) / 4) as u8;
        let m = ((((k + t + 1) / 2) as u8 - ((((b ^ c) & (s ^ t)) | (k ^ t)) & 1) + 256) % 256) as u8;
        m as int == (a + 3 * b + 3 * c + d) / 8
    })) by (bit_vector);
}

/// Pixel `i` of a converted line: `r`, `g` and `b` are `VP8YuvToRgb` of
/// luma `ys[yo + i]` and chroma `u[i]`, `v[i]`.
pub open spec fn rgb_lane_ok(
    ys: Seq<u8>, yo: int, u: Seq<u8>, v: Seq<u8>, r: Seq<u8>, g: Seq<u8>, b: Seq<u8>, i: int,
) -> bool {
    &&& r[i] as int == yuv_r(ys[yo + i] as int, v[i] as int)
    &&& g[i] as int == yuv_g(ys[yo + i] as int, u[i] as int, v[i] as int)
    &&& b[i] as int == yuv_b(ys[yo + i] as int, u[i] as int)
}

/// The in-place conversion, `j` pixels in: `su`, `sg` and `sv` hold red,
/// green and blue of the first `j`, and `su` and `sv` still the chroma
/// `u0`, `v0` of the rest.
pub open spec fn rgb_lanes(
    ys: Seq<u8>, yo: int, u0: Seq<u8>, v0: Seq<u8>, su: Seq<u8>, sv: Seq<u8>, sg: Seq<u8>, j: int,
) -> bool {
    &&& su.len() == u0.len()
    &&& sv.len() == v0.len()
    &&& forall|i: int| 0 <= i < j ==> #[trigger] rgb_lane_ok(ys, yo, u0, v0, su, sg, sv, i)
    &&& forall|i: int| j <= i < su.len() ==> #[trigger] su[i] == u0[i]
    &&& forall|i: int| j <= i < sv.len() ==> #[trigger] sv[i] == v0[i]
}

/// One more pixel converted in place.
proof fn lemma_rgb1(
    ys: Seq<u8>, yo: int, u0: Seq<u8>, v0: Seq<u8>, su1: Seq<u8>, sv1: Seq<u8>, sg1: Seq<u8>,
    su2: Seq<u8>, sv2: Seq<u8>, sg2: Seq<u8>, j: int, r: u8, g: u8, b: u8,
)
    requires
        0 <= j < su1.len(), j < sv1.len(), j < sg1.len(),
        rgb_lanes(ys, yo, u0, v0, su1, sv1, sg1, j),
        r as int == yuv_r(ys[yo + j] as int, sv1[j] as int),
        g as int == yuv_g(ys[yo + j] as int, su1[j] as int, sv1[j] as int),
        b as int == yuv_b(ys[yo + j] as int, su1[j] as int),
        su2 == su1.update(j, r),
        sg2 == sg1.update(j, g),
        sv2 == sv1.update(j, b),
    ensures
        rgb_lanes(ys, yo, u0, v0, su2, sv2, sg2, j + 1),
{
    assert(su1[j] == u0[j] && sv1[j] == v0[j]);
    assert forall|i: int| 0 <= i < j + 1 implies #[trigger] rgb_lane_ok(ys, yo, u0, v0, su2, sg2, sv2, i) by {
        if i < j {
            assert(rgb_lane_ok(ys, yo, u0, v0, su1, sg1, sv1, i));
        }
    }
}

/// Sixteen more pixels converted in place, by vector stores.
proof fn lemma_rgb16(
    ys: Seq<u8>, yo: int, u0: Seq<u8>, v0: Seq<u8>, su1: Seq<u8>, sv1: Seq<u8>, sg1: Seq<u8>,
    su2: Seq<u8>, sv2: Seq<u8>, sg2: Seq<u8>, j: int,
    y: Seq<u8>, u: Seq<u8>, v: Seq<u8>, rr: Seq<u8>, gg: Seq<u8>, bb: Seq<u8>,
)
    requires
        0 <= yo, 0 <= j,
        j + 16 <= su1.len(), j + 16 <= sv1.len(), j + 16 <= sg1.len(),
        yo + j + 16 <= ys.len(),
        rgb_lanes(ys, yo, u0, v0, su1, sv1, sg1, j),
        y == ys.subrange(yo + j, yo + j + 16),
        u == su1.subrange(j, j + 16),
        v == sv1.subrange(j, j + 16),
        rr.len() == 16, gg.len() == 16, bb.len() == 16,
        forall|i: int| 0 <= i < 16 ==> #[trigger] rgb_lane_ok(y, 0, u, v, rr, gg, bb, i),
        su2 == su1.subrange(0, j) + rr + su1.subrange(j + 16, su1.len() as int),
        sg2 == sg1.subrange(0, j) + gg + sg1.subrange(j + 16, sg1.len() as int),
        sv2 == sv1.subrange(0, j) + bb + sv1.subrange(j + 16, sv1.len() as int),
    ensures
        rgb_lanes(ys, yo, u0, v0, su2, sv2, sg2, j + 16),
{
    assert forall|i: int| 0 <= i < j + 16 implies #[trigger] rgb_lane_ok(ys, yo, u0, v0, su2, sg2, sv2, i) by {
        if i < j {
            assert(rgb_lane_ok(ys, yo, u0, v0, su1, sg1, sv1, i));
        } else {
            let q = i - j;
            assert(rgb_lane_ok(y, 0, u, v, rr, gg, bb, q));
            assert(su1[i] == u0[i] && sv1[i] == v0[i]);
            assert(y[0 + q] == ys[yo + i] && u[q] == u0[i] && v[q] == v0[i]);
            assert(su2[i] == rr[q] && sg2[i] == gg[q] && sv2[i] == bb[q]);
        }
    }
}

// The sixteen-pixel conversion in 16-bit lanes (`ConvertYUV444ToRGB_SSE2`).

/// Bytes widened to the high halves of 16-bit lanes: the low eight.
pub open spec fn widen_lo(y: Seq<u8>) -> Seq<u16> {
    u16s(unpacklo8_lanes(splat8(0u8, 16), y))
}

/// The high eight.
pub open spec fn widen_hi(y: Seq<u8>) -> Seq<u16> {
    u16s(unpackhi8_lanes(splat8(0u8, 16), y))
}

pub open spec fn vec_y1(yw: Seq<u16>) -> Seq<u16> {
    mulhi_u16(yw, splat16(19077u16, 8))
}

pub open spec fn vec_r(yw: Seq<u16>, vw: Seq<u16>) -> Seq<u16> {
    srai16(add16(sub16(vec_y1(yw), splat16(14234u16, 8)), mulhi_u16(vw, splat16(26149u16, 8))), 6)
}

pub open spec fn vec_g(yw: Seq<u16>, uw: Seq<u16>, vw: Seq<u16>) -> Seq<u16> {
    srai16(
        sub16(
            add16(vec_y1(yw), splat16(8708u16, 8)),
            add16(mulhi_u16(uw, splat16(6419u16, 8)), mulhi_u16(vw, splat16(13320u16, 8))),
        ),
        6,
    )
}

pub open spec fn vec_b(yw: Seq<u16>, uw: Seq<u16>) -> Seq<u16> {
    srli16(subs_u16(add16(vec_y1(yw), mulhi_u16(uw, splat16(33050u16, 8))), splat16(17685u16, 8)), 6)
}

/// Lane `k` of the three results, saturated to bytes, is `VP8YuvToRgb` of
/// `y[o + k]`, `u[o + k]`, `v[o + k]`.
pub open spec fn lane_ok3(
    r: Seq<u16>, g: Seq<u16>, b: Seq<u16>, y: Seq<u8>, u: Seq<u8>, v: Seq<u8>, o: int, k: int,
) -> bool {
    &&& sat_u8(s16(r[k])) as int == yuv_r(y[o + k] as int, v[o + k] as int)
    &&& sat_u8(s16(g[k])) as int == yuv_g(y[o + k] as int, u[o + k] as int, v[o + k] as int)
    &&& sat_u8(s16(b[k])) as int == yuv_b(y[o + k] as int, u[o + k] as int)
}

/// `_mm_mulhi_epu16(x << 8, c)` is `MultHi(x, c)`.
proof fn lemma_mulhi_const(a: u16, b: u16, x: int, c: int)
    requires
        0 <= x < 256, 0 <= c < 0x1_0000,
        a == 256 * x,
        b == c,
    ensures
        (a as int * b as int) / 0x1_0000 == yuv_mult_hi(x, c),
        0 <= yuv_mult_hi(x, c) <= (255 * c) / 256,
{
    let p = x * c;
    assert(a as int * b as int == 256 * p) by (nonlinear_arith)
        requires a == 256 * x, b == c, p == x * c;
    assert(0 <= p <= 255 * c) by (nonlinear_arith)
        requires 0 <= x <= 255, 0 <= c, p == x * c;
    assert((256 * p) / 0x1_0000 == p / 256);
}

/// The red lane: no 16-bit operation wraps past what the signed shift and
/// the saturating pack undo.
proof fn lemma_lane_r(y1: int, r0: int)
    requires
        0 <= y1 <= 19002, 0 <= r0 <= 26046,
    ensures
        ({
            let t1 = ((y1 - 14234 + 0x1_0000) % 0x1_0000) as u16;
            let t2 = ((t1 + r0) % 0x1_0000) as u16;
            let t3 = ((s16(t2) / 64) % 0x1_0000) as u16;
            sat_u8(s16(t3)) as int == yuv_clip8(y1 + r0 - 14234)
        }),
{
    let t1 = ((y1 - 14234 + 0x1_0000) % 0x1_0000) as u16;
    let t2 = ((t1 + r0) % 0x1_0000) as u16;
    let s = y1 + r0 - 14234;
    assert(s16(t2) == s);
    assert(-512 <= s / 64 < 512);
}

proof fn lemma_lane_g(y1: int, g0: int, g1: int)
    requires
        0 <= y1 <= 19002, 0 <= g0 <= 6393, 0 <= g1 <= 13267,
    ensures
        ({
            let t1 = ((y1 + 8708) % 0x1_0000) as u16;
            let t2 = ((g0 + g1) % 0x1_0000) as u16;
            let t3 = ((t1 - t2 + 0x1_0000) % 0x1_0000) as u16;
            let t4 = ((s16(t3) / 64) % 0x1_0000) as u16;
            sat_u8(s16(t4)) as int == yuv_clip8(y1 - g0 - g1 + 8708)
        }),
{
    let t1 = ((y1 + 8708) % 0x1_0000) as u16;
    let t2 = ((g0 + g1) % 0x1_0000) as u16;
    let t3 = ((t1 - t2 + 0x1_0000) % 0x1_0000) as u16;
    let s = y1 - g0 - g1 + 8708;
    assert(s16(t3) == s);
    assert(-512 <= s / 64 < 512);
}

proof fn lemma_lane_b(y1: int, b0: int)
    requires
        0 <= y1 <= 19002, 0 <= b0 <= 32921,
    ensures
        ({
            let t1 = ((y1 + b0) % 0x1_0000) as u16;
            let t2 = if t1 < 17685 { 0u16 } else { (t1 - 17685) as u16 };
            let t3 = (t2 as nat / 64) as u16;
            sat_u8(s16(t3)) as int == yuv_clip8(y1 + b0 - 17685)
        }),
{
}

/// Eight lanes of `vec_r`, `vec_g`, `vec_b`.
proof fn lemma_convert8(yw: Seq<u16>, uw: Seq<u16>, vw: Seq<u16>, y: Seq<u8>, u: Seq<u8>, v: Seq<u8>, o: int)
    requires
        yw.len() == 8, uw.len() == 8, vw.len() == 8,
        0 <= o, o + 8 <= y.len(), o + 8 <= u.len(), o + 8 <= v.len(),
        forall|k: int| 0 <= k < 8 ==> (#[trigger] yw[k]) as int == 256 * y[o + k],
        forall|k: int| 0 <= k < 8 ==> (#[trigger] uw[k]) as int == 256 * u[o + k],
        forall|k: int| 0 <= k < 8 ==> (#[trigger] vw[k]) as int == 256 * v[o + k],
    ensures
        vec_r(yw, vw).len() == 8,
        vec_g(yw, uw, vw).len() == 8,
        vec_b(yw, uw).len() == 8,
        forall|k: int|
            0 <= k < 8 ==> #[trigger] lane_ok3(vec_r(yw, vw), vec_g(yw, uw, vw), vec_b(yw, uw), y, u, v, o, k),
{
    assert(pow2_spec(6) == 64) by (compute);
    assert forall|k: int| 0 <= k < 8 implies #[trigger] lane_ok3(
        vec_r(yw, vw),
        vec_g(yw, uw, vw),
        vec_b(yw, uw),
        y,
        u,
        v,
        o,
        k,
    ) by {
        let yk = y[o + k] as int;
        let uk = u[o + k] as int;
        let vk = v[o + k] as int;
        assert(yw[k] as int == 256 * yk && uw[k] as int == 256 * uk && vw[k] as int == 256 * vk);
        lemma_mulhi_const(yw[k], 19077u16, yk, 19077);
        lemma_mulhi_const(vw[k], 26149u16, vk, 26149);
        lemma_mulhi_const(uw[k], 6419u16, uk, 6419);
        lemma_mulhi_const(vw[k], 13320u16, vk, 13320);
        lemma_mulhi_const(uw[k], 33050u16, uk, 33050);
        let y1 = yuv_mult_hi(yk, 19077);
        let r0 = yuv_mult_hi(vk, 26149);
        let g0 = yuv_mult_hi(uk, 6419);
        let g1 = yuv_mult_hi(vk, 13320);
        let b0 = yuv_mult_hi(uk, 33050);
        assert(vec_y1(yw)[k] as int == y1);
        assert(mulhi_u16(vw, splat16(26149u16, 8))[k] as int == r0);
        assert(mulhi_u16(uw, splat16(6419u16, 8))[k] as int == g0);
        assert(mulhi_u16(vw, splat16(13320u16, 8))[k] as int == g1);
        assert(mulhi_u16(uw, splat16(33050u16, 8))[k] as int == b0);
        lemma_lane_r(y1, r0);
        lemma_lane_g(y1, g0, g1);
        lemma_lane_b(y1, b0);
        // Red.
        let t1 = sub16(vec_y1(yw), splat16(14234u16, 8));
        assert(t1[k] == ((y1 - 14234 + 0x1_0000) % 0x1_0000) as u16);
        let t2 = add16(t1, mulhi_u16(vw, splat16(26149u16, 8)));
        assert(t2[k] == ((t1[k] + r0) % 0x1_0000) as u16);
        assert(vec_r(yw, vw)[k] == ((s16(t2[k]) / 64) % 0x1_0000) as u16);
        // Green.
        let a1 = add16(vec_y1(yw), splat16(8708u16, 8));
        assert(a1[k] == ((y1 + 8708) % 0x1_0000) as u16);
        let a2 = add16(mulhi_u16(uw, splat16(6419u16, 8)), mulhi_u16(vw, splat16(13320u16, 8)));
        assert(a2[k] == ((g0 + g1) % 0x1_0000) as u16);
        let a3 = sub16(a1, a2);
        assert(a3[k] == ((a1[k] - a2[k] + 0x1_0000) % 0x1_0000) as u16);
        assert(vec_g(yw, uw, vw)[k] == ((s16(a3[k]) / 64) % 0x1_0000) as u16);
        // Blue.
        let c1 = add16(vec_y1(yw), mulhi_u16(uw, splat16(33050u16, 8)));
        assert(c1[k] == ((y1 + b0) % 0x1_0000) as u16);
        let c2 = subs_u16(c1, splat16(17685u16, 8));
        assert(c2[k] == if c1[k] < 17685 { 0u16 } else { (c1[k] - 17685) as u16 });
        assert(vec_b(yw, uw)[k] == (c2[k] as nat / 64) as u16);
    }
}

/// The 16-bit lanes of bytes unpacked under zeros are the bytes times 256.
proof fn lemma_widen(y: Seq<u8>)
    requires
        y.len() == 16,
    ensures
        widen_lo(y).len() == 8,
        widen_hi(y).len() == 8,
        forall|k: int| 0 <= k < 8 ==> (#[trigger] widen_lo(y)[k]) as int == 256 * y[k],
        forall|k: int| 0 <= k < 8 ==> (#[trigger] widen_hi(y)[k]) as int == 256 * y[8 + k],
{
    let z = splat8(0u8, 16);
    let lo = unpacklo8_lanes(z, y);
    let hi = unpackhi8_lanes(z, y);
    lemma_unpack8(z, y);
    assert forall|k: int| 0 <= k < 8 implies (#[trigger] widen_lo(y)[k]) as int == 256 * y[k] by {
        assert(pair2(lo, 0, k) == (z[k], y[k]));
        lemma_le16_value(lo[2 * k], lo[2 * k + 1]);
    }
    assert forall|k: int| 0 <= k < 8 implies (#[trigger] widen_hi(y)[k]) as int == 256 * y[8 + k] by {
        assert(pair2(hi, 0, k) == (z[8 + k], y[8 + k]));
        lemma_le16_value(hi[2 * k], hi[2 * k + 1]);
    }
}

/// The three byte vectors `yuv_to_rgb_sse2` stores.
pub open spec fn conv_r(y: Seq<u8>, v: Seq<u8>) -> Seq<u8> {
    packus16_lanes(vec_r(widen_lo(y), widen_lo(v)), vec_r(widen_hi(y), widen_hi(v)))
}

pub open spec fn conv_g(y: Seq<u8>, u: Seq<u8>, v: Seq<u8>) -> Seq<u8> {
    packus16_lanes(
        vec_g(widen_lo(y), widen_lo(u), widen_lo(v)),
        vec_g(widen_hi(y), widen_hi(u), widen_hi(v)),
    )
}

pub open spec fn conv_b(y: Seq<u8>, u: Seq<u8>) -> Seq<u8> {
    packus16_lanes(vec_b(widen_lo(y), widen_lo(u)), vec_b(widen_hi(y), widen_hi(u)))
}

/// A saturating pack of two eight-lane vectors, byte by byte.
proof fn lemma_packus(a: Seq<u16>, b: Seq<u16>)
    requires
        a.len() == 8, b.len() == 8,
    ensures
        packus16_lanes(a, b).len() == 16,
        forall|i: int| 0 <= i < 8 ==> #[trigger] packus16_lanes(a, b)[i] == sat_u8(s16(a[i])),
        forall|i: int| 8 <= i < 16 ==> #[trigger] packus16_lanes(a, b)[i] == sat_u8(s16(b[i - 8])),
{
}

/// They are `VP8YuvToRgb`, lane by lane.
proof fn lemma_convert16(y: Seq<u8>, u: Seq<u8>, v: Seq<u8>)
    requires
        y.len() == 16, u.len() == 16, v.len() == 16,
    ensures
        conv_r(y, v).len() == 16,
        conv_g(y, u, v).len() == 16,
        conv_b(y, u).len() == 16,
        forall|i: int| 0 <= i < 16 ==> #[trigger] rgb_lane_ok(y, 0, u, v, conv_r(y, v), conv_g(y, u, v), conv_b(y, u), i),
{
    hide(vec_r);
    hide(vec_g);
    hide(vec_b);
    hide(widen_lo);
    hide(widen_hi);
    lemma_widen(y);
    lemma_widen(u);
    lemma_widen(v);
    let (yl, ul, vl) = (widen_lo(y), widen_lo(u), widen_lo(v));
    let (yh, uh, vh) = (widen_hi(y), widen_hi(u), widen_hi(v));
    lemma_convert8(yl, ul, vl, y, u, v, 0);
    lemma_convert8(yh, uh, vh, y, u, v, 8);
    lemma_packus(vec_r(yl, vl), vec_r(yh, vh));
    lemma_packus(vec_g(yl, ul, vl), vec_g(yh, uh, vh));
    lemma_packus(vec_b(yl, ul), vec_b(yh, uh));
    assert forall|i: int| 0 <= i < 16 implies #[trigger] rgb_lane_ok(
        y,
        0,
        u,
        v,
        conv_r(y, v),
        conv_g(y, u, v),
        conv_b(y, u),
        i,
    ) by {
        if i < 8 {
            assert(lane_ok3(vec_r(yl, vl), vec_g(yl, ul, vl), vec_b(yl, ul), y, u, v, 0, i));
            assert(conv_r(y, v)[i] == sat_u8(s16(vec_r(yl, vl)[i])));
            assert(conv_g(y, u, v)[i] == sat_u8(s16(vec_g(yl, ul, vl)[i])));
            assert(conv_b(y, u)[i] == sat_u8(s16(vec_b(yl, ul)[i])));
        } else {
            assert(conv_r(y, v)[i] == sat_u8(s16(vec_r(yh, vh)[i - 8])));
            assert(conv_g(y, u, v)[i] == sat_u8(s16(vec_g(yh, uh, vh)[i - 8])));
            assert(conv_b(y, u)[i] == sat_u8(s16(vec_b(yh, uh)[i - 8])));
            assert(lane_ok3(vec_r(yh, vh), vec_g(yh, uh, vh), vec_b(yh, uh), y, u, v, 8, i - 8));
        }
    }
}

// The same conversion on NEON, sixteen pixels in two vectors of eight
// 16-bit lanes: the bytes shifted left by 7 so that `sqdmulh`, which
// doubles, gives `MultHi`; 33050 does not fit a signed lane, so that
// product is `(u << 7) + sqdmulh(u << 7, 282)` (33050 = 2^15 + 282); the
// shifts by 6 are part of the saturating narrowing.

/// Bytes zero-extended to 16-bit lanes and shifted left by 7 (`ushll`):
/// the low eight.
pub open spec fn nwiden_lo(y: Seq<u8>) -> Seq<u16> {
    slli16(u16s(unpacklo8_lanes(y, splat8(0u8, 16))), 7)
}

/// The high eight (`ushll2`).
pub open spec fn nwiden_hi(y: Seq<u8>) -> Seq<u16> {
    slli16(u16s(unpackhi8_lanes(y, splat8(0u8, 16))), 7)
}

pub open spec fn nvec_y1(yw: Seq<u16>) -> Seq<u16> {
    qdmulh_s16(yw, splat16(19077u16, 8))
}

pub open spec fn nvec_r(yw: Seq<u16>, vw: Seq<u16>) -> Seq<u16> {
    add16(sub16(nvec_y1(yw), splat16(14234u16, 8)), qdmulh_s16(vw, splat16(26149u16, 8)))
}

pub open spec fn nvec_g(yw: Seq<u16>, uw: Seq<u16>, vw: Seq<u16>) -> Seq<u16> {
    sub16(
        add16(nvec_y1(yw), splat16(8708u16, 8)),
        add16(qdmulh_s16(uw, splat16(6419u16, 8)), qdmulh_s16(vw, splat16(13320u16, 8))),
    )
}

pub open spec fn nvec_b(yw: Seq<u16>, uw: Seq<u16>) -> Seq<u16> {
    subs_u16(add16(nvec_y1(yw), add16(uw, qdmulh_s16(uw, splat16(282u16, 8)))), splat16(17685u16, 8))
}

/// `sqdmulh(x << 7, c)` is `MultHi(x, c)`: the doubled product is
/// `(x * c) << 8`, and nothing saturates.
proof fn lemma_qdmulh_const(a: u16, b: u16, x: int, c: int)
    requires
        0 <= x < 256, 0 <= c < 0x8000,
        a == 128 * x,
        b == c,
    ensures
        qdm1(a, b) as int == yuv_mult_hi(x, c),
        0 <= yuv_mult_hi(x, c) <= (255 * c) / 256,
{
    let p = x * c;
    assert(2 * s16(a) * s16(b) == 256 * p) by (nonlinear_arith)
        requires s16(a) == 128 * x, s16(b) == c, p == x * c;
    assert(0 <= p <= 255 * c) by (nonlinear_arith)
        requires 0 <= x <= 255, 0 <= c, p == x * c;
    assert((256 * p) / 0x1_0000 == p / 256);
}

/// One lane of `sqdmulh`.
pub open spec fn qdm1(a: u16, b: u16) -> u16 {
    (sat_s16((2 * s16(a) * s16(b)) / 0x1_0000) % 0x1_0000) as u16
}

proof fn lemma_qdm_lane(a: Seq<u16>, c: u16, k: int)
    requires
        a.len() == 8,
        0 <= k < 8,
    ensures
        qdmulh_s16(a, splat16(c, 8)).len() == 8,
        qdmulh_s16(a, splat16(c, 8))[k] == qdm1(a[k], c),
{
}

/// `MultHi(u, 33050)` in two parts: 33050 = 2^15 + 282.
proof fn lemma_mult_hi_b(u: int)
    requires
        0 <= u < 256,
    ensures
        yuv_mult_hi(u, 33050) == 128 * u + yuv_mult_hi(u, 282),
        0 <= yuv_mult_hi(u, 33050) <= 32921,
{
}

/// One lane of `nvec_r`, `nvec_g` and `nvec_b`, shifted right by 6 and
/// saturated: `VP8YuvToRgb`.
proof fn lemma_nlane(yw: u16, uw: u16, vw: u16, y: int, u: int, v: int)
    requires
        0 <= y < 256, 0 <= u < 256, 0 <= v < 256,
        yw == 128 * y,
        uw == 128 * u,
        vw == 128 * v,
    ensures
        ({
            let y1 = qdm1(yw, 19077u16);
            let t1 = ((y1 - 14234 + 0x1_0000) % 0x1_0000) as u16;
            let r = ((t1 + qdm1(vw, 26149u16)) % 0x1_0000) as u16;
            let a1 = ((y1 + 8708) % 0x1_0000) as u16;
            let a2 = ((qdm1(uw, 6419u16) + qdm1(vw, 13320u16)) % 0x1_0000) as u16;
            let g = ((a1 - a2 + 0x1_0000) % 0x1_0000) as u16;
            let bs = ((uw + qdm1(uw, 282u16)) % 0x1_0000) as u16;
            let c1 = ((y1 + bs) % 0x1_0000) as u16;
            let b = if c1 < 17685 { 0u16 } else { (c1 - 17685) as u16 };
            &&& sat_u8(s16(((s16(r) / 64) % 0x1_0000) as u16)) as int == yuv_r(y, v)
            &&& sat_u8(s16(((s16(g) / 64) % 0x1_0000) as u16)) as int == yuv_g(y, u, v)
            &&& sat_u8(s16((b as nat / 64) as u16)) as int == yuv_b(y, u)
        }),
{
    hide(qdm1);
    hide(yuv_mult_hi);
    hide(yuv_clip8);
    lemma_qdmulh_const(yw, 19077u16, y, 19077);
    lemma_qdmulh_const(vw, 26149u16, v, 26149);
    lemma_qdmulh_const(uw, 6419u16, u, 6419);
    lemma_qdmulh_const(vw, 13320u16, v, 13320);
    lemma_qdmulh_const(uw, 282u16, u, 282);
    lemma_mult_hi_b(u);
    let y1 = yuv_mult_hi(y, 19077);
    let r0 = yuv_mult_hi(v, 26149);
    let g0 = yuv_mult_hi(u, 6419);
    let g1 = yuv_mult_hi(v, 13320);
    let b0 = yuv_mult_hi(u, 33050);
    lemma_lane_r(y1, r0);
    lemma_lane_g(y1, g0, g1);
    lemma_lane_b(y1, b0);
}

/// Eight lanes of `nvec_r`, `nvec_g`, `nvec_b`, shifted right by 6.
proof fn lemma_convert8n(yw: Seq<u16>, uw: Seq<u16>, vw: Seq<u16>, y: Seq<u8>, u: Seq<u8>, v: Seq<u8>, o: int)
    requires
        yw.len() == 8, uw.len() == 8, vw.len() == 8,
        0 <= o, o + 8 <= y.len(), o + 8 <= u.len(), o + 8 <= v.len(),
        forall|k: int| 0 <= k < 8 ==> (#[trigger] yw[k]) as int == 128 * y[o + k],
        forall|k: int| 0 <= k < 8 ==> (#[trigger] uw[k]) as int == 128 * u[o + k],
        forall|k: int| 0 <= k < 8 ==> (#[trigger] vw[k]) as int == 128 * v[o + k],
    ensures
        nvec_r(yw, vw).len() == 8,
        nvec_g(yw, uw, vw).len() == 8,
        nvec_b(yw, uw).len() == 8,
        forall|k: int|
            0 <= k < 8 ==> #[trigger] lane_ok3(
                srai16(nvec_r(yw, vw), 6), srai16(nvec_g(yw, uw, vw), 6), srli16(nvec_b(yw, uw), 6), y, u, v, o, k,
            ),
{
    hide(qdm1);
    hide(qdmulh_s16);
    hide(yuv_r);
    hide(yuv_g);
    hide(yuv_b);
    assert(pow2_spec(6) == 64) by (compute);
    assert(nvec_y1(yw).len() == 8) by {
        reveal(qdmulh_s16);
    }
    assert forall|k: int| 0 <= k < 8 implies #[trigger] lane_ok3(
        srai16(nvec_r(yw, vw), 6),
        srai16(nvec_g(yw, uw, vw), 6),
        srli16(nvec_b(yw, uw), 6),
        y,
        u,
        v,
        o,
        k,
    ) by {
        assert(yw[k] as int == 128 * y[o + k] && uw[k] as int == 128 * u[o + k] && vw[k] as int == 128 * v[o + k]);
        lemma_nlane(yw[k], uw[k], vw[k], y[o + k] as int, u[o + k] as int, v[o + k] as int);
        lemma_qdm_lane(yw, 19077u16, k);
        lemma_qdm_lane(vw, 26149u16, k);
        lemma_qdm_lane(uw, 6419u16, k);
        lemma_qdm_lane(vw, 13320u16, k);
        lemma_qdm_lane(uw, 282u16, k);
        let y1 = qdm1(yw[k], 19077u16);
        assert(nvec_y1(yw)[k] == y1);
        // Red.
        let t1 = sub16(nvec_y1(yw), splat16(14234u16, 8));
        assert(t1[k] == ((y1 - 14234 + 0x1_0000) % 0x1_0000) as u16);
        let t2 = nvec_r(yw, vw);
        assert(t2[k] == ((t1[k] + qdm1(vw[k], 26149u16)) % 0x1_0000) as u16);
        assert(srai16(t2, 6)[k] == ((s16(t2[k]) / 64) % 0x1_0000) as u16);
        // Green.
        let a1 = add16(nvec_y1(yw), splat16(8708u16, 8));
        assert(a1[k] == ((y1 + 8708) % 0x1_0000) as u16);
        let a2 = add16(qdmulh_s16(uw, splat16(6419u16, 8)), qdmulh_s16(vw, splat16(13320u16, 8)));
        assert(a2[k] == ((qdm1(uw[k], 6419u16) + qdm1(vw[k], 13320u16)) % 0x1_0000) as u16);
        let a3 = nvec_g(yw, uw, vw);
        assert(a3[k] == ((a1[k] - a2[k] + 0x1_0000) % 0x1_0000) as u16);
        assert(srai16(a3, 6)[k] == ((s16(a3[k]) / 64) % 0x1_0000) as u16);
        // Blue.
        let bs = add16(uw, qdmulh_s16(uw, splat16(282u16, 8)));
        assert(bs[k] == ((uw[k] + qdm1(uw[k], 282u16)) % 0x1_0000) as u16);
        let c1 = add16(nvec_y1(yw), bs);
        assert(c1[k] == ((y1 + bs[k]) % 0x1_0000) as u16);
        let c2 = nvec_b(yw, uw);
        assert(c2[k] == if c1[k] < 17685 { 0u16 } else { (c1[k] - 17685) as u16 });
        assert(srli16(c2, 6)[k] == (c2[k] as nat / 64) as u16);
    }
}

/// The 16-bit lanes of `nwiden_lo` and `nwiden_hi` are the bytes times 128.
proof fn lemma_nwiden(y: Seq<u8>)
    requires
        y.len() == 16,
    ensures
        nwiden_lo(y).len() == 8,
        nwiden_hi(y).len() == 8,
        forall|k: int| 0 <= k < 8 ==> (#[trigger] nwiden_lo(y)[k]) as int == 128 * y[k],
        forall|k: int| 0 <= k < 8 ==> (#[trigger] nwiden_hi(y)[k]) as int == 128 * y[8 + k],
{
    let z = splat8(0u8, 16);
    let lo = unpacklo8_lanes(y, z);
    let hi = unpackhi8_lanes(y, z);
    lemma_unpack8(y, z);
    assert(pow2_spec(7) == 128) by (compute);
    assert forall|k: int| 0 <= k < 8 implies (#[trigger] nwiden_lo(y)[k]) as int == 128 * y[k] by {
        assert(pair2(lo, 0, k) == (y[k], z[k]));
        lemma_le16_value(lo[2 * k], lo[2 * k + 1]);
        assert(u16s(lo)[k] as int == y[k]);
    }
    assert forall|k: int| 0 <= k < 8 implies (#[trigger] nwiden_hi(y)[k]) as int == 128 * y[8 + k] by {
        assert(pair2(hi, 0, k) == (y[8 + k], z[8 + k]));
        lemma_le16_value(hi[2 * k], hi[2 * k + 1]);
        assert(u16s(hi)[k] as int == y[8 + k]);
    }
}

/// The three byte vectors `yuv_pack4_neon` packs.
pub open spec fn nconv_r(y: Seq<u8>, v: Seq<u8>) -> Seq<u8> {
    packus16_lanes(srai16(nvec_r(nwiden_lo(y), nwiden_lo(v)), 6), srai16(nvec_r(nwiden_hi(y), nwiden_hi(v)), 6))
}

pub open spec fn nconv_g(y: Seq<u8>, u: Seq<u8>, v: Seq<u8>) -> Seq<u8> {
    packus16_lanes(
        srai16(nvec_g(nwiden_lo(y), nwiden_lo(u), nwiden_lo(v)), 6),
        srai16(nvec_g(nwiden_hi(y), nwiden_hi(u), nwiden_hi(v)), 6),
    )
}

pub open spec fn nconv_b(y: Seq<u8>, u: Seq<u8>) -> Seq<u8> {
    packus16_lanes(srli16(nvec_b(nwiden_lo(y), nwiden_lo(u)), 6), srli16(nvec_b(nwiden_hi(y), nwiden_hi(u)), 6))
}

/// They are `VP8YuvToRgb`, lane by lane.
proof fn lemma_convert16n(y: Seq<u8>, u: Seq<u8>, v: Seq<u8>)
    requires
        y.len() == 16, u.len() == 16, v.len() == 16,
    ensures
        nconv_r(y, v).len() == 16,
        nconv_g(y, u, v).len() == 16,
        nconv_b(y, u).len() == 16,
        forall|i: int|
            0 <= i < 16 ==> #[trigger] rgb_lane_ok(y, 0, u, v, nconv_r(y, v), nconv_g(y, u, v), nconv_b(y, u), i),
{
    hide(nvec_r);
    hide(nvec_g);
    hide(nvec_b);
    hide(nwiden_lo);
    hide(nwiden_hi);
    hide(srai16);
    hide(srli16);
    lemma_nwiden(y);
    lemma_nwiden(u);
    lemma_nwiden(v);
    let (yl, ul, vl) = (nwiden_lo(y), nwiden_lo(u), nwiden_lo(v));
    let (yh, uh, vh) = (nwiden_hi(y), nwiden_hi(u), nwiden_hi(v));
    lemma_convert8n(yl, ul, vl, y, u, v, 0);
    lemma_convert8n(yh, uh, vh, y, u, v, 8);
    let (rl, gl, bl) = (srai16(nvec_r(yl, vl), 6), srai16(nvec_g(yl, ul, vl), 6), srli16(nvec_b(yl, ul), 6));
    let (rh, gh, bh) = (srai16(nvec_r(yh, vh), 6), srai16(nvec_g(yh, uh, vh), 6), srli16(nvec_b(yh, uh), 6));
    assert(rl.len() == 8 && gl.len() == 8 && bl.len() == 8 && rh.len() == 8 && gh.len() == 8 && bh.len() == 8) by {
        reveal(srai16);
        reveal(srli16);
    }
    lemma_packus(rl, rh);
    lemma_packus(gl, gh);
    lemma_packus(bl, bh);
    assert forall|i: int| 0 <= i < 16 implies #[trigger] rgb_lane_ok(
        y,
        0,
        u,
        v,
        nconv_r(y, v),
        nconv_g(y, u, v),
        nconv_b(y, u),
        i,
    ) by {
        if i < 8 {
            assert(lane_ok3(rl, gl, bl, y, u, v, 0, i));
            assert(nconv_r(y, v)[i] == sat_u8(s16(rl[i])));
            assert(nconv_g(y, u, v)[i] == sat_u8(s16(gl[i])));
            assert(nconv_b(y, u)[i] == sat_u8(s16(bl[i])));
        } else {
            assert(nconv_r(y, v)[i] == sat_u8(s16(rh[i - 8])));
            assert(nconv_g(y, u, v)[i] == sat_u8(s16(gh[i - 8])));
            assert(nconv_b(y, u)[i] == sat_u8(s16(bh[i - 8])));
            assert(lane_ok3(rh, gh, bh, y, u, v, 8, i - 8));
        }
    }
}

// The same conversion thirty-two pixels at a time, in the sixteen 16-bit
// lanes of a 256-bit vector: every operation works within the vector's
// sixteen-byte halves.

/// Bytes widened to the high halves of 16-bit lanes: the low eight of each
/// sixteen-byte half.
pub open spec fn widen_lo32(y: Seq<u8>) -> Seq<u16> {
    u16s(unpacklo8_lanes(splat8(0u8, 32), y))
}

/// The high eight of each half.
pub open spec fn widen_hi32(y: Seq<u8>) -> Seq<u16> {
    u16s(unpackhi8_lanes(splat8(0u8, 32), y))
}

pub open spec fn wide_y1(yw: Seq<u16>) -> Seq<u16> {
    mulhi_u16(yw, splat16(19077u16, 16))
}

pub open spec fn wide_r(yw: Seq<u16>, vw: Seq<u16>) -> Seq<u16> {
    srai16(add16(sub16(wide_y1(yw), splat16(14234u16, 16)), mulhi_u16(vw, splat16(26149u16, 16))), 6)
}

pub open spec fn wide_g(yw: Seq<u16>, uw: Seq<u16>, vw: Seq<u16>) -> Seq<u16> {
    srai16(
        sub16(
            add16(wide_y1(yw), splat16(8708u16, 16)),
            add16(mulhi_u16(uw, splat16(6419u16, 16)), mulhi_u16(vw, splat16(13320u16, 16))),
        ),
        6,
    )
}

pub open spec fn wide_b(yw: Seq<u16>, uw: Seq<u16>) -> Seq<u16> {
    srli16(subs_u16(add16(wide_y1(yw), mulhi_u16(uw, splat16(33050u16, 16))), splat16(17685u16, 16)), 6)
}

/// The bytes that the low (`h == 0`) or high (`h == 8`) unpack of
/// thirty-two bytes takes: eight from each sixteen-byte half.
pub open spec fn half_bytes(y: Seq<u8>, h: int) -> Seq<u8> {
    Seq::new(16, |k: int| y[(k / 8) * 16 + h + k % 8])
}

/// Sixteen lanes of `wide_r`, `wide_g`, `wide_b`.
proof fn lemma_convert_wide(yw: Seq<u16>, uw: Seq<u16>, vw: Seq<u16>, y: Seq<u8>, u: Seq<u8>, v: Seq<u8>)
    requires
        yw.len() == 16, uw.len() == 16, vw.len() == 16,
        y.len() == 16, u.len() == 16, v.len() == 16,
        forall|k: int| 0 <= k < 16 ==> (#[trigger] yw[k]) as int == 256 * y[k],
        forall|k: int| 0 <= k < 16 ==> (#[trigger] uw[k]) as int == 256 * u[k],
        forall|k: int| 0 <= k < 16 ==> (#[trigger] vw[k]) as int == 256 * v[k],
    ensures
        wide_r(yw, vw).len() == 16,
        wide_g(yw, uw, vw).len() == 16,
        wide_b(yw, uw).len() == 16,
        forall|k: int|
            0 <= k < 16 ==> #[trigger] lane_ok3(wide_r(yw, vw), wide_g(yw, uw, vw), wide_b(yw, uw), y, u, v, 0, k),
{
    assert(pow2_spec(6) == 64) by (compute);
    assert forall|k: int| 0 <= k < 16 implies #[trigger] lane_ok3(
        wide_r(yw, vw),
        wide_g(yw, uw, vw),
        wide_b(yw, uw),
        y,
        u,
        v,
        0,
        k,
    ) by {
        let yk = y[k] as int;
        let uk = u[k] as int;
        let vk = v[k] as int;
        assert(yw[k] as int == 256 * yk && uw[k] as int == 256 * uk && vw[k] as int == 256 * vk);
        lemma_mulhi_const(yw[k], 19077u16, yk, 19077);
        lemma_mulhi_const(vw[k], 26149u16, vk, 26149);
        lemma_mulhi_const(uw[k], 6419u16, uk, 6419);
        lemma_mulhi_const(vw[k], 13320u16, vk, 13320);
        lemma_mulhi_const(uw[k], 33050u16, uk, 33050);
        let y1 = yuv_mult_hi(yk, 19077);
        let r0 = yuv_mult_hi(vk, 26149);
        let g0 = yuv_mult_hi(uk, 6419);
        let g1 = yuv_mult_hi(vk, 13320);
        let b0 = yuv_mult_hi(uk, 33050);
        assert(wide_y1(yw)[k] as int == y1);
        assert(mulhi_u16(vw, splat16(26149u16, 16))[k] as int == r0);
        assert(mulhi_u16(uw, splat16(6419u16, 16))[k] as int == g0);
        assert(mulhi_u16(vw, splat16(13320u16, 16))[k] as int == g1);
        assert(mulhi_u16(uw, splat16(33050u16, 16))[k] as int == b0);
        lemma_lane_r(y1, r0);
        lemma_lane_g(y1, g0, g1);
        lemma_lane_b(y1, b0);
        // Red.
        let t1 = sub16(wide_y1(yw), splat16(14234u16, 16));
        assert(t1[k] == ((y1 - 14234 + 0x1_0000) % 0x1_0000) as u16);
        let t2 = add16(t1, mulhi_u16(vw, splat16(26149u16, 16)));
        assert(t2[k] == ((t1[k] + r0) % 0x1_0000) as u16);
        assert(wide_r(yw, vw)[k] == ((s16(t2[k]) / 64) % 0x1_0000) as u16);
        // Green.
        let a1 = add16(wide_y1(yw), splat16(8708u16, 16));
        assert(a1[k] == ((y1 + 8708) % 0x1_0000) as u16);
        let a2 = add16(mulhi_u16(uw, splat16(6419u16, 16)), mulhi_u16(vw, splat16(13320u16, 16)));
        assert(a2[k] == ((g0 + g1) % 0x1_0000) as u16);
        let a3 = sub16(a1, a2);
        assert(a3[k] == ((a1[k] - a2[k] + 0x1_0000) % 0x1_0000) as u16);
        assert(wide_g(yw, uw, vw)[k] == ((s16(a3[k]) / 64) % 0x1_0000) as u16);
        // Blue.
        let c1 = add16(wide_y1(yw), mulhi_u16(uw, splat16(33050u16, 16)));
        assert(c1[k] == ((y1 + b0) % 0x1_0000) as u16);
        let c2 = subs_u16(c1, splat16(17685u16, 16));
        assert(c2[k] == if c1[k] < 17685 { 0u16 } else { (c1[k] - 17685) as u16 });
        assert(wide_b(yw, uw)[k] == (c2[k] as nat / 64) as u16);
    }
}

/// The 16-bit lanes of thirty-two bytes unpacked under zeros are the
/// bytes times 256.
proof fn lemma_widen32(y: Seq<u8>)
    requires
        y.len() == 32,
    ensures
        widen_lo32(y).len() == 16,
        widen_hi32(y).len() == 16,
        forall|k: int| 0 <= k < 16 ==> (#[trigger] widen_lo32(y)[k]) as int == 256 * half_bytes(y, 0)[k],
        forall|k: int| 0 <= k < 16 ==> (#[trigger] widen_hi32(y)[k]) as int == 256 * half_bytes(y, 8)[k],
{
    let z = splat8(0u8, 32);
    let lo = unpacklo8_lanes(z, y);
    let hi = unpackhi8_lanes(z, y);
    lemma_unpack8x(z, y);
    assert forall|k: int| 0 <= k < 16 implies (#[trigger] widen_lo32(y)[k]) as int == 256 * half_bytes(y, 0)[k] by {
        assert(pair2(lo, 0, k) == (z[(k / 8) * 16 + k % 8], y[(k / 8) * 16 + k % 8]));
        lemma_le16_value(lo[2 * k], lo[2 * k + 1]);
    }
    assert forall|k: int| 0 <= k < 16 implies (#[trigger] widen_hi32(y)[k]) as int == 256 * half_bytes(y, 8)[k] by {
        assert(pair2(hi, 0, k) == (z[(k / 8) * 16 + 8 + k % 8], y[(k / 8) * 16 + 8 + k % 8]));
        lemma_le16_value(hi[2 * k], hi[2 * k + 1]);
    }
}

/// The three byte vectors `yuv_pack4_avx2` packs.
pub open spec fn conv32_r(y: Seq<u8>, v: Seq<u8>) -> Seq<u8> {
    packus16_lanes(wide_r(widen_lo32(y), widen_lo32(v)), wide_r(widen_hi32(y), widen_hi32(v)))
}

pub open spec fn conv32_g(y: Seq<u8>, u: Seq<u8>, v: Seq<u8>) -> Seq<u8> {
    packus16_lanes(
        wide_g(widen_lo32(y), widen_lo32(u), widen_lo32(v)),
        wide_g(widen_hi32(y), widen_hi32(u), widen_hi32(v)),
    )
}

pub open spec fn conv32_b(y: Seq<u8>, u: Seq<u8>) -> Seq<u8> {
    packus16_lanes(wide_b(widen_lo32(y), widen_lo32(u)), wide_b(widen_hi32(y), widen_hi32(u)))
}

/// A saturating pack of two sixteen-lane vectors, byte by byte.
proof fn lemma_packus32(a: Seq<u16>, b: Seq<u16>)
    requires
        a.len() == 16, b.len() == 16,
    ensures
        packus16_lanes(a, b).len() == 32,
        forall|i: int| 0 <= i < 32 && i % 16 < 8 ==> #[trigger] packus16_lanes(a, b)[i] == sat_u8(
            s16(a[(i / 16) * 8 + i % 16]),
        ),
        forall|i: int| 0 <= i < 32 && i % 16 >= 8 ==> #[trigger] packus16_lanes(a, b)[i] == sat_u8(
            s16(b[(i / 16) * 8 + i % 16 - 8]),
        ),
{
}

/// They are `VP8YuvToRgb`, lane by lane.
proof fn lemma_convert32(y: Seq<u8>, u: Seq<u8>, v: Seq<u8>)
    requires
        y.len() == 32, u.len() == 32, v.len() == 32,
    ensures
        conv32_r(y, v).len() == 32,
        conv32_g(y, u, v).len() == 32,
        conv32_b(y, u).len() == 32,
        forall|i: int|
            0 <= i < 32 ==> #[trigger] rgb_lane_ok(y, 0, u, v, conv32_r(y, v), conv32_g(y, u, v), conv32_b(y, u), i),
{
    hide(wide_r);
    hide(wide_g);
    hide(wide_b);
    hide(widen_lo32);
    hide(widen_hi32);
    lemma_widen32(y);
    lemma_widen32(u);
    lemma_widen32(v);
    let (yl, ul, vl) = (widen_lo32(y), widen_lo32(u), widen_lo32(v));
    let (yh, uh, vh) = (widen_hi32(y), widen_hi32(u), widen_hi32(v));
    lemma_convert_wide(yl, ul, vl, half_bytes(y, 0), half_bytes(u, 0), half_bytes(v, 0));
    lemma_convert_wide(yh, uh, vh, half_bytes(y, 8), half_bytes(u, 8), half_bytes(v, 8));
    lemma_packus32(wide_r(yl, vl), wide_r(yh, vh));
    lemma_packus32(wide_g(yl, ul, vl), wide_g(yh, uh, vh));
    lemma_packus32(wide_b(yl, ul), wide_b(yh, uh));
    assert forall|i: int| 0 <= i < 32 implies #[trigger] rgb_lane_ok(
        y,
        0,
        u,
        v,
        conv32_r(y, v),
        conv32_g(y, u, v),
        conv32_b(y, u),
        i,
    ) by {
        if i % 16 < 8 {
            let k = (i / 16) * 8 + i % 16;
            assert(k / 8 == i / 16 && k % 8 == i % 16);
            assert(lane_ok3(
                wide_r(yl, vl), wide_g(yl, ul, vl), wide_b(yl, ul), half_bytes(y, 0), half_bytes(u, 0),
                half_bytes(v, 0), 0, k,
            ));
            assert(half_bytes(y, 0)[k] == y[i] && half_bytes(u, 0)[k] == u[i] && half_bytes(v, 0)[k] == v[i]);
            assert(conv32_r(y, v)[i] == sat_u8(s16(wide_r(yl, vl)[k])));
            assert(conv32_g(y, u, v)[i] == sat_u8(s16(wide_g(yl, ul, vl)[k])));
            assert(conv32_b(y, u)[i] == sat_u8(s16(wide_b(yl, ul)[k])));
        } else {
            let k = (i / 16) * 8 + i % 16 - 8;
            assert(k / 8 == i / 16 && k % 8 == i % 16 - 8);
            assert(lane_ok3(
                wide_r(yh, vh), wide_g(yh, uh, vh), wide_b(yh, uh), half_bytes(y, 8), half_bytes(u, 8),
                half_bytes(v, 8), 0, k,
            ));
            assert(half_bytes(y, 8)[k] == y[i] && half_bytes(u, 8)[k] == u[i] && half_bytes(v, 8)[k] == v[i]);
            assert(conv32_r(y, v)[i] == sat_u8(s16(wide_r(yh, vh)[k])));
            assert(conv32_g(y, u, v)[i] == sat_u8(s16(wide_g(yh, uh, vh)[k])));
            assert(conv32_b(y, u)[i] == sat_u8(s16(wide_b(yh, uh)[k])));
        }
    }
}

/// Red of the first `n` pixels of a line (luma `ys[yo..]`, chroma `u` and
/// `v`), as a byte lane.
pub open spec fn line_r(ys: Seq<u8>, yo: int, v: Seq<u8>, n: int) -> Seq<u8> {
    Seq::new(n as nat, |i: int| yuv_r(ys[yo + i] as int, v[i] as int) as u8)
}

/// Green.
pub open spec fn line_g(ys: Seq<u8>, yo: int, u: Seq<u8>, v: Seq<u8>, n: int) -> Seq<u8> {
    Seq::new(n as nat, |i: int| yuv_g(ys[yo + i] as int, u[i] as int, v[i] as int) as u8)
}

/// Blue.
pub open spec fn line_b(ys: Seq<u8>, yo: int, u: Seq<u8>, n: int) -> Seq<u8> {
    Seq::new(n as nat, |i: int| yuv_b(ys[yo + i] as int, u[i] as int) as u8)
}

/// Channel `k` of the four-byte layout `kind` (1 to 3).
pub open spec fn chan4(kind: int, r: Seq<u8>, g: Seq<u8>, b: Seq<u8>, a: Seq<u8>, k: int) -> Seq<u8> {
    if kind == 1 {
        if k == 0 { r } else if k == 1 { g } else if k == 2 { b } else { a }
    } else if kind == 2 {
        if k == 0 { b } else if k == 1 { g } else if k == 2 { r } else { a }
    } else {
        if k == 0 { a } else if k == 1 { r } else if k == 2 { g } else { b }
    }
}

/// `s` is `s0` with the first `m` pixels of a line of `n`, converted, set
/// in layout `kind` at `s[oo..oo + 4n]`; nothing outside that range differs.
pub open spec fn line_packed4(
    kind: int, s0: Seq<u8>, s: Seq<u8>, ys: Seq<u8>, yo: int, u: Seq<u8>, v: Seq<u8>, a: Seq<u8>, oo: int, m: int,
    n: int,
) -> bool {
    let (r, g, b) = (line_r(ys, yo, v, n), line_g(ys, yo, u, v, n), line_b(ys, yo, u, n));
    packed4(
        s0, s, chan4(kind, r, g, b, a, 0), chan4(kind, r, g, b, a, 1), chan4(kind, r, g, b, a, 2),
        chan4(kind, r, g, b, a, 3), oo, m, n,
    )
}

/// Thirty-two pixels converted at `j` are the line's channels there.
proof fn lemma_line32(
    ys: Seq<u8>, yo: int, u: Seq<u8>, v: Seq<u8>, n: int, j: int, y: Seq<u8>, ub: Seq<u8>, vb: Seq<u8>,
)
    requires
        0 <= yo, 0 <= j, j + 32 <= n,
        yo + n <= ys.len(), n <= u.len(), n <= v.len(),
        y == ys.subrange(yo + j, yo + j + 32),
        ub == u.subrange(j, j + 32),
        vb == v.subrange(j, j + 32),
    ensures
        conv32_r(y, vb) == line_r(ys, yo, v, n).subrange(j, j + 32),
        conv32_g(y, ub, vb) == line_g(ys, yo, u, v, n).subrange(j, j + 32),
        conv32_b(y, ub) == line_b(ys, yo, u, n).subrange(j, j + 32),
{
    hide(conv32_r);
    hide(conv32_g);
    hide(conv32_b);
    lemma_convert32(y, ub, vb);
    let (r, g, b) = (conv32_r(y, vb), conv32_g(y, ub, vb), conv32_b(y, ub));
    assert forall|i: int| 0 <= i < 32 implies r[i] == line_r(ys, yo, v, n)[j + i] && g[i] == line_g(ys, yo, u, v, n)[j
        + i] && b[i] == line_b(ys, yo, u, n)[j + i] by {
        assert(rgb_lane_ok(y, 0, ub, vb, r, g, b, i));
        assert(y[0 + i] == ys[yo + j + i] && ub[i] == u[j + i] && vb[i] == v[j + i]);
    }
    assert(r =~= line_r(ys, yo, v, n).subrange(j, j + 32));
    assert(g =~= line_g(ys, yo, u, v, n).subrange(j, j + 32));
    assert(b =~= line_b(ys, yo, u, n).subrange(j, j + 32));
}

/// Sixteen pixels converted at `j` on NEON are the line's channels there.
proof fn lemma_line16n(
    ys: Seq<u8>, yo: int, u: Seq<u8>, v: Seq<u8>, n: int, j: int, y: Seq<u8>, ub: Seq<u8>, vb: Seq<u8>,
)
    requires
        0 <= yo, 0 <= j, j + 16 <= n,
        yo + n <= ys.len(), n <= u.len(), n <= v.len(),
        y == ys.subrange(yo + j, yo + j + 16),
        ub == u.subrange(j, j + 16),
        vb == v.subrange(j, j + 16),
    ensures
        nconv_r(y, vb) == line_r(ys, yo, v, n).subrange(j, j + 16),
        nconv_g(y, ub, vb) == line_g(ys, yo, u, v, n).subrange(j, j + 16),
        nconv_b(y, ub) == line_b(ys, yo, u, n).subrange(j, j + 16),
{
    hide(nconv_r);
    hide(nconv_g);
    hide(nconv_b);
    lemma_convert16n(y, ub, vb);
    let (r, g, b) = (nconv_r(y, vb), nconv_g(y, ub, vb), nconv_b(y, ub));
    assert forall|i: int| 0 <= i < 16 implies r[i] == line_r(ys, yo, v, n)[j + i] && g[i] == line_g(ys, yo, u, v, n)[j
        + i] && b[i] == line_b(ys, yo, u, n)[j + i] by {
        assert(rgb_lane_ok(y, 0, ub, vb, r, g, b, i));
        assert(y[0 + i] == ys[yo + j + i] && ub[i] == u[j + i] && vb[i] == v[j + i]);
    }
    assert(r =~= line_r(ys, yo, v, n).subrange(j, j + 16));
    assert(g =~= line_g(ys, yo, u, v, n).subrange(j, j + 16));
    assert(b =~= line_b(ys, yo, u, n).subrange(j, j + 16));
}

/// Output layouts: ARGB words (`Vec<u32>`, kind 0), or bytes in the order
/// RGBA (1), BGRA (2), ARGB (3), RGB (4), BGR (5).
pub open spec fn kind_bpp(kind: u8) -> nat {
    if kind == 0 { 1 } else if kind <= 3 { 4 } else { 3 }
}

/// `yuv_to_rgb` on `y[yo..]`, `su` and `sv`, sixteen pixels at a time,
/// into `su` (red), `sg` (green) and `sv` (blue): the pixels `0..r`.
fn yuv_to_rgb_sse2(ys: &[u8], yo: usize, su: &mut [u8], sv: &mut [u8], sg: &mut [u8], len: usize) -> (r: usize)
    requires
        yo + len <= ys@.len(),
        len <= old(su)@.len(),
        len <= old(sv)@.len(),
        len <= old(sg)@.len(),
    ensures
        r <= len,
        final(su)@.len() == old(su)@.len(),
        final(sv)@.len() == old(sv)@.len(),
        final(sg)@.len() == old(sg)@.len(),
        rgb_lanes(ys@, yo as int, old(su)@, old(sv)@, final(su)@, final(sv)@, final(sg)@, r as int),
{
    proof {
        assert(ys@.len() == ys.len());
        assert(33050u16 as i16 == -32486i16) by (bit_vector);
    }
    let ghost u0 = su@;
    let ghost v0 = sv@;
    let z = _mm_setzero_si128();
    let k19077 = _mm_set1_epi16(19077);
    let k26149 = _mm_set1_epi16(26149);
    let k6419 = _mm_set1_epi16(6419);
    let k13320 = _mm_set1_epi16(13320);
    let k33050 = _mm_set1_epi16(33050u16 as i16);
    let k14234 = _mm_set1_epi16(14234);
    let k8708 = _mm_set1_epi16(8708);
    let k17685 = _mm_set1_epi16(17685);
    let mut j: usize = 0;
    while len - j >= 16
        invariant
            j <= len,
            yo + len <= ys@.len(),
            len <= su@.len(),
            len <= sv@.len(),
            len <= sg@.len(),
            su@.len() == old(su)@.len(),
            sv@.len() == old(sv)@.len(),
            sg@.len() == old(sg)@.len(),
            ys@.len() <= usize::MAX,
            u0 == old(su)@,
            v0 == old(sv)@,
            rgb_lanes(ys@, yo as int, u0, v0, su@, sv@, sg@, j as int),
            b128(z) == splat8(0u8, 16),
            u16x8(k19077) == splat16(19077u16, 8),
            u16x8(k26149) == splat16(26149u16, 8),
            u16x8(k6419) == splat16(6419u16, 8),
            u16x8(k13320) == splat16(13320u16, 8),
            u16x8(k33050) == splat16(33050u16, 8),
            u16x8(k14234) == splat16(14234u16, 8),
            u16x8(k8708) == splat16(8708u16, 8),
            u16x8(k17685) == splat16(17685u16, 8),
        decreases len - j,
    {
        let ghost su1 = su@;
        let ghost sv1 = sv@;
        let ghost sg1 = sg@;
        let y = load128_u8(ys, yo + j);
        let u = load128_u8(su, j);
        let v = load128_u8(sv, j);
        // `MultHi(x, c)` as `_mm_mulhi_epu16(x << 8, c)`.
        let ylo = _mm_mulhi_epu16(_mm_unpacklo_epi8(z, y), k19077);
        let yhi = _mm_mulhi_epu16(_mm_unpackhi_epi8(z, y), k19077);
        let ulo = _mm_unpacklo_epi8(z, u);
        let uhi = _mm_unpackhi_epi8(z, u);
        let vlo = _mm_unpacklo_epi8(z, v);
        let vhi = _mm_unpackhi_epi8(z, v);
        let rlo = _mm_srai_epi16::<6>(_mm_add_epi16(_mm_sub_epi16(ylo, k14234), _mm_mulhi_epu16(vlo, k26149)));
        let rhi = _mm_srai_epi16::<6>(_mm_add_epi16(_mm_sub_epi16(yhi, k14234), _mm_mulhi_epu16(vhi, k26149)));
        let glo = _mm_srai_epi16::<6>(_mm_sub_epi16(_mm_add_epi16(ylo, k8708),
            _mm_add_epi16(_mm_mulhi_epu16(ulo, k6419), _mm_mulhi_epu16(vlo, k13320))));
        let ghi = _mm_srai_epi16::<6>(_mm_sub_epi16(_mm_add_epi16(yhi, k8708),
            _mm_add_epi16(_mm_mulhi_epu16(uhi, k6419), _mm_mulhi_epu16(vhi, k13320))));
        let blo = _mm_srli_epi16::<6>(_mm_subs_epu16(_mm_add_epi16(ylo, _mm_mulhi_epu16(ulo, k33050)), k17685));
        let bhi = _mm_srli_epi16::<6>(_mm_subs_epu16(_mm_add_epi16(yhi, _mm_mulhi_epu16(uhi, k33050)), k17685));
        store128_u8(su, j, _mm_packus_epi16(rlo, rhi));
        store128_u8(sg, j, _mm_packus_epi16(glo, ghi));
        store128_u8(sv, j, _mm_packus_epi16(blo, bhi));
        proof {
            let (yb, ub, vb) = (b128(y), b128(u), b128(v));
            assert(u16x8(ylo) == vec_y1(widen_lo(yb)));
            assert(u16x8(yhi) == vec_y1(widen_hi(yb)));
            assert(u16x8(rlo) == vec_r(widen_lo(yb), widen_lo(vb)));
            assert(u16x8(rhi) == vec_r(widen_hi(yb), widen_hi(vb)));
            assert(u16x8(glo) == vec_g(widen_lo(yb), widen_lo(ub), widen_lo(vb)));
            assert(u16x8(ghi) == vec_g(widen_hi(yb), widen_hi(ub), widen_hi(vb)));
            assert(u16x8(blo) == vec_b(widen_lo(yb), widen_lo(ub)));
            assert(u16x8(bhi) == vec_b(widen_hi(yb), widen_hi(ub)));
            lemma_convert16(yb, ub, vb);
            lemma_rgb16(ys@, yo as int, u0, v0, su1, sv1, sg1, su@, sv@, sg@, j as int, yb, ub, vb,
                conv_r(yb, vb), conv_g(yb, ub, vb), conv_b(yb, ub));
        }
        j = j + 16;
    }
    j
}

/// Packs `len` pixels into four-byte pixels at `ob[oo..]`, byte `k` of
/// each from `ck`: sixteen at a time as two perfect-shuffle rounds (byte
/// unpacks on SSE2, `zip1`/`zip2` on NEON), the rest one by one.
fn pack4(c0: &[u8], c1: &[u8], c2: &[u8], c3: &[u8], ob: &mut [u8], oo: usize, len: usize)
    requires
        len <= c0@.len(), len <= c1@.len(), len <= c2@.len(), len <= c3@.len(),
        oo + 4 * len <= old(ob)@.len(),
    ensures
        final(ob)@.len() == old(ob)@.len(),
        packed4(old(ob)@, final(ob)@, c0@, c1@, c2@, c3@, oo as int, len as int, len as int),
{
    proof {
        assert(ob@.len() == ob.len());
    }
    let ghost s0 = ob@;
    let mut j: usize = 0;
    if cfg!(target_arch = "aarch64") && has_neon() {
        while len - j >= 16
            invariant
                neon(),
                j <= len,
                len <= c0@.len(), len <= c1@.len(), len <= c2@.len(), len <= c3@.len(),
                oo + 4 * len <= ob@.len(),
                ob@.len() == old(ob)@.len(),
                ob@.len() <= usize::MAX,
                s0 == old(ob)@,
                packed4(s0, ob@, c0@, c1@, c2@, c3@, oo as int, j as int, len as int),
            decreases len - j,
        {
            proof {
                assert(oo + 4 * j + 64 <= oo + 4 * len);
            }
            let ghost s1 = ob@;
            let x0 = vld1q_u8_at(c0, j);
            let x1 = vld1q_u8_at(c1, j);
            let x2 = vld1q_u8_at(c2, j);
            let x3 = vld1q_u8_at(c3, j);
            let y0 = vzip1q_u8(x0, x2);
            let y1 = vzip2q_u8(x0, x2);
            let y2 = vzip1q_u8(x1, x3);
            let y3 = vzip2q_u8(x1, x3);
            let o = oo + 4 * j;
            vst1q_u8_at(ob, o, vzip1q_u8(y0, y2));
            let ghost s2 = ob@;
            vst1q_u8_at(ob, o + 16, vzip2q_u8(y0, y2));
            let ghost s3 = ob@;
            vst1q_u8_at(ob, o + 32, vzip1q_u8(y1, y3));
            let ghost s4 = ob@;
            vst1q_u8_at(ob, o + 48, vzip2q_u8(y1, y3));
            proof {
                lemma_pack16(s0, s1, s2, s3, s4, ob@, c0@, c1@, c2@, c3@, oo as int, j as int, len as int,
                    n8(x0), n8(x1), n8(x2), n8(x3));
            }
            j = j + 16;
        }
    } else {
        // SAFETY: SSE2 is part of x86-64 (and emulated elsewhere).
        j = unsafe { pack4_sse2(c0, c1, c2, c3, ob, oo, len) };
    }
    while j < len
        invariant
            j <= len,
            len <= c0@.len(), len <= c1@.len(), len <= c2@.len(), len <= c3@.len(),
            oo + 4 * len <= ob@.len(),
            ob@.len() == old(ob)@.len(),
            ob@.len() <= usize::MAX,
            s0 == old(ob)@,
            packed4(s0, ob@, c0@, c1@, c2@, c3@, oo as int, j as int, len as int),
        decreases len - j,
    {
        proof {
            assert(oo + 4 * j + 4 <= oo + 4 * len);
        }
        let ghost s1 = ob@;
        let o = oo + 4 * j;
        set(ob, o, get(c0, j));
        set(ob, o + 1, get(c1, j));
        set(ob, o + 2, get(c2, j));
        set(ob, o + 3, get(c3, j));
        proof {
            lemma_pack1(s0, s1, ob@, c0@, c1@, c2@, c3@, oo as int, j as int, len as int);
        }
        j = j + 1;
    }
}

/// `pack4`'s SSE2 loop: the pixels `0..r`, a multiple of sixteen.
fn pack4_sse2(c0: &[u8], c1: &[u8], c2: &[u8], c3: &[u8], ob: &mut [u8], oo: usize, len: usize) -> (r: usize)
    requires
        len <= c0@.len(), len <= c1@.len(), len <= c2@.len(), len <= c3@.len(),
        oo + 4 * len <= old(ob)@.len(),
    ensures
        r <= len,
        final(ob)@.len() == old(ob)@.len(),
        packed4(old(ob)@, final(ob)@, c0@, c1@, c2@, c3@, oo as int, r as int, len as int),
{
    proof {
        assert(ob@.len() == ob.len());
    }
    let ghost s0 = ob@;
    let mut j: usize = 0;
    while len - j >= 16
        invariant
            j <= len,
            len <= c0@.len(), len <= c1@.len(), len <= c2@.len(), len <= c3@.len(),
            oo + 4 * len <= ob@.len(),
            ob@.len() == old(ob)@.len(),
            ob@.len() <= usize::MAX,
            s0 == old(ob)@,
            packed4(s0, ob@, c0@, c1@, c2@, c3@, oo as int, j as int, len as int),
        decreases len - j,
    {
        proof {
            assert(oo + 4 * j + 64 <= oo + 4 * len);
        }
        let ghost s1 = ob@;
        let x0 = load128_u8(c0, j);
        let x1 = load128_u8(c1, j);
        let x2 = load128_u8(c2, j);
        let x3 = load128_u8(c3, j);
        let y0 = _mm_unpacklo_epi8(x0, x2);
        let y1 = _mm_unpackhi_epi8(x0, x2);
        let y2 = _mm_unpacklo_epi8(x1, x3);
        let y3 = _mm_unpackhi_epi8(x1, x3);
        let o = oo + 4 * j;
        store128_u8(ob, o, _mm_unpacklo_epi8(y0, y2));
        let ghost s2 = ob@;
        store128_u8(ob, o + 16, _mm_unpackhi_epi8(y0, y2));
        let ghost s3 = ob@;
        store128_u8(ob, o + 32, _mm_unpacklo_epi8(y1, y3));
        let ghost s4 = ob@;
        store128_u8(ob, o + 48, _mm_unpackhi_epi8(y1, y3));
        proof {
            lemma_pack16(s0, s1, s2, s3, s4, ob@, c0@, c1@, c2@, c3@, oo as int, j as int, len as int,
                b128(x0), b128(x1), b128(x2), b128(x3));
        }
        j = j + 16;
    }
    j
}

/// `yuv_to_rgb` on `ys[yo..]`, `su` and `sv`, packed with the alpha `sa`
/// into four-byte pixels of layout `kind` at `ob[oo..]`, thirty-two pixels
/// at a time: the pixels `0..r`. The channels are interleaved by a round
/// of byte unpacks and one of 16-bit unpacks, which work within the
/// vectors' halves; `_mm256_permute2x128_si256` puts the halves in order.
#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "avx2"))]
fn yuv_pack4_avx2(
    ys: &[u8], yo: usize, su: &[u8], sv: &[u8], sa: &[u8], ob: &mut [u8], oo: usize, len: usize, kind: u8,
) -> (r: usize)
    requires
        avx2(),
        1 <= kind <= 3,
        yo + len <= ys@.len(),
        len <= su@.len(), len <= sv@.len(), len <= sa@.len(),
        oo + 4 * len <= old(ob)@.len(),
    ensures
        r <= len,
        final(ob)@.len() == old(ob)@.len(),
        line_packed4(kind as int, old(ob)@, final(ob)@, ys@, yo as int, su@, sv@, sa@, oo as int, r as int, len as int),
{
    proof {
        assert(ys@.len() == ys.len());
        assert(ob@.len() == ob.len());
        assert(33050u16 as i16 == -32486i16) by (bit_vector);
    }
    let ghost s0 = ob@;
    let ghost lr = line_r(ys@, yo as int, sv@, len as int);
    let ghost lg = line_g(ys@, yo as int, su@, sv@, len as int);
    let ghost lb = line_b(ys@, yo as int, su@, len as int);
    let ghost e0 = chan4(kind as int, lr, lg, lb, sa@, 0);
    let ghost e1 = chan4(kind as int, lr, lg, lb, sa@, 1);
    let ghost e2 = chan4(kind as int, lr, lg, lb, sa@, 2);
    let ghost e3 = chan4(kind as int, lr, lg, lb, sa@, 3);
    let z = _mm256_setzero_si256();
    let k19077 = _mm256_set1_epi16(19077);
    let k26149 = _mm256_set1_epi16(26149);
    let k6419 = _mm256_set1_epi16(6419);
    let k13320 = _mm256_set1_epi16(13320);
    let k33050 = _mm256_set1_epi16(33050u16 as i16);
    let k14234 = _mm256_set1_epi16(14234);
    let k8708 = _mm256_set1_epi16(8708);
    let k17685 = _mm256_set1_epi16(17685);
    let mut j: usize = 0;
    while len - j >= 32
        invariant
            avx2(),
            1 <= kind <= 3,
            j <= len,
            yo + len <= ys@.len(),
            len <= su@.len(), len <= sv@.len(), len <= sa@.len(),
            oo + 4 * len <= ob@.len(),
            ob@.len() == old(ob)@.len(),
            ob@.len() <= usize::MAX,
            ys@.len() <= usize::MAX,
            s0 == old(ob)@,
            lr == line_r(ys@, yo as int, sv@, len as int),
            lg == line_g(ys@, yo as int, su@, sv@, len as int),
            lb == line_b(ys@, yo as int, su@, len as int),
            e0 == chan4(kind as int, lr, lg, lb, sa@, 0),
            e1 == chan4(kind as int, lr, lg, lb, sa@, 1),
            e2 == chan4(kind as int, lr, lg, lb, sa@, 2),
            e3 == chan4(kind as int, lr, lg, lb, sa@, 3),
            packed4(s0, ob@, e0, e1, e2, e3, oo as int, j as int, len as int),
            b256(z) == splat8(0u8, 32),
            u16x16(k19077) == splat16(19077u16, 16),
            u16x16(k26149) == splat16(26149u16, 16),
            u16x16(k6419) == splat16(6419u16, 16),
            u16x16(k13320) == splat16(13320u16, 16),
            u16x16(k33050) == splat16(33050u16, 16),
            u16x16(k14234) == splat16(14234u16, 16),
            u16x16(k8708) == splat16(8708u16, 16),
            u16x16(k17685) == splat16(17685u16, 16),
        decreases len - j,
    {
        proof {
            assert(oo + 4 * j + 128 <= oo + 4 * len);
        }
        let ghost s1 = ob@;
        let y = load256_u8(ys, yo + j);
        let u = load256_u8(su, j);
        let v = load256_u8(sv, j);
        let a = load256_u8(sa, j);
        // `MultHi(x, c)` as `_mm256_mulhi_epu16(x << 8, c)`.
        let ylo = _mm256_mulhi_epu16(_mm256_unpacklo_epi8(z, y), k19077);
        let yhi = _mm256_mulhi_epu16(_mm256_unpackhi_epi8(z, y), k19077);
        let ulo = _mm256_unpacklo_epi8(z, u);
        let uhi = _mm256_unpackhi_epi8(z, u);
        let vlo = _mm256_unpacklo_epi8(z, v);
        let vhi = _mm256_unpackhi_epi8(z, v);
        let rlo = _mm256_srai_epi16::<6>(_mm256_add_epi16(_mm256_sub_epi16(ylo, k14234), _mm256_mulhi_epu16(vlo, k26149)));
        let rhi = _mm256_srai_epi16::<6>(_mm256_add_epi16(_mm256_sub_epi16(yhi, k14234), _mm256_mulhi_epu16(vhi, k26149)));
        let glo = _mm256_srai_epi16::<6>(_mm256_sub_epi16(_mm256_add_epi16(ylo, k8708),
            _mm256_add_epi16(_mm256_mulhi_epu16(ulo, k6419), _mm256_mulhi_epu16(vlo, k13320))));
        let ghi = _mm256_srai_epi16::<6>(_mm256_sub_epi16(_mm256_add_epi16(yhi, k8708),
            _mm256_add_epi16(_mm256_mulhi_epu16(uhi, k6419), _mm256_mulhi_epu16(vhi, k13320))));
        let blo = _mm256_srli_epi16::<6>(_mm256_subs_epu16(_mm256_add_epi16(ylo, _mm256_mulhi_epu16(ulo, k33050)), k17685));
        let bhi = _mm256_srli_epi16::<6>(_mm256_subs_epu16(_mm256_add_epi16(yhi, _mm256_mulhi_epu16(uhi, k33050)), k17685));
        let r = _mm256_packus_epi16(rlo, rhi);
        let g = _mm256_packus_epi16(glo, ghi);
        let b = _mm256_packus_epi16(blo, bhi);
        proof {
            let (yb, ub, vb) = (b256(y), b256(u), b256(v));
            assert(u16x16(ylo) == wide_y1(widen_lo32(yb)));
            assert(u16x16(yhi) == wide_y1(widen_hi32(yb)));
            assert(u16x16(rlo) == wide_r(widen_lo32(yb), widen_lo32(vb)));
            assert(u16x16(rhi) == wide_r(widen_hi32(yb), widen_hi32(vb)));
            assert(u16x16(glo) == wide_g(widen_lo32(yb), widen_lo32(ub), widen_lo32(vb)));
            assert(u16x16(ghi) == wide_g(widen_hi32(yb), widen_hi32(ub), widen_hi32(vb)));
            assert(u16x16(blo) == wide_b(widen_lo32(yb), widen_lo32(ub)));
            assert(u16x16(bhi) == wide_b(widen_hi32(yb), widen_hi32(ub)));
            lemma_line32(ys@, yo as int, su@, sv@, len as int, j as int, yb, ub, vb);
            assert(b256(r) == lr.subrange(j as int, j + 32));
            assert(b256(g) == lg.subrange(j as int, j + 32));
            assert(b256(b) == lb.subrange(j as int, j + 32));
        }
        let (c0, c1, c2, c3) = if kind == 1 {
            (r, g, b, a)
        } else if kind == 2 {
            (b, g, r, a)
        } else {
            (a, r, g, b)
        };
        let p01l = _mm256_unpacklo_epi8(c0, c1);
        let p01h = _mm256_unpackhi_epi8(c0, c1);
        let p23l = _mm256_unpacklo_epi8(c2, c3);
        let p23h = _mm256_unpackhi_epi8(c2, c3);
        let t0 = _mm256_unpacklo_epi16(p01l, p23l);
        let t1 = _mm256_unpackhi_epi16(p01l, p23l);
        let t2 = _mm256_unpacklo_epi16(p01h, p23h);
        let t3 = _mm256_unpackhi_epi16(p01h, p23h);
        let o = oo + 4 * j;
        store256_u8(ob, o, _mm256_permute2x128_si256::<0x20>(t0, t1));
        let ghost s2 = ob@;
        store256_u8(ob, o + 32, _mm256_permute2x128_si256::<0x20>(t2, t3));
        let ghost s3 = ob@;
        store256_u8(ob, o + 64, _mm256_permute2x128_si256::<0x31>(t0, t1));
        let ghost s4 = ob@;
        store256_u8(ob, o + 96, _mm256_permute2x128_si256::<0x31>(t2, t3));
        proof {
            let (x0, x1, x2, x3) = (b256(c0), b256(c1), b256(c2), b256(c3));
            lemma_shuffle8(x0, x1, x2, x3, b256(p01l), b256(p23l), b256(t0), 0, 0);
            lemma_shuffle8(x0, x1, x2, x3, b256(p01l), b256(p23l), b256(t1), 0, 4);
            lemma_shuffle8(x0, x1, x2, x3, b256(p01h), b256(p23h), b256(t2), 8, 0);
            lemma_shuffle8(x0, x1, x2, x3, b256(p01h), b256(p23h), b256(t3), 8, 4);
            lemma_pack32(s0, s1, s2, s3, s4, ob@, e0, e1, e2, e3, oo as int, j as int, len as int,
                x0, x1, x2, x3, b256(t0), b256(t1), b256(t2), b256(t3));
        }
        j = j + 32;
    }
    j
}

/// `yuv_pack4_avx2` on NEON, sixteen pixels at a time: the pixels `0..r`.
/// The channels are interleaved by two rounds of `zip1`/`zip2`, as in
/// `pack4`.
fn yuv_pack4_neon(
    ys: &[u8], yo: usize, su: &[u8], sv: &[u8], sa: &[u8], ob: &mut [u8], oo: usize, len: usize, kind: u8,
) -> (r: usize)
    requires
        neon(),
        1 <= kind <= 3,
        yo + len <= ys@.len(),
        len <= su@.len(), len <= sv@.len(), len <= sa@.len(),
        oo + 4 * len <= old(ob)@.len(),
    ensures
        r <= len,
        final(ob)@.len() == old(ob)@.len(),
        line_packed4(kind as int, old(ob)@, final(ob)@, ys@, yo as int, su@, sv@, sa@, oo as int, r as int, len as int),
{
    proof {
        assert(ys@.len() == ys.len());
        assert(ob@.len() == ob.len());
    }
    let ghost s0 = ob@;
    let ghost lr = line_r(ys@, yo as int, sv@, len as int);
    let ghost lg = line_g(ys@, yo as int, su@, sv@, len as int);
    let ghost lb = line_b(ys@, yo as int, su@, len as int);
    let ghost e0 = chan4(kind as int, lr, lg, lb, sa@, 0);
    let ghost e1 = chan4(kind as int, lr, lg, lb, sa@, 1);
    let ghost e2 = chan4(kind as int, lr, lg, lb, sa@, 2);
    let ghost e3 = chan4(kind as int, lr, lg, lb, sa@, 3);
    let k19077 = vdupq_n_s16(19077);
    let k26149 = vdupq_n_s16(26149);
    let k6419 = vdupq_n_s16(6419);
    let k13320 = vdupq_n_s16(13320);
    let k282 = vdupq_n_s16(282);
    let k14234 = vdupq_n_s16(14234);
    let k8708 = vdupq_n_s16(8708);
    let k17685 = vdupq_n_s16(17685);
    let mut j: usize = 0;
    while len - j >= 16
        invariant
            neon(),
            1 <= kind <= 3,
            j <= len,
            yo + len <= ys@.len(),
            len <= su@.len(), len <= sv@.len(), len <= sa@.len(),
            oo + 4 * len <= ob@.len(),
            ob@.len() == old(ob)@.len(),
            ob@.len() <= usize::MAX,
            ys@.len() <= usize::MAX,
            s0 == old(ob)@,
            lr == line_r(ys@, yo as int, sv@, len as int),
            lg == line_g(ys@, yo as int, su@, sv@, len as int),
            lb == line_b(ys@, yo as int, su@, len as int),
            e0 == chan4(kind as int, lr, lg, lb, sa@, 0),
            e1 == chan4(kind as int, lr, lg, lb, sa@, 1),
            e2 == chan4(kind as int, lr, lg, lb, sa@, 2),
            e3 == chan4(kind as int, lr, lg, lb, sa@, 3),
            packed4(s0, ob@, e0, e1, e2, e3, oo as int, j as int, len as int),
            u16s(n8(k19077)) == splat16(19077u16, 8),
            u16s(n8(k26149)) == splat16(26149u16, 8),
            u16s(n8(k6419)) == splat16(6419u16, 8),
            u16s(n8(k13320)) == splat16(13320u16, 8),
            u16s(n8(k282)) == splat16(282u16, 8),
            u16s(n8(k14234)) == splat16(14234u16, 8),
            u16s(n8(k8708)) == splat16(8708u16, 8),
            u16s(n8(k17685)) == splat16(17685u16, 8),
        decreases len - j,
    {
        proof {
            assert(oo + 4 * j + 64 <= oo + 4 * len);
        }
        let ghost s1 = ob@;
        let y = vld1q_u8_at(ys, yo + j);
        let u = vld1q_u8_at(su, j);
        let v = vld1q_u8_at(sv, j);
        let a = vld1q_u8_at(sa, j);
        // `MultHi(x, c)` as `sqdmulh(x << 7, c)`.
        let ylo = vqdmulhq_s16(vshll_low_n_u8::<7>(y), k19077);
        let yhi = vqdmulhq_s16(vshll_high_n_u8::<7>(y), k19077);
        let ulo = vshll_low_n_u8::<7>(u);
        let uhi = vshll_high_n_u8::<7>(u);
        let vlo = vshll_low_n_u8::<7>(v);
        let vhi = vshll_high_n_u8::<7>(v);
        let rlo = vaddq_s16(vsubq_s16(ylo, k14234), vqdmulhq_s16(vlo, k26149));
        let rhi = vaddq_s16(vsubq_s16(yhi, k14234), vqdmulhq_s16(vhi, k26149));
        let glo = vsubq_s16(vaddq_s16(ylo, k8708), vaddq_s16(vqdmulhq_s16(ulo, k6419), vqdmulhq_s16(vlo, k13320)));
        let ghi = vsubq_s16(vaddq_s16(yhi, k8708), vaddq_s16(vqdmulhq_s16(uhi, k6419), vqdmulhq_s16(vhi, k13320)));
        let blo = vqsubq_u16(vaddq_s16(ylo, vaddq_s16(ulo, vqdmulhq_s16(ulo, k282))), k17685);
        let bhi = vqsubq_u16(vaddq_s16(yhi, vaddq_s16(uhi, vqdmulhq_s16(uhi, k282))), k17685);
        let r = vqshrun2_n_s16::<6>(rlo, rhi);
        let g = vqshrun2_n_s16::<6>(glo, ghi);
        let b = vqshrn2_n_u16::<6>(blo, bhi);
        proof {
            let (yb, ub, vb) = (n8(y), n8(u), n8(v));
            assert(u16s(n8(ylo)) == nvec_y1(nwiden_lo(yb)));
            assert(u16s(n8(yhi)) == nvec_y1(nwiden_hi(yb)));
            assert(u16s(n8(rlo)) == nvec_r(nwiden_lo(yb), nwiden_lo(vb)));
            assert(u16s(n8(rhi)) == nvec_r(nwiden_hi(yb), nwiden_hi(vb)));
            assert(u16s(n8(glo)) == nvec_g(nwiden_lo(yb), nwiden_lo(ub), nwiden_lo(vb)));
            assert(u16s(n8(ghi)) == nvec_g(nwiden_hi(yb), nwiden_hi(ub), nwiden_hi(vb)));
            assert(u16s(n8(blo)) == nvec_b(nwiden_lo(yb), nwiden_lo(ub)));
            assert(u16s(n8(bhi)) == nvec_b(nwiden_hi(yb), nwiden_hi(ub)));
            lemma_line16n(ys@, yo as int, su@, sv@, len as int, j as int, yb, ub, vb);
            assert(n8(r) == lr.subrange(j as int, j + 16));
            assert(n8(g) == lg.subrange(j as int, j + 16));
            assert(n8(b) == lb.subrange(j as int, j + 16));
        }
        let (c0, c1, c2, c3) = if kind == 1 {
            (r, g, b, a)
        } else if kind == 2 {
            (b, g, r, a)
        } else {
            (a, r, g, b)
        };
        let y0 = vzip1q_u8(c0, c2);
        let y1 = vzip2q_u8(c0, c2);
        let y2 = vzip1q_u8(c1, c3);
        let y3 = vzip2q_u8(c1, c3);
        let o = oo + 4 * j;
        vst1q_u8_at(ob, o, vzip1q_u8(y0, y2));
        let ghost s2 = ob@;
        vst1q_u8_at(ob, o + 16, vzip2q_u8(y0, y2));
        let ghost s3 = ob@;
        vst1q_u8_at(ob, o + 32, vzip1q_u8(y1, y3));
        let ghost s4 = ob@;
        vst1q_u8_at(ob, o + 48, vzip2q_u8(y1, y3));
        proof {
            lemma_pack16(s0, s1, s2, s3, s4, ob@, e0, e1, e2, e3, oo as int, j as int, len as int,
                n8(c0), n8(c1), n8(c2), n8(c3));
        }
        j = j + 16;
    }
    j
}

/// One line converted and packed in a single pass, for the four-byte
/// layouts (kinds 1 to 3) on AVX2 or NEON: `yuv_pack4_avx2` or
/// `yuv_pack4_neon`, the rest one by one.
fn yuv_pack4(
    ys: &[u8], yo: usize, su: &[u8], sv: &[u8], sa: &[u8], ob: &mut [u8], oo: usize, len: usize, kind: u8,
)
    requires
        avx2() || neon(),
        1 <= kind <= 3,
        yo + len <= ys@.len(),
        len <= su@.len(), len <= sv@.len(), len <= sa@.len(),
        oo + 4 * len <= old(ob)@.len(),
    ensures
        final(ob)@.len() == old(ob)@.len(),
        line_packed4(kind as int, old(ob)@, final(ob)@, ys@, yo as int, su@, sv@, sa@, oo as int, len as int, len as int),
{
    proof {
        assert(ys@.len() == ys.len());
        assert(ob@.len() == ob.len());
    }
    let ghost s0 = ob@;
    let ghost lr = line_r(ys@, yo as int, sv@, len as int);
    let ghost lg = line_g(ys@, yo as int, su@, sv@, len as int);
    let ghost lb = line_b(ys@, yo as int, su@, len as int);
    let ghost e0 = chan4(kind as int, lr, lg, lb, sa@, 0);
    let ghost e1 = chan4(kind as int, lr, lg, lb, sa@, 1);
    let ghost e2 = chan4(kind as int, lr, lg, lb, sa@, 2);
    let ghost e3 = chan4(kind as int, lr, lg, lb, sa@, 3);
    let mut j: usize = 0;
    if has_avx2() {
        // SAFETY: the CPU has AVX2.
        j = unsafe { yuv_pack4_avx2(ys, yo, su, sv, sa, ob, oo, len, kind) };
    } else if cfg!(target_arch = "aarch64") && has_neon() {
        j = yuv_pack4_neon(ys, yo, su, sv, sa, ob, oo, len, kind);
    }
    while j < len
        invariant
            1 <= kind <= 3,
            j <= len,
            yo + len <= ys@.len(),
            len <= su@.len(), len <= sv@.len(), len <= sa@.len(),
            oo + 4 * len <= ob@.len(),
            ob@.len() == old(ob)@.len(),
            ob@.len() <= usize::MAX,
            ys@.len() <= usize::MAX,
            s0 == old(ob)@,
            lr == line_r(ys@, yo as int, sv@, len as int),
            lg == line_g(ys@, yo as int, su@, sv@, len as int),
            lb == line_b(ys@, yo as int, su@, len as int),
            e0 == chan4(kind as int, lr, lg, lb, sa@, 0),
            e1 == chan4(kind as int, lr, lg, lb, sa@, 1),
            e2 == chan4(kind as int, lr, lg, lb, sa@, 2),
            e3 == chan4(kind as int, lr, lg, lb, sa@, 3),
            packed4(s0, ob@, e0, e1, e2, e3, oo as int, j as int, len as int),
        decreases len - j,
    {
        proof {
            assert(oo + 4 * j + 4 <= oo + 4 * len);
        }
        let ghost s1 = ob@;
        let (r, g, b) = yuv_to_rgb(get(ys, yo + j), get(su, j), get(sv, j));
        let a = get(sa, j);
        let (p0, p1, p2, p3) = if kind == 1 {
            (r, g, b, a)
        } else if kind == 2 {
            (b, g, r, a)
        } else {
            (a, r, g, b)
        };
        let o = oo + 4 * j;
        set(ob, o, p0);
        set(ob, o + 1, p1);
        set(ob, o + 2, p2);
        set(ob, o + 3, p3);
        proof {
            assert(lr[j as int] == r && lg[j as int] == g && lb[j as int] == b);
            lemma_pack1(s0, s1, ob@, e0, e1, e2, e3, oo as int, j as int, len as int);
        }
        j = j + 1;
    }
}

/// Packs `len` pixels into three-byte pixels at `ob[oo..]`, red at byte
/// `pr`, green `pg`, blue `pb` of each.
#[inline(always)]
fn pack3(
    sr: &[u8], sg: &[u8], sb: &[u8], ob: &mut [u8], oo: usize, len: usize,
    pr: usize, pg: usize, pb: usize,
)
    requires
        len <= sr@.len(), len <= sg@.len(), len <= sb@.len(),
        oo + 3 * len <= old(ob)@.len(),
        pr < 3, pg < 3, pb < 3,
        pr != pg, pg != pb, pr != pb,
    ensures
        final(ob)@.len() == old(ob)@.len(),
        packed3(old(ob)@, final(ob)@, sr@, sg@, sb@, oo as int, len as int, len as int, pr as int, pg as int, pb as int),
{
    proof {
        assert(ob@.len() == ob.len());
    }
    let ghost s0 = ob@;
    let mut j: usize = 0;
    while j < len
        invariant
            j <= len,
            len <= sr@.len(), len <= sg@.len(), len <= sb@.len(),
            oo + 3 * len <= ob@.len(),
            ob@.len() == old(ob)@.len(),
            ob@.len() <= usize::MAX,
            pr < 3, pg < 3, pb < 3,
            pr != pg, pg != pb, pr != pb,
            s0 == old(ob)@,
            packed3(s0, ob@, sr@, sg@, sb@, oo as int, j as int, len as int, pr as int, pg as int, pb as int),
        decreases len - j,
    {
        proof {
            assert(oo + 3 * j + 3 <= oo + 3 * len);
        }
        let ghost s1 = ob@;
        let o = oo + 3 * j;
        set(ob, o + pr, get(sr, j));
        set(ob, o + pg, get(sg, j));
        set(ob, o + pb, get(sb, j));
        proof {
            lemma_pack3(s0, s1, ob@, sr@, sg@, sb@, oo as int, j as int, len as int, pr as int, pg as int, pb as int);
        }
        j = j + 1;
    }
}

/// The ARGB word of pixel `j` of a line: luma `ys[yo + j]`, chroma `u[j]`
/// and `v[j]`, alpha `a[j]`.
pub open spec fn line_argb(ys: Seq<u8>, yo: int, u: Seq<u8>, v: Seq<u8>, a: Seq<u8>, j: int) -> int {
    argb_word(
        a[j] as int,
        yuv_r(ys[yo + j] as int, v[j] as int),
        yuv_g(ys[yo + j] as int, u[j] as int, v[j] as int),
        yuv_b(ys[yo + j] as int, u[j] as int),
    )
}

/// Byte `k` of that pixel in byte layout `kind`.
pub open spec fn line_byte(kind: int, ys: Seq<u8>, yo: int, u: Seq<u8>, v: Seq<u8>, a: Seq<u8>, j: int, k: int) -> int {
    rgb_byte(
        kind,
        a[j] as int,
        yuv_r(ys[yo + j] as int, v[j] as int),
        yuv_g(ys[yo + j] as int, u[j] as int, v[j] as int),
        yuv_b(ys[yo + j] as int, u[j] as int),
        k,
    )
}

/// What `upsample_line` writes: the `len` pixels of the line at `oo`, in
/// `out` (kind 0) or `ob` (the byte kinds), and nothing else.
#[verifier::opaque]
pub open spec fn line_out(
    kind: int, out0: Seq<u32>, ob0: Seq<u8>, out1: Seq<u32>, ob1: Seq<u8>, oo: int, len: int,
    ys: Seq<u8>, yo: int, u: Seq<u8>, v: Seq<u8>, a: Seq<u8>,
) -> bool {
    &&& out1.len() == out0.len()
    &&& ob1.len() == ob0.len()
    &&& kind == 0 ==> {
        &&& ob1 == ob0
        &&& forall|j: int| 0 <= j < len ==> out1[oo + j] as int == #[trigger] line_argb(ys, yo, u, v, a, j)
        &&& forall|i: int| 0 <= i < out1.len() && !(oo <= i < oo + len) ==> #[trigger] out1[i] == out0[i]
    }
    &&& kind != 0 ==> {
        &&& out1 == out0
        &&& forall|j: int, k: int|
            0 <= j < len && 0 <= k < rgb_bpp(kind) ==> ob1[oo + rgb_bpp(kind) * j + k] as int == #[trigger] line_byte(
                kind,
                ys,
                yo,
                u,
                v,
                a,
                j,
                k,
            )
        &&& forall|i: int|
            0 <= i < ob1.len() && !(oo <= i < oo + rgb_bpp(kind) * len) ==> #[trigger] ob1[i] == ob0[i]
    }
}

/// The byte kinds: the converted channels, packed by `pack4` or `pack3`
/// in the kind's order, are the line.
proof fn lemma_line_bytes(
    kind: int, out: Seq<u32>, ob0: Seq<u8>, ob1: Seq<u8>, oo: int, len: int,
    ys: Seq<u8>, yo: int, u0: Seq<u8>, v0: Seq<u8>, su: Seq<u8>, sg: Seq<u8>, sv: Seq<u8>, sa: Seq<u8>,
)
    requires
        1 <= kind <= 5,
        forall|i: int| 0 <= i < len ==> #[trigger] rgb_lane_ok(ys, yo, u0, v0, su, sg, sv, i),
        kind == 1 ==> packed4(ob0, ob1, su, sg, sv, sa, oo, len, len),
        kind == 2 ==> packed4(ob0, ob1, sv, sg, su, sa, oo, len, len),
        kind == 3 ==> packed4(ob0, ob1, sa, su, sg, sv, oo, len, len),
        kind == 4 ==> packed3(ob0, ob1, su, sg, sv, oo, len, len, 0, 1, 2),
        kind == 5 ==> packed3(ob0, ob1, su, sg, sv, oo, len, len, 2, 1, 0),
    ensures
        line_out(kind, out, ob0, out, ob1, oo, len, ys, yo, u0, v0, sa),
{
    reveal(line_out);
    assert forall|j: int, k: int| 0 <= j < len && 0 <= k < rgb_bpp(kind) implies ob1[oo + rgb_bpp(kind) * j + k] as int
        == #[trigger] line_byte(kind, ys, yo, u0, v0, sa, j, k) by {
        assert(rgb_lane_ok(ys, yo, u0, v0, su, sg, sv, j));
        if kind == 1 {
            assert(px4(ob1, oo, j) == (su[j], sg[j], sv[j], sa[j]));
        } else if kind == 2 {
            assert(px4(ob1, oo, j) == (sv[j], sg[j], su[j], sa[j]));
        } else if kind == 3 {
            assert(px4(ob1, oo, j) == (sa[j], su[j], sg[j], sv[j]));
        } else if kind == 4 {
            assert(px3(ob1, oo, j, 0, 1, 2) == (su[j], sg[j], sv[j]));
        } else {
            assert(px3(ob1, oo, j, 2, 1, 0) == (su[j], sg[j], sv[j]));
        }
    }
}

/// The four-byte kinds: a line converted and packed in one pass is the line.
proof fn lemma_line_packed4(
    kind: int, out: Seq<u32>, ob0: Seq<u8>, ob1: Seq<u8>, oo: int, len: int,
    ys: Seq<u8>, yo: int, u: Seq<u8>, v: Seq<u8>, sa: Seq<u8>,
)
    requires
        1 <= kind <= 3,
        0 <= len,
        line_packed4(kind, ob0, ob1, ys, yo, u, v, sa, oo, len, len),
    ensures
        line_out(kind, out, ob0, out, ob1, oo, len, ys, yo, u, v, sa),
{
    let (r, g, b) = (line_r(ys, yo, v, len), line_g(ys, yo, u, v, len), line_b(ys, yo, u, len));
    assert forall|i: int| 0 <= i < len implies #[trigger] rgb_lane_ok(ys, yo, u, v, r, g, b, i) by {}
    lemma_line_bytes(kind, out, ob0, ob1, oo, len, ys, yo, u, v, r, g, b, sa);
}

/// One output line of the fancy upsampler: luma from `y[yo..yo + len]`,
/// the line's upsampled chroma in `su` and `sv` (overwritten with red and
/// blue), alpha from `sa`. Written to `out[oo..]` (kind 0) or `ob[oo..]` (the byte kinds).
fn upsample_line(
    pl: &Planes,
    yo: usize,
    sa: &[u8],
    out: &mut Vec<u32>,
    ob: &mut [u8],
    kind: u8,
    oo: usize,
    len: usize,
    su: &mut [u8],
    sv: &mut [u8],
    sg: &mut [u8],
)
    requires
        len >= 1,
        len <= old(su)@.len(),
        len <= old(sv)@.len(),
        len <= old(sg)@.len(),
        len <= sa@.len(),
        yo + len <= pl.y@.len(),
        kind <= 5,
        kind == 0 ==> oo + len <= old(out)@.len(),
        kind != 0 ==> oo + kind_bpp(kind) * len <= old(ob)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        final(ob)@.len() == old(ob)@.len(),
        final(su)@.len() == old(su)@.len(),
        final(sv)@.len() == old(sv)@.len(),
        final(sg)@.len() == old(sg)@.len(),
        line_out(
            kind as int,
            old(out)@,
            old(ob)@,
            final(out)@,
            final(ob)@,
            oo as int,
            len as int,
            pl.y@,
            yo as int,
            old(su)@,
            old(sv)@,
            sa@,
        ),
{
    let ghost u0 = su@;
    let ghost v0 = sv@;
    let ghost out0 = out@;
    let ghost ob0 = ob@;
    let ys = pl.y.as_slice();
    proof {
        assert(ys@.len() == ys.len());
        assert(sa@.len() == sa.len());
        assert(su@.len() == su.len());
        assert(sv@.len() == sv.len());
        assert(sg@.len() == sg.len());
        assert(out@.len() == out.len());
    }
    // With AVX2 or NEON, the four-byte layouts in one pass.
    if kind >= 1 && kind <= 3 && (has_avx2() || (cfg!(target_arch = "aarch64") && has_neon())) {
        yuv_pack4(ys, yo, su, sv, sa, ob, oo, len, kind);
        proof {
            lemma_line_packed4(kind as int, out0, ob0, ob@, oo as int, len as int, ys@, yo as int, u0, v0, sa@);
        }
        return;
    }
    // The channels first, in byte lanes, then packed: two loops that each
    // vectorize at full width (`su` and `sv` take red and blue, `sg` green).
    // On x86, sixteen at a time as `ConvertYUV444ToRGB_SSE2` does them.
    let mut j: usize = 0;
    if !(cfg!(target_arch = "aarch64") && has_neon()) {
        // SAFETY: SSE2 is part of x86-64 (and emulated elsewhere).
        j = unsafe { yuv_to_rgb_sse2(ys, yo, su, sv, sg, len) };
    }
    while j < len
        invariant
            j <= len,
            yo + len <= ys@.len(),
            len <= su@.len(),
            len <= sv@.len(),
            len <= sg@.len(),
            su@.len() == old(su)@.len(),
            sv@.len() == old(sv)@.len(),
            sg@.len() == old(sg)@.len(),
            ys@.len() <= usize::MAX,
            rgb_lanes(ys@, yo as int, u0, v0, su@, sv@, sg@, j as int),
        decreases len - j,
    {
        let ghost (su1, sv1, sg1) = (su@, sv@, sg@);
        let (r, g, b) = yuv_to_rgb(get(ys, yo + j), get(su, j), get(sv, j));
        set(su, j, r);
        set(sg, j, g);
        set(sv, j, b);
        proof {
            lemma_rgb1(ys@, yo as int, u0, v0, su1, sv1, sg1, su@, sv@, sg@, j as int, r, g, b);
        }
        j = j + 1;
    }
    if kind == 0 {
        let mut j: usize = 0;
        while j < len
            invariant
                j <= len,
                len <= sa@.len(),
                len <= su@.len(),
                len <= sv@.len(),
                len <= sg@.len(),
                oo + len <= out@.len(),
                out@.len() == old(out)@.len(),
                out@.len() <= usize::MAX,
                out0 == old(out)@,
                rgb_lanes(ys@, yo as int, u0, v0, su@, sv@, sg@, len as int),
                forall|p: int| 0 <= p < j ==> out@[oo + p] as int == #[trigger] line_argb(ys@, yo as int, u0, v0, sa@, p),
                forall|i: int| 0 <= i < out@.len() && !(oo <= i < oo + len) ==> #[trigger] out@[i] == out0[i],
            decreases len - j,
        {
            proof {
                assert(rgb_lane_ok(ys@, yo as int, u0, v0, su@, sg@, sv@, j as int));
            }
            store_at(out, oo + j, argb(get(sa, j), get(su, j), get(sg, j), get(sv, j)));
            j = j + 1;
        }
        proof {
            reveal(line_out);
        }
    } else {
        if kind == 1 {
            pack4(su, sg, sv, sa, ob, oo, len);
        } else if kind == 2 {
            pack4(sv, sg, su, sa, ob, oo, len);
        } else if kind == 3 {
            pack4(sa, su, sg, sv, ob, oo, len);
        } else if kind == 4 {
            pack3(su, sg, sv, ob, oo, len, 0, 1, 2);
        } else {
            pack3(su, sg, sv, ob, oo, len, 2, 1, 0);
        }
        proof {
            lemma_line_bytes(kind as int, out0, ob0, ob@, oo as int, len as int, ys@, yo as int, u0, v0, su@, sg@, sv@, sa@);
        }
    }
}

impl Planes {
    /// The planes as `vp8spec` sees them.
    pub open spec fn yuv(&self) -> Yuv420 {
        Yuv420 {
            y: self.y@,
            u: self.u@,
            v: self.v@,
            y_stride: self.y_stride as int,
            uv_stride: self.uv_stride as int,
            width: self.width as int,
            height: self.height as int,
        }
    }
}

/// `s` is row `y` of plane `c`'s upsampled chroma.
pub open spec fn chroma_row(s: Seq<u8>, c: Seq<u8>, im: Yuv420, y: int) -> bool {
    forall|x: int|
        0 <= x < im.width ==> (#[trigger] s[x]) as int == fancy_chroma(c, im.uv_stride, im.width, im.height, x, y)
}

/// `sa` is row `y` of the alpha.
pub open spec fn alpha_row(sa: Seq<u8>, alpha: Seq<u8>, has_alpha: bool, w: int, y: int) -> bool {
    forall|x: int| 0 <= x < w ==> (#[trigger] sa[x]) as int == rgb_a(alpha, has_alpha, w, x, y)
}

/// Row `y` of the output is the specification's.
pub open spec fn row_done(
    kind: int, out: Seq<u32>, ob: Seq<u8>, im: Yuv420, alpha: Seq<u8>, has_alpha: bool, y: int,
) -> bool {
    if kind == 0 {
        forall|x: int|
            0 <= x < im.width ==> out[y * im.width + x] as int == #[trigger] rgb_argb(im, alpha, has_alpha, x, y)
    } else {
        forall|x: int, k: int|
            0 <= x < im.width && 0 <= k < rgb_bpp(kind) ==> ob[(y * im.width + x) * rgb_bpp(kind) + k] as int
                == #[trigger] rgb_out_byte(im, alpha, has_alpha, kind, x, y, k)
    }
}

/// So are rows `0..n`.
#[verifier::opaque]
pub open spec fn rows_done(
    kind: int, out: Seq<u32>, ob: Seq<u8>, im: Yuv420, alpha: Seq<u8>, has_alpha: bool, n: int,
) -> bool {
    forall|y: int| 0 <= y < n ==> #[trigger] row_done(kind, out, ob, im, alpha, has_alpha, y)
}

/// A line from the right chroma lines is the row's chroma.
proof fn lemma_chroma_row(s: Seq<u8>, c: Seq<u8>, im: Yuv420, y: int, no: int, fo: int)
    requires
        fancy_row(s, c, no, fo, im.width),
        no == (y / 2) * im.uv_stride,
        fo == fancy_far_row(y, im.height) * im.uv_stride,
    ensures
        chroma_row(s, c, im, y),
{
}

/// Where pixel `(x, y)`'s byte `k` is, by rows of `bpp * w` bytes.
proof fn lemma_px_index(y: int, w: int, x: int, bpp: int, k: int)
    requires
        0 <= y, 0 <= x < w, 1 <= bpp, 0 <= k < bpp,
    ensures
        (y * w + x) * bpp + k == y * (bpp * w) + bpp * x + k,
        0 <= bpp * x + k < bpp * w,
        (y + 1) * (bpp * w) == y * (bpp * w) + bpp * w,
        0 <= y * (bpp * w),
{
    assert((y * w + x) * bpp == y * (bpp * w) + bpp * x) by (nonlinear_arith);
    assert(bpp * x + bpp <= bpp * w && 0 <= bpp * x) by (nonlinear_arith)
        requires 0 <= x, x + 1 <= w, bpp >= 1;
    assert((y + 1) * (bpp * w) == y * (bpp * w) + bpp * w) by (nonlinear_arith);
    assert(0 <= y * (bpp * w)) by (nonlinear_arith)
        requires 0 <= y, 0 <= w, 1 <= bpp;
}

/// A later line leaves row `r` as it was.
proof fn lemma_row_keep(
    kind: int, out0: Seq<u32>, ob0: Seq<u8>, out1: Seq<u32>, ob1: Seq<u8>, im: Yuv420, alpha: Seq<u8>,
    has_alpha: bool, r: int, y: int, su: Seq<u8>, sv: Seq<u8>, sa: Seq<u8>, yo: int,
)
    requires
        0 <= kind <= 5,
        1 <= im.width,
        0 <= r < y,
        kind == 0 ==> y * (rgb_bpp(kind) * im.width) + im.width <= out0.len(),
        kind != 0 ==> y * (rgb_bpp(kind) * im.width) + rgb_bpp(kind) * im.width <= ob0.len(),
        line_out(kind, out0, ob0, out1, ob1, y * (rgb_bpp(kind) * im.width), im.width, im.y, yo, su, sv, sa),
        row_done(kind, out0, ob0, im, alpha, has_alpha, r),
    ensures
        row_done(kind, out1, ob1, im, alpha, has_alpha, r),
{
    reveal(line_out);
    let w = im.width;
    let bpp = rgb_bpp(kind);
    let os = bpp * w;
    assert((r + 1) * os <= y * os) by (nonlinear_arith)
        requires r + 1 <= y, os >= 0;
    if kind == 0 {
        assert forall|x: int| 0 <= x < w implies out1[r * w + x] as int == #[trigger] rgb_argb(im, alpha, has_alpha, x, r) by {
            lemma_px_index(r, w, x, 1, 0);
            assert(out1[r * w + x] == out0[r * w + x]);
        }
    } else {
        assert forall|x: int, k: int| 0 <= x < w && 0 <= k < bpp implies ob1[(r * w + x) * bpp + k] as int
            == #[trigger] rgb_out_byte(im, alpha, has_alpha, kind, x, r, k) by {
            lemma_px_index(r, w, x, bpp, k);
            let i = (r * w + x) * bpp + k;
            assert(0 <= i < y * os);
            assert(ob1[i] == ob0[i]);
        }
    }
}

/// The line written for row `y` is the specification's row `y`.
proof fn lemma_row_new(
    kind: int, out0: Seq<u32>, ob0: Seq<u8>, out1: Seq<u32>, ob1: Seq<u8>, im: Yuv420, alpha: Seq<u8>,
    has_alpha: bool, y: int, su: Seq<u8>, sv: Seq<u8>, sa: Seq<u8>,
)
    requires
        0 <= kind <= 5,
        1 <= im.width,
        0 <= y,
        line_out(
            kind, out0, ob0, out1, ob1, y * (rgb_bpp(kind) * im.width), im.width, im.y, y * im.y_stride, su, sv, sa,
        ),
        chroma_row(su, im.u, im, y),
        chroma_row(sv, im.v, im, y),
        alpha_row(sa, alpha, has_alpha, im.width, y),
    ensures
        row_done(kind, out1, ob1, im, alpha, has_alpha, y),
{
    reveal(line_out);
    let w = im.width;
    let bpp = rgb_bpp(kind);
    let ys = y * im.y_stride;
    if kind == 0 {
        assert forall|x: int| 0 <= x < w implies out1[y * w + x] as int == #[trigger] rgb_argb(im, alpha, has_alpha, x, y) by {
            lemma_px_index(y, w, x, 1, 0);
            assert(out1[y * (1 * w) + x] as int == line_argb(im.y, ys, su, sv, sa, x));
            assert(su[x] as int == fancy_chroma(im.u, im.uv_stride, w, im.height, x, y));
            assert(sv[x] as int == fancy_chroma(im.v, im.uv_stride, w, im.height, x, y));
            assert(sa[x] as int == rgb_a(alpha, has_alpha, w, x, y));
        }
    } else {
        assert forall|x: int, k: int| 0 <= x < w && 0 <= k < bpp implies ob1[(y * w + x) * bpp + k] as int
            == #[trigger] rgb_out_byte(im, alpha, has_alpha, kind, x, y, k) by {
            lemma_px_index(y, w, x, bpp, k);
            assert(ob1[y * (bpp * w) + bpp * x + k] as int == line_byte(kind, im.y, ys, su, sv, sa, x, k));
            assert(su[x] as int == fancy_chroma(im.u, im.uv_stride, w, im.height, x, y));
            assert(sv[x] as int == fancy_chroma(im.v, im.uv_stride, w, im.height, x, y));
            assert(sa[x] as int == rgb_a(alpha, has_alpha, w, x, y));
        }
    }
}

/// One more row done.
proof fn lemma_emit_row(
    kind: int, out0: Seq<u32>, ob0: Seq<u8>, out1: Seq<u32>, ob1: Seq<u8>, im: Yuv420, alpha: Seq<u8>,
    has_alpha: bool, y: int, su: Seq<u8>, sv: Seq<u8>, sa: Seq<u8>,
)
    requires
        0 <= kind <= 5,
        1 <= im.width,
        0 <= y,
        kind == 0 ==> y * (rgb_bpp(kind) * im.width) + im.width <= out0.len(),
        kind != 0 ==> y * (rgb_bpp(kind) * im.width) + rgb_bpp(kind) * im.width <= ob0.len(),
        line_out(
            kind, out0, ob0, out1, ob1, y * (rgb_bpp(kind) * im.width), im.width, im.y, y * im.y_stride, su, sv, sa,
        ),
        chroma_row(su, im.u, im, y),
        chroma_row(sv, im.v, im, y),
        alpha_row(sa, alpha, has_alpha, im.width, y),
        rows_done(kind, out0, ob0, im, alpha, has_alpha, y),
    ensures
        rows_done(kind, out1, ob1, im, alpha, has_alpha, y + 1),
{
    reveal(rows_done);
    assert forall|r: int| 0 <= r < y + 1 implies #[trigger] row_done(kind, out1, ob1, im, alpha, has_alpha, r) by {
        if r < y {
            lemma_row_keep(kind, out0, ob0, out1, ob1, im, alpha, has_alpha, r, y, su, sv, sa, y * im.y_stride);
        } else {
            lemma_row_new(kind, out0, ob0, out1, ob1, im, alpha, has_alpha, y, su, sv, sa);
        }
    }
}

/// All rows done is the whole image.
proof fn lemma_rows_image(kind: int, out: Seq<u32>, ob: Seq<u8>, im: Yuv420, alpha: Seq<u8>, has_alpha: bool)
    requires
        rows_done(kind, out, ob, im, alpha, has_alpha, im.height),
        kind == 0 ==> out.len() == im.width * im.height,
        kind != 0 ==> ob.len() >= rgb_bpp(kind) * im.width * im.height,
    ensures
        kind == 0 ==> rgb_image_argb(im, alpha, has_alpha, out),
        kind != 0 ==> rgb_image_bytes(im, alpha, has_alpha, kind, ob),
{
    reveal(rows_done);
    if kind == 0 {
        assert forall|x: int, y: int| 0 <= x < im.width && 0 <= y < im.height implies out[y * im.width + x] as int
            == #[trigger] rgb_argb(im, alpha, has_alpha, x, y) by {
            assert(row_done(kind, out, ob, im, alpha, has_alpha, y));
        }
    } else {
        assert forall|x: int, y: int, k: int|
            0 <= x < im.width && 0 <= y < im.height && 0 <= k < rgb_bpp(kind) implies ob[(y * im.width + x) * rgb_bpp(
            kind,
        ) + k] as int == #[trigger] rgb_out_byte(im, alpha, has_alpha, kind, x, y, k) by {
            assert(row_done(kind, out, ob, im, alpha, has_alpha, y));
        }
    }
}

/// The ARGB image of the planes (`EmitFancyRGB` over the whole frame),
/// with alpha from `alpha` (one byte per pixel) if `has_alpha`.
pub fn planes_to_argb(pl: &Planes, alpha: &Vec<u8>, has_alpha: bool) -> (r: Result<Vec<u32>, Error>)
    requires
        pl.ok(),
        has_alpha ==> alpha@.len() >= pl.width * pl.height,
    ensures
        r matches Ok(px) ==> px@.len() == pl.width * pl.height,
        r matches Ok(px) ==> rgb_image_argb(pl.yuv(), alpha@, has_alpha, px@),
{
    proof {
        assert(pl.width * pl.height <= 16384 * 16384) by (nonlinear_arith)
            requires 1 <= pl.width <= 16384, 1 <= pl.height <= 16384;
    }
    let mut out = match alloc_u32(pl.width * pl.height) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut none: [u8; 0] = [];
    match planes_emit(pl, alpha, has_alpha, &mut out, &mut none, 0) {
        Ok(()) => Ok(out),
        Err(e) => Err(e),
    }
}

/// The image of the planes written straight to `ob` in byte layout `kind`
/// (1 to 5, see `kind_bpp`), rows packed.
pub fn planes_to_bytes(pl: &Planes, alpha: &Vec<u8>, has_alpha: bool, ob: &mut [u8], kind: u8) -> (r: Result<(), Error>)
    requires
        pl.ok(),
        has_alpha ==> alpha@.len() >= pl.width * pl.height,
        1 <= kind <= 5,
        old(ob)@.len() >= kind_bpp(kind) * pl.width * pl.height,
    ensures
        final(ob)@.len() == old(ob)@.len(),
        r is Ok ==> rgb_image_bytes(pl.yuv(), alpha@, has_alpha, kind as int, final(ob)@),
{
    let mut none: Vec<u32> = Vec::new();
    planes_emit(pl, alpha, has_alpha, &mut none, ob, kind)
}

fn planes_emit(pl: &Planes, alpha: &Vec<u8>, has_alpha: bool, out: &mut Vec<u32>, ob: &mut [u8], kind: u8) -> (r: Result<(), Error>)
    requires
        pl.ok(),
        has_alpha ==> alpha@.len() >= pl.width * pl.height,
        kind <= 5,
        kind == 0 ==> old(out)@.len() == pl.width * pl.height,
        kind != 0 ==> old(ob)@.len() >= kind_bpp(kind) * pl.width * pl.height,
    ensures
        final(out)@.len() == old(out)@.len(),
        final(ob)@.len() == old(ob)@.len(),
        r is Ok ==> kind == 0 ==> rgb_image_argb(pl.yuv(), alpha@, has_alpha, final(out)@),
        r is Ok ==> kind != 0 ==> rgb_image_bytes(pl.yuv(), alpha@, has_alpha, kind as int, final(ob)@),
{
    let w = pl.width;
    let h = pl.height;
    let bpp: usize = if kind == 0 { 1 } else if kind <= 3 { 4 } else { 3 };
    let os = bpp * w;
    let ghost im = pl.yuv();
    let ghost ki = kind as int;
    proof {
        assert(bpp == kind_bpp(kind));
        assert(bpp == rgb_bpp(ki));
        assert(w * h <= 16384 * 16384) by (nonlinear_arith)
            requires 1 <= w <= 16384, 1 <= h <= 16384;
        assert(w <= w * h) by (nonlinear_arith) requires 1 <= w, 1 <= h;
        assert(w <= pl.y_stride * h) by (nonlinear_arith) requires 1 <= w <= pl.y_stride, 1 <= h;
        assert((w + 1) / 2 <= pl.uv_stride * ((h + 1) / 2)) by (nonlinear_arith)
            requires (w + 1) / 2 <= pl.uv_stride, 1 <= (h + 1) / 2;
        assert(os * h == bpp * w * h) by (nonlinear_arith) requires os == bpp * w;
        assert(os * h <= 4 * 16384 * 16384) by (nonlinear_arith)
            requires os == bpp * w, bpp <= 4, 1 <= w <= 16384, 1 <= h <= 16384;
        assert(os <= os * h) by (nonlinear_arith) requires 1 <= h;
    }
    let olen: usize = if kind == 0 { out.len() } else { ob.len() };
    let mut su = match alloc_u8(w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut sv = match alloc_u8(w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut sg = match alloc_u8(w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    // Alpha for the row: the row of `alpha`, or opaque.
    let mut sa = match alloc_u8(w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    // The second line of a pair's chroma, and the pair computation's
    // odd and even halves.
    let mut su2 = match alloc_u8(w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut sv2 = match alloc_u8(w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut e0 = match alloc_u8(w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut o0 = match alloc_u8(w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut e1 = match alloc_u8(w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut o1 = match alloc_u8(w) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let al = alpha.as_slice();
    proof {
        assert(al@.len() == al.len());
        assert(sa@.len() == sa.len());
    }
    if !has_alpha {
        let mut i: usize = 0;
        while i < w
            invariant
                i <= w,
                sa@.len() == w,
                forall|x: int| 0 <= x < i ==> #[trigger] sa@[x] == 255,
            decreases w - i,
        {
            set(sa.as_mut_slice(), i, 255);
            i = i + 1;
        }
    } else {
        copy_in(sa.as_mut_slice(), 0, al, 0, w);
    }
    let ys = pl.y_stride;
    let uvs = pl.uv_stride;
    // Row 0: its own chroma line only.
    upsample_chroma(pl.u.as_slice(), 0, 0, su.as_mut_slice(), w);
    upsample_chroma(pl.v.as_slice(), 0, 0, sv.as_mut_slice(), w);
    let ghost (out_a, ob_a, su_a, sv_a) = (out@, ob@, su@, sv@);
    proof {
        lemma_chroma_row(su_a, pl.u@, im, 0, 0, 0);
        lemma_chroma_row(sv_a, pl.v@, im, 0, 0, 0);
        assert(alpha_row(sa@, alpha@, has_alpha, w as int, 0));
        assert(rows_done(ki, out_a, ob_a, im, alpha@, has_alpha, 0)) by {
            reveal(rows_done);
        }
    }
    upsample_line(pl, 0, sa.as_slice(), out, ob, kind, 0, w, su.as_mut_slice(), sv.as_mut_slice(), sg.as_mut_slice());
    proof {
        lemma_emit_row(ki, out_a, ob_a, out@, ob@, im, alpha@, has_alpha, 0, su_a, sv_a, sa@);
    }
    // Rows 2k-1 and 2k from chroma lines k-1 and k.
    let mut k: usize = 1;
    while 2 * k < h
        invariant
            pl.ok(),
            w == pl.width,
            h == pl.height,
            ys == pl.y_stride,
            uvs == pl.uv_stride,
            1 <= k,
            2 * k <= h + 1,
            kind <= 5,
            bpp == kind_bpp(kind),
            1 <= bpp <= 4,
            os == bpp * w,
            os * h <= 4 * 16384 * 16384,
            olen == if kind == 0 { out@.len() } else { ob@.len() },
            olen >= os * h,
            out@.len() == old(out)@.len(),
            ob@.len() == old(ob)@.len(),
            has_alpha ==> alpha@.len() >= w * h,
            al@ == alpha@,
            su@.len() == w,
            sv@.len() == w,
            sg@.len() == w,
            sa@.len() == w,
            su2@.len() == w,
            sv2@.len() == w,
            e0@.len() == w,
            o0@.len() == w,
            e1@.len() == w,
            o1@.len() == w,
            im == pl.yuv(),
            ki == kind as int,
            bpp == rgb_bpp(ki),
            !has_alpha ==> forall|x: int| 0 <= x < w ==> #[trigger] sa@[x] == 255,
            rows_done(ki, out@, ob@, im, alpha@, has_alpha, 2 * k - 1),
        decreases h - k,
    {
        let top = 2 * k - 1;
        let bot = 2 * k;
        proof {
            assert(ys * h <= 16400 * 16384) by (nonlinear_arith)
                requires ys <= 16400, h <= 16384;
            assert(uvs * ((h + 1) / 2) <= 8200 * 8192) by (nonlinear_arith)
                requires uvs <= 8200, (h + 1) / 2 <= 8192;
            assert(top * ys <= ys * h) by (nonlinear_arith) requires top < h;
            assert(k * uvs <= uvs * ((h + 1) / 2)) by (nonlinear_arith) requires 2 * k < h;
            assert(w * h <= 16384 * 16384) by (nonlinear_arith) requires 1 <= w <= 16384, 1 <= h <= 16384;
            assert(bot * ys <= ys * h) by (nonlinear_arith) requires bot < h;
            assert(top * w <= w * h) by (nonlinear_arith) requires top < h;
            assert(bot * w <= w * h) by (nonlinear_arith) requires bot < h;
            assert(bot * ys + w <= ys * h) by (nonlinear_arith)
                requires bot < h, w <= ys;
            assert(top * ys + w <= ys * h) by (nonlinear_arith)
                requires top < bot, bot < h, w <= ys;
            assert(bot * w + w <= w * h) by (nonlinear_arith)
                requires bot < h;
            assert(top * w + w <= w * h) by (nonlinear_arith)
                requires top < bot, bot < h;
            assert(bot * os + os <= os * h) by (nonlinear_arith)
                requires bot < h;
            assert(top * os + os <= os * h) by (nonlinear_arith)
                requires top < bot, bot < h;
            assert(k * uvs + (w + 1) / 2 <= uvs * ((h + 1) / 2)) by (nonlinear_arith)
                requires 2 * k < h, (w + 1) / 2 <= uvs;
            assert((k - 1) * uvs <= k * uvs) by (nonlinear_arith)
                requires k >= 1;
            assert(kind == 0 ==> bpp == 1);
            assert(kind == 0 ==> os == w) by (nonlinear_arith)
                requires os == bpp * w, kind == 0 ==> bpp == 1;
            assert(top * os + os <= olen && bot * os + os <= olen);
        }
        upsample_chroma_pair(pl.u.as_slice(), (k - 1) * uvs, k * uvs, su.as_mut_slice(), su2.as_mut_slice(),
            e0.as_mut_slice(), o0.as_mut_slice(), e1.as_mut_slice(), o1.as_mut_slice(), w);
        upsample_chroma_pair(pl.v.as_slice(), (k - 1) * uvs, k * uvs, sv.as_mut_slice(), sv2.as_mut_slice(),
            e0.as_mut_slice(), o0.as_mut_slice(), e1.as_mut_slice(), o1.as_mut_slice(), w);
        if has_alpha {
            copy_in(sa.as_mut_slice(), 0, al, top * w, w);
        }
        let ghost (out_a, ob_a, su_a, sv_a) = (out@, ob@, su@, sv@);
        proof {
            assert((top as int) / 2 == k - 1 && fancy_far_row(top as int, h as int) == k);
            assert((bot as int) / 2 == k && fancy_far_row(bot as int, h as int) == k - 1);
            lemma_chroma_row(su_a, pl.u@, im, top as int, (k - 1) * uvs, k * uvs);
            lemma_chroma_row(sv_a, pl.v@, im, top as int, (k - 1) * uvs, k * uvs);
            lemma_chroma_row(su2@, pl.u@, im, bot as int, k * uvs, (k - 1) * uvs);
            lemma_chroma_row(sv2@, pl.v@, im, bot as int, k * uvs, (k - 1) * uvs);
            assert(alpha_row(sa@, alpha@, has_alpha, w as int, top as int));
        }
        upsample_line(pl, top * ys, sa.as_slice(), out, ob, kind, top * os, w, su.as_mut_slice(), sv.as_mut_slice(), sg.as_mut_slice());
        proof {
            lemma_emit_row(ki, out_a, ob_a, out@, ob@, im, alpha@, has_alpha, top as int, su_a, sv_a, sa@);
        }
        if has_alpha {
            copy_in(sa.as_mut_slice(), 0, al, bot * w, w);
        }
        let ghost (out_b, ob_b, su_b, sv_b) = (out@, ob@, su2@, sv2@);
        proof {
            assert(alpha_row(sa@, alpha@, has_alpha, w as int, bot as int));
        }
        upsample_line(pl, bot * ys, sa.as_slice(), out, ob, kind, bot * os, w, su2.as_mut_slice(), sv2.as_mut_slice(), sg.as_mut_slice());
        proof {
            lemma_emit_row(ki, out_b, ob_b, out@, ob@, im, alpha@, has_alpha, bot as int, su_b, sv_b, sa@);
        }
        k = k + 1;
    }
    // The last row of an even height: its own chroma line only.
    if h % 2 == 0 {
        let last = h - 1;
        proof {
            assert(ys * h <= 16400 * 16384) by (nonlinear_arith)
                requires ys <= 16400, h <= 16384;
            assert(uvs * ((h + 1) / 2) <= 8200 * 8192) by (nonlinear_arith)
                requires uvs <= 8200, (h + 1) / 2 <= 8192;
            assert(last * ys <= ys * h) by (nonlinear_arith) requires last < h;
            assert(last * w <= w * h) by (nonlinear_arith) requires last < h;
            assert((h / 2 - 1) * uvs <= uvs * ((h + 1) / 2)) by (nonlinear_arith) requires h >= 2;
            assert(last * ys + w <= ys * h) by (nonlinear_arith)
                requires last + 1 == h, w <= ys;
            assert(last * w + w <= w * h) by (nonlinear_arith)
                requires last + 1 == h;
            assert(last * os + os <= os * h) by (nonlinear_arith)
                requires last + 1 == h;
            assert((h / 2 - 1) * uvs + (w + 1) / 2 <= uvs * ((h + 1) / 2)) by (nonlinear_arith)
                requires h >= 2, h % 2 == 0, (w + 1) / 2 <= uvs;
            assert(kind == 0 ==> bpp == 1);
            assert(kind == 0 ==> os == w) by (nonlinear_arith)
                requires os == bpp * w, kind == 0 ==> bpp == 1;
            assert(last * os + os <= olen);
        }
        let c = (h / 2 - 1) * uvs;
        if has_alpha {
            copy_in(sa.as_mut_slice(), 0, al, last * w, w);
        }
        upsample_chroma(pl.u.as_slice(), c, c, su.as_mut_slice(), w);
        upsample_chroma(pl.v.as_slice(), c, c, sv.as_mut_slice(), w);
        let ghost (out_a, ob_a, su_a, sv_a) = (out@, ob@, su@, sv@);
        proof {
            assert((last as int) / 2 == h / 2 - 1 && fancy_far_row(last as int, h as int) == h / 2 - 1);
            lemma_chroma_row(su_a, pl.u@, im, last as int, c as int, c as int);
            lemma_chroma_row(sv_a, pl.v@, im, last as int, c as int, c as int);
            assert(alpha_row(sa@, alpha@, has_alpha, w as int, last as int));
        }
        upsample_line(pl, last * ys, sa.as_slice(), out, ob, kind, last * os, w, su.as_mut_slice(), sv.as_mut_slice(), sg.as_mut_slice());
        proof {
            lemma_emit_row(ki, out_a, ob_a, out@, ob@, im, alpha@, has_alpha, last as int, su_a, sv_a, sa@);
        }
    }
    proof {
        lemma_rows_image(ki, out@, ob@, im, alpha@, has_alpha);
    }
    Ok(())
}

} // verus!

#[cfg(test)]
mod tests {
    /// `VP8YuvToRgb` as `src/dsp/yuv.h` writes it, in 32-bit arithmetic.
    fn reference(y: u8, u: u8, v: u8) -> u32 {
        fn mh(v: i32, c: i32) -> i32 {
            (v * c) >> 8
        }
        fn clip(v: i32) -> u32 {
            if v < 0 {
                0
            } else if v >= 16384 {
                255
            } else {
                (v >> 6) as u32
            }
        }
        let (y, u, v) = (y as i32, u as i32, v as i32);
        let r = clip(mh(y, 19077) + mh(v, 26149) - 14234);
        let g = clip(mh(y, 19077) - mh(u, 6419) - mh(v, 13320) + 8708);
        let b = clip(mh(y, 19077) + mh(u, 33050) - 17685);
        0xff00_0000 | (r << 16) | (g << 8) | b
    }

    #[test]
    fn yuv_to_argb_matches_reference() {
        for y in 0..=255u8 {
            for u in 0..=255u8 {
                for v in 0..=255u8 {
                    assert_eq!(super::yuv_to_argb(y, u, v, 255), reference(y, u, v), "{y} {u} {v}");
                }
            }
        }
    }
}

//! VP8 4x4 intra prediction (RFC 6386 section 12.3) from shuffle tables:
//! every mode but TM with no branch on the mode, on NEON and on SSSE3.
use crate::vp8dsp::*;
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

// Every pixel of every 4x4 mode but TM is a byte of the block's edge, or
// the rounded average of two neighbouring edge bytes, or the `1 2 1`
// average of three. So one 16-byte edge vector `E` (`p4_edges`: the left
// column from the bottom up, its last pixel twice, then the corner, the
// eight pixels above, the last of them twice, and DC's value), the
// vector `A2` of the averages of `E[i]` and `E[i + 1]` and the vector
// `A3` of the averages of `E[i]`, `E[i + 1]` and `E[i + 2]` hold every
// value any mode needs, and a mode is three byte shuffles, one of each
// vector, ORed together: a table lookup in place of a ten-way branch
// that a decoder cannot predict. `P4T` holds the shuffles; they are data
// the proof reads (`lemma_p4_table`), not trusted.

/// For each mode three rows of sixteen shuffle indices, one row for each
/// of `E`, `A2` and `A3`: pixel `p` (in raster order) is byte `i` of the
/// one vector whose row holds `i < 16` at `p`; the other two rows hold
/// 128 there, which both `tbl` and `pshufb` turn into 0. The last row
/// shuffles the sixteen bytes that start at the corner into their places
/// in `E`.
pub const P4T: [u8; 496] = [
    // DC
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    // TM (not used)
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    // VE
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    5, 6, 7, 8, 5, 6, 7, 8, 5, 6, 7, 8, 5, 6, 7, 8,
    // HE
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    3, 3, 3, 3, 2, 2, 2, 2, 1, 1, 1, 1, 0, 0, 0, 0,
    // RD
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 2, 3, 4,
    // VR
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    5, 6, 7, 8, 128, 128, 128, 128, 128, 5, 6, 7, 128, 128, 128, 128,
    128, 128, 128, 128, 4, 5, 6, 7, 3, 128, 128, 128, 2, 4, 5, 6,
    // LD
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    6, 7, 8, 9, 7, 8, 9, 10, 8, 9, 10, 11, 9, 10, 11, 12,
    // VL
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    6, 7, 8, 9, 128, 128, 128, 128, 7, 8, 9, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 6, 7, 8, 9, 128, 128, 128, 10, 7, 8, 9, 11,
    // HD
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    4, 128, 128, 128, 3, 128, 4, 128, 2, 128, 3, 128, 1, 128, 2, 128,
    128, 4, 5, 6, 128, 3, 128, 4, 128, 2, 128, 3, 128, 1, 128, 2,
    // HU
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 0, 0, 0, 0, 0, 0,
    3, 128, 2, 128, 2, 128, 1, 128, 1, 128, 128, 128, 128, 128, 128, 128,
    128, 2, 128, 1, 128, 1, 128, 0, 128, 0, 128, 128, 128, 128, 128, 128,
    // the edge vector from the 16 bytes at the corner
    128, 128, 128, 128, 128, 0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 128,
];

/// The edge vector of a subblock: the RFC's `E` (`edge4`) one place up,
/// with `E[0]` first once more, then the last pixel above once more and
/// the DC mode's value.
pub open spec fn p4_edges(a: Seq<int>, l: Seq<int>) -> Seq<int> {
    Seq::new(
        16,
        |i: int|
            if i == 0 {
                l[3]
            } else if i < 14 {
                edge4(a, l, i - 1)
            } else if i == 14 {
                a[8]
            } else {
                (sum_range(a, 1, 5) + sum_range(l, 0, 4) + 4) / 8
            },
    )
}

/// Source `k` of the edge vector `e`: `e[k]` for `k < 16`, `A2[k - 16]`
/// for `k < 32`, and `A3[k - 32]`.
pub open spec fn p4_src(e: Seq<int>, k: int) -> int {
    if k < 16 {
        e[k]
    } else if k < 32 {
        spec_avg2(e[k - 16], e[k - 15])
    } else {
        spec_avg3(e[k - 32], e[k - 31], e[k - 30])
    }
}

/// The source that one pixel's three table entries select.
pub open spec fn p4_pick(t0: u8, t1: u8, t2: u8) -> int {
    if t0 < 16 {
        t0 as int
    } else if t1 < 16 {
        16 + t1
    } else {
        32 + t2
    }
}

/// One pixel's three table entries select exactly one source, and one
/// that exists: `A2` has 15 entries and `A3` has 14.
pub open spec fn p4_wf(t0: u8, t1: u8, t2: u8) -> bool {
    ||| (t0 < 16 && t1 == 128 && t2 == 128)
    ||| (t0 == 128 && t1 < 15 && t2 == 128)
    ||| (t0 == 128 && t1 == 128 && t2 < 14)
}

/// The table's entries for pixel `p` of `mode` select the value the
/// specification gives that pixel.
pub open spec fn p4_cell(a: Seq<int>, l: Seq<int>, mode: int, p: int) -> bool {
    let t0 = P4T@[48 * mode + p];
    let t1 = P4T@[48 * mode + 16 + p];
    let t2 = P4T@[48 * mode + 32 + p];
    &&& p4_wf(t0, t1, t2)
    &&& p4_src(p4_edges(a, l), p4_pick(t0, t1, t2)) == pred4_px(mode, a, l, p / 4, p % 4)
}

proof fn lemma_p4_mode0(a: Seq<int>, l: Seq<int>)
    ensures
        forall|p: int| 0 <= p < 16 ==> #[trigger] p4_cell(a, l, 0, p),
{
    assert(p4_cell(a, l, 0, 0));
    assert(p4_cell(a, l, 0, 1));
    assert(p4_cell(a, l, 0, 2));
    assert(p4_cell(a, l, 0, 3));
    assert(p4_cell(a, l, 0, 4));
    assert(p4_cell(a, l, 0, 5));
    assert(p4_cell(a, l, 0, 6));
    assert(p4_cell(a, l, 0, 7));
    assert(p4_cell(a, l, 0, 8));
    assert(p4_cell(a, l, 0, 9));
    assert(p4_cell(a, l, 0, 10));
    assert(p4_cell(a, l, 0, 11));
    assert(p4_cell(a, l, 0, 12));
    assert(p4_cell(a, l, 0, 13));
    assert(p4_cell(a, l, 0, 14));
    assert(p4_cell(a, l, 0, 15));
}

proof fn lemma_p4_mode2(a: Seq<int>, l: Seq<int>)
    ensures
        forall|p: int| 0 <= p < 16 ==> #[trigger] p4_cell(a, l, 2, p),
{
    assert(p4_cell(a, l, 2, 0));
    assert(p4_cell(a, l, 2, 1));
    assert(p4_cell(a, l, 2, 2));
    assert(p4_cell(a, l, 2, 3));
    assert(p4_cell(a, l, 2, 4));
    assert(p4_cell(a, l, 2, 5));
    assert(p4_cell(a, l, 2, 6));
    assert(p4_cell(a, l, 2, 7));
    assert(p4_cell(a, l, 2, 8));
    assert(p4_cell(a, l, 2, 9));
    assert(p4_cell(a, l, 2, 10));
    assert(p4_cell(a, l, 2, 11));
    assert(p4_cell(a, l, 2, 12));
    assert(p4_cell(a, l, 2, 13));
    assert(p4_cell(a, l, 2, 14));
    assert(p4_cell(a, l, 2, 15));
}

proof fn lemma_p4_mode3(a: Seq<int>, l: Seq<int>)
    ensures
        forall|p: int| 0 <= p < 16 ==> #[trigger] p4_cell(a, l, 3, p),
{
    assert(p4_cell(a, l, 3, 0));
    assert(p4_cell(a, l, 3, 1));
    assert(p4_cell(a, l, 3, 2));
    assert(p4_cell(a, l, 3, 3));
    assert(p4_cell(a, l, 3, 4));
    assert(p4_cell(a, l, 3, 5));
    assert(p4_cell(a, l, 3, 6));
    assert(p4_cell(a, l, 3, 7));
    assert(p4_cell(a, l, 3, 8));
    assert(p4_cell(a, l, 3, 9));
    assert(p4_cell(a, l, 3, 10));
    assert(p4_cell(a, l, 3, 11));
    assert(p4_cell(a, l, 3, 12));
    assert(p4_cell(a, l, 3, 13));
    assert(p4_cell(a, l, 3, 14));
    assert(p4_cell(a, l, 3, 15));
}

proof fn lemma_p4_mode4(a: Seq<int>, l: Seq<int>)
    ensures
        forall|p: int| 0 <= p < 16 ==> #[trigger] p4_cell(a, l, 4, p),
{
    assert(p4_cell(a, l, 4, 0));
    assert(p4_cell(a, l, 4, 1));
    assert(p4_cell(a, l, 4, 2));
    assert(p4_cell(a, l, 4, 3));
    assert(p4_cell(a, l, 4, 4));
    assert(p4_cell(a, l, 4, 5));
    assert(p4_cell(a, l, 4, 6));
    assert(p4_cell(a, l, 4, 7));
    assert(p4_cell(a, l, 4, 8));
    assert(p4_cell(a, l, 4, 9));
    assert(p4_cell(a, l, 4, 10));
    assert(p4_cell(a, l, 4, 11));
    assert(p4_cell(a, l, 4, 12));
    assert(p4_cell(a, l, 4, 13));
    assert(p4_cell(a, l, 4, 14));
    assert(p4_cell(a, l, 4, 15));
}

proof fn lemma_p4_mode5(a: Seq<int>, l: Seq<int>)
    ensures
        forall|p: int| 0 <= p < 16 ==> #[trigger] p4_cell(a, l, 5, p),
{
    assert(p4_cell(a, l, 5, 0));
    assert(p4_cell(a, l, 5, 1));
    assert(p4_cell(a, l, 5, 2));
    assert(p4_cell(a, l, 5, 3));
    assert(p4_cell(a, l, 5, 4));
    assert(p4_cell(a, l, 5, 5));
    assert(p4_cell(a, l, 5, 6));
    assert(p4_cell(a, l, 5, 7));
    assert(p4_cell(a, l, 5, 8));
    assert(p4_cell(a, l, 5, 9));
    assert(p4_cell(a, l, 5, 10));
    assert(p4_cell(a, l, 5, 11));
    assert(p4_cell(a, l, 5, 12));
    assert(p4_cell(a, l, 5, 13));
    assert(p4_cell(a, l, 5, 14));
    assert(p4_cell(a, l, 5, 15));
}

proof fn lemma_p4_mode6(a: Seq<int>, l: Seq<int>)
    ensures
        forall|p: int| 0 <= p < 16 ==> #[trigger] p4_cell(a, l, 6, p),
{
    assert(p4_cell(a, l, 6, 0));
    assert(p4_cell(a, l, 6, 1));
    assert(p4_cell(a, l, 6, 2));
    assert(p4_cell(a, l, 6, 3));
    assert(p4_cell(a, l, 6, 4));
    assert(p4_cell(a, l, 6, 5));
    assert(p4_cell(a, l, 6, 6));
    assert(p4_cell(a, l, 6, 7));
    assert(p4_cell(a, l, 6, 8));
    assert(p4_cell(a, l, 6, 9));
    assert(p4_cell(a, l, 6, 10));
    assert(p4_cell(a, l, 6, 11));
    assert(p4_cell(a, l, 6, 12));
    assert(p4_cell(a, l, 6, 13));
    assert(p4_cell(a, l, 6, 14));
    assert(p4_cell(a, l, 6, 15));
}

proof fn lemma_p4_mode7(a: Seq<int>, l: Seq<int>)
    ensures
        forall|p: int| 0 <= p < 16 ==> #[trigger] p4_cell(a, l, 7, p),
{
    assert(p4_cell(a, l, 7, 0));
    assert(p4_cell(a, l, 7, 1));
    assert(p4_cell(a, l, 7, 2));
    assert(p4_cell(a, l, 7, 3));
    assert(p4_cell(a, l, 7, 4));
    assert(p4_cell(a, l, 7, 5));
    assert(p4_cell(a, l, 7, 6));
    assert(p4_cell(a, l, 7, 7));
    assert(p4_cell(a, l, 7, 8));
    assert(p4_cell(a, l, 7, 9));
    assert(p4_cell(a, l, 7, 10));
    assert(p4_cell(a, l, 7, 11));
    assert(p4_cell(a, l, 7, 12));
    assert(p4_cell(a, l, 7, 13));
    assert(p4_cell(a, l, 7, 14));
    assert(p4_cell(a, l, 7, 15));
}

proof fn lemma_p4_mode8(a: Seq<int>, l: Seq<int>)
    ensures
        forall|p: int| 0 <= p < 16 ==> #[trigger] p4_cell(a, l, 8, p),
{
    assert(p4_cell(a, l, 8, 0));
    assert(p4_cell(a, l, 8, 1));
    assert(p4_cell(a, l, 8, 2));
    assert(p4_cell(a, l, 8, 3));
    assert(p4_cell(a, l, 8, 4));
    assert(p4_cell(a, l, 8, 5));
    assert(p4_cell(a, l, 8, 6));
    assert(p4_cell(a, l, 8, 7));
    assert(p4_cell(a, l, 8, 8));
    assert(p4_cell(a, l, 8, 9));
    assert(p4_cell(a, l, 8, 10));
    assert(p4_cell(a, l, 8, 11));
    assert(p4_cell(a, l, 8, 12));
    assert(p4_cell(a, l, 8, 13));
    assert(p4_cell(a, l, 8, 14));
    assert(p4_cell(a, l, 8, 15));
}

proof fn lemma_p4_mode9(a: Seq<int>, l: Seq<int>)
    ensures
        forall|p: int| 0 <= p < 16 ==> #[trigger] p4_cell(a, l, 9, p),
{
    assert(p4_cell(a, l, 9, 0));
    assert(p4_cell(a, l, 9, 1));
    assert(p4_cell(a, l, 9, 2));
    assert(p4_cell(a, l, 9, 3));
    assert(p4_cell(a, l, 9, 4));
    assert(p4_cell(a, l, 9, 5));
    assert(p4_cell(a, l, 9, 6));
    assert(p4_cell(a, l, 9, 7));
    assert(p4_cell(a, l, 9, 8));
    assert(p4_cell(a, l, 9, 9));
    assert(p4_cell(a, l, 9, 10));
    assert(p4_cell(a, l, 9, 11));
    assert(p4_cell(a, l, 9, 12));
    assert(p4_cell(a, l, 9, 13));
    assert(p4_cell(a, l, 9, 14));
    assert(p4_cell(a, l, 9, 15));
}

/// The table is right: for every mode but TM and every pixel.
proof fn lemma_p4_table(a: Seq<int>, l: Seq<int>, mode: int)
    requires
        0 <= mode < 10,
        mode != 1,
    ensures
        forall|p: int| 0 <= p < 16 ==> #[trigger] p4_cell(a, l, mode, p),
{
    if mode == 0 {
        lemma_p4_mode0(a, l);
    } else if mode == 2 {
        lemma_p4_mode2(a, l);
    } else if mode == 3 {
        lemma_p4_mode3(a, l);
    } else if mode == 4 {
        lemma_p4_mode4(a, l);
    } else if mode == 5 {
        lemma_p4_mode5(a, l);
    } else if mode == 6 {
        lemma_p4_mode6(a, l);
    } else if mode == 7 {
        lemma_p4_mode7(a, l);
    } else if mode == 8 {
        lemma_p4_mode8(a, l);
    } else {
        lemma_p4_mode9(a, l);
    }
}

/// The bytes of the vector made of the left column and DC's value.
proof fn lemma_p4_make(s: Seq<u8>, l0: u8, l1: u8, l2: u8, l3: u8, dc: u8)
    requires
        s.len() == 16,
        u64s(s)[0] == (l3 as u64) | ((l3 as u64) << 8u64) | ((l2 as u64) << 16u64) | ((l1 as u64) << 24u64) | ((l0 as u64) << 32u64),
        u64s(s)[1] == (dc as u64) << 56u64,
    ensures
        s[0] == l3 && s[1] == l3 && s[2] == l2 && s[3] == l1 && s[4] == l0,
        forall|i: int| 5 <= i < 15 ==> s[i] == 0,
        s[15] == dc,
{
    let (b0, b1, b2, b3, b4, b5, b6, b7) = (s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]);
    let (c0, c1, c2, c3, c4, c5, c6, c7) = (s[8], s[9], s[10], s[11], s[12], s[13], s[14], s[15]);
    assert(u64s(s)[0] == le64(le32(b0, b1, b2, b3), le32(b4, b5, b6, b7)));
    assert(u64s(s)[1] == le64(le32(c0, c1, c2, c3), le32(c4, c5, c6, c7)));
    assert((((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) as u64) | ((((b4 as u32) | ((b5 as u32)
        << 8u32) | ((b6 as u32) << 16u32) | ((b7 as u32) << 24u32)) as u64) << 32u64) == (l3 as u64) | ((l3 as u64) << 8u64) | ((l2 as u64)
        << 16u64) | ((l1 as u64) << 24u64) | ((l0 as u64) << 32u64) ==> b0 == l3 && b1 == l3 && b2 == l2 && b3 == l1 && b4 == l0 && b5 == 0
        && b6 == 0 && b7 == 0) by (bit_vector);
    assert((((c0 as u32) | ((c1 as u32) << 8u32) | ((c2 as u32) << 16u32) | ((c3 as u32) << 24u32)) as u64) | ((((c4 as u32) | ((c5 as u32)
        << 8u32) | ((c6 as u32) << 16u32) | ((c7 as u32) << 24u32)) as u64) << 32u64) == (dc as u64) << 56u64 ==> c0 == 0 && c1 == 0 && c2
        == 0 && c3 == 0 && c4 == 0 && c5 == 0 && c6 == 0 && c7 == dc) by (bit_vector);
}

/// `avg(x, y) - ((x ^ y) & 1)` is the average rounded down.
proof fn lemma_p4_floor(x: u8, y: u8)
    ensures
        ((((x + y + 1) / 2) as u8 - ((x ^ y) & 1u8) + 256) % 256) as u8 as int == (x + y) / 2,
{
    assert((x ^ y) & 1u8 == (if x % 2u8 == y % 2u8 { 0u8 } else { 1u8 })) by (bit_vector);
}

/// A 16-byte vector type the table predictor can run on: NEON's
/// `uint8x16_t` and, with SSSE3, `__m128i`. Each operation states what
/// it does to the bytes, the same for both, so the predictor and its
/// proof are written once.
pub trait P4v: Copy + Sized {
    /// The vector's sixteen bytes in memory order.
    spec fn pb(self) -> Seq<u8>;

    /// What the operations need of the CPU.
    spec fn pok() -> bool;

    proof fn lemma_plen(self)
        ensures
            self.pb().len() == 16,
    ;

    /// The sixteen bytes at `s[i..i + 16]`.
    fn pload(s: &[u8], i: usize) -> (r: Self)
        requires
            Self::pok(),
            i + 16 <= s@.len(),
        ensures
            r.pb() == s@.subrange(i as int, i + 16),
    ;

    /// The vector of two 64-bit halves.
    fn pmake(lo: u64, hi: u64) -> (r: Self)
        requires
            Self::pok(),
        ensures
            u64s(r.pb()) == seq![lo, hi],
    ;

    /// A byte shuffle: an index below 16 picks that byte of `t`, and 128
    /// or more gives 0.
    fn ptbl(t: Self, idx: Self) -> (r: Self)
        requires
            Self::pok(),
        ensures
            forall|k: int|
                0 <= k < 16 ==> (idx.pb()[k] < 16 ==> #[trigger] r.pb()[k] == t.pb()[idx.pb()[k] as int]) && (idx.pb()[k] >= 128 ==> r.pb()[k]
                    == 0),
    ;

    fn por(a: Self, b: Self) -> (r: Self)
        requires
            Self::pok(),
        ensures
            forall|k: int| 0 <= k < 16 ==> #[trigger] r.pb()[k] == a.pb()[k] | b.pb()[k],
    ;

    /// The bytes moved down one place (the top byte is not specified).
    fn pshr1(a: Self) -> (r: Self)
        requires
            Self::pok(),
        ensures
            forall|k: int| 0 <= k < 15 ==> #[trigger] r.pb()[k] == a.pb()[k + 1],
    ;

    /// The bytes moved down two places.
    fn pshr2(a: Self) -> (r: Self)
        requires
            Self::pok(),
        ensures
            forall|k: int| 0 <= k < 14 ==> #[trigger] r.pb()[k] == a.pb()[k + 2],
    ;

    /// The average of each pair of bytes, rounded up.
    fn pavg(a: Self, b: Self) -> (r: Self)
        requires
            Self::pok(),
        ensures
            forall|k: int| 0 <= k < 16 ==> #[trigger] r.pb()[k] as int == (a.pb()[k] + b.pb()[k] + 1) / 2,
    ;

    /// The average of each pair of bytes, rounded down.
    fn pavgf(a: Self, b: Self) -> (r: Self)
        requires
            Self::pok(),
        ensures
            forall|k: int| 0 <= k < 16 ==> #[trigger] r.pb()[k] as int == (a.pb()[k] + b.pb()[k]) / 2,
    ;

    /// Stores bytes `4 * k..4 * k + 4` at `s[i..i + 4]`.
    fn pst4(s: &mut [u8], i: usize, v: Self, k: usize)
        requires
            Self::pok(),
            k < 4,
            i + 4 <= old(s)@.len(),
        ensures
            final(s)@ == old(s)@.subrange(0, i as int) + v.pb().subrange(4 * k as int, 4 * k + 4) + old(s)@.subrange(
                i + 4,
                old(s)@.len() as int,
            ),
    ;
}

/// NEON (the AArch64 baseline).
impl P4v for uint8x16_t {
    open spec fn pb(self) -> Seq<u8> {
        n8(self)
    }

    open spec fn pok() -> bool {
        neon()
    }

    proof fn lemma_plen(self) {
    }

    #[inline(always)]
    fn pload(s: &[u8], i: usize) -> (r: Self) {
        vld1q_u8_at(s, i)
    }

    #[inline(always)]
    fn pmake(lo: u64, hi: u64) -> (r: Self) {
        vcombine_u64(lo, hi)
    }

    #[inline(always)]
    fn ptbl(t: Self, idx: Self) -> (r: Self) {
        vqtbl1q_u8(t, idx)
    }

    #[inline(always)]
    fn por(a: Self, b: Self) -> (r: Self) {
        vorrq_u8(a, b)
    }

    #[inline(always)]
    fn pshr1(a: Self) -> (r: Self) {
        vextq_u8::<1>(a, a)
    }

    #[inline(always)]
    fn pshr2(a: Self) -> (r: Self) {
        vextq_u8::<2>(a, a)
    }

    #[inline(always)]
    fn pavg(a: Self, b: Self) -> (r: Self) {
        vrhaddq_u8(a, b)
    }

    #[inline(always)]
    fn pavgf(a: Self, b: Self) -> (r: Self) {
        let r = vsubq_u8(vrhaddq_u8(a, b), vandq_u8(veorq_u8(a, b), vdupq_n_u8(1)));
        proof {
            assert forall|k: int| 0 <= k < 16 implies #[trigger] n8(r)[k] as int == (n8(a)[k] + n8(b)[k]) / 2 by {
                lemma_p4_floor(n8(a)[k], n8(b)[k]);
            }
        }
        r
    }

    #[inline(always)]
    fn pst4(s: &mut [u8], i: usize, v: Self, k: usize) {
        if k == 0 {
            vst1q_lane_u32_at::<0>(s, i, v);
        } else if k == 1 {
            vst1q_lane_u32_at::<1>(s, i, v);
        } else if k == 2 {
            vst1q_lane_u32_at::<2>(s, i, v);
        } else {
            vst1q_lane_u32_at::<3>(s, i, v);
        }
    }
}

/// The `i64` with the bits of `x`.
#[inline(always)]
fn i64_of(x: u64) -> (r: i64)
    ensures
        u64_of_i64(r) == x,
{
    if x < 0x8000_0000_0000_0000 {
        x as i64
    } else {
        ((x - 0x8000_0000_0000_0000) as i64) - 0x7fff_ffff_ffff_ffff - 1
    }
}

/// SSSE3, for `pshufb`; everything else is SSE2.
impl P4v for __m128i {
    open spec fn pb(self) -> Seq<u8> {
        b128(self)
    }

    open spec fn pok() -> bool {
        ssse3()
    }

    proof fn lemma_plen(self) {
    }

    #[inline(always)]
    fn pload(s: &[u8], i: usize) -> (r: Self) {
        load128_u8(s, i)
    }

    #[inline(always)]
    fn pmake(lo: u64, hi: u64) -> (r: Self) {
        let a = _mm_cvtsi64_si128(i64_of(lo));
        let b = _mm_cvtsi64_si128(i64_of(hi));
        let r = _mm_unpacklo_epi64(a, b);
        proof {
            assert(u64x2(r)[0] == u64x2(a)[0] && u64x2(r)[1] == u64x2(b)[0]);
            assert(u64s(b128(r)) =~= seq![lo, hi]);
        }
        r
    }

    #[inline(always)]
    fn ptbl(t: Self, idx: Self) -> (r: Self) {
        _mm_shuffle_epi8(t, idx)
    }

    #[inline(always)]
    fn por(a: Self, b: Self) -> (r: Self) {
        _mm_or_si128(a, b)
    }

    #[inline(always)]
    fn pshr1(a: Self) -> (r: Self) {
        _mm_srli_si128::<1>(a)
    }

    #[inline(always)]
    fn pshr2(a: Self) -> (r: Self) {
        _mm_srli_si128::<2>(a)
    }

    #[inline(always)]
    fn pavg(a: Self, b: Self) -> (r: Self) {
        _mm_avg_epu8(a, b)
    }

    #[inline(always)]
    fn pavgf(a: Self, b: Self) -> (r: Self) {
        let r = _mm_sub_epi8(_mm_avg_epu8(a, b), _mm_and_si128(_mm_xor_si128(a, b), _mm_set1_epi8(1)));
        proof {
            assert forall|k: int| 0 <= k < 16 implies #[trigger] b128(r)[k] as int == (b128(a)[k] + b128(b)[k]) / 2 by {
                lemma_p4_floor(b128(a)[k], b128(b)[k]);
            }
        }
        r
    }

    #[inline(always)]
    fn pst4(s: &mut [u8], i: usize, v: Self, k: usize) {
        let w = if k == 0 {
            v
        } else if k == 1 {
            _mm_srli_si128::<4>(v)
        } else if k == 2 {
            _mm_srli_si128::<8>(v)
        } else {
            _mm_srli_si128::<12>(v)
        };
        proof {
            assert(b128(w).subrange(0, 4) =~= b128(v).subrange(4 * k as int, 4 * k + 4));
        }
        storel32_u8(s, i, w);
    }
}

/// The edge vector of the subblock at `d`.
#[inline(always)]
fn p4_edge_vec<V: P4v>(b: &[u8], d: usize) -> (e: V)
    requires
        V::pok(),
        pred_ok(b@.len(), d as int, 4),
    ensures
        e.pb().len() == 16,
        forall|i: int| 0 <= i < 16 ==> #[trigger] e.pb()[i] as int == p4_edges(nb_above(b@, d as int, 8), nb_left(b@, d as int, 4))[i],
{
    proof {
        assert(b@.len() == b.len());
    }
    let ghost a = nb_above(b@, d as int, 8);
    let ghost l = nb_left(b@, d as int, 4);
    let ghost ev = p4_edges(a, l);
    let l0 = get(b, d - 1);
    let l1 = get(b, d + BPS - 1);
    let l2 = get(b, d + 2 * BPS - 1);
    let l3 = get(b, d + 3 * BPS - 1);
    let s = sum4(b, d);
    proof {
        lemma_sum_range_eq(nb_above(b@, d as int, 4), a, 1, 5);
    }
    let t = s + 4;
    assert(t <= 2044 ==> (t >> 3u32) == t / 8 && (t >> 3u32) <= 255) by (bit_vector);
    let dc = (t >> 3u32) as u8;
    let lw = (l3 as u64) | ((l3 as u64) << 8u64) | ((l2 as u64) << 16u64) | ((l1 as u64) << 24u64) | ((l0 as u64) << 32u64);
    let v = V::pload(b, d - 33);
    let ix = V::pload(P4T.as_slice(), 480);
    let top = V::ptbl(v, ix);
    let lv = V::pmake(lw, (dc as u64) << 56u64);
    let e = V::por(top, lv);
    proof {
        v.lemma_plen();
        ix.lemma_plen();
        top.lemma_plen();
        lv.lemma_plen();
        e.lemma_plen();
        lemma_p4_make(lv.pb(), l0, l1, l2, l3, dc);
        assert(dc as int == ev[15]);
        assert forall|i: int| 0 <= i < 16 implies #[trigger] e.pb()[i] as int == ev[i] by {
            let x = top.pb()[i];
            let y = lv.pb()[i];
            assert(e.pb()[i] == x | y);
            assert(ix.pb()[i] == P4T@[480 + i]);
            assert(x | 0u8 == x && 0u8 | y == y) by (bit_vector);
            if 5 <= i < 15 {
                let j = ix.pb()[i] as int;
                assert(v.pb()[j] == b@[d - 33 + j]);
                assert(a[j] == b@[d - 33 + j]);
            }
        }
    }
    e
}

/// The sixteen pixels of `mode`, in raster order, from the edge vector.
#[inline(always)]
fn p4_pixels<V: P4v>(e: V, mode: u8, Ghost(a): Ghost<Seq<int>>, Ghost(l): Ghost<Seq<int>>) -> (r: V)
    requires
        V::pok(),
        mode < 10,
        mode != 1,
        e.pb().len() == 16,
        forall|i: int| 0 <= i < 16 ==> #[trigger] e.pb()[i] as int == p4_edges(a, l)[i],
    ensures
        r.pb().len() == 16,
        forall|p: int| 0 <= p < 16 ==> #[trigger] r.pb()[p] as int == pred4_px(mode as int, a, l, p / 4, p % 4),
{
    hide(pred4_px);
    hide(p4_edges);
    let ghost ev = p4_edges(a, l);
    let e1 = V::pshr1(e);
    let e2 = V::pshr2(e);
    let a2 = V::pavg(e, e1);
    let f = V::pavgf(e, e2);
    let a3 = V::pavg(f, e1);
    let m = mode as usize * 48;
    let t0 = V::pload(P4T.as_slice(), m);
    let t1 = V::pload(P4T.as_slice(), m + 16);
    let t2 = V::pload(P4T.as_slice(), m + 32);
    let r0 = V::ptbl(e, t0);
    let r1 = V::ptbl(a2, t1);
    let r2 = V::ptbl(a3, t2);
    let r01 = V::por(r0, r1);
    let r = V::por(r01, r2);
    proof {
        e1.lemma_plen();
        e2.lemma_plen();
        a2.lemma_plen();
        f.lemma_plen();
        a3.lemma_plen();
        r.lemma_plen();
        lemma_p4_table(a, l, mode as int);
        assert forall|p: int| 0 <= p < 16 implies #[trigger] r.pb()[p] as int == pred4_px(mode as int, a, l, p / 4, p % 4) by {
            assert(p4_cell(a, l, mode as int, p));
            let (x0, x1, x2) = (r0.pb()[p], r1.pb()[p], r2.pb()[p]);
            let (i0, i1, i2) = (t0.pb()[p], t1.pb()[p], t2.pb()[p]);
            assert(i0 == P4T@[48 * mode + p]);
            assert(i1 == P4T@[48 * mode + 16 + p]);
            assert(i2 == P4T@[48 * mode + 32 + p]);
            assert(p4_wf(i0, i1, i2));
            assert(r01.pb()[p] == x0 | x1);
            assert(r.pb()[p] == r01.pb()[p] | x2);
            assert((x0 | 0u8) | 0u8 == x0 && (0u8 | x1) | 0u8 == x1 && (0u8 | 0u8) | x2 == x2) by (bit_vector);
            if i0 < 16 {
                assert(x0 == e.pb()[i0 as int]);
                assert(x0 as int == ev[i0 as int]);
            } else if i1 < 16 {
                let k = i1 as int;
                assert(x1 == a2.pb()[k]);
                assert(e1.pb()[k] == e.pb()[k + 1]);
                assert(x1 as int == spec_avg2(ev[k], ev[k + 1]));
            } else {
                let k = i2 as int;
                assert(x2 == a3.pb()[k]);
                assert(e1.pb()[k] == e.pb()[k + 1]);
                assert(e2.pb()[k] == e.pb()[k + 2]);
                assert(f.pb()[k] as int == (ev[k] + ev[k + 2]) / 2);
                assert(x2 as int == spec_avg3(ev[k], ev[k + 1], ev[k + 2]));
            }
        }
    }
    r
}

/// Stores the sixteen bytes of `r` as the four rows of the subblock at `d`.
#[inline(always)]
fn p4_store<V: P4v>(b: &mut [u8], d: usize, r: V)
    requires
        V::pok(),
        r.pb().len() == 16,
        d + 3 * BPS + 4 <= old(b)@.len(),
    ensures
        final(b)@.len() == old(b)@.len(),
        forall|j: int| 0 <= j < old(b)@.len() && !in_sq4(j - d) ==> #[trigger] final(b)@[j] == old(b)@[j],
        final(b)@[d + 0] == r.pb()[0int] && final(b)@[d + 1] == r.pb()[1int] && final(b)@[d + 2] == r.pb()[2int] && final(b)@[d + 3] == r.pb()[3int],
        final(b)@[d + 32] == r.pb()[4int] && final(b)@[d + 33] == r.pb()[5int] && final(b)@[d + 34] == r.pb()[6int] && final(b)@[d + 35] == r.pb()[7int],
        final(b)@[d + 64] == r.pb()[8int] && final(b)@[d + 65] == r.pb()[9int] && final(b)@[d + 66] == r.pb()[10int] && final(b)@[d + 67] == r.pb()[11int],
        final(b)@[d + 96] == r.pb()[12int] && final(b)@[d + 97] == r.pb()[13int] && final(b)@[d + 98] == r.pb()[14int] && final(b)@[d + 99] == r.pb()[15int],
{
    proof {
        assert(b@.len() == b.len());
    }
    V::pst4(b, d, r, 0);
    let ghost b1 = b@;
    V::pst4(b, d + BPS, r, 1);
    let ghost b2 = b@;
    V::pst4(b, d + 2 * BPS, r, 2);
    let ghost b3 = b@;
    V::pst4(b, d + 3 * BPS, r, 3);
    proof {
        assert(b1.len() == old(b)@.len() && b2.len() == b1.len() && b3.len() == b1.len() && b@.len() == b1.len());
        assert forall|j: int| 0 <= j < b1.len() implies #[trigger] b1[j] == (if d <= j < d + 4 { r.pb()[j - d] } else { old(b)@[j] }) by {}
        assert forall|j: int| 0 <= j < b1.len() implies #[trigger] b2[j] == (if d + 32 <= j < d + 36 { r.pb()[4 + j - d - 32] } else { b1[j] }) by {}
        assert forall|j: int| 0 <= j < b1.len() implies #[trigger] b3[j] == (if d + 64 <= j < d + 68 { r.pb()[8 + j - d - 64] } else { b2[j] }) by {}
        assert forall|j: int| 0 <= j < b1.len() implies #[trigger] b@[j] == (if d + 96 <= j < d + 100 { r.pb()[12 + j - d - 96] } else { b3[j] }) by {}
    }
}

/// `VP8PredLuma4[mode]` for every mode but TM, from `P4T`.
#[inline(always)]
fn pred4_tbl<V: P4v>(b: &mut [u8], d: usize, mode: u8)
    requires
        V::pok(),
        mode < 10,
        mode != 1,
        pred_ok(old(b)@.len(), d as int, 4),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint4(old(b)@, d as int, mode as int),
{
    hide(pred4_px);
    hide(p4_edges);
    let ghost b0 = b@;
    let ghost a = nb_above(b@, d as int, 8);
    let ghost l = nb_left(b@, d as int, 4);
    let e = p4_edge_vec::<V>(b, d);
    let r = p4_pixels::<V>(e, mode, Ghost(a), Ghost(l));
    p4_store::<V>(b, d, r);
    proof {
        assert(row_ok(b0, b@, d as int, mode as int, 0)) by {
            assert(r.pb()[0int] as int == pred4_px(mode as int, a, l, 0int / 4, 0int % 4) && r.pb()[1int] as int == pred4_px(mode as int, a, l, 1int / 4, 1int % 4) && r.pb()[2int] as int == pred4_px(mode as int, a, l, 2int / 4, 2int % 4) && r.pb()[3int] as int == pred4_px(mode as int, a, l, 3int / 4, 3int % 4));
        }
        assert(row_ok(b0, b@, d as int, mode as int, 1)) by {
            assert(r.pb()[4int] as int == pred4_px(mode as int, a, l, 4int / 4, 4int % 4) && r.pb()[5int] as int == pred4_px(mode as int, a, l, 5int / 4, 5int % 4) && r.pb()[6int] as int == pred4_px(mode as int, a, l, 6int / 4, 6int % 4) && r.pb()[7int] as int == pred4_px(mode as int, a, l, 7int / 4, 7int % 4));
        }
        assert(row_ok(b0, b@, d as int, mode as int, 2)) by {
            assert(r.pb()[8int] as int == pred4_px(mode as int, a, l, 8int / 4, 8int % 4) && r.pb()[9int] as int == pred4_px(mode as int, a, l, 9int / 4, 9int % 4) && r.pb()[10int] as int == pred4_px(mode as int, a, l, 10int / 4, 10int % 4) && r.pb()[11int] as int == pred4_px(mode as int, a, l, 11int / 4, 11int % 4));
        }
        assert(row_ok(b0, b@, d as int, mode as int, 3)) by {
            assert(r.pb()[12int] as int == pred4_px(mode as int, a, l, 12int / 4, 12int % 4) && r.pb()[13int] as int == pred4_px(mode as int, a, l, 13int / 4, 13int % 4) && r.pb()[14int] as int == pred4_px(mode as int, a, l, 14int / 4, 14int % 4) && r.pb()[15int] as int == pred4_px(mode as int, a, l, 15int / 4, 15int % 4));
        }
        lemma_paint4_cells(b0, b@, d as int, mode as int);
    }
}

/// `VP8PredLuma4[mode]`: the ten 4x4 modes (DC, TM, VE, HE, RD, VR, LD,
/// VL, HD, HU). In an x86 build for SSSE3 every mode but TM comes from
/// the table (`pred4_tbl`), with no branch on the mode; otherwise, and
/// for TM, `vp8dsp::pred4`.
#[inline(always)]
pub fn pred4_fast(b: &mut [u8], d: usize, mode: u8)
    requires
        mode < 10,
        pred_ok(old(b)@.len(), d as int, 4),
    ensures
        final(b)@.len() == old(b)@.len(),
        final(b)@ == paint4(old(b)@, d as int, mode as int),
{
    if mode != 1 {
        // Not on NEON: measured on an Apple M3 the table path (the
        // `uint8x16_t` instance of `pred4_tbl`, still proven and tested)
        // was 1.7% slower per decode than the match, whose jump that core
        // predicts well. On x86 only in a build for SSSE3, where `pshufb`
        // is inlined: a run-time check would put this small kernel behind
        // a call.
        if compiled_with_ssse3() {
            pred4_tbl::<__m128i>(b, d, mode);
            return;
        }
    }
    pred4(b, d, mode);
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    /// The table predictor writes what `vp8dsp::pred4`'s match writes, for
    /// every mode but TM, on random and on flat neighbourhoods, at every
    /// place a subblock can stand in the smallest buffer that holds it.
    #[test]
    fn table_matches_match() {
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for iter in 0..200_000usize {
            let d = 33 + (rnd() % 40) as usize;
            // `pred_ok`: the last byte read or written is `d + 3 * 32 + 7`.
            let mut buf = vec![0u8; d + 3 * 32 + 8];
            let flat = iter % 8 == 0;
            let base = rnd() as u8;
            for v in buf.iter_mut() {
                *v = if flat { base } else if iter % 8 == 1 { [0u8, 255][(rnd() % 2) as usize] } else { rnd() as u8 };
            }
            for mode in [0u8, 2, 3, 4, 5, 6, 7, 8, 9] {
                let mut want = buf.clone();
                pred4(&mut want, d, mode);
                let mut got = buf.clone();
                pred4_tbl::<uint8x16_t>(&mut got, d, mode);
                assert!(got == want, "NEON, mode {mode}, iteration {iter}");
                let mut got = buf.clone();
                // Off x86 this runs vsimd's emulation of the intrinsics.
                #[cfg(target_arch = "x86_64")]
                let ssse3 = std::is_x86_feature_detected!("ssse3");
                #[cfg(not(target_arch = "x86_64"))]
                let ssse3 = true;
                if ssse3 {
                    pred4_tbl::<__m128i>(&mut got, d, mode);
                    assert!(got == want, "SSSE3, mode {mode}, iteration {iter}");
                }
            }
        }
    }
}

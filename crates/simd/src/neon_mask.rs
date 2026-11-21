//! Verified NEON patterns built from the trusted wrappers in `crate::neon`.
//!
//! `movemask64` is x86's `movemask` for NEON, which has no such
//! instruction: it packs four vectors of 0x00/0xFF bytes into a 64-bit mask,
//! one bit per byte, with the usual AND-with-bit-weights and three pairwise
//! additions. `movemask16` is the same for one vector.
use crate::lanes::*;
use crate::neon::*;
use crate::ops::*;
use vstd::prelude::*;

verus! {

broadcast use {crate::lanes::group_lanes, crate::neon::group_neon};

/// Each byte is 0x00 or 0xFF.
pub open spec fn is_mask(b: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] == 0 || b[i] == 0xFF
}

/// Byte `k` of the 64 bytes `a ++ b ++ c ++ d`.
pub open spec fn byte4(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>, d: Seq<u8>, k: int) -> u8 {
    if k < 16 {
        a[k]
    } else if k < 32 {
        b[k - 16]
    } else if k < 48 {
        c[k - 32]
    } else {
        d[k - 48]
    }
}

pub const WEIGHTS: [u8; 16] = [1, 2, 4, 8, 16, 32, 64, 128, 1, 2, 4, 8, 16, 32, 64, 128];

/// Eight weighted mask bytes, summed as the pairwise-add tree does, are the
/// mask's bits.
#[verifier::bit_vector]
proof fn lemma_byte_sum(c0: u8, c1: u8, c2: u8, c3: u8, c4: u8, c5: u8, c6: u8, c7: u8)
    requires
        c0 == 0 || c0 == 0xFF,
        c1 == 0 || c1 == 0xFF,
        c2 == 0 || c2 == 0xFF,
        c3 == 0 || c3 == 0xFF,
        c4 == 0 || c4 == 0xFF,
        c5 == 0 || c5 == 0xFF,
        c6 == 0 || c6 == 0xFF,
        c7 == 0 || c7 == 0xFF,
    ensures
        ({
            let s = add(add(add(c0 & 1, c1 & 2), add(c2 & 4, c3 & 8)), add(add(c4 & 16, c5 & 32), add(c6 & 64, c7 & 128)));
            &&& ((s >> 0u8) & 1 == 1) == (c0 == 0xFF)
            &&& ((s >> 1u8) & 1 == 1) == (c1 == 0xFF)
            &&& ((s >> 2u8) & 1 == 1) == (c2 == 0xFF)
            &&& ((s >> 3u8) & 1 == 1) == (c3 == 0xFF)
            &&& ((s >> 4u8) & 1 == 1) == (c4 == 0xFF)
            &&& ((s >> 5u8) & 1 == 1) == (c5 == 0xFF)
            &&& ((s >> 6u8) & 1 == 1) == (c6 == 0xFF)
            &&& ((s >> 7u8) & 1 == 1) == (c7 == 0xFF)
        }),
{
}

/// The pairwise-add tree over `x[o..o + 8]`, as three rounds of `addp` give.
pub open spec fn tree(x: Seq<u8>, o: int) -> u8 {
    let p = |i: int| ((x[o + 2 * i] + x[o + 2 * i + 1]) % 256) as u8;
    let q0 = ((p(0) + p(1)) % 256) as u8;
    let q1 = ((p(2) + p(3)) % 256) as u8;
    ((q0 + q1) % 256) as u8
}

proof fn lemma_add_small(x: u8, y: u8)
    requires
        x + y < 256,
    ensures
        add(x, y) == (x + y) as u8,
        ((x + y) % 256) as u8 == (x + y) as u8,
{
}

/// The bits of `tree` over weighted mask bytes are the masks.
proof fn lemma_tree_bits(msk: Seq<u8>, x: Seq<u8>, o: int)
    requires
        msk.len() == 16 && x.len() == 16,
        o == 0 || o == 8,
        is_mask(msk),
        x == and8(msk, WEIGHTS@),
    ensures
        forall|m: int| 0 <= m < 8 ==> ((tree(x, o) >> (m as u8)) & 1u8 == 1u8) == (#[trigger] msk[o + m] == 0xFF),
{
    let (c0, c1, c2, c3, c4, c5, c6, c7) = (msk[o], msk[o + 1], msk[o + 2], msk[o + 3], msk[o + 4], msk[o + 5], msk[o + 6],
    msk[o + 7]);
    assert(WEIGHTS@[o] == 1 && WEIGHTS@[o + 1] == 2 && WEIGHTS@[o + 2] == 4 && WEIGHTS@[o + 3] == 8);
    assert(WEIGHTS@[o + 4] == 16 && WEIGHTS@[o + 5] == 32 && WEIGHTS@[o + 6] == 64 && WEIGHTS@[o + 7] == 128);
    let (y0, y1, y2, y3, y4, y5, y6, y7) = (c0 & 1, c1 & 2, c2 & 4, c3 & 8, c4 & 16, c5 & 32, c6 & 64, c7 & 128);
    assert(x[o] == y0 && x[o + 1] == y1 && x[o + 2] == y2 && x[o + 3] == y3);
    assert(x[o + 4] == y4 && x[o + 5] == y5 && x[o + 6] == y6 && x[o + 7] == y7);
    assert((c0 & 1) <= 1 && (c1 & 2) <= 2 && (c2 & 4) <= 4 && (c3 & 8) <= 8) by (bit_vector);
    assert((c4 & 16) <= 16 && (c5 & 32) <= 32 && (c6 & 64) <= 64 && (c7 & 128) <= 128) by (bit_vector);
    lemma_add_small(y0, y1);
    lemma_add_small(y2, y3);
    lemma_add_small(y4, y5);
    lemma_add_small(y6, y7);
    lemma_add_small(add(y0, y1), add(y2, y3));
    lemma_add_small(add(y4, y5), add(y6, y7));
    lemma_add_small(add(add(y0, y1), add(y2, y3)), add(add(y4, y5), add(y6, y7)));
    assert(tree(x, o) == add(add(add(y0, y1), add(y2, y3)), add(add(y4, y5), add(y6, y7))));
    assert(msk[o] == c0 && msk[o + 1] == c1 && msk[o + 2] == c2 && msk[o + 3] == c3);
    assert(msk[o + 4] == c4 && msk[o + 5] == c5 && msk[o + 6] == c6 && msk[o + 7] == c7);
    lemma_byte_sum(c0, c1, c2, c3, c4, c5, c6, c7);
}

/// Byte `j` of the third round is `tree` over bytes `8j..8j + 8` of the
/// four weighted vectors.
proof fn lemma_rounds(xa: Seq<u8>, xb: Seq<u8>, xc: Seq<u8>, xd: Seq<u8>, t0: Seq<u8>, t1: Seq<u8>, t2: Seq<u8>, t3: Seq<u8>, j: int)
    requires
        xa.len() == 16 && xb.len() == 16 && xc.len() == 16 && xd.len() == 16,
        t0 == padd8(xa, xb),
        t1 == padd8(xc, xd),
        t2 == padd8(t0, t1),
        t3 == padd8(t2, t2),
        0 <= j < 8,
    ensures
        t3[j] == tree(if j < 2 { xa } else if j < 4 { xb } else if j < 6 { xc } else { xd }, if j % 2 == 0 { 0 } else { 8 }),
{
    if j == 0 {
        assert(t3[0] == ((t2[0] + t2[1]) % 256) as u8);
        assert(t2[0] == ((t0[0] + t0[1]) % 256) as u8);
        assert(t0[0] == ((xa[0] + xa[1]) % 256) as u8);
        assert(t0[1] == ((xa[2] + xa[3]) % 256) as u8);
        assert(t2[1] == ((t0[2] + t0[3]) % 256) as u8);
        assert(t0[2] == ((xa[4] + xa[5]) % 256) as u8);
        assert(t0[3] == ((xa[6] + xa[7]) % 256) as u8);
        assert(t3[0] == tree(xa, 0));
    } else if j == 1 {
        assert(t3[1] == ((t2[2] + t2[3]) % 256) as u8);
        assert(t2[2] == ((t0[4] + t0[5]) % 256) as u8);
        assert(t0[4] == ((xa[8] + xa[9]) % 256) as u8);
        assert(t0[5] == ((xa[10] + xa[11]) % 256) as u8);
        assert(t2[3] == ((t0[6] + t0[7]) % 256) as u8);
        assert(t0[6] == ((xa[12] + xa[13]) % 256) as u8);
        assert(t0[7] == ((xa[14] + xa[15]) % 256) as u8);
        assert(t3[1] == tree(xa, 8));
    } else if j == 2 {
        assert(t3[2] == ((t2[4] + t2[5]) % 256) as u8);
        assert(t2[4] == ((t0[8] + t0[9]) % 256) as u8);
        assert(t0[8] == ((xb[0] + xb[1]) % 256) as u8);
        assert(t0[9] == ((xb[2] + xb[3]) % 256) as u8);
        assert(t2[5] == ((t0[10] + t0[11]) % 256) as u8);
        assert(t0[10] == ((xb[4] + xb[5]) % 256) as u8);
        assert(t0[11] == ((xb[6] + xb[7]) % 256) as u8);
        assert(t3[2] == tree(xb, 0));
    } else if j == 3 {
        assert(t3[3] == ((t2[6] + t2[7]) % 256) as u8);
        assert(t2[6] == ((t0[12] + t0[13]) % 256) as u8);
        assert(t0[12] == ((xb[8] + xb[9]) % 256) as u8);
        assert(t0[13] == ((xb[10] + xb[11]) % 256) as u8);
        assert(t2[7] == ((t0[14] + t0[15]) % 256) as u8);
        assert(t0[14] == ((xb[12] + xb[13]) % 256) as u8);
        assert(t0[15] == ((xb[14] + xb[15]) % 256) as u8);
        assert(t3[3] == tree(xb, 8));
    } else if j == 4 {
        assert(t3[4] == ((t2[8] + t2[9]) % 256) as u8);
        assert(t2[8] == ((t1[0] + t1[1]) % 256) as u8);
        assert(t1[0] == ((xc[0] + xc[1]) % 256) as u8);
        assert(t1[1] == ((xc[2] + xc[3]) % 256) as u8);
        assert(t2[9] == ((t1[2] + t1[3]) % 256) as u8);
        assert(t1[2] == ((xc[4] + xc[5]) % 256) as u8);
        assert(t1[3] == ((xc[6] + xc[7]) % 256) as u8);
        assert(t3[4] == tree(xc, 0));
    } else if j == 5 {
        assert(t3[5] == ((t2[10] + t2[11]) % 256) as u8);
        assert(t2[10] == ((t1[4] + t1[5]) % 256) as u8);
        assert(t1[4] == ((xc[8] + xc[9]) % 256) as u8);
        assert(t1[5] == ((xc[10] + xc[11]) % 256) as u8);
        assert(t2[11] == ((t1[6] + t1[7]) % 256) as u8);
        assert(t1[6] == ((xc[12] + xc[13]) % 256) as u8);
        assert(t1[7] == ((xc[14] + xc[15]) % 256) as u8);
        assert(t3[5] == tree(xc, 8));
    } else if j == 6 {
        assert(t3[6] == ((t2[12] + t2[13]) % 256) as u8);
        assert(t2[12] == ((t1[8] + t1[9]) % 256) as u8);
        assert(t1[8] == ((xd[0] + xd[1]) % 256) as u8);
        assert(t1[9] == ((xd[2] + xd[3]) % 256) as u8);
        assert(t2[13] == ((t1[10] + t1[11]) % 256) as u8);
        assert(t1[10] == ((xd[4] + xd[5]) % 256) as u8);
        assert(t1[11] == ((xd[6] + xd[7]) % 256) as u8);
        assert(t3[6] == tree(xd, 0));
    } else if j == 7 {
        assert(t3[7] == ((t2[14] + t2[15]) % 256) as u8);
        assert(t2[14] == ((t1[12] + t1[13]) % 256) as u8);
        assert(t1[12] == ((xd[8] + xd[9]) % 256) as u8);
        assert(t1[13] == ((xd[10] + xd[11]) % 256) as u8);
        assert(t2[15] == ((t1[14] + t1[15]) % 256) as u8);
        assert(t1[14] == ((xd[12] + xd[13]) % 256) as u8);
        assert(t1[15] == ((xd[14] + xd[15]) % 256) as u8);
        assert(t3[7] == tree(xd, 8));
    }
}

/// Bit `8j + m` of a little-endian u64 is bit `m` of byte `j`.
proof fn lemma_u64_bit(b: Seq<u8>, k: int)
    requires
        b.len() == 16,
        0 <= k < 64,
    ensures
        ((u64s(b)[0] >> (k as u64)) & 1u64 == 1u64) == ((b[k / 8] >> ((k % 8) as u8)) & 1u8 == 1u8),
{
    let (b0, b1, b2, b3, b4, b5, b6, b7) = (b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
    let x = le64(le32(b0, b1, b2, b3), le32(b4, b5, b6, b7));
    assert(u64s(b)[0] == x);
    let kk = k as u64;
    let m = (k % 8) as u8;
    let j = k / 8;
    assert(kk == 8 * (j as u64) + m as u64);
    if j == 0 {
        assert(kk < 8 ==> ((le64(le32(b0, b1, b2, b3), le32(b4, b5, b6, b7)) >> kk) & 1u64 == 1u64) == ((b0 >> ((kk
            % 8) as u8)) & 1u8 == 1u8)) by (bit_vector);
    } else if j == 1 {
        assert(8 <= kk < 16 ==> ((le64(le32(b0, b1, b2, b3), le32(b4, b5, b6, b7)) >> kk) & 1u64 == 1u64) == ((b1 >> ((kk
            % 8) as u8)) & 1u8 == 1u8)) by (bit_vector);
    } else if j == 2 {
        assert(16 <= kk < 24 ==> ((le64(le32(b0, b1, b2, b3), le32(b4, b5, b6, b7)) >> kk) & 1u64 == 1u64) == ((b2 >> ((
        kk % 8) as u8)) & 1u8 == 1u8)) by (bit_vector);
    } else if j == 3 {
        assert(24 <= kk < 32 ==> ((le64(le32(b0, b1, b2, b3), le32(b4, b5, b6, b7)) >> kk) & 1u64 == 1u64) == ((b3 >> ((
        kk % 8) as u8)) & 1u8 == 1u8)) by (bit_vector);
    } else if j == 4 {
        assert(32 <= kk < 40 ==> ((le64(le32(b0, b1, b2, b3), le32(b4, b5, b6, b7)) >> kk) & 1u64 == 1u64) == ((b4 >> ((
        kk % 8) as u8)) & 1u8 == 1u8)) by (bit_vector);
    } else if j == 5 {
        assert(40 <= kk < 48 ==> ((le64(le32(b0, b1, b2, b3), le32(b4, b5, b6, b7)) >> kk) & 1u64 == 1u64) == ((b5 >> ((
        kk % 8) as u8)) & 1u8 == 1u8)) by (bit_vector);
    } else if j == 6 {
        assert(48 <= kk < 56 ==> ((le64(le32(b0, b1, b2, b3), le32(b4, b5, b6, b7)) >> kk) & 1u64 == 1u64) == ((b6 >> ((
        kk % 8) as u8)) & 1u8 == 1u8)) by (bit_vector);
    } else {
        assert(56 <= kk < 64 ==> ((le64(le32(b0, b1, b2, b3), le32(b4, b5, b6, b7)) >> kk) & 1u64 == 1u64) == ((b7 >> ((
        kk % 8) as u8)) & 1u8 == 1u8)) by (bit_vector);
    }
}

/// Bit `k` of the result, from the four inputs through the rounds.
proof fn lemma_bit(
    a: Seq<u8>, b: Seq<u8>, c: Seq<u8>, d: Seq<u8>,
    xa: Seq<u8>, xb: Seq<u8>, xc: Seq<u8>, xd: Seq<u8>,
    t0: Seq<u8>, t1: Seq<u8>, t2: Seq<u8>, t3: Seq<u8>, k: int,
)
    requires
        a.len() == 16 && b.len() == 16 && c.len() == 16 && d.len() == 16,
        is_mask(a) && is_mask(b) && is_mask(c) && is_mask(d),
        xa == and8(a, WEIGHTS@), xb == and8(b, WEIGHTS@), xc == and8(c, WEIGHTS@), xd == and8(d, WEIGHTS@),
        t0 == padd8(xa, xb),
        t1 == padd8(xc, xd),
        t2 == padd8(t0, t1),
        t3 == padd8(t2, t2),
        0 <= k < 64,
    ensures
        ((u64s(t3)[0] >> (k as u64)) & 1u64 == 1u64) == (byte4(a, b, c, d, k) == 0xFF),
{
    assert(t3.len() == 16);
    lemma_u64_bit(t3, k);
    if k < 8 {
        assert(k / 8 == 0 && k % 8 == k - 0);
        lemma_rounds(xa, xb, xc, xd, t0, t1, t2, t3, 0);
        lemma_tree_bits(a, xa, 0);
        assert(a[0 + (k - 0)] == byte4(a, b, c, d, k));
    } else if k < 16 {
        assert(k / 8 == 1 && k % 8 == k - 8);
        lemma_rounds(xa, xb, xc, xd, t0, t1, t2, t3, 1);
        lemma_tree_bits(a, xa, 8);
        assert(a[8 + (k - 8)] == byte4(a, b, c, d, k));
    } else if k < 24 {
        assert(k / 8 == 2 && k % 8 == k - 16);
        lemma_rounds(xa, xb, xc, xd, t0, t1, t2, t3, 2);
        lemma_tree_bits(b, xb, 0);
        assert(b[0 + (k - 16)] == byte4(a, b, c, d, k));
    } else if k < 32 {
        assert(k / 8 == 3 && k % 8 == k - 24);
        lemma_rounds(xa, xb, xc, xd, t0, t1, t2, t3, 3);
        lemma_tree_bits(b, xb, 8);
        assert(b[8 + (k - 24)] == byte4(a, b, c, d, k));
    } else if k < 40 {
        assert(k / 8 == 4 && k % 8 == k - 32);
        lemma_rounds(xa, xb, xc, xd, t0, t1, t2, t3, 4);
        lemma_tree_bits(c, xc, 0);
        assert(c[0 + (k - 32)] == byte4(a, b, c, d, k));
    } else if k < 48 {
        assert(k / 8 == 5 && k % 8 == k - 40);
        lemma_rounds(xa, xb, xc, xd, t0, t1, t2, t3, 5);
        lemma_tree_bits(c, xc, 8);
        assert(c[8 + (k - 40)] == byte4(a, b, c, d, k));
    } else if k < 56 {
        assert(k / 8 == 6 && k % 8 == k - 48);
        lemma_rounds(xa, xb, xc, xd, t0, t1, t2, t3, 6);
        lemma_tree_bits(d, xd, 0);
        assert(d[0 + (k - 48)] == byte4(a, b, c, d, k));
    } else if k < 64 {
        assert(k / 8 == 7 && k % 8 == k - 56);
        lemma_rounds(xa, xb, xc, xd, t0, t1, t2, t3, 7);
        lemma_tree_bits(d, xd, 8);
        assert(d[8 + (k - 56)] == byte4(a, b, c, d, k));
    }
}

/// One bit per byte of `a ++ b ++ c ++ d`, whose bytes are 0x00 or 0xFF:
/// bit `k` is set exactly when byte `k` is 0xFF.
#[inline(always)]
pub fn movemask64(a: uint8x16_t, b: uint8x16_t, c: uint8x16_t, d: uint8x16_t) -> (r: u64)
    requires
        neon(),
        is_mask(n8(a)),
        is_mask(n8(b)),
        is_mask(n8(c)),
        is_mask(n8(d)),
    ensures
        forall|k: int| 0 <= k < 64 ==> ((r >> (k as u64)) & 1u64 == 1u64) == (#[trigger] byte4(n8(a), n8(b), n8(c), n8(d), k) == 0xFF),
{
    let w = vld1q_u8_at(WEIGHTS.as_slice(), 0);
    let xa = vandq_u8(a, w);
    let xb = vandq_u8(b, w);
    let xc = vandq_u8(c, w);
    let xd = vandq_u8(d, w);
    let t0 = vpaddq_u8(xa, xb);
    let t1 = vpaddq_u8(xc, xd);
    let t2 = vpaddq_u8(t0, t1);
    let t3 = vpaddq_u8(t2, t2);
    let r = vgetq_lane_u64_0(t3);
    proof {
        assert(n8(w) =~= WEIGHTS@);
        assert forall|k: int| 0 <= k < 64 implies ((r >> (k as u64)) & 1u64 == 1u64) == (#[trigger] byte4(
            n8(a),
            n8(b),
            n8(c),
            n8(d),
            k,
        ) == 0xFF) by {
            lemma_bit(n8(a), n8(b), n8(c), n8(d), n8(xa), n8(xb), n8(xc), n8(xd), n8(t0), n8(t1), n8(t2), n8(t3), k);
        }
    }
    r
}

/// One bit per byte of `a`, whose bytes are 0x00 or 0xFF: bit `k` is set
/// exactly when byte `k` is 0xFF.
#[inline(always)]
pub fn movemask16(a: uint8x16_t) -> (r: u32)
    requires
        neon(),
        is_mask(n8(a)),
    ensures
        r < 0x10000,
        forall|k: u32| k < 16 ==> ((r >> k) & 1u32 == 1u32) == (#[trigger] n8(a)[k as int] == 0xFF),
{
    // The same vector four times: the pairwise adds then reduce to three
    // (every half of each step is the same), with no zero vector.
    let m = movemask64(a, a, a, a);
    let r = (m & 0xFFFF) as u32;
    proof {
        assert(r < 0x10000) by (bit_vector)
            requires r == (m & 0xFFFFu64) as u32;
        assert forall|k: u32| k < 16 implies ((r >> k) & 1u32 == 1u32) == (#[trigger] n8(a)[k as int] == 0xFF) by {
            assert(((m >> ((k as int) as u64)) & 1u64 == 1u64) == (byte4(n8(a), n8(a), n8(a), n8(a), k as int) == 0xFF));
            assert(k < 16 && r == (m & 0xFFFFu64) as u32 ==> (((r >> k) & 1u32 == 1u32) == ((m >> (k as u64)) & 1u64
                == 1u64))) by (bit_vector);
        }
    }
    r
}

/// One nibble per byte of `a`, whose bytes are 0x00 or 0xFF: nibble `k`
/// (bits `4k` to `4k + 3`) is all ones when byte `k` is 0xFF and all zeros
/// otherwise. Two instructions, where `movemask16` takes five.
#[inline(always)]
pub fn nibmask16(a: uint8x16_t) -> (r: u64)
    requires
        neon(),
        is_mask(n8(a)),
    ensures
        forall|k: u64| k < 16 ==> #[trigger] ((r >> (4 * k)) & 15) == if n8(a)[k as int] == 0xFF { 15u64 } else { 0u64 },
{
    let r = vshrn4_u64(a);
    proof {
        assert forall|k: u64| k < 16 implies #[trigger] ((r >> (4 * k)) & 15) == if n8(a)[k as int] == 0xFF { 15u64 } else { 0u64 } by {
            let x = n8(a)[k as int];
            assert(x == 0 || x == 0xFF);
            assert(x == 0xFF ==> (x >> 4u8) as u64 == 15 && (x & 15u8) as u64 == 15) by (bit_vector);
            assert(x == 0 ==> (x >> 4u8) as u64 == 0 && (x & 15u8) as u64 == 0) by (bit_vector);
        }
    }
    r
}

/// Bit `j` of a `nibmask16` result is set exactly when byte `j / 4` is
/// 0xFF.
pub proof fn lemma_nibmask_bit(r: u64, a: Seq<u8>, j: u64)
    requires
        j < 64,
        a.len() == 16,
        forall|k: u64| k < 16 ==> #[trigger] ((r >> (4 * k)) & 15) == if a[k as int] == 0xFF { 15u64 } else { 0u64 },
    ensures
        ((r >> j) & 1 == 1) == (a[(j / 4) as int] == 0xFF),
{
    let k = j / 4;
    let d: u64 = (j % 4) as u64;
    let s: u64 = (4 * k) as u64;
    let q: u64 = (r >> s) & 15;
    assert(q == if a[k as int] == 0xFF { 15u64 } else { 0u64 });
    assert(j < 64 && s == 4 * (j / 4) && d == j % 4 ==> (((r >> j) & 1) == ((((r >> s) & 15) >> d) & 1))) by (bit_vector);
    assert(d < 4 ==> ((15u64 >> d) & 1 == 1) && ((0u64 >> d) & 1 == 0)) by (bit_vector);
}

} // verus!

//! Lemmas for moving between the byte and 32-bit lane views of vsimd's
//! vectors, and for the lane shifts the kernels use.
use verilith_simd::lanes::*;
use verilith_simd::ops::*;
use vstd::prelude::*;

verus! {

broadcast use verilith_simd::lanes::group_lanes;

pub proof fn lemma_le32_and(a0: u8, a1: u8, a2: u8, a3: u8, b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        le32(a0 & b0, a1 & b1, a2 & b2, a3 & b3) == le32(a0, a1, a2, a3) & le32(b0, b1, b2, b3),
{
    assert((((a0 & b0) as u32) | (((a1 & b1) as u32) << 8u32) | (((a2 & b2) as u32) << 16u32) | (((a3 & b3) as u32)
        << 24u32)) == (((a0 as u32) | ((a1 as u32) << 8u32) | ((a2 as u32) << 16u32) | ((a3 as u32) << 24u32)) & ((
    b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)))) by (bit_vector);
}

pub proof fn lemma_le32_or(a0: u8, a1: u8, a2: u8, a3: u8, b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        le32(a0 | b0, a1 | b1, a2 | b2, a3 | b3) == le32(a0, a1, a2, a3) | le32(b0, b1, b2, b3),
{
    assert((((a0 | b0) as u32) | (((a1 | b1) as u32) << 8u32) | (((a2 | b2) as u32) << 16u32) | (((a3 | b3) as u32)
        << 24u32)) == (((a0 as u32) | ((a1 as u32) << 8u32) | ((a2 as u32) << 16u32) | ((a3 as u32) << 24u32)) | ((
    b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)))) by (bit_vector);
}

/// `and8` is `&` on 32-bit lanes.
pub proof fn lemma_and8_u32s(x: Seq<u8>, y: Seq<u8>)
    requires
        x.len() == y.len(),
        x.len() % 4 == 0,
    ensures
        u32s(and8(x, y)).len() == u32s(x).len(),
        forall|i: int| 0 <= i < u32s(x).len() ==> #[trigger] u32s(and8(x, y))[i] == u32s(x)[i] & u32s(y)[i],
{
    assert forall|i: int| 0 <= i < u32s(x).len() implies #[trigger] u32s(and8(x, y))[i] == u32s(x)[i] & u32s(y)[i] by {
        lemma_le32_and(x[4 * i], x[4 * i + 1], x[4 * i + 2], x[4 * i + 3], y[4 * i], y[4 * i + 1], y[4 * i + 2], y[4 * i + 3]);
    }
}

/// `or8` is `|` on 32-bit lanes.
pub proof fn lemma_or8_u32s(x: Seq<u8>, y: Seq<u8>)
    requires
        x.len() == y.len(),
        x.len() % 4 == 0,
    ensures
        u32s(or8(x, y)).len() == u32s(x).len(),
        forall|i: int| 0 <= i < u32s(x).len() ==> #[trigger] u32s(or8(x, y))[i] == u32s(x)[i] | u32s(y)[i],
{
    assert forall|i: int| 0 <= i < u32s(x).len() implies #[trigger] u32s(or8(x, y))[i] == u32s(x)[i] | u32s(y)[i] by {
        lemma_le32_or(x[4 * i], x[4 * i + 1], x[4 * i + 2], x[4 * i + 3], y[4 * i], y[4 * i + 1], y[4 * i + 2], y[4 * i + 3]);
    }
}

/// Byte `j` of a vector is byte `j % 4` of 32-bit lane `j / 4`.
pub proof fn lemma_byte_of_lane(b: Seq<u8>, j: int)
    requires
        b.len() % 4 == 0,
        0 <= j < b.len(),
    ensures
        b[j] == byte32(u32s(b)[j / 4], j % 4),
{
    lemma_u32s_bytes(b);
    assert(j == 4 * (j / 4) + j % 4);
}

pub proof fn lemma_pow2_spec()
    ensures
        pow2_spec(4) == 16,
        pow2_spec(6) == 64,
        pow2_spec(8) == 256,
        pow2_spec(10) == 1024,
{
    assert(pow2_spec(4) == 16) by (compute_only);
    assert(pow2_spec(6) == 64) by (compute_only);
    assert(pow2_spec(8) == 256) by (compute_only);
    assert(pow2_spec(10) == 1024) by (compute_only);
}

/// A lane of `srli32` by 6 or 10 is `>>`.
pub proof fn lemma_srli32_lane(x: u32, n: int)
    requires
        n == 6 || n == 10,
    ensures
        (x as nat / pow2_spec(n as nat)) as u32 == if n == 6 { x >> 6u32 } else { x >> 10u32 },
{
    lemma_pow2_spec();
    assert(x >> 6u32 == x / 64) by (bit_vector);
    assert(x >> 10u32 == x / 1024) by (bit_vector);
}

/// A lane of `slli32` by 4 or 8 is `<<`, when nothing is shifted out.
pub proof fn lemma_slli32_lane(x: u32, n: int)
    requires
        n == 4 && x <= 0x3f0 || n == 8 && x <= 0x3f0000,
    ensures
        ((x as nat * pow2_spec(n as nat)) % 0x1_0000_0000) as u32 == if n == 4 { x << 4u32 } else { x << 8u32 },
{
    lemma_pow2_spec();
    if n == 4 {
        assert(x <= 0x3f0 ==> x << 4u32 == x * 16) by (bit_vector);
        assert(x * 16 < 0x1_0000_0000);
    } else {
        assert(x <= 0x3f0000 ==> x << 8u32 == x * 256) by (bit_vector);
        assert(x * 256 < 0x1_0000_0000);
    }
}

/// `movemask` is below `2^len`, and reaches `2^len - 1` exactly when
/// every byte has its top bit set.
pub proof fn lemma_movemask_full(b: Seq<u8>)
    ensures
        movemask(b) < pow2_spec(b.len()),
        (movemask(b) == pow2_spec(b.len()) - 1) <==> forall|k: int| 0 <= k < b.len() ==> #[trigger] b[k] >= 128,
    decreases b.len(),
{
    if b.len() > 0 {
        let r = b.drop_first();
        lemma_movemask_full(r);
        assert(pow2_spec(b.len()) == 2 * pow2_spec(r.len()));
        if forall|k: int| 0 <= k < b.len() ==> #[trigger] b[k] >= 128 {
            assert forall|k: int| 0 <= k < r.len() implies #[trigger] r[k] >= 128 by {
                assert(r[k] == b[k + 1]);
            }
        }
        if movemask(b) == pow2_spec(b.len()) - 1 {
            assert(b[0] >= 128);
            assert(movemask(r) == pow2_spec(r.len()) - 1);
            assert forall|k: int| 0 <= k < b.len() implies #[trigger] b[k] >= 128 by {
                if k > 0 {
                    assert(r[k - 1] == b[k]);
                }
            }
        }
    }
}

/// The movemask of a byte compare against zero is all ones (as an `i32`,
/// -1) exactly when every byte is zero.
pub proof fn lemma_all_zero(e: Seq<u8>, z: Seq<u8>, c: Seq<u8>, r: i32)
    requires
        e.len() == 32,
        z == splat8(0u8, 32),
        c == cmpeq8(e, z),
        u32_of_i32(r) as nat == movemask(c),
    ensures
        (r == -1) <==> forall|k: int| 0 <= k < 32 ==> #[trigger] e[k] == 0,
{
    lemma_movemask_full(c);
    assert(pow2_spec(32) == 0x1_0000_0000) by (compute_only);
    assert(c.len() == 32);
    if forall|k: int| 0 <= k < 32 ==> #[trigger] e[k] == 0 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] c[k] >= 128 by {
            assert(e[k] == 0);
        }
    }
    if r == -1 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] e[k] == 0 by {
            assert(c[k] >= 128);
        }
    }
}

/// Bytes of `srli32(.., 4)` masked with 0x0f are the high nibbles.
pub proof fn lemma_hi_nibbles(ib: Seq<u8>, sh: Seq<u8>, k: Seq<u8>, hb: Seq<u8>)
    requires
        ib.len() == 32 && sh.len() == 32 && k.len() == 32,
        u32s(sh) == srli32(u32s(ib), 4),
        k == splat8(0x0f, 32),
        hb == and8(sh, k),
    ensures
        hb.len() == 32,
        forall|i: int| 0 <= i < 32 ==> #[trigger] hb[i] == ib[i] >> 4,
{
    lemma_pow2_spec();
    assert forall|j: int| 0 <= j < 32 implies #[trigger] hb[j] == ib[j] >> 4 by {
        let g = j / 4;
        let t = j % 4;
        assert(j == 4 * g + t);
        lemma_byte_of_lane(sh, j);
        let (b0, b1, b2, b3) = (ib[4 * g], ib[4 * g + 1], ib[4 * g + 2], ib[4 * g + 3]);
        let w = le32(b0, b1, b2, b3);
        assert(u32s(ib)[g] == w);
        assert(u32s(sh)[g] == (w as nat / 16) as u32);
        assert(w >> 4u32 == w / 16) by (bit_vector);
        assert(byte32(w >> 4u32, 0) & 0x0f == b0 >> 4 && byte32(w >> 4u32, 1) & 0x0f == b1 >> 4 && byte32(w >> 4u32, 2) & 0x0f == b2 >> 4
            && byte32(w >> 4u32, 3) & 0x0f == b3 >> 4) by {
            assert(((((((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) >> 4u32) & 0xff) as u8) & 0x0f) == b0 >> 4) by (bit_vector);
            assert((((((((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) >> 4u32) >> 8u32) & 0xff) as u8) & 0x0f) == b1 >> 4) by (bit_vector);
            assert((((((((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) >> 4u32) >> 16u32) & 0xff) as u8) & 0x0f) == b2 >> 4) by (bit_vector);
            assert((((((((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) >> 4u32) >> 24u32) & 0xff) as u8) & 0x0f) == b3 >> 4) by (bit_vector);
        }
    }
}

} // verus!

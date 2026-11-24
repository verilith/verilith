//! Lemmas about the lane views of verilith-simd's vectors that the AVX2
//! message schedules (`crate::avx2`) need: bitwise operations and shifts on
//! 32- and 64-bit lanes, the byte moves (`alignr`, the byte swap of
//! `shuffle_epi8`) as moves of whole lanes, and lanes of concatenated and
//! split vectors.
use verilith_simd::lanes::*;
use verilith_simd::ops::*;
use vstd::prelude::*;

verus! {

broadcast use verilith_simd::lanes::group_lanes;

// ---------------------------------------------------------------------------
// Bitwise operations on bytes are bitwise operations on lanes
// ---------------------------------------------------------------------------

proof fn lemma_le32_xor(a0: u8, a1: u8, a2: u8, a3: u8, b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        le32((a0 ^ b0), (a1 ^ b1), (a2 ^ b2), (a3 ^ b3)) == le32(a0, a1, a2, a3) ^ le32(b0, b1, b2, b3),
{
    assert((((a0 ^ b0) as u32) | (((a1 ^ b1) as u32) << 8u32) | (((a2 ^ b2) as u32) << 16u32) | (((a3 ^ b3) as u32) << 24u32)) == (((a0 as u32) | ((a1 as u32) << 8u32) | ((a2 as u32) << 16u32) | ((a3 as u32) << 24u32)) ^ ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)))) by (bit_vector);
}

proof fn lemma_le32_or(a0: u8, a1: u8, a2: u8, a3: u8, b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        le32((a0 | b0), (a1 | b1), (a2 | b2), (a3 | b3)) == le32(a0, a1, a2, a3) | le32(b0, b1, b2, b3),
{
    assert((((a0 | b0) as u32) | (((a1 | b1) as u32) << 8u32) | (((a2 | b2) as u32) << 16u32) | (((a3 | b3) as u32) << 24u32)) == (((a0 as u32) | ((a1 as u32) << 8u32) | ((a2 as u32) << 16u32) | ((a3 as u32) << 24u32)) | ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)))) by (bit_vector);
}

proof fn lemma_le32_and(a0: u8, a1: u8, a2: u8, a3: u8, b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        le32((a0 & b0), (a1 & b1), (a2 & b2), (a3 & b3)) == le32(a0, a1, a2, a3) & le32(b0, b1, b2, b3),
{
    assert((((a0 & b0) as u32) | (((a1 & b1) as u32) << 8u32) | (((a2 & b2) as u32) << 16u32) | (((a3 & b3) as u32) << 24u32)) == (((a0 as u32) | ((a1 as u32) << 8u32) | ((a2 as u32) << 16u32) | ((a3 as u32) << 24u32)) & ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)))) by (bit_vector);
}

proof fn lemma_le32_andnot(a0: u8, a1: u8, a2: u8, a3: u8, b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        le32((!a0 & b0), (!a1 & b1), (!a2 & b2), (!a3 & b3)) == !le32(a0, a1, a2, a3) & le32(b0, b1, b2, b3),
{
    assert((((!a0 & b0) as u32) | (((!a1 & b1) as u32) << 8u32) | (((!a2 & b2) as u32) << 16u32) | (((!a3 & b3) as u32) << 24u32)) == (!((a0 as u32) | ((a1 as u32) << 8u32) | ((a2 as u32) << 16u32) | ((a3 as u32) << 24u32)) & ((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)))) by (bit_vector);
}

proof fn lemma_le64_xor(x0: u32, x1: u32, y0: u32, y1: u32)
    ensures
        le64(x0 ^ y0, x1 ^ y1) == le64(x0, x1) ^ le64(y0, y1),
{
    assert((((x0 ^ y0) as u64) | (((x1 ^ y1) as u64) << 32u64)) == (((x0 as u64) | ((x1 as u64) << 32u64)) ^ ((y0 as u64) | ((y1 as u64) << 32u64)))) by (bit_vector);
}

proof fn lemma_le64_or(x0: u32, x1: u32, y0: u32, y1: u32)
    ensures
        le64(x0 | y0, x1 | y1) == le64(x0, x1) | le64(y0, y1),
{
    assert((((x0 | y0) as u64) | (((x1 | y1) as u64) << 32u64)) == (((x0 as u64) | ((x1 as u64) << 32u64)) | ((y0 as u64) | ((y1 as u64) << 32u64)))) by (bit_vector);
}

/// `xor8`, `or8`, `and8` and `andnot8` are the same operations on 32-bit lanes.
pub proof fn lemma_bitw_u32s(x: Seq<u8>, y: Seq<u8>)
    requires
        x.len() == y.len(),
        x.len() % 4 == 0,
    ensures
        u32s(xor8(x, y)).len() == u32s(x).len(),
        u32s(or8(x, y)).len() == u32s(x).len(),
        u32s(and8(x, y)).len() == u32s(x).len(),
        u32s(andnot8(x, y)).len() == u32s(x).len(),
        forall|i: int| 0 <= i < u32s(x).len() ==> #[trigger] u32s(xor8(x, y))[i] == u32s(x)[i] ^ u32s(y)[i],
        forall|i: int| 0 <= i < u32s(x).len() ==> #[trigger] u32s(or8(x, y))[i] == u32s(x)[i] | u32s(y)[i],
        forall|i: int| 0 <= i < u32s(x).len() ==> #[trigger] u32s(and8(x, y))[i] == u32s(x)[i] & u32s(y)[i],
        forall|i: int| 0 <= i < u32s(x).len() ==> #[trigger] u32s(andnot8(x, y))[i] == !u32s(x)[i] & u32s(y)[i],
{
    assert forall|i: int| 0 <= i < u32s(x).len() implies #[trigger] u32s(xor8(x, y))[i] == u32s(x)[i] ^ u32s(y)[i] by {
        let (k0, k1, k2, k3) = (4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3);
        lemma_le32_xor(x[k0], x[k1], x[k2], x[k3], y[k0], y[k1], y[k2], y[k3]);
    }
    assert forall|i: int| 0 <= i < u32s(x).len() implies #[trigger] u32s(or8(x, y))[i] == u32s(x)[i] | u32s(y)[i] by {
        let (k0, k1, k2, k3) = (4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3);
        lemma_le32_or(x[k0], x[k1], x[k2], x[k3], y[k0], y[k1], y[k2], y[k3]);
    }
    assert forall|i: int| 0 <= i < u32s(x).len() implies #[trigger] u32s(and8(x, y))[i] == u32s(x)[i] & u32s(y)[i] by {
        let (k0, k1, k2, k3) = (4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3);
        lemma_le32_and(x[k0], x[k1], x[k2], x[k3], y[k0], y[k1], y[k2], y[k3]);
    }
    assert forall|i: int| 0 <= i < u32s(x).len() implies #[trigger] u32s(andnot8(x, y))[i] == !u32s(x)[i] & u32s(y)[i] by {
        let (k0, k1, k2, k3) = (4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3);
        lemma_le32_andnot(x[k0], x[k1], x[k2], x[k3], y[k0], y[k1], y[k2], y[k3]);
    }
}

/// `xor8` and `or8` are the same operations on 64-bit lanes.
pub proof fn lemma_bitw_u64s(x: Seq<u8>, y: Seq<u8>)
    requires
        x.len() == y.len(),
        x.len() % 8 == 0,
    ensures
        u64s(xor8(x, y)).len() == u64s(x).len(),
        u64s(or8(x, y)).len() == u64s(x).len(),
        forall|i: int| 0 <= i < u64s(x).len() ==> #[trigger] u64s(xor8(x, y))[i] == u64s(x)[i] ^ u64s(y)[i],
        forall|i: int| 0 <= i < u64s(x).len() ==> #[trigger] u64s(or8(x, y))[i] == u64s(x)[i] | u64s(y)[i],
{
    lemma_bitw_u32s(x, y);
    assert forall|i: int| 0 <= i < u64s(x).len() implies #[trigger] u64s(xor8(x, y))[i] == u64s(x)[i] ^ u64s(y)[i] by {
        assert(u32s(xor8(x, y))[2 * i] == u32s(x)[2 * i] ^ u32s(y)[2 * i]);
        assert(u32s(xor8(x, y))[2 * i + 1] == u32s(x)[2 * i + 1] ^ u32s(y)[2 * i + 1]);
        lemma_le64_xor(u32s(x)[2 * i], u32s(x)[2 * i + 1], u32s(y)[2 * i], u32s(y)[2 * i + 1]);
    }
    assert forall|i: int| 0 <= i < u64s(x).len() implies #[trigger] u64s(or8(x, y))[i] == u64s(x)[i] | u64s(y)[i] by {
        assert(u32s(or8(x, y))[2 * i] == u32s(x)[2 * i] | u32s(y)[2 * i]);
        assert(u32s(or8(x, y))[2 * i + 1] == u32s(x)[2 * i + 1] | u32s(y)[2 * i + 1]);
        lemma_le64_or(u32s(x)[2 * i], u32s(x)[2 * i + 1], u32s(y)[2 * i], u32s(y)[2 * i + 1]);
    }
}

// ---------------------------------------------------------------------------
// Shifts by a constant
// ---------------------------------------------------------------------------

pub proof fn lemma_shr64_1(x: u64)
    ensures
        (x as nat / pow2_spec(1)) as u64 == x >> 1u64,
{
    assert(pow2_spec(1) == 2) by (compute_only);
    assert(x / 2u64 == x >> 1u64) by (bit_vector);
}

pub proof fn lemma_shr64_6(x: u64)
    ensures
        (x as nat / pow2_spec(6)) as u64 == x >> 6u64,
{
    assert(pow2_spec(6) == 64) by (compute_only);
    assert(x / 64u64 == x >> 6u64) by (bit_vector);
}

pub proof fn lemma_shr64_7(x: u64)
    ensures
        (x as nat / pow2_spec(7)) as u64 == x >> 7u64,
{
    assert(pow2_spec(7) == 128) by (compute_only);
    assert(x / 128u64 == x >> 7u64) by (bit_vector);
}

pub proof fn lemma_shr64_8(x: u64)
    ensures
        (x as nat / pow2_spec(8)) as u64 == x >> 8u64,
{
    assert(pow2_spec(8) == 256) by (compute_only);
    assert(x / 256u64 == x >> 8u64) by (bit_vector);
}

pub proof fn lemma_shr64_19(x: u64)
    ensures
        (x as nat / pow2_spec(19)) as u64 == x >> 19u64,
{
    assert(pow2_spec(19) == 524288) by (compute_only);
    assert(x / 524288u64 == x >> 19u64) by (bit_vector);
}

pub proof fn lemma_shr64_61(x: u64)
    ensures
        (x as nat / pow2_spec(61)) as u64 == x >> 61u64,
{
    assert(pow2_spec(61) == 2305843009213693952) by (compute_only);
    assert(x / 2305843009213693952u64 == x >> 61u64) by (bit_vector);
}

pub proof fn lemma_shl64_63(x: u64)
    ensures
        ((x as nat * pow2_spec(63)) % 0x10000000000000000) as u64 == x << 63u64,
{
    assert(pow2_spec(63) == 0x8000000000000000) by (compute_only);
    assert(x << 63u64 == ((x % 0x2u64) * 0x8000000000000000u64) as u64) by (bit_vector);
    let q = x as int / 0x2;
    let r = x as int % 0x2;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 0x2);
    assert(x as int * 0x8000000000000000 == q * 0x10000000000000000 + r * 0x8000000000000000) by (nonlinear_arith)
        requires
            x as int == 0x2 * q + r,
    ;
    assert(r * 0x8000000000000000 < 0x10000000000000000) by (nonlinear_arith)
        requires
            0 <= r < 0x2,
    ;
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, r * 0x8000000000000000, 0x10000000000000000);
    vstd::arithmetic::div_mod::lemma_small_mod((r * 0x8000000000000000) as nat, 0x10000000000000000);
}

pub proof fn lemma_shl64_56(x: u64)
    ensures
        ((x as nat * pow2_spec(56)) % 0x10000000000000000) as u64 == x << 56u64,
{
    assert(pow2_spec(56) == 0x100000000000000) by (compute_only);
    assert(x << 56u64 == ((x % 0x100u64) * 0x100000000000000u64) as u64) by (bit_vector);
    let q = x as int / 0x100;
    let r = x as int % 0x100;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 0x100);
    assert(x as int * 0x100000000000000 == q * 0x10000000000000000 + r * 0x100000000000000) by (nonlinear_arith)
        requires
            x as int == 0x100 * q + r,
    ;
    assert(r * 0x100000000000000 < 0x10000000000000000) by (nonlinear_arith)
        requires
            0 <= r < 0x100,
    ;
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, r * 0x100000000000000, 0x10000000000000000);
    vstd::arithmetic::div_mod::lemma_small_mod((r * 0x100000000000000) as nat, 0x10000000000000000);
}

pub proof fn lemma_shl64_45(x: u64)
    ensures
        ((x as nat * pow2_spec(45)) % 0x10000000000000000) as u64 == x << 45u64,
{
    assert(pow2_spec(45) == 0x200000000000) by (compute_only);
    assert(x << 45u64 == ((x % 0x80000u64) * 0x200000000000u64) as u64) by (bit_vector);
    let q = x as int / 0x80000;
    let r = x as int % 0x80000;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 0x80000);
    assert(x as int * 0x200000000000 == q * 0x10000000000000000 + r * 0x200000000000) by (nonlinear_arith)
        requires
            x as int == 0x80000 * q + r,
    ;
    assert(r * 0x200000000000 < 0x10000000000000000) by (nonlinear_arith)
        requires
            0 <= r < 0x80000,
    ;
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, r * 0x200000000000, 0x10000000000000000);
    vstd::arithmetic::div_mod::lemma_small_mod((r * 0x200000000000) as nat, 0x10000000000000000);
}

pub proof fn lemma_shl64_3(x: u64)
    ensures
        ((x as nat * pow2_spec(3)) % 0x10000000000000000) as u64 == x << 3u64,
{
    assert(pow2_spec(3) == 0x8) by (compute_only);
    assert(x << 3u64 == ((x % 0x2000000000000000u64) * 0x8u64) as u64) by (bit_vector);
    let q = x as int / 0x2000000000000000;
    let r = x as int % 0x2000000000000000;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 0x2000000000000000);
    assert(x as int * 0x8 == q * 0x10000000000000000 + r * 0x8) by (nonlinear_arith)
        requires
            x as int == 0x2000000000000000 * q + r,
    ;
    assert(r * 0x8 < 0x10000000000000000) by (nonlinear_arith)
        requires
            0 <= r < 0x2000000000000000,
    ;
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, r * 0x8, 0x10000000000000000);
    vstd::arithmetic::div_mod::lemma_small_mod((r * 0x8) as nat, 0x10000000000000000);
}

pub proof fn lemma_shr32_3(x: u32)
    ensures
        (x as nat / pow2_spec(3)) as u32 == x >> 3u32,
{
    assert(pow2_spec(3) == 8) by (compute_only);
    assert(x / 8u32 == x >> 3u32) by (bit_vector);
}

pub proof fn lemma_shr32_7(x: u32)
    ensures
        (x as nat / pow2_spec(7)) as u32 == x >> 7u32,
{
    assert(pow2_spec(7) == 128) by (compute_only);
    assert(x / 128u32 == x >> 7u32) by (bit_vector);
}

pub proof fn lemma_shr32_10(x: u32)
    ensures
        (x as nat / pow2_spec(10)) as u32 == x >> 10u32,
{
    assert(pow2_spec(10) == 1024) by (compute_only);
    assert(x / 1024u32 == x >> 10u32) by (bit_vector);
}

pub proof fn lemma_shr32_17(x: u32)
    ensures
        (x as nat / pow2_spec(17)) as u32 == x >> 17u32,
{
    assert(pow2_spec(17) == 131072) by (compute_only);
    assert(x / 131072u32 == x >> 17u32) by (bit_vector);
}

pub proof fn lemma_shr32_18(x: u32)
    ensures
        (x as nat / pow2_spec(18)) as u32 == x >> 18u32,
{
    assert(pow2_spec(18) == 262144) by (compute_only);
    assert(x / 262144u32 == x >> 18u32) by (bit_vector);
}

pub proof fn lemma_shr32_19(x: u32)
    ensures
        (x as nat / pow2_spec(19)) as u32 == x >> 19u32,
{
    assert(pow2_spec(19) == 524288) by (compute_only);
    assert(x / 524288u32 == x >> 19u32) by (bit_vector);
}

pub proof fn lemma_shl32_25(x: u32)
    ensures
        ((x as nat * pow2_spec(25)) % 0x100000000) as u32 == x << 25u32,
{
    assert(pow2_spec(25) == 0x2000000) by (compute_only);
    assert(x << 25u32 == ((x % 0x80u32) * 0x2000000u32) as u32) by (bit_vector);
    let q = x as int / 0x80;
    let r = x as int % 0x80;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 0x80);
    assert(x as int * 0x2000000 == q * 0x100000000 + r * 0x2000000) by (nonlinear_arith)
        requires
            x as int == 0x80 * q + r,
    ;
    assert(r * 0x2000000 < 0x100000000) by (nonlinear_arith)
        requires
            0 <= r < 0x80,
    ;
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, r * 0x2000000, 0x100000000);
    vstd::arithmetic::div_mod::lemma_small_mod((r * 0x2000000) as nat, 0x100000000);
}

pub proof fn lemma_shl32_14(x: u32)
    ensures
        ((x as nat * pow2_spec(14)) % 0x100000000) as u32 == x << 14u32,
{
    assert(pow2_spec(14) == 0x4000) by (compute_only);
    assert(x << 14u32 == ((x % 0x40000u32) * 0x4000u32) as u32) by (bit_vector);
    let q = x as int / 0x40000;
    let r = x as int % 0x40000;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 0x40000);
    assert(x as int * 0x4000 == q * 0x100000000 + r * 0x4000) by (nonlinear_arith)
        requires
            x as int == 0x40000 * q + r,
    ;
    assert(r * 0x4000 < 0x100000000) by (nonlinear_arith)
        requires
            0 <= r < 0x40000,
    ;
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, r * 0x4000, 0x100000000);
    vstd::arithmetic::div_mod::lemma_small_mod((r * 0x4000) as nat, 0x100000000);
}

pub proof fn lemma_shl32_15(x: u32)
    ensures
        ((x as nat * pow2_spec(15)) % 0x100000000) as u32 == x << 15u32,
{
    assert(pow2_spec(15) == 0x8000) by (compute_only);
    assert(x << 15u32 == ((x % 0x20000u32) * 0x8000u32) as u32) by (bit_vector);
    let q = x as int / 0x20000;
    let r = x as int % 0x20000;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 0x20000);
    assert(x as int * 0x8000 == q * 0x100000000 + r * 0x8000) by (nonlinear_arith)
        requires
            x as int == 0x20000 * q + r,
    ;
    assert(r * 0x8000 < 0x100000000) by (nonlinear_arith)
        requires
            0 <= r < 0x20000,
    ;
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, r * 0x8000, 0x100000000);
    vstd::arithmetic::div_mod::lemma_small_mod((r * 0x8000) as nat, 0x100000000);
}

pub proof fn lemma_shl32_13(x: u32)
    ensures
        ((x as nat * pow2_spec(13)) % 0x100000000) as u32 == x << 13u32,
{
    assert(pow2_spec(13) == 0x2000) by (compute_only);
    assert(x << 13u32 == ((x % 0x80000u32) * 0x2000u32) as u32) by (bit_vector);
    let q = x as int / 0x80000;
    let r = x as int % 0x80000;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 0x80000);
    assert(x as int * 0x2000 == q * 0x100000000 + r * 0x2000) by (nonlinear_arith)
        requires
            x as int == 0x80000 * q + r,
    ;
    assert(r * 0x2000 < 0x100000000) by (nonlinear_arith)
        requires
            0 <= r < 0x80000,
    ;
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, r * 0x2000, 0x100000000);
    vstd::arithmetic::div_mod::lemma_small_mod((r * 0x2000) as nat, 0x100000000);
}
// ---------------------------------------------------------------------------
// Lanes of concatenated and split byte sequences
// ---------------------------------------------------------------------------

pub proof fn lemma_u32s_concat(a: Seq<u8>, b: Seq<u8>)
    requires
        a.len() % 4 == 0,
        b.len() % 4 == 0,
    ensures
        u32s(a + b) == u32s(a) + u32s(b),
{
    let na = a.len() / 4;
    let nb = b.len() / 4;
    assert(a.len() == 4 * na && b.len() == 4 * nb);
    assert((a + b).len() / 4 == na + nb);
    assert forall|i: int| 0 <= i < na + nb implies #[trigger] u32s(a + b)[i] == (u32s(a) + u32s(b))[i] by {
        if i >= na {
            let j = i - na;
            assert(4 * i == a.len() + 4 * j);
        }
    }
    assert(u32s(a + b) =~= u32s(a) + u32s(b));
}

pub proof fn lemma_u64s_concat(a: Seq<u8>, b: Seq<u8>)
    requires
        a.len() % 8 == 0,
        b.len() % 8 == 0,
    ensures
        u64s(a + b) == u64s(a) + u64s(b),
{
    lemma_u32s_concat(a, b);
    let na = a.len() / 8;
    let nb = b.len() / 8;
    assert(a.len() == 8 * na && b.len() == 8 * nb);
    assert((a + b).len() / 8 == na + nb);
    assert(u32s(a).len() == 2 * na);
    assert forall|i: int| 0 <= i < na + nb implies #[trigger] u64s(a + b)[i] == (u64s(a) + u64s(b))[i] by {
        if i >= na {
            let j = i - na;
            assert(2 * i == 2 * na + 2 * j);
        }
    }
    assert(u64s(a + b) =~= u64s(a) + u64s(b));
}

/// The 32-bit lanes `i..j` are the lanes of bytes `4i..4j`.
pub proof fn lemma_u32s_sub(b: Seq<u8>, i: int, j: int)
    requires
        0 <= i <= j,
        4 * j <= b.len(),
    ensures
        u32s(b.subrange(4 * i, 4 * j)) == u32s(b).subrange(i, j),
{
    let c = b.subrange(4 * i, 4 * j);
    assert(c.len() / 4 == j - i);
    assert forall|k: int| 0 <= k < j - i implies #[trigger] u32s(c)[k] == u32s(b).subrange(i, j)[k] by {
        assert(4 * k + 4 * i == 4 * (i + k));
    }
    assert(u32s(c) =~= u32s(b).subrange(i, j));
}

/// The 64-bit lanes `i..j` are the lanes of bytes `8i..8j`.
pub proof fn lemma_u64s_sub(b: Seq<u8>, i: int, j: int)
    requires
        0 <= i <= j,
        8 * j <= b.len(),
    ensures
        u64s(b.subrange(8 * i, 8 * j)) == u64s(b).subrange(i, j),
{
    let c = b.subrange(8 * i, 8 * j);
    lemma_u32s_sub(b, 2 * i, 2 * j);
    assert(c.len() / 8 == j - i);
    assert forall|k: int| 0 <= k < j - i implies #[trigger] u64s(c)[k] == u64s(b).subrange(i, j)[k] by {
        assert(u32s(c)[2 * k] == u32s(b)[2 * (i + k)]);
        assert(u32s(c)[2 * k + 1] == u32s(b)[2 * (i + k) + 1]);
    }
    assert(u64s(c) =~= u64s(b).subrange(i, j));
}

// ---------------------------------------------------------------------------
// Byte moves as lane moves
// ---------------------------------------------------------------------------

/// `alignr` by 8 bytes: in each 128-bit half, the high word of `lo` then
/// the low word of `hi`.
pub proof fn lemma_alignr8_u64s(hi: Seq<u8>, lo: Seq<u8>)
    requires
        hi.len() == 32,
        lo.len() == 32,
    ensures
        u64s(alignr_lanes(hi, lo, 8)) == seq![u64s(lo)[1], u64s(hi)[0], u64s(lo)[3], u64s(hi)[2]],
{
    let r = alignr_lanes(hi, lo, 8);
    let (p0, p1, p2, p3) = (lo.subrange(8, 16), hi.subrange(0, 8), lo.subrange(24, 32), hi.subrange(16, 24));
    assert(r =~= p0 + p1 + p2 + p3);
    lemma_u64s_concat(p0, p1);
    lemma_u64s_concat(p0 + p1, p2);
    lemma_u64s_concat(p0 + p1 + p2, p3);
    lemma_u64s_sub(lo, 1, 2);
    lemma_u64s_sub(hi, 0, 1);
    lemma_u64s_sub(lo, 3, 4);
    lemma_u64s_sub(hi, 2, 3);
    assert(u64s(r) =~= seq![u64s(lo)[1], u64s(hi)[0], u64s(lo)[3], u64s(hi)[2]]);
}

/// `alignr` by 4 bytes: in each 128-bit half, words 1 to 3 of `lo` then
/// word 0 of `hi`.
pub proof fn lemma_alignr4_u32s(hi: Seq<u8>, lo: Seq<u8>)
    requires
        hi.len() == 32,
        lo.len() == 32,
    ensures
        u32s(alignr_lanes(hi, lo, 4)) == seq![
            u32s(lo)[1], u32s(lo)[2], u32s(lo)[3], u32s(hi)[0],
            u32s(lo)[5], u32s(lo)[6], u32s(lo)[7], u32s(hi)[4],
        ],
{
    let r = alignr_lanes(hi, lo, 4);
    let (p0, p1, p2, p3) = (lo.subrange(4, 16), hi.subrange(0, 4), lo.subrange(20, 32), hi.subrange(16, 20));
    assert(r =~= p0 + p1 + p2 + p3);
    lemma_u32s_concat(p0, p1);
    lemma_u32s_concat(p0 + p1, p2);
    lemma_u32s_concat(p0 + p1 + p2, p3);
    lemma_u32s_sub(lo, 1, 4);
    lemma_u32s_sub(hi, 0, 1);
    lemma_u32s_sub(lo, 5, 8);
    lemma_u32s_sub(hi, 4, 5);
    assert(u32s(r) =~= seq![
        u32s(lo)[1], u32s(lo)[2], u32s(lo)[3], u32s(hi)[0],
        u32s(lo)[5], u32s(lo)[6], u32s(lo)[7], u32s(hi)[4],
    ]);
}

/// The `shuffle_epi8` control that reverses the bytes of each 64-bit lane.
pub open spec fn bswap64_mask() -> Seq<u8> {
    Seq::new(32, |i: int| (8 * ((i % 16) / 8) + 7 - i % 8) as u8)
}

/// The `shuffle_epi8` control that reverses the bytes of each 32-bit lane.
pub open spec fn bswap32_mask() -> Seq<u8> {
    Seq::new(32, |i: int| (4 * ((i % 16) / 4) + 3 - i % 4) as u8)
}

proof fn lemma_be64_bytes(c0: u8, c1: u8, c2: u8, c3: u8, c4: u8, c5: u8, c6: u8, c7: u8)
    ensures
        le64(le32(c7, c6, c5, c4), le32(c3, c2, c1, c0)) == ((c0 as u64) << 56u64 | (c1 as u64) << 48u64 | (c2 as u64) << 40u64 | (c3 as u64) << 32u64 | (c4 as u64) << 24u64 | (c5 as u64) << 16u64 | (c6 as u64) << 8u64 | (c7 as u64)),
{
    assert(((((c7 as u32) | ((c6 as u32) << 8u32) | ((c5 as u32) << 16u32) | ((c4 as u32) << 24u32)) as u64) | ((((c3 as u32) | ((c2 as u32) << 8u32) | ((c1 as u32) << 16u32) | ((c0 as u32) << 24u32)) as u64) << 32u64)) == ((c0 as u64) << 56u64 | (c1 as u64) << 48u64 | (c2 as u64) << 40u64 | (c3 as u64) << 32u64 | (c4 as u64) << 24u64 | (c5 as u64) << 16u64 | (c6 as u64) << 8u64 | (c7 as u64))) by (bit_vector);
}

proof fn lemma_be32_bytes(c0: u8, c1: u8, c2: u8, c3: u8)
    ensures
        le32(c3, c2, c1, c0) == ((c0 as u32) << 24u32 | (c1 as u32) << 16u32 | (c2 as u32) << 8u32 | (c3 as u32)),
{
    assert(((c3 as u32) | ((c2 as u32) << 8u32) | ((c1 as u32) << 16u32) | ((c0 as u32) << 24u32)) == ((c0 as u32)
        << 24u32 | (c1 as u32) << 16u32 | (c2 as u32) << 8u32 | (c3 as u32))) by (bit_vector);
}

/// Shuffling with [`bswap64_mask`] reads each 64-bit lane big-endian.
pub proof fn lemma_bswap64(src: Seq<u8>, m: Seq<u8>)
    requires
        src.len() == 32,
        m == bswap64_mask(),
    ensures
        forall|j: int| 0 <= j < 4 ==> #[trigger] u64s(shuffle8_lanes(src, m))[j] == crate::spec512::be64_at(src, 8 * j),
{
    let r = shuffle8_lanes(src, m);
    assert forall|i: int| 0 <= i < 32 implies #[trigger] r[i] == src[8 * (i / 8) + 7 - i % 8] by {}
    assert forall|j: int| 0 <= j < 4 implies #[trigger] u64s(r)[j] == crate::spec512::be64_at(src, 8 * j) by {
        let k = 8 * j;
        assert(r[k] == src[k + 7] && r[k + 1] == src[k + 6] && r[k + 2] == src[k + 5] && r[k + 3] == src[k + 4]);
        assert(r[k + 4] == src[k + 3] && r[k + 5] == src[k + 2] && r[k + 6] == src[k + 1] && r[k + 7] == src[k]);
        lemma_be64_bytes(src[k], src[k + 1], src[k + 2], src[k + 3], src[k + 4], src[k + 5], src[k + 6], src[k + 7]);
    }
}

/// Shuffling with [`bswap32_mask`] reads each 32-bit lane big-endian.
pub proof fn lemma_bswap32(src: Seq<u8>, m: Seq<u8>)
    requires
        src.len() == 32,
        m == bswap32_mask(),
    ensures
        forall|j: int| 0 <= j < 8 ==> #[trigger] u32s(shuffle8_lanes(src, m))[j] == crate::spec::be32(src, 4 * j),
{
    let r = shuffle8_lanes(src, m);
    assert forall|i: int| 0 <= i < 32 implies #[trigger] r[i] == src[4 * (i / 4) + 3 - i % 4] by {}
    assert forall|j: int| 0 <= j < 8 implies #[trigger] u32s(r)[j] == crate::spec::be32(src, 4 * j) by {
        let k = 4 * j;
        assert(r[k] == src[k + 3] && r[k + 1] == src[k + 2] && r[k + 2] == src[k + 1] && r[k + 3] == src[k]);
        lemma_be32_bytes(src[k], src[k + 1], src[k + 2], src[k + 3]);
    }
}

} // verus!

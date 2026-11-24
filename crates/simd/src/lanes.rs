//! Lane views of 128- and 256-bit vectors.
//!
//! A vector is modelled as its bytes in memory order (`b128`, `b256`):
//! byte 0 is the lowest-addressed byte when the vector is stored, which on
//! x86 is also the least significant byte of lane 0. Every wider view
//! (`u16s`, `u32s`, `u64s`) is defined from the bytes, little-endian, so the
//! views of one vector always agree with each other.
//!
//! `b128` and `b256` are uninterpreted: the only facts about a vector are its
//! length (32 or 16 bytes, an axiom) and what the intrinsic specifications in
//! `crate::x86` say about the vectors they return.
use crate::arch::{__m128i, __m256i};
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

/// Tells Verus about `__m128i`, an opaque type here: its contents are seen through the lane views.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExM128i(__m128i);

/// Tells Verus about `__m256i`, an opaque type here: its contents are seen through the lane views.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExM256i(__m256i);

/// The 16 bytes of a 128-bit vector, lane 0 first.
pub uninterp spec fn b128(v: __m128i) -> Seq<u8>;

/// The 32 bytes of a 256-bit vector, lane 0 first.
pub uninterp spec fn b256(v: __m256i) -> Seq<u8>;

pub broadcast axiom fn axiom_b128_len(v: __m128i)
    ensures
        #[trigger] b128(v).len() == 16,
;

pub broadcast axiom fn axiom_b256_len(v: __m256i)
    ensures
        #[trigger] b256(v).len() == 32,
;

/// The axioms of this module, for `broadcast use group_lanes`.
pub broadcast group group_lanes {
    axiom_b128_len,
    axiom_b256_len,
}

// ---------------------------------------------------------------------------
// Little-endian packing
// ---------------------------------------------------------------------------

pub open spec fn le16(b0: u8, b1: u8) -> u16 {
    (b0 as u16) | ((b1 as u16) << 8u16)
}

pub open spec fn le32(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    (b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)
}

pub open spec fn le64(w0: u32, w1: u32) -> u64 {
    (w0 as u64) | ((w1 as u64) << 32u64)
}

/// Byte `k` (0 = least significant) of a 32-bit lane.
pub open spec fn byte32(x: u32, k: int) -> u8 {
    if k == 0 {
        (x & 0xff) as u8
    } else if k == 1 {
        ((x >> 8u32) & 0xff) as u8
    } else if k == 2 {
        ((x >> 16u32) & 0xff) as u8
    } else {
        ((x >> 24u32) & 0xff) as u8
    }
}

/// Byte `k` of a 16-bit lane.
pub open spec fn byte16(x: u16, k: int) -> u8 {
    if k == 0 {
        (x & 0xff) as u8
    } else {
        ((x >> 8u16) & 0xff) as u8
    }
}

// ---------------------------------------------------------------------------
// Views
// ---------------------------------------------------------------------------

pub open spec fn u16s(b: Seq<u8>) -> Seq<u16> {
    Seq::new(b.len() / 2, |i: int| le16(b[2 * i], b[2 * i + 1]))
}

pub open spec fn u32s(b: Seq<u8>) -> Seq<u32> {
    Seq::new(b.len() / 4, |i: int| le32(b[4 * i], b[4 * i + 1], b[4 * i + 2], b[4 * i + 3]))
}

pub open spec fn u64s(b: Seq<u8>) -> Seq<u64> {
    Seq::new(b.len() / 8, |i: int| le64(u32s(b)[2 * i], u32s(b)[2 * i + 1]))
}

/// Two's-complement readings of unsigned lanes.
pub open spec fn s8(x: u8) -> int {
    if x < 128 {
        x as int
    } else {
        x - 256
    }
}

pub open spec fn s16(x: u16) -> int {
    if x < 0x8000 {
        x as int
    } else {
        x - 0x10000
    }
}

pub open spec fn s32(x: u32) -> int {
    if x < 0x8000_0000 {
        x as int
    } else {
        x - 0x1_0000_0000
    }
}

/// The bytes of a sequence of 32-bit lanes.
pub open spec fn bytes_of_u32s(s: Seq<u32>) -> Seq<u8> {
    Seq::new(4 * s.len(), |j: int| byte32(s[j / 4], j % 4))
}

/// The bytes of a sequence of 16-bit lanes.
pub open spec fn bytes_of_u16s(s: Seq<u16>) -> Seq<u8> {
    Seq::new(2 * s.len(), |j: int| byte16(s[j / 2], j % 2))
}

pub open spec fn u8x16(v: __m128i) -> Seq<u8> {
    b128(v)
}

pub open spec fn u16x8(v: __m128i) -> Seq<u16> {
    u16s(b128(v))
}

pub open spec fn u32x4(v: __m128i) -> Seq<u32> {
    u32s(b128(v))
}

pub open spec fn u64x2(v: __m128i) -> Seq<u64> {
    u64s(b128(v))
}

pub open spec fn u8x32(v: __m256i) -> Seq<u8> {
    b256(v)
}

pub open spec fn u16x16(v: __m256i) -> Seq<u16> {
    u16s(b256(v))
}

pub open spec fn u32x8(v: __m256i) -> Seq<u32> {
    u32s(b256(v))
}

pub open spec fn u64x4(v: __m256i) -> Seq<u64> {
    u64s(b256(v))
}

// ---------------------------------------------------------------------------
// Moving between views
// ---------------------------------------------------------------------------

pub proof fn lemma_le32_bytes(b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        byte32(le32(b0, b1, b2, b3), 0) == b0,
        byte32(le32(b0, b1, b2, b3), 1) == b1,
        byte32(le32(b0, b1, b2, b3), 2) == b2,
        byte32(le32(b0, b1, b2, b3), 3) == b3,
{
    assert(((((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) & 0xff) as u8) == b0)
        by (bit_vector);
    assert(((((((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) >> 8u32) & 0xff)) as u8) == b1)
        by (bit_vector);
    assert(((((((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) >> 16u32) & 0xff)) as u8) == b2)
        by (bit_vector);
    assert(((((((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32)) >> 24u32) & 0xff)) as u8) == b3)
        by (bit_vector);
}

pub proof fn lemma_bytes_le32(x: u32)
    ensures
        le32(byte32(x, 0), byte32(x, 1), byte32(x, 2), byte32(x, 3)) == x,
{
    assert(((((x & 0xff) as u8) as u32) | (((((x >> 8u32) & 0xff) as u8) as u32) << 8u32) | (((((x >> 16u32)
        & 0xff) as u8) as u32) << 16u32) | (((((x >> 24u32) & 0xff) as u8) as u32) << 24u32)) == x) by (bit_vector);
}

pub proof fn lemma_le16_bytes(b0: u8, b1: u8)
    ensures
        byte16(le16(b0, b1), 0) == b0,
        byte16(le16(b0, b1), 1) == b1,
{
    assert(((((b0 as u16) | ((b1 as u16) << 8u16)) & 0xff) as u8) == b0) by (bit_vector);
    assert((((((b0 as u16) | ((b1 as u16) << 8u16)) >> 8u16) & 0xff) as u8) == b1) by (bit_vector);
}

pub proof fn lemma_bytes_le16(x: u16)
    ensures
        le16(byte16(x, 0), byte16(x, 1)) == x,
{
    assert(((((x & 0xff) as u8) as u16) | (((((x >> 8u16) & 0xff) as u8) as u16) << 8u16)) == x) by (bit_vector);
}

/// Each byte is the matching byte of its 32-bit lane.
pub proof fn lemma_u32s_bytes(b: Seq<u8>)
    requires
        b.len() % 4 == 0,
    ensures
        u32s(b).len() * 4 == b.len(),
        forall|i: int, k: int|
            0 <= i < u32s(b).len() && 0 <= k < 4 ==> #[trigger] byte32(u32s(b)[i], k) == b[4 * i + k],
{
    assert forall|i: int, k: int| 0 <= i < u32s(b).len() && 0 <= k < 4 implies #[trigger] byte32(u32s(b)[i], k)
        == b[4 * i + k] by {
        lemma_le32_bytes(b[4 * i], b[4 * i + 1], b[4 * i + 2], b[4 * i + 3]);
    }
}

/// Each byte is the matching byte of its 16-bit lane.
pub proof fn lemma_u16s_bytes(b: Seq<u8>)
    requires
        b.len() % 2 == 0,
    ensures
        u16s(b).len() * 2 == b.len(),
        forall|i: int, k: int|
            0 <= i < u16s(b).len() && 0 <= k < 2 ==> #[trigger] byte16(u16s(b)[i], k) == b[2 * i + k],
{
    assert forall|i: int, k: int| 0 <= i < u16s(b).len() && 0 <= k < 2 implies #[trigger] byte16(u16s(b)[i], k)
        == b[2 * i + k] by {
        lemma_le16_bytes(b[2 * i], b[2 * i + 1]);
    }
}

/// Bytes are determined by their 32-bit lanes.
pub proof fn lemma_u32s_inj(b: Seq<u8>, c: Seq<u8>)
    requires
        b.len() == c.len(),
        b.len() % 4 == 0,
        u32s(b) == u32s(c),
    ensures
        b == c,
{
    lemma_u32s_bytes(b);
    lemma_u32s_bytes(c);
    assert forall|j: int| 0 <= j < b.len() implies b[j] == c[j] by {
        lemma_fundamental_div_mod(j, 4);
        let i = j / 4;
        let k = j % 4;
        assert(byte32(u32s(b)[i], k) == b[4 * i + k]);
        assert(byte32(u32s(c)[i], k) == c[4 * i + k]);
    }
    assert(b =~= c);
}

/// The 32-bit lanes of `bytes_of_u32s(s)` are `s`.
pub proof fn lemma_u32s_of_bytes(s: Seq<u32>)
    ensures
        u32s(bytes_of_u32s(s)) == s,
        bytes_of_u32s(s).len() == 4 * s.len(),
{
    let b = bytes_of_u32s(s);
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] u32s(b)[i] == s[i] by {
        assert((4 * i) / 4 == i && (4 * i) % 4 == 0) by (nonlinear_arith)
            requires
                i >= 0,
        ;
        assert((4 * i + 1) / 4 == i && (4 * i + 1) % 4 == 1) by (nonlinear_arith)
            requires
                i >= 0,
        ;
        assert((4 * i + 2) / 4 == i && (4 * i + 2) % 4 == 2) by (nonlinear_arith)
            requires
                i >= 0,
        ;
        assert((4 * i + 3) / 4 == i && (4 * i + 3) % 4 == 3) by (nonlinear_arith)
            requires
                i >= 0,
        ;
        lemma_bytes_le32(s[i]);
    }
    assert(u32s(b) =~= s);
}

/// The 16-bit lanes of `bytes_of_u16s(s)` are `s`.
pub proof fn lemma_u16s_of_bytes(s: Seq<u16>)
    ensures
        u16s(bytes_of_u16s(s)) == s,
        bytes_of_u16s(s).len() == 2 * s.len(),
{
    let b = bytes_of_u16s(s);
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] u16s(b)[i] == s[i] by {
        assert((2 * i) / 2 == i && (2 * i) % 2 == 0) by (nonlinear_arith)
            requires
                i >= 0,
        ;
        assert((2 * i + 1) / 2 == i && (2 * i + 1) % 2 == 1) by (nonlinear_arith)
            requires
                i >= 0,
        ;
        lemma_bytes_le16(s[i]);
    }
    assert(u16s(b) =~= s);
}

/// A byte sequence is `bytes_of_u32s` of its lanes.
pub proof fn lemma_bytes_of_u32s(b: Seq<u8>)
    requires
        b.len() % 4 == 0,
    ensures
        b == bytes_of_u32s(u32s(b)),
{
    lemma_u32s_of_bytes(u32s(b));
    lemma_u32s_inj(b, bytes_of_u32s(u32s(b)));
}

/// A byte sequence is `bytes_of_u16s` of its lanes.
pub proof fn lemma_bytes_of_u16s(b: Seq<u8>)
    requires
        b.len() % 2 == 0,
    ensures
        b == bytes_of_u16s(u16s(b)),
{
    let s = u16s(b);
    lemma_u16s_bytes(b);
    let c = bytes_of_u16s(s);
    assert forall|j: int| 0 <= j < b.len() implies b[j] == c[j] by {
        lemma_fundamental_div_mod(j, 2);
        assert(byte16(s[j / 2], j % 2) == b[2 * (j / 2) + j % 2]);
    }
    assert(b =~= c);
}

/// The 16-bit lanes are the halves of the 32-bit lanes.
pub proof fn lemma_u16s_of_u32s(b: Seq<u8>)
    requires
        b.len() % 4 == 0,
    ensures
        u16s(b).len() == 2 * u32s(b).len(),
        forall|k: int|
            0 <= k < u32s(b).len() ==> #[trigger] u16s(b)[2 * k] == (u32s(b)[k] & 0xffff) as u16 && u16s(b)[2 * k
                + 1] == (u32s(b)[k] >> 16u32) as u16,
{
    assert forall|k: int| 0 <= k < u32s(b).len() implies #[trigger] u16s(b)[2 * k] == (u32s(b)[k] & 0xffff) as u16
        && u16s(b)[2 * k + 1] == (u32s(b)[k] >> 16u32) as u16 by {
        let (b0, b1, b2, b3) = (b[4 * k], b[4 * k + 1], b[4 * k + 2], b[4 * k + 3]);
        assert(u16s(b)[2 * k] == le16(b0, b1));
        assert(u16s(b)[2 * k + 1] == le16(b2, b3));
        assert(((b0 as u16) | ((b1 as u16) << 8u16)) == ((((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32)
            | ((b3 as u32) << 24u32)) & 0xffff) as u16)) by (bit_vector);
        assert(((b2 as u16) | ((b3 as u16) << 8u16)) == ((((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32)
            | ((b3 as u32) << 24u32)) >> 16u32) as u16)) by (bit_vector);
    }
}

/// A byte is the matching byte of its 16-bit lane, for lanes of a 32-bit
/// lane.
pub proof fn lemma_u16_lane_bytes(b: Seq<u8>, i: int)
    requires
        b.len() % 2 == 0,
        0 <= i < b.len() / 2,
    ensures
        b[2 * i] == byte16(u16s(b)[i], 0),
        b[2 * i + 1] == byte16(u16s(b)[i], 1),
{
    lemma_le16_bytes(b[2 * i], b[2 * i + 1]);
}

/// `le16` as a number.
pub proof fn lemma_le16_value(b0: u8, b1: u8)
    ensures
        le16(b0, b1) as int == b0 + 256 * b1,
{
    assert((b0 as u16) | ((b1 as u16) << 8u16) == (b0 as u16) + (b1 as u16) * 256) by (bit_vector);
}

/// `le32` as a number.
pub proof fn lemma_le32_value(b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        le32(b0, b1, b2, b3) as int == b0 + 0x100 * b1 + 0x1_0000 * b2 + 0x100_0000 * b3,
{
    assert((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32) == (b0 as u32) + (
    b1 as u32) * 0x100 + (b2 as u32) * 0x1_0000 + (b3 as u32) * 0x100_0000) by (bit_vector);
}

/// The low byte of a 16-bit lane is the lane mod 256.
pub proof fn lemma_byte16_lo(x: u16)
    ensures
        byte16(x, 0) as int == x % 256,
        byte16(x, 1) as int == x / 256,
{
    assert(((x & 0xff) as u8) as u16 == x % 256) by (bit_vector);
    assert((((x >> 8u16) & 0xff) as u8) as u16 == x / 256) by (bit_vector);
}

} // verus!

//! Pixels as vector lanes: the bridge between `vsimd`'s byte view of a
//! vector and the spec's ARGB pixel functions.
//!
//! A pixel `p` in a 32-bit lane occupies four bytes, little-endian: blue,
//! green, red, alpha.
#[cfg(verus_only)]
use crate::pixels::lemma_argb;
#[cfg(verus_only)]
use crate::spec::*;
use vstd::prelude::*;
#[cfg(verus_only)]
use verilith_simd::lanes::*;
#[cfg(verus_only)]
use verilith_simd::ops::*;

verus! {

/// The channels of a pixel are its bytes.
pub proof fn lemma_px_bytes(p: u32)
    ensures
        blue(p) == byte32(p, 0) as u32,
        green(p) == byte32(p, 1) as u32,
        red(p) == byte32(p, 2) as u32,
        alpha(p) == byte32(p, 3) as u32,
{
    assert(p & 0xffu32 == ((p & 0xff) as u8) as u32) by (bit_vector);
    assert((p >> 8u32) & 0xffu32 == (((p >> 8u32) & 0xff) as u8) as u32) by (bit_vector);
    assert((p >> 16u32) & 0xffu32 == (((p >> 16u32) & 0xff) as u8) as u32) by (bit_vector);
    assert(p >> 24u32 == (((p >> 24u32) & 0xff) as u8) as u32) by (bit_vector);
}

/// A pixel from its channels is the little-endian word of its bytes.
pub proof fn lemma_argb_le32(a: u8, r: u8, g: u8, b: u8)
    ensures
        argb(a as nat, r as nat, g as nat, b as nat) == le32(b, g, r, a),
{
    lemma_argb(a as u32, r as u32, g as u32, b as u32);
    assert(((a as u32) << 24u32) | ((r as u32) << 16u32) | ((g as u32) << 8u32) | (b as u32) == (b as u32) | ((
    g as u32) << 8u32) | ((r as u32) << 16u32) | ((a as u32) << 24u32)) by (bit_vector);
}

/// The channels of the pixel in lane `i` of a byte sequence.
pub proof fn lemma_lane_px(b: Seq<u8>, i: int)
    requires
        b.len() % 4 == 0,
        0 <= i < b.len() / 4,
    ensures
        blue(u32s(b)[i]) == b[4 * i] as u32,
        green(u32s(b)[i]) == b[4 * i + 1] as u32,
        red(u32s(b)[i]) == b[4 * i + 2] as u32,
        alpha(u32s(b)[i]) == b[4 * i + 3] as u32,
        u32s(b)[i] == le32(b[4 * i], b[4 * i + 1], b[4 * i + 2], b[4 * i + 3]),
{
    lemma_u32s_bytes(b);
    let p = u32s(b)[i];
    assert(byte32(p, 0) == b[4 * i + 0]);
    assert(byte32(p, 1) == b[4 * i + 1]);
    assert(byte32(p, 2) == b[4 * i + 2]);
    assert(byte32(p, 3) == b[4 * i + 3]);
    lemma_px_bytes(p);
}

/// Bytewise addition is `add_px` on each pixel.
pub proof fn lemma_add8_px(a: Seq<u8>, b: Seq<u8>)
    requires
        a.len() == b.len(),
        a.len() % 4 == 0,
    ensures
        u32s(add8(a, b)).len() == u32s(a).len(),
        forall|i: int| 0 <= i < u32s(a).len() ==> #[trigger] u32s(add8(a, b))[i] == add_px(u32s(a)[i], u32s(b)[i]),
{
    let c = add8(a, b);
    assert forall|i: int| 0 <= i < u32s(a).len() implies #[trigger] u32s(c)[i] == add_px(u32s(a)[i], u32s(b)[i]) by {
        lemma_lane_px(a, i);
        lemma_lane_px(b, i);
        lemma_lane_px(c, i);
        let (pa, pb) = (u32s(a)[i], u32s(b)[i]);
        lemma_argb_le32(
            ((alpha(pa) + alpha(pb)) % 256) as u8,
            ((red(pa) + red(pb)) % 256) as u8,
            ((green(pa) + green(pb)) % 256) as u8,
            ((blue(pa) + blue(pb)) % 256) as u8,
        );
    }
}

/// A pixel is determined by its bytes.
pub proof fn lemma_px_ext(x: u32, y: u32)
    requires
        byte32(x, 0) == byte32(y, 0),
        byte32(x, 1) == byte32(y, 1),
        byte32(x, 2) == byte32(y, 2),
        byte32(x, 3) == byte32(y, 3),
    ensures
        x == y,
{
    lemma_bytes_le32(x);
    lemma_bytes_le32(y);
}

/// The bytes of `add_px`.
pub proof fn lemma_add_px_bytes(x: u32, y: u32)
    ensures
        forall|c: int| 0 <= c < 4 ==> #[trigger] byte32(add_px(x, y), c) as int == (byte32(x, c) + byte32(y, c)) % 256,
{
    lemma_px_bytes(x);
    lemma_px_bytes(y);
    let (b0, b1, b2, b3) = (
        ((blue(x) + blue(y)) % 256) as u8,
        ((green(x) + green(y)) % 256) as u8,
        ((red(x) + red(y)) % 256) as u8,
        ((alpha(x) + alpha(y)) % 256) as u8,
    );
    lemma_argb_le32(b3, b2, b1, b0);
    lemma_le32_bytes(b0, b1, b2, b3);
}

/// The bytes of `avg2`.
pub proof fn lemma_avg2_bytes(x: u32, y: u32)
    ensures
        forall|c: int| 0 <= c < 4 ==> #[trigger] byte32(avg2(x, y), c) as int == (byte32(x, c) + byte32(y, c)) / 2,
{
    lemma_px_bytes(x);
    lemma_px_bytes(y);
    let (b0, b1, b2, b3) = (
        ((blue(x) + blue(y)) / 2) as u8,
        ((green(x) + green(y)) / 2) as u8,
        ((red(x) + red(y)) / 2) as u8,
        ((alpha(x) + alpha(y)) / 2) as u8,
    );
    lemma_argb_le32(b3, b2, b1, b0);
    lemma_le32_bytes(b0, b1, b2, b3);
}

pub proof fn lemma_add_px_comm(x: u32, y: u32)
    ensures
        add_px(x, y) == add_px(y, x),
{
    lemma_add_px_bytes(x, y);
    lemma_add_px_bytes(y, x);
    lemma_px_ext(add_px(x, y), add_px(y, x));
}

pub proof fn lemma_add_px_assoc(x: u32, y: u32, z: u32)
    ensures
        add_px(x, add_px(y, z)) == add_px(add_px(x, y), z),
{
    lemma_add_px_bytes(y, z);
    lemma_add_px_bytes(x, add_px(y, z));
    lemma_add_px_bytes(x, y);
    lemma_add_px_bytes(add_px(x, y), z);
    assert forall|c: int| 0 <= c < 4 implies #[trigger] byte32(add_px(x, add_px(y, z)), c) == byte32(
        add_px(add_px(x, y), z),
        c,
    ) by {
        let (a, b, d) = (byte32(x, c) as int, byte32(y, c) as int, byte32(z, c) as int);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(a, b + d, 256);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(a + b, d, 256);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(b, d, 256);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(a, b, 256);
        vstd::arithmetic::div_mod::lemma_mod_twice(b + d, 256);
        vstd::arithmetic::div_mod::lemma_mod_twice(a + b, 256);
        vstd::arithmetic::div_mod::lemma_small_mod(a as nat, 256);
        vstd::arithmetic::div_mod::lemma_small_mod(d as nat, 256);
    }
    lemma_px_ext(add_px(x, add_px(y, z)), add_px(add_px(x, y), z));
}

pub proof fn lemma_add_px_zero(x: u32)
    ensures
        add_px(x, 0) == x,
{
    lemma_add_px_bytes(x, 0);
    assert(byte32(0u32, 0) == 0 && byte32(0u32, 1) == 0 && byte32(0u32, 2) == 0 && byte32(0u32, 3) == 0) by (compute);
    assert forall|c: int| 0 <= c < 4 implies #[trigger] byte32(add_px(x, 0), c) == byte32(x, c) by {
        vstd::arithmetic::div_mod::lemma_small_mod(byte32(x, c) as nat, 256);
    }
    lemma_px_ext(add_px(x, 0), x);
}

/// Pixel `k` of a byte sequence is `x` when its four bytes are `x`'s.
pub proof fn lemma_lane_is(b: Seq<u8>, k: int, x: u32)
    requires
        b.len() % 4 == 0,
        0 <= k < b.len() / 4,
        b[4 * k] == byte32(x, 0),
        b[4 * k + 1] == byte32(x, 1),
        b[4 * k + 2] == byte32(x, 2),
        b[4 * k + 3] == byte32(x, 3),
    ensures
        u32s(b)[k] == x,
{
    lemma_bytes_le32(x);
}

/// Byte `c` of pixel `k`.
pub proof fn lemma_lane_byte(b: Seq<u8>, k: int, c: int)
    requires
        b.len() % 4 == 0,
        0 <= k < b.len() / 4,
        0 <= c < 4,
    ensures
        b[4 * k + c] == byte32(u32s(b)[k], c),
{
    lemma_u32s_bytes(b);
}

/// `avg_epu8(a, b) - ((a ^ b) & 1)` is the rounded-down average, per pixel.
pub proof fn lemma_avgf_px(a: Seq<u8>, b: Seq<u8>, ones: Seq<u8>, r: Seq<u8>)
    requires
        a.len() == b.len(),
        a.len() % 4 == 0,
        ones == splat8(1u8, a.len()),
        r == sub8(avg_u8(a, b), and8(xor8(a, b), ones)),
    ensures
        forall|k: int| 0 <= k < a.len() / 4 ==> #[trigger] u32s(r)[k] == avg2(u32s(a)[k], u32s(b)[k]),
{
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] r[i] as int == (a[i] + b[i]) / 2 by {
        let (x, y) = (a[i], b[i]);
        assert((x ^ y) & 1u8 == ((x as u16 + y as u16) % 2) as u8) by (bit_vector);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x + y, 2);
    }
    assert forall|k: int| 0 <= k < a.len() / 4 implies #[trigger] u32s(r)[k] == avg2(u32s(a)[k], u32s(b)[k]) by {
        let (x, y) = (u32s(a)[k], u32s(b)[k]);
        lemma_avg2_bytes(x, y);
        lemma_lane_byte(a, k, 0);
        lemma_lane_byte(a, k, 1);
        lemma_lane_byte(a, k, 2);
        lemma_lane_byte(a, k, 3);
        lemma_lane_byte(b, k, 0);
        lemma_lane_byte(b, k, 1);
        lemma_lane_byte(b, k, 2);
        lemma_lane_byte(b, k, 3);
        lemma_lane_is(r, k, avg2(x, y));
    }
}

/// `(a & b) + ((a ^ b) >> 1)` byte by byte is the rounded-down average,
/// per pixel.
pub proof fn lemma_avgh_px(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>)
    requires
        a.len() == b.len(),
        a.len() % 4 == 0,
        r == add8(and8(a, b), shr8(xor8(a, b), 1)),
    ensures
        forall|k: int| 0 <= k < a.len() / 4 ==> #[trigger] u32s(r)[k] == avg2(u32s(a)[k], u32s(b)[k]),
{
    reveal_with_fuel(pow2_spec, 2);
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] r[i] as int == (a[i] + b[i]) / 2 by {
        let (x, y) = (a[i], b[i]);
        assert(((x & y) as u16 + ((x ^ y) / 2u8) as u16) == (x as u16 + y as u16) / 2) by (bit_vector);
    }
    assert forall|k: int| 0 <= k < a.len() / 4 implies #[trigger] u32s(r)[k] == avg2(u32s(a)[k], u32s(b)[k]) by {
        let (x, y) = (u32s(a)[k], u32s(b)[k]);
        lemma_avg2_bytes(x, y);
        lemma_lane_byte(a, k, 0);
        lemma_lane_byte(a, k, 1);
        lemma_lane_byte(a, k, 2);
        lemma_lane_byte(a, k, 3);
        lemma_lane_byte(b, k, 0);
        lemma_lane_byte(b, k, 1);
        lemma_lane_byte(b, k, 2);
        lemma_lane_byte(b, k, 3);
        lemma_lane_is(r, k, avg2(x, y));
    }
}

} // verus!

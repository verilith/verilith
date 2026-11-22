//! XXH32 with seed 0, proven equal to `spec::xxh32`.
#[cfg(verus_only)]
use crate::bytes::lemma_le_is;
use crate::spec::*;
use verilith_core::lz::load32;
use verilith_core::prims::get;
use vstd::prelude::*;

verus! {

const XQ1: u32 = 0x9E3779B1;

const XQ2: u32 = 0x85EBCA77;

const XQ3: u32 = 0xC2B2AE3D;

const XQ4: u32 = 0x27D4EB2F;

const XQ5: u32 = 0x165667B1;

#[inline(always)]
fn rotl(x: u32, r: u32) -> (y: u32)
    requires
        1 <= r <= 31,
    ensures
        y == rotl32(x, r),
{
    proof {
        reveal(rotl32);
    }
    (x << r) | (x >> (32 - r))
}

/// The four bytes at `i`, little-endian.
#[inline(always)]
fn word(b: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= b@.len(),
    ensures
        r == le32(b@, i as int),
        r == le(b@, i as int, 4),
{
    let r = load32(b, i);
    proof {
        lemma_le_is(b@, i as int, 4);
    }
    r
}

#[inline(always)]
fn add(a: u32, b: u32) -> (r: u32)
    ensures
        r == add32(a, b),
{
    proof {
        reveal(add32);
    }
    a.wrapping_add(b)
}

#[inline(always)]
fn mul(a: u32, b: u32) -> (r: u32)
    ensures
        r == mul32(a, b),
{
    proof {
        reveal(mul32);
    }
    a.wrapping_mul(b)
}

#[inline(always)]
fn round(acc: u32, lane: u32) -> (r: u32)
    ensures
        r == round32(acc, lane),
{
    proof {
        reveal(round32);
    }
    mul(rotl(add(acc, mul(lane, XQ2)), 13), XQ1)
}

/// The accumulators after all whole stripes (`stripes32`).
fn stripes(b: &[u8]) -> (r: (u32, u32, u32, u32))
    ensures
        r == stripes32(b@, 0, (add32(PRIME32_1, PRIME32_2), PRIME32_2, 0u32, (0x1_0000_0000 - PRIME32_1) as u32)),
{
    let n = b.len();
    let ghost v0 = (add32(PRIME32_1, PRIME32_2), PRIME32_2, 0u32, (0x1_0000_0000 - PRIME32_1) as u32);
    let ghost goal = stripes32(b@, 0, v0);
    let mut v1 = add(XQ1, XQ2);
    let mut v2 = XQ2;
    let mut v3 = 0u32;
    let mut v4 = 0u32.wrapping_sub(XQ1);
    let mut i: usize = 0;
    proof {
        assert(v4 == (0x1_0000_0000 - PRIME32_1) as u32);
    }
    while n - i >= 16
        invariant
            n == b@.len(),
            i <= n,
            goal == stripes32(b@, 0, v0),
            stripes32(b@, i as int, (v1, v2, v3, v4)) == goal,
        decreases n - i,
    {
        v1 = round(v1, word(b, i));
        v2 = round(v2, word(b, i + 4));
        v3 = round(v3, word(b, i + 8));
        v4 = round(v4, word(b, i + 12));
        i = i + 16;
    }
    (v1, v2, v3, v4)
}

/// The tail from `i0` on (`tail32`).
fn tail(b: &[u8], i0: usize, h0: u32) -> (r: u32)
    requires
        i0 <= b@.len(),
    ensures
        r == tail32(b@, i0 as int, h0),
{
    let n = b.len();
    let mut h = h0;
    let mut i = i0;
    let ghost goal = tail32(b@, i0 as int, h0);
    while i < n
        invariant
            n == b@.len(),
            i <= n,
            goal == tail32(b@, i0 as int, h0),
            tail32(b@, i as int, h) == goal,
        decreases n - i,
    {
        if n - i >= 4 {
            h = mul(rotl(add(h, mul(word(b, i), XQ3)), 17), XQ4);
            i = i + 4;
        } else {
            h = mul(rotl(add(h, mul(get(b, i) as u32, XQ5)), 11), XQ1);
            i = i + 1;
        }
    }
    h
}

/// XXH32 of `b` with seed 0 (`xxh32`).
pub fn xxh32_exec(b: &[u8]) -> (r: u32)
    ensures
        r == xxh32(b@),
{
    let n = b.len();
    let full = n / 16 * 16;
    let h0 = if n >= 16 {
        let (v1, v2, v3, v4) = stripes(b);
        add(add(add(rotl(v1, 1), rotl(v2, 7)), rotl(v3, 12)), rotl(v4, 18))
    } else {
        XQ5
    };
    let h = tail(b, full, add(h0, (n & 0xffff_ffff) as u32));
    proof {
        assert(n & 0xffff_ffff == n % 0x1_0000_0000) by (bit_vector);
    }
    let h1 = mul(h ^ (h >> 15), XQ2);
    let h2 = mul(h1 ^ (h1 >> 13), XQ3);
    h2 ^ (h2 >> 16)
}

} // verus!

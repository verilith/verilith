//! XXH32 and XXH64 with seed 0, as pure functions, written from the xxHash
//! specification (`doc/xxhash_spec.md` in the xxHash repository). This
//! file is the trusted specification: everything else in the crate is
//! proven against it.
//!
//! The names follow the specification's: `PRIME32_1` to `PRIME32_5` and
//! `PRIME64_1` to `PRIME64_5` are its constants, and the steps are those
//! of its sections "XXH32 Algorithm Description" and "XXH64 Algorithm
//! Description": initialize the four accumulators, process stripes, merge
//! the accumulators (XXH64 only), add the input length, consume the
//! remaining input, and the final mix (avalanche).
use vstd::prelude::*;

verus! {

/// The `n` bytes at `i` as a little-endian number.
pub open spec fn le(b: Seq<u8>, i: int, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        b[i] as nat + 256 * le(b, i + 1, (n - 1) as nat)
    }
}

// ---------------------------------------------------------------------------
// XXH32
// ---------------------------------------------------------------------------

#[verifier::opaque]
pub open spec fn add32(a: u32, b: u32) -> u32 {
    vstd::wrapping::u32_specs::wrapping_add(a, b)
}

#[verifier::opaque]
pub open spec fn mul32(a: u32, b: u32) -> u32 {
    vstd::wrapping::u32_specs::wrapping_mul(a, b)
}

#[verifier::opaque]
pub open spec fn rotl32(x: u32, r: u32) -> u32 {
    (x << r) | (x >> (32 - r) as u32)
}

pub spec const PRIME32_1: u32 = 0x9E3779B1;

pub spec const PRIME32_2: u32 = 0x85EBCA77;

pub spec const PRIME32_3: u32 = 0xC2B2AE3D;

pub spec const PRIME32_4: u32 = 0x27D4EB2F;

pub spec const PRIME32_5: u32 = 0x165667B1;

/// The four bytes at `i`, little-endian.
pub open spec fn le32(b: Seq<u8>, i: int) -> u32 {
    le(b, i, 4) as u32
}

/// One lane of a stripe added into an accumulator.
#[verifier::opaque]
pub open spec fn round32(acc: u32, lane: u32) -> u32 {
    mul32(rotl32(add32(acc, mul32(lane, PRIME32_2)), 13), PRIME32_1)
}

/// The four accumulators after the 16-byte stripes starting at `i`.
pub open spec fn stripes32(b: Seq<u8>, i: int, v: (u32, u32, u32, u32)) -> (u32, u32, u32, u32)
    decreases b.len() - i,
{
    if i < 0 || i + 16 > b.len() {
        v
    } else {
        stripes32(
            b,
            i + 16,
            (
                round32(v.0, le32(b, i)),
                round32(v.1, le32(b, i + 4)),
                round32(v.2, le32(b, i + 8)),
                round32(v.3, le32(b, i + 12)),
            ),
        )
    }
}

/// The last `b.len() - i` (fewer than 16) bytes.
pub open spec fn tail32(b: Seq<u8>, i: int, h: u32) -> u32
    decreases b.len() - i,
{
    if i < 0 || i >= b.len() {
        h
    } else if i + 4 <= b.len() {
        tail32(b, i + 4, mul32(rotl32(add32(h, mul32(le32(b, i), PRIME32_3)), 17), PRIME32_4))
    } else {
        tail32(b, i + 1, mul32(rotl32(add32(h, mul32(b[i] as u32, PRIME32_5)), 11), PRIME32_1))
    }
}

pub open spec fn avalanche32(h: u32) -> u32 {
    let h1 = mul32(h ^ (h >> 15), PRIME32_2);
    let h2 = mul32(h1 ^ (h1 >> 13), PRIME32_3);
    h2 ^ (h2 >> 16)
}

/// XXH32 of `b` with seed 0.
pub open spec fn xxh32(b: Seq<u8>) -> u32 {
    let n = b.len();
    let full = (n / 16 * 16) as int;
    let h0 = if n >= 16 {
        let v = stripes32(
            b,
            0,
            (add32(PRIME32_1, PRIME32_2), PRIME32_2, 0, (0x1_0000_0000 - PRIME32_1) as u32),
        );
        add32(add32(add32(rotl32(v.0, 1), rotl32(v.1, 7)), rotl32(v.2, 12)), rotl32(v.3, 18))
    } else {
        PRIME32_5
    };
    avalanche32(tail32(b, full, add32(h0, (n % 0x1_0000_0000) as u32)))
}

// ---------------------------------------------------------------------------
// XXH64
// ---------------------------------------------------------------------------

#[verifier::opaque]
pub open spec fn add64(a: u64, b: u64) -> u64 {
    vstd::wrapping::u64_specs::wrapping_add(a, b)
}

#[verifier::opaque]
pub open spec fn mul64(a: u64, b: u64) -> u64 {
    vstd::wrapping::u64_specs::wrapping_mul(a, b)
}

#[verifier::opaque]
pub open spec fn rotl64(x: u64, r: u64) -> u64 {
    (x << r) | (x >> (64 - r) as u64)
}

pub spec const PRIME64_1: u64 = 0x9E3779B185EBCA87;

pub spec const PRIME64_2: u64 = 0xC2B2AE3D27D4EB4F;

pub spec const PRIME64_3: u64 = 0x165667B19E3779F9;

pub spec const PRIME64_4: u64 = 0x85EBCA77C2B2AE63;

pub spec const PRIME64_5: u64 = 0x27D4EB2F165667C5;

/// The eight bytes at `i`, little-endian.
pub open spec fn le64(b: Seq<u8>, i: int) -> u64 {
    le(b, i, 8) as u64
}

/// One lane of a stripe added into an accumulator.
#[verifier::opaque]
pub open spec fn round64(acc: u64, lane: u64) -> u64 {
    mul64(rotl64(add64(acc, mul64(lane, PRIME64_2)), 31), PRIME64_1)
}

/// One accumulator merged into the hash.
#[verifier::opaque]
pub open spec fn merge64(h: u64, v: u64) -> u64 {
    add64(mul64(h ^ round64(0, v), PRIME64_1), PRIME64_4)
}

/// The four accumulators after the 32-byte stripes starting at `i`.
pub open spec fn stripes64(b: Seq<u8>, i: int, v: (u64, u64, u64, u64)) -> (u64, u64, u64, u64)
    decreases b.len() - i,
{
    if i < 0 || i + 32 > b.len() {
        v
    } else {
        stripes64(
            b,
            i + 32,
            (
                round64(v.0, le64(b, i)),
                round64(v.1, le64(b, i + 8)),
                round64(v.2, le64(b, i + 16)),
                round64(v.3, le64(b, i + 24)),
            ),
        )
    }
}

/// The last `b.len() - i` (fewer than 32) bytes.
pub open spec fn tail64(b: Seq<u8>, i: int, h: u64) -> u64
    decreases b.len() - i,
{
    if i < 0 || i >= b.len() {
        h
    } else if i + 8 <= b.len() {
        tail64(b, i + 8, add64(mul64(rotl64(h ^ round64(0, le64(b, i)), 27), PRIME64_1), PRIME64_4))
    } else if i + 4 <= b.len() {
        tail64(
            b,
            i + 4,
            add64(mul64(rotl64(h ^ mul64(le(b, i, 4) as u64, PRIME64_1), 23), PRIME64_2), PRIME64_3),
        )
    } else {
        tail64(b, i + 1, mul64(rotl64(h ^ mul64(b[i] as u64, PRIME64_5), 11), PRIME64_1))
    }
}

pub open spec fn avalanche64(h: u64) -> u64 {
    let h1 = mul64(h ^ (h >> 33), PRIME64_2);
    let h2 = mul64(h1 ^ (h1 >> 29), PRIME64_3);
    h2 ^ (h2 >> 32)
}

/// XXH64 of `b` with seed 0.
pub open spec fn xxh64(b: Seq<u8>) -> u64 {
    let n = b.len();
    let full = (n / 32 * 32) as int;
    let h0 = if n >= 32 {
        let v = stripes64(
            b,
            0,
            (add64(PRIME64_1, PRIME64_2), PRIME64_2, 0, (0x1_0000_0000_0000_0000 - PRIME64_1) as u64),
        );
        let h = add64(
            add64(add64(rotl64(v.0, 1), rotl64(v.1, 7)), rotl64(v.2, 12)),
            rotl64(v.3, 18),
        );
        merge64(merge64(merge64(merge64(h, v.0), v.1), v.2), v.3)
    } else {
        PRIME64_5
    };
    avalanche64(tail64(b, full, add64(h0, (n % 0x1_0000_0000_0000_0000) as u64)))
}

} // verus!

//! What each intrinsic computes, as functions on lane sequences.
//!
//! These are the meanings the trusted specifications in `crate::x86` give
//! the intrinsics. Each is written lane by lane from Intel's pseudocode;
//! `crate::refs` has an executable, verified implementation of each, and
//! `tests/difftest.rs` checks the CPU against those on random inputs.
//! Functions named `*_lanes` act within each 16-byte lane (the 256-bit forms
//! of most shuffles and byte shifts work on the two halves separately).
use crate::lanes::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Signed scalars as lane bits
// ---------------------------------------------------------------------------
//
// Verus leaves `x as u8` unspecified when `x` is out of `u8`'s range, so the
// two's-complement reinterpretation of a signed argument is spelled out.

pub open spec fn u8_of_i8(x: i8) -> u8 {
    if x < 0 {
        (x + 0x100) as u8
    } else {
        x as u8
    }
}

pub open spec fn u16_of_i16(x: i16) -> u16 {
    if x < 0 {
        (x + 0x1_0000) as u16
    } else {
        x as u16
    }
}

pub open spec fn u32_of_i32(x: i32) -> u32 {
    if x < 0 {
        (x + 0x1_0000_0000) as u32
    } else {
        x as u32
    }
}

pub open spec fn u64_of_i64(x: i64) -> u64 {
    if x < 0 {
        (x + 0x1_0000_0000_0000_0000) as u64
    } else {
        x as u64
    }
}

// ---------------------------------------------------------------------------
// Bytewise
// ---------------------------------------------------------------------------

pub open spec fn add8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| ((a[i] + b[i]) % 256) as u8)
}

pub open spec fn sub8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| ((a[i] - b[i] + 256) % 256) as u8)
}

/// Saturating unsigned add (`adds_epu8`).
pub open spec fn adds_u8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if a[i] + b[i] > 255 { 255u8 } else { (a[i] + b[i]) as u8 })
}

/// Saturating unsigned subtract (`subs_epu8`).
pub open spec fn subs_u16(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(a.len(), |i: int| if a[i] < b[i] { 0u16 } else { (a[i] - b[i]) as u16 })
}

pub open spec fn subs_u8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if a[i] < b[i] { 0u8 } else { (a[i] - b[i]) as u8 })
}

/// A value clamped to a signed byte, `[-128, 127]`.
pub open spec fn sat_s8(x: int) -> int {
    if x < -0x80 {
        -0x80
    } else if x > 0x7f {
        0x7f
    } else {
        x
    }
}

/// Saturating signed add (`adds_epi8`): the bytes read as signed, their sum
/// clamped to `[-128, 127]`, as its two's-complement byte.
pub open spec fn adds_s8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| (sat_s8(s8(a[i]) + s8(b[i])) % 256) as u8)
}

/// Saturating signed subtract (`subs_epi8`): `a - b` on signed bytes,
/// clamped to `[-128, 127]`.
pub open spec fn subs_s8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| (sat_s8(s8(a[i]) - s8(b[i])) % 256) as u8)
}

pub open spec fn min_u8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if a[i] < b[i] { a[i] } else { b[i] })
}

pub open spec fn max_u8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if a[i] > b[i] { a[i] } else { b[i] })
}

/// Rounding-up average (`avg_epu8`).
pub open spec fn avg_u8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| ((a[i] + b[i] + 1) / 2) as u8)
}

/// Unsigned less-or-equal, as a byte mask.
pub open spec fn cmple_u8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if a[i] <= b[i] { 0xffu8 } else { 0u8 })
}

/// Whether `a & b` is nonzero, as a byte mask (`ptestm`).
pub open spec fn testm8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if a[i] & b[i] != 0 { 0xffu8 } else { 0u8 })
}

pub open spec fn and8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| a[i] & b[i])
}

pub open spec fn or8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| a[i] | b[i])
}

pub open spec fn xor8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| a[i] ^ b[i])
}

/// `!a & b` (`andnot`: the first operand is the one complemented).
pub open spec fn andnot8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| !a[i] & b[i])
}

pub open spec fn cmpeq8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if a[i] == b[i] { 0xffu8 } else { 0u8 })
}

/// Signed greater-than (`cmpgt_epi8`).
pub open spec fn cmpgt_s8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if s8(a[i]) > s8(b[i]) { 0xffu8 } else { 0u8 })
}

/// Picks `b`'s byte where the mask byte's top bit is set (`blendv_epi8`).
pub open spec fn blendv8(a: Seq<u8>, b: Seq<u8>, m: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if m[i] >= 128 { b[i] } else { a[i] })
}

/// The top bit of every byte, byte 0 in bit 0 (`movemask_epi8`).
pub open spec fn movemask(a: Seq<u8>) -> nat
    decreases a.len(),
{
    if a.len() == 0 {
        0
    } else {
        (if a[0] >= 128 {
            1nat
        } else {
            0nat
        }) + 2 * movemask(a.drop_first())
    }
}

pub open spec fn splat8(x: u8, n: nat) -> Seq<u8> {
    Seq::new(n, |i: int| x)
}

pub open spec fn splat16(x: u16, n: nat) -> Seq<u16> {
    Seq::new(n, |i: int| x)
}

pub open spec fn splat32(x: u32, n: nat) -> Seq<u32> {
    Seq::new(n, |i: int| x)
}

pub open spec fn splat64(x: u64, n: nat) -> Seq<u64> {
    Seq::new(n, |i: int| x)
}

/// `pshufb`: each byte of `b` picks a byte of `a` from the same 16-byte
/// lane by its low 4 bits, or zero when its top bit is set.
pub open spec fn shuffle8_lanes(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if b[i] >= 128 { 0u8 } else { a[(i / 16) * 16 + (b[i] % 16) as int] })
}

/// Shift each 16-byte lane up by `n` bytes, shifting in zeros (`bslli`).
pub open spec fn bslli_lanes(a: Seq<u8>, n: int) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if i % 16 >= n { a[i - n] } else { 0u8 })
}

/// Shift each 16-byte lane down by `n` bytes, shifting in zeros (`bsrli`).
pub open spec fn bsrli_lanes(a: Seq<u8>, n: int) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if i % 16 + n < 16 { a[i + n] } else { 0u8 })
}

/// `palignr`: per 16-byte lane, bytes `n..n+16` of `hi:lo` (`hi` above).
pub open spec fn alignr_lanes(hi: Seq<u8>, lo: Seq<u8>, n: int) -> Seq<u8> {
    Seq::new(
        lo.len(),
        |i: int|
            if i % 16 + n < 16 {
                lo[i + n]
            } else if i % 16 + n < 32 {
                hi[i + n - 16]
            } else {
                0u8
            },
    )
}

/// Interleave the low 8 bytes of each lane of `a` and `b`.
pub open spec fn unpacklo8_lanes(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(
        a.len(),
        |i: int|
            if i % 2 == 0 {
                a[(i / 16) * 16 + (i % 16) / 2]
            } else {
                b[(i / 16) * 16 + (i % 16) / 2]
            },
    )
}

/// Interleave the high 8 bytes of each lane of `a` and `b`.
pub open spec fn unpackhi8_lanes(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(
        a.len(),
        |i: int|
            if i % 2 == 0 {
                a[(i / 16) * 16 + 8 + (i % 16) / 2]
            } else {
                b[(i / 16) * 16 + 8 + (i % 16) / 2]
            },
    )
}

/// Interleave the low two 32-bit lanes of each 16-byte lane.
pub open spec fn unpacklo32_lanes(a: Seq<u32>, b: Seq<u32>) -> Seq<u32> {
    Seq::new(
        a.len(),
        |i: int|
            if i % 2 == 0 {
                a[(i / 4) * 4 + (i % 4) / 2]
            } else {
                b[(i / 4) * 4 + (i % 4) / 2]
            },
    )
}

/// Interleave the high two 32-bit lanes of each 16-byte lane.
pub open spec fn unpackhi32_lanes(a: Seq<u32>, b: Seq<u32>) -> Seq<u32> {
    Seq::new(
        a.len(),
        |i: int|
            if i % 2 == 0 {
                a[(i / 4) * 4 + 2 + (i % 4) / 2]
            } else {
                b[(i / 4) * 4 + 2 + (i % 4) / 2]
            },
    )
}

/// Interleave the low four 16-bit lanes of each 16-byte lane.
pub open spec fn unpacklo16_lanes(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(
        a.len(),
        |i: int|
            if i % 2 == 0 {
                a[(i / 8) * 8 + (i % 8) / 2]
            } else {
                b[(i / 8) * 8 + (i % 8) / 2]
            },
    )
}

/// Interleave the high four 16-bit lanes of each 16-byte lane.
pub open spec fn unpackhi16_lanes(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(
        a.len(),
        |i: int|
            if i % 2 == 0 {
                a[(i / 8) * 8 + 4 + (i % 8) / 2]
            } else {
                b[(i / 8) * 8 + 4 + (i % 8) / 2]
            },
    )
}

/// Interleave the high 64-bit lane of each 16-byte lane.
pub open spec fn unpackhi64_lanes(a: Seq<u64>, b: Seq<u64>) -> Seq<u64> {
    Seq::new(a.len(), |i: int| if i % 2 == 0 { a[i + 1] } else { b[i] })
}

/// Interleave the low 64-bit lane of each 16-byte lane.
pub open spec fn unpacklo64_lanes(a: Seq<u64>, b: Seq<u64>) -> Seq<u64> {
    Seq::new(a.len(), |i: int| if i % 2 == 0 { a[i] } else { b[i - 1] })
}

pub open spec fn sat_u8(x: int) -> u8 {
    if x < 0 {
        0u8
    } else if x > 255 {
        255u8
    } else {
        x as u8
    }
}

/// `packus_epi16`: signed 16-bit lanes to unsigned bytes, saturating; per
/// 16-byte lane, `a`'s eight then `b`'s eight.
pub open spec fn packus16_lanes(a: Seq<u16>, b: Seq<u16>) -> Seq<u8> {
    Seq::new(
        2 * a.len(),
        |i: int|
            if i % 16 < 8 {
                sat_u8(s16(a[(i / 16) * 8 + i % 16]))
            } else {
                sat_u8(s16(b[(i / 16) * 8 + i % 16 - 8]))
            },
    )
}

/// `packs_epi16`: signed 16-bit lanes to signed bytes, saturating to
/// `[-128, 127]`; per 16-byte lane, `a`'s eight then `b`'s eight.
pub open spec fn packs16_lanes(a: Seq<u16>, b: Seq<u16>) -> Seq<u8> {
    Seq::new(
        2 * a.len(),
        |i: int|
            if i % 16 < 8 {
                (sat_s8(s16(a[(i / 16) * 8 + i % 16])) % 256) as u8
            } else {
                (sat_s8(s16(b[(i / 16) * 8 + i % 16 - 8])) % 256) as u8
            },
    )
}

/// `sad_epu8`: per 8 bytes, the sum of absolute differences, in a 64-bit
/// lane.
pub open spec fn sad8(a: Seq<u8>, b: Seq<u8>) -> Seq<u64> {
    Seq::new(a.len() / 8, |j: int| sad_bytes(a.subrange(8 * j, 8 * j + 8), b.subrange(8 * j, 8 * j + 8)) as u64)
}

pub open spec fn absdiff(x: u8, y: u8) -> nat {
    if x >= y {
        (x - y) as nat
    } else {
        (y - x) as nat
    }
}

pub open spec fn sad_bytes(a: Seq<u8>, b: Seq<u8>) -> nat
    decreases a.len(),
{
    if a.len() == 0 {
        0
    } else {
        absdiff(a[0], b[0]) + sad_bytes(a.drop_first(), b.drop_first())
    }
}

// ---------------------------------------------------------------------------
// 16-bit lanes
// ---------------------------------------------------------------------------

pub open spec fn add16(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(a.len(), |i: int| ((a[i] + b[i]) % 0x10000) as u16)
}

pub open spec fn sub16(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(a.len(), |i: int| ((a[i] - b[i] + 0x10000) % 0x10000) as u16)
}

pub open spec fn mullo16(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(a.len(), |i: int| ((a[i] * b[i]) % 0x10000) as u16)
}

/// High half of the signed product (`mulhi_epi16`).
pub open spec fn mulhi_s16(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(a.len(), |i: int| (((s16(a[i]) * s16(b[i])) / 0x10000) % 0x10000) as u16)
}

/// Signed saturating doubling multiply, high half (`sqdmulh`): twice the
/// product over 2^16, saturated (only `-0x8000 * -0x8000` saturates).
pub open spec fn qdmulh_s16(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(a.len(), |i: int| (sat_s16((2 * s16(a[i]) * s16(b[i])) / 0x10000) % 0x10000) as u16)
}

/// The high 16 bits of the unsigned 32-bit products.
pub open spec fn mulhi_u16(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(a.len(), |i: int| ((a[i] as int * b[i] as int) / 0x10000) as u16)
}

pub open spec fn cmpeq16(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(a.len(), |i: int| if a[i] == b[i] { 0xffffu16 } else { 0u16 })
}

pub open spec fn srli16(a: Seq<u16>, n: int) -> Seq<u16> {
    Seq::new(a.len(), |i: int| if n > 15 { 0u16 } else { (a[i] as nat / pow2_spec(n as nat)) as u16 })
}

pub open spec fn slli16(a: Seq<u16>, n: int) -> Seq<u16> {
    Seq::new(a.len(), |i: int| if n > 15 { 0u16 } else { ((a[i] as nat * pow2_spec(n as nat)) % 0x10000) as u16 })
}

/// Arithmetic right shift (`srai_epi16`); shifts past 15 fill with the sign.
pub open spec fn srai16(a: Seq<u16>, n: int) -> Seq<u16> {
    Seq::new(a.len(), |i: int| ((s16(a[i]) / pow2_spec(if n > 15 { 15 } else { n as nat }) as int) % 0x10000) as u16)
}

/// Multiply signed 16-bit lanes and add adjacent pairs into 32-bit lanes
/// (`madd_epi16`).
pub open spec fn madd16(a: Seq<u16>, b: Seq<u16>) -> Seq<u32> {
    Seq::new(
        a.len() / 2,
        |i: int| ((s16(a[2 * i]) * s16(b[2 * i]) + s16(a[2 * i + 1]) * s16(b[2 * i + 1])) % 0x1_0000_0000) as u32,
    )
}

/// Multiply unsigned bytes of `a` by signed bytes of `b` and add adjacent
/// pairs into signed-saturated 16-bit lanes (`maddubs_epi16`).
pub open spec fn maddubs(a: Seq<u8>, b: Seq<u8>) -> Seq<u16> {
    Seq::new(a.len() / 2, |i: int| (sat_s16(a[2 * i] * s8(b[2 * i]) + a[2 * i + 1] * s8(b[2 * i + 1])) % 0x10000) as u16)
}

pub open spec fn sat_s16(x: int) -> int {
    if x < -0x8000 {
        -0x8000
    } else if x > 0x7fff {
        0x7fff
    } else {
        x
    }
}

// ---------------------------------------------------------------------------
// 32- and 64-bit lanes
// ---------------------------------------------------------------------------

pub open spec fn add32(a: Seq<u32>, b: Seq<u32>) -> Seq<u32> {
    Seq::new(a.len(), |i: int| ((a[i] + b[i]) % 0x1_0000_0000) as u32)
}

pub open spec fn sub32(a: Seq<u32>, b: Seq<u32>) -> Seq<u32> {
    Seq::new(a.len(), |i: int| ((a[i] - b[i] + 0x1_0000_0000) % 0x1_0000_0000) as u32)
}

pub open spec fn add64(a: Seq<u64>, b: Seq<u64>) -> Seq<u64> {
    Seq::new(a.len(), |i: int| ((a[i] + b[i]) % 0x1_0000_0000_0000_0000) as u64)
}

pub open spec fn cmpeq32(a: Seq<u32>, b: Seq<u32>) -> Seq<u32> {
    Seq::new(a.len(), |i: int| if a[i] == b[i] { 0xffff_ffffu32 } else { 0u32 })
}

/// Signed greater-than (`cmpgt_epi32`).
pub open spec fn cmpgt_s32(a: Seq<u32>, b: Seq<u32>) -> Seq<u32> {
    Seq::new(a.len(), |i: int| if s32(a[i]) > s32(b[i]) { 0xffff_ffffu32 } else { 0u32 })
}

pub open spec fn srli32(a: Seq<u32>, n: int) -> Seq<u32> {
    Seq::new(a.len(), |i: int| if n > 31 { 0u32 } else { (a[i] as nat / pow2_spec(n as nat)) as u32 })
}

pub open spec fn slli32(a: Seq<u32>, n: int) -> Seq<u32> {
    Seq::new(
        a.len(),
        |i: int| if n > 31 { 0u32 } else { ((a[i] as nat * pow2_spec(n as nat)) % 0x1_0000_0000) as u32 },
    )
}

pub open spec fn srli64(a: Seq<u64>, n: int) -> Seq<u64> {
    Seq::new(a.len(), |i: int| if n > 63 { 0u64 } else { (a[i] as nat / pow2_spec(n as nat)) as u64 })
}

pub open spec fn slli64(a: Seq<u64>, n: int) -> Seq<u64> {
    Seq::new(
        a.len(),
        |i: int| if n > 63 { 0u64 } else { ((a[i] as nat * pow2_spec(n as nat)) % 0x1_0000_0000_0000_0000) as u64 },
    )
}

/// `pshufd`: per 16-byte lane, 32-bit lane `i` takes lane `imm[2i+1:2i]`.
pub open spec fn shuffle32_lanes(a: Seq<u32>, imm: int) -> Seq<u32> {
    Seq::new(a.len(), |i: int| a[(i / 4) * 4 + (imm / pow2_spec(2 * (i % 4) as nat) as int) % 4])
}

/// `vpermd`: 32-bit lane `i` takes lane `idx[i] % 8` of `a`.
pub open spec fn permvar32(a: Seq<u32>, idx: Seq<u32>) -> Seq<u32> {
    Seq::new(a.len(), |i: int| a[(idx[i] % 8) as int])
}

/// `2^n`, as `vstd::arithmetic::power2::pow2` (restated so this crate's
/// specs do not depend on vstd's opaque definitions).
pub open spec fn pow2_spec(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        2 * pow2_spec((n - 1) as nat)
    }
}

// ---------------------------------------------------------------------------
// NEON-only lane operations
// ---------------------------------------------------------------------------

/// `ushr` by `n` on each byte (`vshrq_n_u8`).
pub open spec fn shr8(a: Seq<u8>, n: int) -> Seq<u8> {
    Seq::new(a.len(), |i: int| (a[i] as nat / pow2_spec(n as nat)) as u8)
}

/// `uabd` on each byte (`vabdq_u8`): the absolute difference of two
/// unsigned bytes.
pub open spec fn abd_u8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| absdiff(a[i], b[i]) as u8)
}

/// `sshr` by `n` on each byte (`vshrq_n_s8`): the byte read as signed,
/// divided by `2^n` rounding down, as its two's-complement byte.
pub open spec fn sra8(a: Seq<u8>, n: int) -> Seq<u8> {
    Seq::new(a.len(), |i: int| ((s8(a[i]) / pow2_spec(n as nat) as int) % 256) as u8)
}

/// `tbl` with one 16-byte table (`vqtbl1q_u8`): an index past the table
/// gives 0.
pub open spec fn tbl1(t: Seq<u8>, idx: Seq<u8>) -> Seq<u8> {
    Seq::new(idx.len(), |i: int| if idx[i] < 16 { t[idx[i] as int] } else { 0u8 })
}

/// `uzp1` on bytes (`vuzp1q_u8`): the even bytes of `a`, then of `b`.
pub open spec fn uzp1_8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| if i < a.len() / 2 { a[2 * i] } else { b[2 * i - a.len()] })
}

/// The low 8 bits of the bytewise products (`mul` on bytes).
pub open spec fn mullo8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| ((a[i] * b[i]) % 256) as u8)
}

/// The low 32 bits of the 32-bit products (`mul` on 32-bit lanes).
pub open spec fn mullo32(a: Seq<u32>, b: Seq<u32>) -> Seq<u32> {
    Seq::new(a.len(), |i: int| ((a[i] * b[i]) % 0x1_0000_0000) as u32)
}

/// `uaddlp` on bytes (`vpaddlq_u8`): the sum of each adjacent pair, as a
/// 16-bit lane. Nothing wraps.
pub open spec fn paddl8(a: Seq<u8>) -> Seq<u16> {
    Seq::new(a.len() / 2, |i: int| (a[2 * i] + a[2 * i + 1]) as u16)
}

/// `uaddlp` on 16-bit lanes (`vpaddlq_u16`).
pub open spec fn paddl16(a: Seq<u16>) -> Seq<u32> {
    Seq::new(a.len() / 2, |i: int| (a[2 * i] + a[2 * i + 1]) as u32)
}

/// `uaddlp` on 32-bit lanes (`vpaddlq_u32`).
pub open spec fn paddl32(a: Seq<u32>) -> Seq<u64> {
    Seq::new(a.len() / 2, |i: int| (a[2 * i] + a[2 * i + 1]) as u64)
}

/// `addp` on bytes (`vpaddq_u8`): sums of adjacent pairs of `a`, then of
/// `b`, modulo 256.
pub open spec fn padd8(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(
        a.len(),
        |i: int|
            if i < a.len() / 2 {
                ((a[2 * i] + a[2 * i + 1]) % 256) as u8
            } else {
                ((b[2 * i - a.len()] + b[2 * i - a.len() + 1]) % 256) as u8
            },
    )
}

// ---------------------------------------------------------------------------
// Mask registers and bit instructions
// ---------------------------------------------------------------------------

/// The positions of the set bits of `m` below `n`, ascending.
pub open spec fn set_bits(m: u64, n: nat) -> Seq<int>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        let p = set_bits(m, (n - 1) as nat);
        if (m >> ((n - 1) as u64)) & 1u64 == 1u64 {
            p.push(n - 1)
        } else {
            p
        }
    }
}

/// The number of set bits (`popcnt`).
pub open spec fn popcount64(m: u64) -> nat {
    set_bits(m, 64).len()
}

/// `vpcompressb` with zero masking: the lanes of `a` that `m` selects,
/// packed into the low lanes in order; the other lanes are zero.
pub open spec fn compress8(m: u64, a: Seq<u8>) -> Seq<u8> {
    let p = set_bits(m, a.len());
    Seq::new(a.len(), |j: int| if j < p.len() { a[p[j]] } else { 0u8 })
}

/// Zero-extends bytes to 32-bit lanes (`vpmovzxbd`).
pub open spec fn zext8_32(a: Seq<u8>) -> Seq<u32> {
    Seq::new(a.len(), |i: int| a[i] as u32)
}

/// `packs_epi32`: signed 32-bit lanes to signed 16-bit lanes, saturating;
/// per 128-bit lane, `a`'s four then `b`'s four.
pub open spec fn packs32_lanes(a: Seq<u32>, b: Seq<u32>) -> Seq<u16> {
    Seq::new(
        2 * a.len(),
        |i: int|
            if i % 8 < 4 {
                (sat_s16(s32(a[(i / 8) * 4 + i % 8])) % 0x10000) as u16
            } else {
                (sat_s16(s32(b[(i / 8) * 4 + i % 8 - 4])) % 0x10000) as u16
            },
    )
}

/// Carry-less multiplication, low 64 bits: the XOR of `a << i` over the set
/// bits `i < n` of `b` (`pclmulqdq`).
pub open spec fn clmul_lo(a: u64, b: u64, n: nat) -> u64
    decreases n,
{
    if n == 0 {
        0
    } else {
        clmul_lo(a, b, (n - 1) as nat) ^ (if (b >> ((n - 1) as u64)) & 1u64 == 1u64 {
            a << ((n - 1) as u64)
        } else {
            0
        })
    }
}

// ---------------------------------------------------------------------------
// Integer transforms on NEON (the JPEG inverse DCT)
// ---------------------------------------------------------------------------

/// Absolute value of signed 16-bit lanes (`abs`), read unsigned: `-0x8000`
/// gives `0x8000`.
pub open spec fn abs16(a: Seq<u16>) -> Seq<u16> {
    Seq::new(a.len(), |i: int| if a[i] <= 0x8000 { a[i] } else { (0x10000 - a[i]) as u16 })
}

/// Unsigned 16-bit maximum (`umax`).
pub open spec fn max_u16(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(a.len(), |i: int| if a[i] >= b[i] { a[i] } else { b[i] })
}

/// The signed products of the low half of the 16-bit lanes, as 32-bit
/// lanes (`smull`).
pub open spec fn mull_lo_s16(a: Seq<u16>, b: Seq<u16>) -> Seq<u32> {
    Seq::new(a.len() / 2, |i: int| ((s16(a[i]) * s16(b[i])) % 0x1_0000_0000) as u32)
}

/// The signed products of the high half of the 16-bit lanes, as 32-bit
/// lanes (`smull2`).
pub open spec fn mull_hi_s16(a: Seq<u16>, b: Seq<u16>) -> Seq<u32> {
    Seq::new(
        a.len() / 2,
        |i: int| ((s16(a[a.len() / 2 + i]) * s16(b[a.len() / 2 + i])) % 0x1_0000_0000) as u32,
    )
}

/// Rounding arithmetic shift right of signed 32-bit lanes by `n` (1 to 31)
/// (`srshr`): `(x + 2^(n-1)) / 2^n` rounded down, the sum taken without
/// overflow.
pub open spec fn rshr_s32(a: Seq<u32>, n: int) -> Seq<u32> {
    Seq::new(
        a.len(),
        |i: int|
            (((s32(a[i]) + pow2_spec((n - 1) as nat)) / pow2_spec(n as nat) as int) % 0x1_0000_0000) as u32,
    )
}

/// The odd 16-bit lanes of `a`, then those of `b` (`uzp2`).
pub open spec fn uzp2_16(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(a.len(), |i: int| if i < a.len() / 2 { a[2 * i + 1] } else { b[2 * i + 1 - a.len()] })
}

/// Three byte vectors interleaved: `a[0], b[0], c[0], a[1], ...` (what
/// `st3` writes).
pub open spec fn interleave3(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>) -> Seq<u8> {
    Seq::new(
        3 * a.len(),
        |j: int|
            if j % 3 == 0 {
                a[j / 3]
            } else if j % 3 == 1 {
                b[j / 3]
            } else {
                c[j / 3]
            },
    )
}

// ---------------------------------------------------------------------------
// The 16-bit inverse DCT on NEON
// ---------------------------------------------------------------------------

/// The signed products of the low half of the 16-bit lanes of `a` with
/// lane `l` of `c`, as 32-bit lanes (`smull` by element).
pub open spec fn mull_lo_lane_s16(a: Seq<u16>, c: Seq<u16>, l: int) -> Seq<u32> {
    Seq::new(a.len() / 2, |i: int| ((s16(a[i]) * s16(c[l])) % 0x1_0000_0000) as u32)
}

/// The signed products of the high half of the 16-bit lanes of `a` with
/// lane `l` of `c`, as 32-bit lanes (`smull2` by element).
pub open spec fn mull_hi_lane_s16(a: Seq<u16>, c: Seq<u16>, l: int) -> Seq<u32> {
    Seq::new(a.len() / 2, |i: int| ((s16(a[a.len() / 2 + i]) * s16(c[l])) % 0x1_0000_0000) as u32)
}

/// `acc` plus the signed products of the low half of the 16-bit lanes of
/// `a` with lane `l` of `c`, wrapping (`smlal` by element).
pub open spec fn mlal_lo_lane_s16(acc: Seq<u32>, a: Seq<u16>, c: Seq<u16>, l: int) -> Seq<u32> {
    Seq::new(acc.len(), |i: int| ((acc[i] + s16(a[i]) * s16(c[l])) % 0x1_0000_0000) as u32)
}

/// `acc` plus the signed products of the high half of the 16-bit lanes of
/// `a` with lane `l` of `c`, wrapping (`smlal2` by element).
pub open spec fn mlal_hi_lane_s16(acc: Seq<u32>, a: Seq<u16>, c: Seq<u16>, l: int) -> Seq<u32> {
    Seq::new(acc.len(), |i: int| ((acc[i] + s16(a[acc.len() + i]) * s16(c[l])) % 0x1_0000_0000) as u32)
}

/// Rounding shift right of signed 32-bit lanes by `n` (1 to 16), keeping
/// the low 16 bits of each (`rshrn`): `(x + 2^(n-1)) / 2^n` rounded down,
/// the sum taken without overflow, modulo 2^16.
pub open spec fn rshrn_s32(a: Seq<u32>, n: int) -> Seq<u16> {
    Seq::new(
        a.len(),
        |i: int| (((s32(a[i]) + pow2_spec((n - 1) as nat)) / pow2_spec(n as nat) as int) % 0x1_0000) as u16,
    )
}

/// Unsigned saturating 16-bit addition (`uqadd`).
pub open spec fn adds_u16(a: Seq<u16>, b: Seq<u16>) -> Seq<u16> {
    Seq::new(a.len(), |i: int| if a[i] + b[i] > 0xffff { 0xffffu16 } else { (a[i] + b[i]) as u16 })
}

/// The sum of 16-bit lanes (`uaddlv`).
pub open spec fn sum_u16(a: Seq<u16>) -> int
    decreases a.len(),
{
    if a.len() == 0 {
        0
    } else {
        sum_u16(a.drop_last()) + a.last()
    }
}

} // verus!

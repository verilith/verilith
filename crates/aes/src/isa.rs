//! What the instructions compute (TRUSTED): the specification the kernels
//! are proven against, transcribed from the vendors' pseudocode, as
//! functions on a 128-bit register's 16 bytes, byte 0 first (bits 7:0 of
//! an x86 register, byte element 0 of an Arm one). A register loaded from
//! memory holds the bytes in memory order, so a block of FIPS 197's state
//! (byte r + 4c is row r, column c) is the register's bytes as they are.
//!
//! - x86-64 AES-NI and VAES: `AESENC` and `AESENCLAST` (Intel 64 and IA-32
//!   Architectures Software Developer's Manual, volume 2: their
//!   "Operation" sections, which apply FIPS 197's ShiftRows, SubBytes and
//!   MixColumns). `VAESENC` and `VAESENCLAST` do the same on each 128-bit
//!   lane.
//! - AArch64 FEAT_AES: `AESE` (AddRoundKey, then ShiftRows, then SubBytes)
//!   and `AESMC` (MixColumns), as the Arm Architecture Reference Manual
//!   for A-profile defines them.
//! - Carry-less multiplication: `PCLMULQDQ` (and `VPCLMULQDQ` per lane)
//!   and AArch64 `PMULL`/`PMULL2` on 64-bit elements: the carry-less
//!   product of two 64-bit operands, `gf::clmul`.
//! - Byte shuffles (`PSHUFB`), 32-bit lane addition (`PADDD`), 64-bit lane
//!   shifts (`PSLLQ`, `PSRLQ`) and whole-register byte shifts (`PSLLDQ`,
//!   `PSRLDQ`), on the register as a 128-bit integer.
//!
//! Each is also checked against the CPU: `tests/isa.rs` runs every
//! wrapper on random operands against verified reference functions.
#![allow(unused_imports)]
use crate::gf::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The sixteen bytes of a register, byte 0 (bits 7:0) first.
pub open spec fn bytes16(v: u128) -> Seq<u8> {
    Seq::new(16, |k: int| (v >> (8 * k) as u128) as u8)
}

/// The register holding sixteen bytes, byte 0 first: the inverse of
/// [`bytes16`].
pub open spec fn le128(b: Seq<u8>) -> u128 {
    (b[15] as u128) << 120u128 | (b[14] as u128) << 112u128 | (b[13] as u128) << 104u128 | (b[12] as u128)
        << 96u128 | (b[11] as u128) << 88u128 | (b[10] as u128) << 80u128 | (b[9] as u128) << 72u128 | (
    b[8] as u128) << 64u128 | (b[7] as u128) << 56u128 | (b[6] as u128) << 48u128 | (b[5] as u128)
        << 40u128 | (b[4] as u128) << 32u128 | (b[3] as u128) << 24u128 | (b[2] as u128) << 16u128 | (
    b[1] as u128) << 8u128 | (b[0] as u128)
}

// ---------------------------------------------------------------------------
// AES
// ---------------------------------------------------------------------------

/// `AESENC state, roundkey`: ShiftRows, SubBytes, MixColumns, then XOR
/// with the round key.
#[verifier::opaque]
pub open spec fn aesenc(s: Seq<u8>, k: Seq<u8>) -> Seq<u8> {
    add_round_key(mix_columns(sub_bytes(shift_rows(s))), k)
}

/// `AESENCLAST state, roundkey`: ShiftRows, SubBytes, then XOR with the
/// round key.
#[verifier::opaque]
pub open spec fn aesenclast(s: Seq<u8>, k: Seq<u8>) -> Seq<u8> {
    add_round_key(sub_bytes(shift_rows(s)), k)
}

/// `AESE Vd, Vn`: AddRoundKey (Vd XOR Vn), ShiftRows, SubBytes.
#[verifier::opaque]
pub open spec fn aese(d: Seq<u8>, k: Seq<u8>) -> Seq<u8> {
    sub_bytes(shift_rows(add_round_key(d, k)))
}

/// `AESMC Vd, Vn`: MixColumns.
pub open spec fn aesmc(d: Seq<u8>) -> Seq<u8> {
    mix_columns(d)
}

// ---------------------------------------------------------------------------
// Integer operations on the register as a 128-bit integer
// ---------------------------------------------------------------------------

/// `PSHUFB a, m`: byte k of the result is byte `m[k] & 15` of `a`, or 0 if
/// bit 7 of `m[k]` is set.
pub open spec fn pshufb(a: Seq<u8>, m: Seq<u8>) -> Seq<u8> {
    Seq::new(16, |k: int| if m[k] & 0x80 != 0 { 0u8 } else { a[(m[k] & 15) as int] })
}

/// 32-bit lane j of a register.
pub open spec fn lane32(v: u128, j: int) -> u32 {
    (v >> (32 * j) as u128) as u32
}

/// `PADDD a, b`: the four 32-bit lanes added, each modulo 2^32.
pub open spec fn add32x4(a: u128, b: u128) -> u128 {
    (lane32(a, 0).wrapping_add(lane32(b, 0)) as u128) | (lane32(a, 1).wrapping_add(lane32(b, 1)) as u128) << 32u128
        | (lane32(a, 2).wrapping_add(lane32(b, 2)) as u128) << 64u128 | (lane32(a, 3).wrapping_add(lane32(b, 3)) as u128)
        << 96u128
}

/// `PSLLQ a, n`: each 64-bit lane shifted left by n < 64.
pub open spec fn sll64x2(a: u128, n: u64) -> u128 {
    ((hi64(a) << n) as u128) << 64u128 | ((lo64(a) << n) as u128)
}

/// `PSRLQ a, n`: each 64-bit lane shifted right by n < 64.
pub open spec fn srl64x2(a: u128, n: u64) -> u128 {
    ((hi64(a) >> n) as u128) << 64u128 | ((lo64(a) >> n) as u128)
}

/// The 64-bit half of `a` that bit `sel` of an immediate picks: the low
/// one if it is 0, the high one if it is 1.
pub open spec fn half(a: u128, sel: bool) -> u64 {
    if sel {
        hi64(a)
    } else {
        lo64(a)
    }
}

/// `PCLMULQDQ a, b, imm`: the carry-less product of the half of `a` that
/// bit 0 of `imm` picks and the half of `b` that bit 4 picks.
pub open spec fn pclmul(a: u128, b: u128, imm: i32) -> u128 {
    clmul(half(a, imm & 1 != 0), half(b, imm & 0x10 != 0))
}

} // verus!

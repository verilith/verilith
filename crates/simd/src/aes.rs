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
//! Each is also checked against the CPU: verilith-aes's `tests/isa.rs` runs every
//! wrapper on random operands against verified reference functions.
#![allow(unused_imports, missing_docs)]
#[cfg(verus_only)]
pub use crate::clmul::{clmul, clmul_n, hi64, lo64};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// FIPS 197 §5.1.1: SubBytes. The S-box, as Table 4 gives it.
// ---------------------------------------------------------------------------

/// The S-box (Table 4), indexed by the input byte. `tests/vectors.rs`
/// derives it again from §5.1.1's definition (the multiplicative inverse
/// in GF(2^8), then the affine transformation).
pub const SBOX: [u8; 256] = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
];

pub open spec fn sbox(b: u8) -> u8 {
    SBOX[b as int]
}

// ---------------------------------------------------------------------------
// FIPS 197 §5.1: the round transformations, on the state as 16 bytes.
// §3.4: the input bytes fill the state column by column, so byte r + 4c is
// s[r, c]: row r, column c.
// ---------------------------------------------------------------------------

/// SUBBYTES() (§5.1.1): the S-box on every byte.
pub open spec fn sub_bytes(s: Seq<u8>) -> Seq<u8> {
    Seq::new(16, |i: int| sbox(s[i]))
}

/// SHIFTROWS() (§5.1.2): row r is rotated left by r, s'[r, c] = s[r, (c + r) mod 4].
pub open spec fn shift_rows(s: Seq<u8>) -> Seq<u8> {
    Seq::new(16, |i: int| s[i % 4 + 4 * ((i / 4 + i % 4) % 4)])
}

/// XTIMES() (§4.2): multiplication by x (0x02) in GF(2^8), modulo
/// m(x) = x^8 + x^4 + x^3 + x + 1.
pub open spec fn xtimes(b: u8) -> u8 {
    if b & 0x80 == 0 {
        ((b as u16) << 1u16) as u8
    } else {
        (((b as u16) << 1u16) as u8) ^ 0x1b
    }
}

/// {03} • b: (x + 1) times b.
pub open spec fn times3(b: u8) -> u8 {
    xtimes(b) ^ b
}

/// MIXCOLUMNS() (§5.1.3), equation (5.7): each column times the matrix
/// with rows (02 03 01 01), (01 02 03 01), (01 01 02 03), (03 01 01 02).
pub open spec fn mix_columns(s: Seq<u8>) -> Seq<u8> {
    Seq::new(
        16,
        |i: int|
            {
                let c = 4 * (i / 4);
                let r = i % 4;
                let s0 = s[c + r];
                let s1 = s[c + (r + 1) % 4];
                let s2 = s[c + (r + 2) % 4];
                let s3 = s[c + (r + 3) % 4];
                xtimes(s0) ^ times3(s1) ^ s2 ^ s3
            },
    )
}

/// ADDROUNDKEY() (§5.1.4): XOR with the round key's 16 bytes.
pub open spec fn add_round_key(s: Seq<u8>, k: Seq<u8>) -> Seq<u8> {
    Seq::new(16, |i: int| s[i] ^ k[i])
}



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

//! The standards, as spec functions (TRUSTED): AES-128 and AES-256 as
//! FIPS 197 (2001, updated 2023) defines them, and the Galois/Counter
//! Mode of NIST SP 800-38D (2007) with 96-bit IVs and 128-bit tags.
//!
//! Everything the proofs show is stated in terms of these functions, so
//! they are the part to review against the documents. Section numbers are
//! FIPS 197's (upd1, 2023) and SP 800-38D's.
//!
//! Narrowings, all of which TLS 1.3 and QUIC stay inside:
//! - AES-192 is left out (Nk = 6). No TLS 1.3 suite uses it.
//! - GCM takes 96-bit IVs only (§7.1 step 2, first case), so J0 is
//!   IV || 0^31 || 1, and 128-bit tags only (t = 128).
//! - Lengths are whole bytes, and the plaintext is at most 2^32 - 2
//!   blocks (§5.2.1.1: len(P) <= 2^39 - 256 bits). Then the 32-bit counter
//!   never wraps, though the spec's `inc32` still says what it would do.
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Bytes and 128-bit blocks
// ---------------------------------------------------------------------------

/// `n` zero bytes.
pub open spec fn zeros(n: nat) -> Seq<u8> {
    Seq::new(n, |_i: int| 0u8)
}

/// Byte-wise XOR of two sequences of the same length.
pub open spec fn xor_bytes(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::new(a.len(), |i: int| a[i] ^ b[i])
}

/// A 16-byte string as a 128-bit integer, byte 0 most significant. SP
/// 800-38D numbers the bits of a block from the left (§6.1: bit 0 is the
/// leftmost, the most significant bit of byte 0), so this is the block
/// with its bit i at integer bit 127 - i.
pub open spec fn be128(b: Seq<u8>) -> u128 {
    (b[0] as u128) << 120u128 | (b[1] as u128) << 112u128 | (b[2] as u128) << 104u128 | (b[3] as u128)
        << 96u128 | (b[4] as u128) << 88u128 | (b[5] as u128) << 80u128 | (b[6] as u128) << 72u128 | (
    b[7] as u128) << 64u128 | (b[8] as u128) << 56u128 | (b[9] as u128) << 48u128 | (b[10] as u128)
        << 40u128 | (b[11] as u128) << 32u128 | (b[12] as u128) << 24u128 | (b[13] as u128) << 16u128 | (
    b[14] as u128) << 8u128 | (b[15] as u128)
}

/// The 16 bytes of a block, most significant first: the inverse of
/// [`be128`].
pub open spec fn be_bytes(v: u128) -> Seq<u8> {
    Seq::new(16, |i: int| (v >> (8 * (15 - i)) as u128) as u8)
}

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

/// One of rounds 1 to Nr - 1 of CIPHER() (§5.1, Algorithm 1, lines 4-7).
#[verifier::opaque]
pub open spec fn round(s: Seq<u8>, k: Seq<u8>) -> Seq<u8> {
    add_round_key(mix_columns(shift_rows(sub_bytes(s))), k)
}

/// The last round, without MIXCOLUMNS() (lines 9-11).
#[verifier::opaque]
pub open spec fn final_round(s: Seq<u8>, k: Seq<u8>) -> Seq<u8> {
    add_round_key(shift_rows(sub_bytes(s)), k)
}

// ---------------------------------------------------------------------------
// FIPS 197 §5.2: KEYEXPANSION(), Algorithm 2. A word is 4 bytes; here a
// u32 whose byte j (bits 8j..8j+7) is the word's byte a_j, so that the
// word's bytes in memory order are its little-endian bytes.
// ---------------------------------------------------------------------------

/// Byte j of a word.
pub open spec fn wbyte(w: u32, j: int) -> u8 {
    (w >> (8 * j) as u32) as u8
}

/// The word [a0, a1, a2, a3].
pub open spec fn word(a0: u8, a1: u8, a2: u8, a3: u8) -> u32 {
    (a0 as u32) | (a1 as u32) << 8u32 | (a2 as u32) << 16u32 | (a3 as u32) << 24u32
}

/// ROTWORD([a0, a1, a2, a3]) = [a1, a2, a3, a0] (5.10).
pub open spec fn rot_word(w: u32) -> u32 {
    word(wbyte(w, 1), wbyte(w, 2), wbyte(w, 3), wbyte(w, 0))
}

/// SUBWORD() (5.11): the S-box on each byte.
pub open spec fn sub_word(w: u32) -> u32 {
    word(sbox(wbyte(w, 0)), sbox(wbyte(w, 1)), sbox(wbyte(w, 2)), sbox(wbyte(w, 3)))
}

/// Rcon[j] = [x^(j-1), 0, 0, 0] for j = 1..10 (Table 5).
pub open spec fn rcon(j: int) -> u32 {
    if j == 1 {
        0x01
    } else if j == 2 {
        0x02
    } else if j == 3 {
        0x04
    } else if j == 4 {
        0x08
    } else if j == 5 {
        0x10
    } else if j == 6 {
        0x20
    } else if j == 7 {
        0x40
    } else if j == 8 {
        0x80
    } else if j == 9 {
        0x1b
    } else {
        0x36
    }
}

/// Nk: the key length in words, 4 or 8.
pub open spec fn nk(key: Seq<u8>) -> int {
    key.len() as int / 4
}

/// Nr: the number of rounds, 10 or 14 (Table 3).
pub open spec fn nr(key: Seq<u8>) -> int {
    nk(key) + 6
}

/// The key lengths this crate takes: AES-128 and AES-256.
pub open spec fn key_ok(key: Seq<u8>) -> bool {
    key.len() == 16 || key.len() == 32
}

/// w[i] of the expanded key (Algorithm 2), 0 <= i < 4 * (Nr + 1).
pub open spec fn w(key: Seq<u8>, i: int) -> u32
    decreases i,
{
    if i < 0 || nk(key) < 1 {
        0
    } else if i < nk(key) {
        word(key[4 * i], key[4 * i + 1], key[4 * i + 2], key[4 * i + 3])
    } else {
        let temp = w(key, i - 1);
        let t = if i % nk(key) == 0 {
            sub_word(rot_word(temp)) ^ rcon(i / nk(key))
        } else if nk(key) > 6 && i % nk(key) == 4 {
            sub_word(temp)
        } else {
            temp
        };
        w(key, i - nk(key)) ^ t
    }
}

/// The round key of round r: w[4r..4r+3] as 16 bytes (Algorithm 1, the
/// argument of ADDROUNDKEY()).
pub open spec fn round_key(key: Seq<u8>, r: int) -> Seq<u8> {
    Seq::new(16, |i: int| wbyte(w(key, 4 * r + i / 4), i % 4))
}

// ---------------------------------------------------------------------------
// FIPS 197 §5.1: CIPHER(), Algorithm 1.
// ---------------------------------------------------------------------------

/// The state after rounds 0 to n - 1 of Algorithm 1 (line 3, then lines
/// 4-7 for rounds 1 to n - 1), 1 <= n <= Nr.
#[verifier::opaque]
pub open spec fn rounds(key: Seq<u8>, input: Seq<u8>, n: int) -> Seq<u8>
    decreases n,
{
    if n <= 1 {
        add_round_key(input, round_key(key, 0))
    } else {
        round(rounds(key, input, n - 1), round_key(key, n - 1))
    }
}

/// CIPHER(in, Nr, w): the 16-byte block `input` encrypted under `key`.
#[verifier::opaque]
pub open spec fn cipher(key: Seq<u8>, input: Seq<u8>) -> Seq<u8> {
    final_round(rounds(key, input, nr(key)), round_key(key, nr(key)))
}

// ---------------------------------------------------------------------------
// SP 800-38D §6.3: multiplication in GF(2^128), Algorithm 1, on blocks as
// [`be128`] integers (bit i of the block is integer bit 127 - i).
// ---------------------------------------------------------------------------

/// R = 11100001 || 0^120.
pub open spec fn gf_r() -> u128 {
    0xe1u128 << 120u128
}

/// Algorithm 1 step 3's update of V: V >> 1 if LSB_1(V) = 0, else
/// (V >> 1) XOR R. The rightmost bit, LSB_1(V) = V_127, is integer bit 0.
pub open spec fn gf_shift(v: u128) -> u128 {
    if v & 1 == 0 {
        v >> 1u128
    } else {
        (v >> 1u128) ^ gf_r()
    }
}

/// (Z_n, V_n) of Algorithm 1: Z_0 = 0, V_0 = Y, and for i = 0..n-1,
/// Z_{i+1} = Z_i if x_i = 0, else Z_i XOR V_i; V_{i+1} = gf_shift(V_i).
pub open spec fn gf_steps(x: u128, y: u128, n: nat) -> (u128, u128)
    decreases n,
{
    if n == 0 {
        (0, y)
    } else {
        let (z, v) = gf_steps(x, y, (n - 1) as nat);
        let i = (n - 1) as u128;
        let z1 = if (x >> (127 - i) as u128) & 1 == 0 {
            z
        } else {
            z ^ v
        };
        (z1, gf_shift(v))
    }
}

/// X • Y = Z_128.
pub open spec fn gf_mul(x: u128, y: u128) -> u128 {
    gf_steps(x, y, 128).0
}

// ---------------------------------------------------------------------------
// SP 800-38D §6.4: GHASH, §6.5: GCTR, §7: GCM-AE and GCM-AD.
// ---------------------------------------------------------------------------

/// Y_m of GHASH_H(X_1 || ... || X_m) (Algorithm 2), started from Y = y
/// rather than Y_0 = 0: Y_i = (Y_{i-1} XOR X_i) • H.
pub open spec fn ghash_from(h: u128, y: u128, xs: Seq<u128>) -> u128
    decreases xs.len(),
{
    if xs.len() == 0 {
        y
    } else {
        ghash_from(h, gf_mul(y ^ xs[0], h), xs.drop_first())
    }
}

/// GHASH_H(X) (Algorithm 2).
pub open spec fn ghash(h: u128, xs: Seq<u128>) -> u128 {
    ghash_from(h, 0, xs)
}

/// The string padded with 0^v to whole blocks, as blocks: A || 0^v and
/// C || 0^u in §7.1 step 5.
pub open spec fn pad_blocks(s: Seq<u8>) -> Seq<u128>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s.len() <= 16 {
        seq![be128(s + zeros((16 - s.len()) as nat))]
    } else {
        seq![be128(s.take(16))] + pad_blocks(s.skip(16))
    }
}

/// [len(A)]_64 || [len(C)]_64: the lengths in bits.
pub open spec fn len_block(alen: nat, clen: nat) -> u128 {
    (((8 * alen) % 0x1_0000_0000_0000_0000) as u128) << 64u128 | ((8 * clen) % 0x1_0000_0000_0000_0000) as u128
}

/// S of §7.1 step 5 (and §7.2 step 6): GHASH_H(A || 0^v || C || 0^u ||
/// [len(A)]_64 || [len(C)]_64).
pub open spec fn gcm_s(h: u128, aad: Seq<u8>, c: Seq<u8>) -> u128 {
    ghash(h, pad_blocks(aad) + pad_blocks(c) + seq![len_block(aad.len(), c.len())])
}

/// H = CIPH_K(0^128) (§7.1 step 1), as a block.
pub open spec fn hash_key(key: Seq<u8>) -> u128 {
    be128(cipher(key, zeros(16)))
}

/// The counter block IV || [c mod 2^32]_32: J0 for c = 1 (§7.1 step 2,
/// for a 96-bit IV) and inc32 applied c - 1 times to it (§6.2) otherwise.
#[verifier::opaque]
pub open spec fn counter_block(iv: Seq<u8>, c: int) -> Seq<u8> {
    let c32 = c % 0x1_0000_0000;
    iv + seq![(c32 / 0x100_0000) as u8, ((c32 / 0x1_0000) % 0x100) as u8, ((c32 / 0x100) % 0x100) as u8, (c32 % 0x100) as u8]
}

/// GCTR_K(inc32(J0), X) (§6.5, Algorithm 3, and §7.1 step 3): block i of X
/// (from 0) XOR CIPH_K(CB_{i+1}), CB_1 = inc32(J0), the last block
/// truncated (MSB_u).
pub open spec fn gctr(key: Seq<u8>, iv: Seq<u8>, x: Seq<u8>) -> Seq<u8> {
    Seq::new(x.len(), |i: int| x[i] ^ cipher(key, counter_block(iv, 2 + i / 16))[i % 16])
}

/// T = MSB_128(GCTR_K(J0, S)) = CIPH_K(J0) XOR S (§7.1 step 6).
pub open spec fn gcm_tag(key: Seq<u8>, iv: Seq<u8>, aad: Seq<u8>, c: Seq<u8>) -> Seq<u8> {
    xor_bytes(cipher(key, counter_block(iv, 1)), be_bytes(gcm_s(hash_key(key), aad, c)))
}

/// The largest plaintext: 2^32 - 2 blocks (§5.2.1.1).
pub open spec fn max_len() -> nat {
    (16 * (0x1_0000_0000 - 2)) as nat
}

/// What the inputs of GCM must be: an AES-128 or AES-256 key, a 96-bit IV,
/// and lengths within §5.2.1.1's (additional data below 2^61 bytes).
pub open spec fn gcm_ok(key: Seq<u8>, iv: Seq<u8>, aad: Seq<u8>, p_len: nat) -> bool {
    key_ok(key) && iv.len() == 12 && p_len <= max_len() && aad.len() < 0x2000_0000_0000_0000
}

/// GCM-AE_K(IV, P, A) = (C, T) (§7.1), as C || T.
pub open spec fn gcm_seal(key: Seq<u8>, iv: Seq<u8>, aad: Seq<u8>, p: Seq<u8>) -> Seq<u8> {
    let c = gctr(key, iv, p);
    c + gcm_tag(key, iv, aad, c)
}

/// GCM-AD_K(IV, C, T, A) (§7.2) on C || T: the plaintext, or `None`
/// (FAIL) if the tag is not T, or the input is shorter than a tag.
pub open spec fn gcm_open(key: Seq<u8>, iv: Seq<u8>, aad: Seq<u8>, ct: Seq<u8>) -> Option<Seq<u8>> {
    if ct.len() < 16 {
        None
    } else {
        let c = ct.take(ct.len() - 16);
        let t = ct.skip(ct.len() - 16);
        if gcm_tag(key, iv, aad, c) == t {
            Some(gctr(key, iv, c))
        } else {
            None
        }
    }
}

} // verus!

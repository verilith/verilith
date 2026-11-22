//! SHA-384, SHA-512, SHA-512/224 and SHA-512/256 as FIPS 180-4 defines
//! them, as pure functions over `Seq<u8>`: the trusted specification the
//! exec code in `compress512` and `hash512` is proven to compute. Each
//! definition names the section it transcribes; the shapes are those of
//! [`crate::spec`] with 64-bit words, 80 rounds, 128-byte blocks and a
//! 128-bit length.
//!
//! FIPS 180-4 defines these hashes for messages of fewer than 2^128 bits,
//! and so do these functions: the length field (§5.1.2) is the bit length
//! modulo 2^128, which below 2^128 bits is the bit length itself.
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// §3.2: operations on 64-bit words
// ---------------------------------------------------------------------------

/// Addition modulo 2^64 (§3.2 item 1).
pub open spec fn add(x: u64, y: u64) -> u64 {
    ((x as int + y as int) % 0x1_0000_0000_0000_0000) as u64
}

/// ROTR^n(x), 0 < n < 64 (§3.2 item 4, §2.2.2).
pub open spec fn rotr(x: u64, n: u64) -> u64 {
    (x >> n) | (x << ((64 - n) as u64))
}

// ---------------------------------------------------------------------------
// §4.1.3: SHA-384, SHA-512, SHA-512/224 and SHA-512/256 functions
// ---------------------------------------------------------------------------

/// Ch(x, y, z) (4.8).
pub open spec fn ch(x: u64, y: u64, z: u64) -> u64 {
    (x & y) ^ (!x & z)
}

/// Maj(x, y, z) (4.9).
pub open spec fn maj(x: u64, y: u64, z: u64) -> u64 {
    (x & y) ^ (x & z) ^ (y & z)
}

/// Σ0 (4.10).
pub open spec fn big_sigma0(x: u64) -> u64 {
    rotr(x, 28) ^ rotr(x, 34) ^ rotr(x, 39)
}

/// Σ1 (4.11).
pub open spec fn big_sigma1(x: u64) -> u64 {
    rotr(x, 14) ^ rotr(x, 18) ^ rotr(x, 41)
}

/// σ0 (4.12).
pub open spec fn small_sigma0(x: u64) -> u64 {
    rotr(x, 1) ^ rotr(x, 8) ^ (x >> 7u64)
}

/// σ1 (4.13).
pub open spec fn small_sigma1(x: u64) -> u64 {
    rotr(x, 19) ^ rotr(x, 61) ^ (x >> 6u64)
}

// ---------------------------------------------------------------------------
// §4.2.3: constants
// ---------------------------------------------------------------------------

/// K0..K79: the first 64 bits of the fractional parts of the cube roots of
/// the first 80 primes. (`tests/vectors512.rs` derives them again.)
pub const K: [u64; 80] = [
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
];

// ---------------------------------------------------------------------------
// §5.3.4 to §5.3.6: initial hash values
// ---------------------------------------------------------------------------

/// H(0) for SHA-384 (§5.3.4): the first 64 bits of the fractional parts of
/// the square roots of the 9th through 16th primes.
pub const IV384: [u64; 8] = [
    0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
    0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4,
];

/// H(0) for SHA-512 (§5.3.5): the first 64 bits of the fractional parts of
/// the square roots of the first 8 primes.
pub const IV512: [u64; 8] = [
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
];

/// H(0) for SHA-512/224 (§5.3.6.1), from the SHA-512/t IV generation
/// function of §5.3.6 with t = 224. (`tests/vectors512.rs` runs it.)
pub const IV512_224: [u64; 8] = [
    0x8c3d37c819544da2, 0x73e1996689dcd4d6, 0x1dfab7ae32ff9c82, 0x679dd514582f9fcf,
    0x0f6d2b697bd44da8, 0x77e36f7304c48942, 0x3f9d85a86a1d36c8, 0x1112e6ad91d692a1,
];

/// H(0) for SHA-512/256 (§5.3.6.2), from the same function with t = 256.
pub const IV512_256: [u64; 8] = [
    0x22312194fc2bf72c, 0x9f555fa3c84c64c2, 0x2393b86b6f53b151, 0x963877195940eabd,
    0x96283ee2a88effe3, 0xbe5e1e2553863992, 0x2b0199fc2c85b8aa, 0x0eb72ddc81c52ca2,
];

// ---------------------------------------------------------------------------
// §5.1.2, §5.2.2: padding and parsing the message
// ---------------------------------------------------------------------------

/// The number of zero bytes after the 0x80 byte: the least k >= 0 with
/// len + 1 + k = 112 (mod 128), so that the 16-byte length ends a block.
pub open spec fn zeros(len: nat) -> nat {
    ((111 - len as int) % 128) as nat
}

/// The message length in bits, modulo 2^128, as 16 bytes, most significant
/// first: its high 64 bits, then its low 64 bits.
pub open spec fn len128(len: nat) -> Seq<u8> {
    let m64 = 0x1_0000_0000_0000_0000nat;
    let bits = (len * 8) % (m64 * m64);
    crate::spec::be64((bits / m64) as u64) + crate::spec::be64((bits % m64) as u64)
}

/// The padded message (§5.1.2): the message, a 1 bit, zero bits, then the
/// length. In whole bytes: 0x80, `zeros` zero bytes, the 128-bit length.
pub open spec fn pad(m: Seq<u8>) -> Seq<u8> {
    m + seq![0x80u8] + Seq::new(zeros(m.len()), |i: int| 0u8) + len128(m.len())
}

/// The 64-bit word at byte `i` of `b`, most significant byte first (§3.1).
pub open spec fn be64_at(b: Seq<u8>, i: int) -> u64 {
    (b[i] as u64) << 56u64 | (b[i + 1] as u64) << 48u64 | (b[i + 2] as u64) << 40u64 | (b[i
        + 3] as u64) << 32u64 | (b[i + 4] as u64) << 24u64 | (b[i + 5] as u64) << 16u64 | (b[i
        + 6] as u64) << 8u64 | (b[i + 7] as u64)
}

/// Block `i` of a padded message (§5.2.2): its 128 bytes.
pub open spec fn block(p: Seq<u8>, i: int) -> Seq<u8> {
    p.subrange(128 * i, 128 * i + 128)
}

/// The sixteen words M0..M15 of a 128-byte block (§5.2.2).
pub open spec fn words(b: Seq<u8>) -> Seq<u64> {
    Seq::new(16, |j: int| be64_at(b, 8 * j))
}

// ---------------------------------------------------------------------------
// §6.4.2: SHA-512 hash computation
// ---------------------------------------------------------------------------

/// The message schedule W0..W79 of a block's words `m` (step 1).
pub open spec fn schedule(m: Seq<u64>, t: int) -> u64
    decreases t,
{
    if t < 16 {
        m[t]
    } else {
        add(
            add(add(small_sigma1(schedule(m, t - 2)), schedule(m, t - 7)), small_sigma0(schedule(m, t - 15))),
            schedule(m, t - 16),
        )
    }
}

/// The eight working variables a, b, c, d, e, f, g, h.
pub struct Vars {
    pub a: u64,
    pub b: u64,
    pub c: u64,
    pub d: u64,
    pub e: u64,
    pub f: u64,
    pub g: u64,
    pub h: u64,
}

/// The working variables initialized from H(i-1) (step 2).
pub open spec fn init(h: Seq<u64>) -> Vars {
    Vars { a: h[0], b: h[1], c: h[2], d: h[3], e: h[4], f: h[5], g: h[6], h: h[7] }
}

/// One iteration of step 3, with K_t = `k` and W_t = `w`.
pub open spec fn round(v: Vars, k: u64, w: u64) -> Vars {
    let t1 = add(add(add(add(v.h, big_sigma1(v.e)), ch(v.e, v.f, v.g)), k), w);
    let t2 = add(big_sigma0(v.a), maj(v.a, v.b, v.c));
    Vars { a: add(t1, t2), b: v.a, c: v.b, d: v.c, e: add(v.d, t1), f: v.e, g: v.f, h: v.g }
}

/// The working variables after the first `t` iterations of step 3.
pub open spec fn rounds(v: Vars, m: Seq<u64>, t: nat) -> Vars
    decreases t,
{
    if t == 0 {
        v
    } else {
        round(rounds(v, m, (t - 1) as nat), K[t - 1], schedule(m, t - 1))
    }
}

/// H(i) from H(i-1) and block M(i) (steps 1 to 4). Opaque to the proofs
/// about whole messages, which do not need its contents.
#[verifier::opaque]
pub open spec fn compress(h: Seq<u64>, b: Seq<u8>) -> Seq<u64> {
    let v = rounds(init(h), words(b), 80);
    seq![
        add(v.a, h[0]),
        add(v.b, h[1]),
        add(v.c, h[2]),
        add(v.d, h[3]),
        add(v.e, h[4]),
        add(v.f, h[5]),
        add(v.g, h[6]),
        add(v.h, h[7]),
    ]
}

/// H(n): the hash value after the first `n` blocks of `p`, from H(0) = `h0`.
pub open spec fn hash_blocks(h0: Seq<u64>, p: Seq<u8>, n: nat) -> Seq<u64>
    decreases n,
{
    if n == 0 {
        h0
    } else {
        compress(hash_blocks(h0, p, (n - 1) as nat), block(p, n - 1))
    }
}

/// The final hash value H(N) over a whole message, N = len(pad(m)) / 128.
pub open spec fn hash(h0: Seq<u64>, m: Seq<u8>) -> Seq<u64> {
    hash_blocks(h0, pad(m), pad(m).len() / 128)
}

/// The words of a hash value as bytes, most significant first.
pub open spec fn digest_bytes(h: Seq<u64>) -> Seq<u8> {
    Seq::new(64, |i: int| ((h[i / 8] >> ((56 - 8 * (i % 8)) as u64)) & 0xff) as u8)
}

/// SHA-512(m): H(N) as 64 bytes (§6.4.2).
pub open spec fn sha512(m: Seq<u8>) -> Seq<u8> {
    digest_bytes(hash(IV512@, m))
}

/// SHA-384(m): the leftmost 384 bits of H(N) from SHA-384's H(0) (§6.5).
pub open spec fn sha384(m: Seq<u8>) -> Seq<u8> {
    digest_bytes(hash(IV384@, m)).subrange(0, 48)
}

/// SHA-512/224(m): the leftmost 224 bits of H(N) from its H(0) (§6.6).
pub open spec fn sha512_224(m: Seq<u8>) -> Seq<u8> {
    digest_bytes(hash(IV512_224@, m)).subrange(0, 28)
}

/// SHA-512/256(m): the leftmost 256 bits of H(N) from its H(0) (§6.7).
pub open spec fn sha512_256(m: Seq<u8>) -> Seq<u8> {
    digest_bytes(hash(IV512_256@, m)).subrange(0, 32)
}

} // verus!

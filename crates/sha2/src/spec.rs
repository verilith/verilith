//! SHA-224 and SHA-256 as FIPS 180-4 defines them, as pure functions over
//! `Seq<u8>`: the trusted specification the exec code in this crate is
//! proven to compute. Each definition names the section it transcribes.
//!
//! FIPS 180-4 defines the hashes for messages of fewer than 2^64 bits. Here
//! the length field of the padding (§5.1.1) is the bit length modulo 2^64,
//! so the functions are total; below 2^64 bits that is the standard's
//! definition, and above it is what OpenSSL and other libraries compute.
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// §2.2.2, §3.2: operations on 32-bit words
// ---------------------------------------------------------------------------

/// Addition modulo 2^32 (§3.2 item 1).
pub open spec fn add(x: u32, y: u32) -> u32 {
    ((x as int + y as int) % 0x1_0000_0000) as u32
}

/// The rotate right (circular right shift) operation ROTR^n(x), 0 < n < 32
/// (§3.2 item 4, §2.2.2).
pub open spec fn rotr(x: u32, n: u32) -> u32 {
    (x >> n) | (x << ((32 - n) as u32))
}

// ---------------------------------------------------------------------------
// §4.1.2: SHA-224 and SHA-256 functions
// ---------------------------------------------------------------------------

/// Ch(x, y, z) (4.2).
pub open spec fn ch(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (!x & z)
}

/// Maj(x, y, z) (4.3).
pub open spec fn maj(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (x & z) ^ (y & z)
}

/// Σ0 (4.4).
pub open spec fn big_sigma0(x: u32) -> u32 {
    rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22)
}

/// Σ1 (4.5).
pub open spec fn big_sigma1(x: u32) -> u32 {
    rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25)
}

/// σ0 (4.6).
pub open spec fn small_sigma0(x: u32) -> u32 {
    rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3u32)
}

/// σ1 (4.7).
pub open spec fn small_sigma1(x: u32) -> u32 {
    rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10u32)
}

// ---------------------------------------------------------------------------
// §4.2.2: SHA-224 and SHA-256 constants
// ---------------------------------------------------------------------------

/// K0..K63: the first 32 bits of the fractional parts of the cube roots of
/// the first 64 primes. (`tests/vectors.rs` derives them again.)
pub const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

// ---------------------------------------------------------------------------
// §5.3.2, §5.3.3: initial hash values
// ---------------------------------------------------------------------------

/// H(0) for SHA-256 (§5.3.3): the first 32 bits of the fractional parts of
/// the square roots of the first 8 primes.
pub const IV256: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// H(0) for SHA-224 (§5.3.2): the second 32 bits of the fractional parts
/// of the square roots of the 9th through 16th primes.
pub const IV224: [u32; 8] = [
    0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939, 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4,
];

// ---------------------------------------------------------------------------
// §5.1.1, §5.2.1: padding and parsing the message
// ---------------------------------------------------------------------------

/// The number of zero bytes after the 0x80 byte: the least k >= 0 with
/// len + 1 + k = 56 (mod 64), so that the 8-byte length ends a block.
pub open spec fn zeros(len: nat) -> nat {
    ((55 - len as int) % 64) as nat
}

/// The message length in bits, modulo 2^64 (see the module comment).
pub open spec fn bit_len(len: nat) -> u64 {
    ((len * 8) % 0x1_0000_0000_0000_0000) as u64
}

/// A 64-bit number as 8 bytes, most significant first (§3.1 item 2).
pub open spec fn be64(x: u64) -> Seq<u8> {
    Seq::new(8, |i: int| ((x >> ((56 - 8 * i) as u64)) & 0xff) as u8)
}

/// The padded message (§5.1.1): the message, a 1 bit, zero bits, then the
/// length. In whole bytes: 0x80, `zeros` zero bytes, the 64-bit length.
pub open spec fn pad(m: Seq<u8>) -> Seq<u8> {
    m + seq![0x80u8] + Seq::new(zeros(m.len()), |i: int| 0u8) + be64(bit_len(m.len()))
}

/// The 32-bit word at byte `i` of `b`, most significant byte first (§3.1).
pub open spec fn be32(b: Seq<u8>, i: int) -> u32 {
    (b[i] as u32) << 24u32 | (b[i + 1] as u32) << 16u32 | (b[i + 2] as u32) << 8u32 | (b[i
        + 3] as u32)
}

/// Block `i` of a padded message (§5.2.1): its 64 bytes.
pub open spec fn block(p: Seq<u8>, i: int) -> Seq<u8> {
    p.subrange(64 * i, 64 * i + 64)
}

/// The sixteen words M0..M15 of a 64-byte block (§5.2.1).
pub open spec fn words(b: Seq<u8>) -> Seq<u32> {
    Seq::new(16, |j: int| be32(b, 4 * j))
}

// ---------------------------------------------------------------------------
// §6.2.2: SHA-256 hash computation
// ---------------------------------------------------------------------------

/// The message schedule W0..W63 of a block's words `m` (step 1).
pub open spec fn schedule(m: Seq<u32>, t: int) -> u32
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
    pub a: u32,
    pub b: u32,
    pub c: u32,
    pub d: u32,
    pub e: u32,
    pub f: u32,
    pub g: u32,
    pub h: u32,
}

/// The working variables initialized from H(i-1) (step 2).
pub open spec fn init(h: Seq<u32>) -> Vars {
    Vars { a: h[0], b: h[1], c: h[2], d: h[3], e: h[4], f: h[5], g: h[6], h: h[7] }
}

/// One iteration of step 3, with K_t = `k` and W_t = `w`.
pub open spec fn round(v: Vars, k: u32, w: u32) -> Vars {
    let t1 = add(add(add(add(v.h, big_sigma1(v.e)), ch(v.e, v.f, v.g)), k), w);
    let t2 = add(big_sigma0(v.a), maj(v.a, v.b, v.c));
    Vars { a: add(t1, t2), b: v.a, c: v.b, d: v.c, e: add(v.d, t1), f: v.e, g: v.f, h: v.g }
}

/// The working variables after the first `t` iterations of step 3.
pub open spec fn rounds(v: Vars, m: Seq<u32>, t: nat) -> Vars
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
pub open spec fn compress(h: Seq<u32>, b: Seq<u8>) -> Seq<u32> {
    let v = rounds(init(h), words(b), 64);
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
pub open spec fn hash_blocks(h0: Seq<u32>, p: Seq<u8>, n: nat) -> Seq<u32>
    decreases n,
{
    if n == 0 {
        h0
    } else {
        compress(hash_blocks(h0, p, (n - 1) as nat), block(p, n - 1))
    }
}

/// The final hash value H(N) over a whole message, N = len(pad(m)) / 64.
pub open spec fn hash(h0: Seq<u32>, m: Seq<u8>) -> Seq<u32> {
    hash_blocks(h0, pad(m), pad(m).len() / 64)
}

/// The words of a hash value as bytes, most significant first.
pub open spec fn digest_bytes(h: Seq<u32>) -> Seq<u8> {
    Seq::new(32, |i: int| ((h[i / 4] >> ((24 - 8 * (i % 4)) as u32)) & 0xff) as u8)
}

/// SHA-256(m): H(N) as 32 bytes (§6.2.2).
pub open spec fn sha256(m: Seq<u8>) -> Seq<u8> {
    digest_bytes(hash(IV256@, m))
}

/// SHA-224(m): the leftmost 224 bits of H(N) computed from SHA-224's H(0)
/// (§6.3).
pub open spec fn sha224(m: Seq<u8>) -> Seq<u8> {
    digest_bytes(hash(IV224@, m)).subrange(0, 28)
}

} // verus!

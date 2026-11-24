//! HMAC as FIPS 198-1 defines it (and RFC 2104), as pure functions over
//! `Seq<u8>`: the trusted specification the HMAC code in this crate is
//! proven to compute. Each definition names the section or step it
//! transcribes.
//!
//! FIPS 198-1 §4, with B the hash's input block size in bytes, L its output
//! size in bytes, K the key and text the message:
//!
//! - Step 1 to 3: K0 is K if len(K) = B; H(K) followed by B − L zeros if
//!   len(K) > B; and K followed by B − len(K) zeros if len(K) < B.
//! - Step 4 to 9: HMAC(K, text) = H((K0 ⊕ opad) ‖ H((K0 ⊕ ipad) ‖ text)),
//!   where ipad is the byte 0x36 repeated B times and opad the byte 0x5c
//!   repeated B times.
//!
//! The hashes are the ones in `spec` and `spec512`. HMAC with SHA-224 or
//! SHA-256 has B = 64; with SHA-384, SHA-512, SHA-512/224 or SHA-512/256,
//! B = 128 (FIPS 180-4 §1, Figure 1).
use crate::spec;
use crate::spec512;
use vstd::prelude::*;

verus! {

/// ipad (§3): the byte 0x36.
pub open spec fn ipad() -> u8 {
    0x36
}

/// opad (§3): the byte 0x5c.
pub open spec fn opad() -> u8 {
    0x5c
}

/// K0 (§4 steps 1 to 3): the key made exactly `b` bytes long.
pub open spec fn key0(h: spec_fn(Seq<u8>) -> Seq<u8>, b: nat, k: Seq<u8>) -> Seq<u8> {
    let k1 = if k.len() > b { h(k) } else { k };
    k1 + Seq::new((b - k1.len()) as nat, |i: int| 0u8)
}

/// K0 ⊕ pad, byte by byte (§4 steps 4 and 7).
pub open spec fn xor_pad(k0: Seq<u8>, pad: u8) -> Seq<u8> {
    Seq::new(k0.len(), |i: int| k0[i] ^ pad)
}

/// HMAC(K, text) (§4 steps 4 to 9) with the hash `h` of block size `b`.
pub open spec fn hmac(h: spec_fn(Seq<u8>) -> Seq<u8>, b: nat, k: Seq<u8>, text: Seq<u8>) -> Seq<u8> {
    let k0 = key0(h, b, k);
    h(xor_pad(k0, opad()) + h(xor_pad(k0, ipad()) + text))
}

/// HMAC-SHA-224.
pub open spec fn hmac_sha224(k: Seq<u8>, text: Seq<u8>) -> Seq<u8> {
    hmac(|m: Seq<u8>| spec::sha224(m), 64, k, text)
}

/// HMAC-SHA-256.
pub open spec fn hmac_sha256(k: Seq<u8>, text: Seq<u8>) -> Seq<u8> {
    hmac(|m: Seq<u8>| spec::sha256(m), 64, k, text)
}

/// HMAC-SHA-384.
pub open spec fn hmac_sha384(k: Seq<u8>, text: Seq<u8>) -> Seq<u8> {
    hmac(|m: Seq<u8>| spec512::sha384(m), 128, k, text)
}

/// HMAC-SHA-512.
pub open spec fn hmac_sha512(k: Seq<u8>, text: Seq<u8>) -> Seq<u8> {
    hmac(|m: Seq<u8>| spec512::sha512(m), 128, k, text)
}

/// HMAC-SHA-512/224.
pub open spec fn hmac_sha512_224(k: Seq<u8>, text: Seq<u8>) -> Seq<u8> {
    hmac(|m: Seq<u8>| spec512::sha512_224(m), 128, k, text)
}

/// HMAC-SHA-512/256.
pub open spec fn hmac_sha512_256(k: Seq<u8>, text: Seq<u8>) -> Seq<u8> {
    hmac(|m: Seq<u8>| spec512::sha512_256(m), 128, k, text)
}

} // verus!

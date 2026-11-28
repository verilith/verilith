//! The signature check the validator trusts: aws-lc's RSA, ECDSA and
//! Ed25519 verification, for the DNSSEC encodings of keys and signatures.
//! Everything here is trusted (TRUST.md). `dspec::sig_valid` is
//! uninterpreted: the proofs know only that the same inputs give the same
//! answer, so what they establish is that the bytes checked are exactly
//! the ones RFC 4034 says are signed, under the key the chain of trust
//! says to use.
#[cfg(verus_only)]
use crate::dspec::sig_valid;
use vstd::prelude::*;

verus! {

/// Does `sig` sign `data` under DNSKEY public key `key` (the DNSKEY RDATA
/// after its first four octets), with algorithm `alg`?
#[verifier::external_body]
pub fn verify_sig(alg: u8, key: &[u8], data: &[u8], sig: &[u8]) -> (r: bool)
    ensures
        r == sig_valid(alg, key@, data@, sig@),
{
    verify_impl(alg, key, data, sig)
}

} // verus!

#[cfg(not(verus_keep_ghost))]
fn verify_impl(alg: u8, key: &[u8], data: &[u8], sig: &[u8]) -> bool {
    use aws_lc_rs::signature::{self, RsaPublicKeyComponents, UnparsedPublicKey};
    match alg {
        // RSA/SHA-256 and RSA/SHA-512 (RFC 5702): the key is RFC 3110's
        // exponent length (one octet, or zero and two), exponent, modulus.
        8 | 10 => {
            let (elen, off) = match key.first() {
                Some(0) if key.len() >= 3 => (u16::from_be_bytes([key[1], key[2]]) as usize, 3),
                Some(&l) if l != 0 => (l as usize, 1),
                _ => return false,
            };
            if key.len() <= off + elen {
                return false;
            }
            let (e, n) = key[off..].split_at(elen);
            let p = if alg == 8 {
                &signature::RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY
            } else {
                &signature::RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY
            };
            RsaPublicKeyComponents { n, e }.verify(p, data, sig).is_ok()
        }
        // ECDSA (RFC 6605): the key is x | y, the signature r | s.
        13 | 14 => {
            let (len, a) = if alg == 13 {
                (64, &signature::ECDSA_P256_SHA256_FIXED)
            } else {
                (96, &signature::ECDSA_P384_SHA384_FIXED)
            };
            if key.len() != len {
                return false;
            }
            let mut k = Vec::with_capacity(len + 1);
            k.push(4);
            k.extend_from_slice(key);
            UnparsedPublicKey::new(a, &k).verify(data, sig).is_ok()
        }
        // Ed25519 (RFC 8080).
        15 => key.len() == 32 && UnparsedPublicKey::new(&signature::ED25519, key).verify(data, sig).is_ok(),
        _ => false,
    }
}

#[cfg(verus_keep_ghost)]
fn verify_impl(_alg: u8, _key: &[u8], _data: &[u8], _sig: &[u8]) -> bool {
    false
}

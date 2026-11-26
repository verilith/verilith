//! This crate's HPKE opens what rustls's HPKE seals (RFC 9180 base mode).
use rustls::crypto::hpke::{Hpke, HpkePublicKey};
use verilith_tls_aws_lc::hpke::*;

#[test]
fn opens_what_rustls_seals() {
    use rustls::crypto::aws_lc_rs::hpke as r;
    let suites: [(&dyn Hpke, u16); 3] = [
        (r::DH_KEM_X25519_HKDF_SHA256_AES_128, AEAD_AES_128_GCM),
        (r::DH_KEM_X25519_HKDF_SHA256_AES_256, AEAD_AES_256_GCM),
        (r::DH_KEM_X25519_HKDF_SHA256_CHACHA20_POLY1305, AEAD_CHACHA20_POLY1305),
    ];
    let k = HpkeKey::generate().unwrap();
    for (s, aead) in suites {
        for n in [0usize, 1, 200, 5000] {
            let pt: Vec<u8> = (0..n).map(|i| i as u8).collect();
            let (enc, ct) = s.seal(b"info", b"aad", &pt, &HpkePublicKey(k.public().to_vec())).unwrap();
            assert_eq!(k.open(KDF_SHA256, aead, &enc.0, b"info", b"aad", &ct).as_deref(), Some(&pt[..]));
            assert!(k.open(KDF_SHA256, aead, &enc.0, b"info", b"aaD", &ct).is_none());
            assert!(k.open(KDF_SHA256, aead, &enc.0, b"inf0", b"aad", &ct).is_none());
        }
    }
    // Another key does not open it.
    let k2 = HpkeKey::generate().unwrap();
    let (enc, ct) = suites[0].0.seal(b"", b"", b"x", &HpkePublicKey(k.public().to_vec())).unwrap();
    assert!(k2.open(KDF_SHA256, AEAD_AES_128_GCM, &enc.0, b"", b"", &ct).is_none());
}

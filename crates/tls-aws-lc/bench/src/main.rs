//! Each primitive aws-lc gives verilith-tls, against its formally verified
//! alternative: libcrux (HACL*) and verilith-sha2. Best of 7 runs of 200 ms.
//! CRYPTO.md has the results.
use std::hint::black_box as bb;
use std::time::Instant;
use aws_lc_rs::{aead, agreement, kem, rand::{SecureRandom, SystemRandom}, signature::{self, KeyPair}};

fn time<F: FnMut()>(name: &str, bytes: usize, mut f: F) -> f64 {
    for _ in 0..50 { f(); }
    let mut best = f64::MAX;
    for _ in 0..7 {
        let mut n = 0u64; let t = Instant::now();
        while t.elapsed().as_millis() < 200 { f(); n += 1; }
        let per = t.elapsed().as_secs_f64() / n as f64;
        if per < best { best = per; }
    }
    if bytes > 0 { println!("{name}\t{:.3} us\t{:.2} GB/s", best * 1e6, bytes as f64 / best / 1e9); }
    else { println!("{name}\t{:.3} us", best * 1e6); }
    best
}

fn main() {
    let rng = SystemRandom::new();
    let key = [7u8; 32]; let nonce = [1u8; 12]; let aad = [0x17u8, 3, 3, 0x40, 0x11];
    for &len in &[16384usize, 1200, 256, 64] {
        let k = aead::LessSafeKey::new(aead::UnboundKey::new(&aead::CHACHA20_POLY1305, &key).unwrap());
        let mut buf = vec![0u8; len];
        time(&format!("chacha20poly1305 seal {len}B aws-lc"), len, || {
            let t = k.seal_in_place_separate_tag(aead::Nonce::assume_unique_for_key(nonce), aead::Aad::from(aad), &mut buf).unwrap(); let _ = bb(t);
        });
        let mut ct = vec![0u8; len]; let mut tag = [0u8; 16];
        let pt = vec![0u8; len];
        time(&format!("chacha20poly1305 seal {len}B libcrux"), len, || {
            libcrux_chacha20poly1305::encrypt_detached(&key, &pt, &mut ct, &mut tag, &aad, &nonce).unwrap(); bb(&tag);
        });
        let mut out = vec![0u8; len];
        time(&format!("chacha20poly1305 open {len}B libcrux"), len, || {
            libcrux_chacha20poly1305::decrypt_detached(&key, &mut out, &ct, &tag, &aad, &nonce).unwrap(); bb(&out);
        });
        let mut sealed = pt.clone(); let t = k.seal_in_place_separate_tag(aead::Nonce::assume_unique_for_key(nonce), aead::Aad::from(aad), &mut sealed).unwrap(); sealed.extend_from_slice(t.as_ref());
        time(&format!("chacha20poly1305 open {len}B aws-lc (incl. a copy)"), len, || {
            let mut b = sealed.clone(); let r = k.open_in_place(aead::Nonce::assume_unique_for_key(nonce), aead::Aad::from(aad), &mut b).unwrap().len(); bb(r);
        });
    }
    // HMAC-SHA256 (HPKE labeled extract/expand inputs are ~100 bytes)
    {
        use aws_lc_rs::hmac;
        let m = [0x42u8; 100];
        time("hmac-sha256 100B aws-lc", 0, || { let k = hmac::Key::new(hmac::HMAC_SHA256, &key); bb(hmac::sign(&k, &m)); });
        time("hmac-sha256 100B verilith-sha2", 0, || { let mut h = verilith_sha2::HmacSha256::new(&key); h.update(&m); bb(h.finalize()); });
        let k = hmac::Key::new(hmac::HMAC_SHA256, &key);
        let mut h = verilith_sha2::HmacSha256::new(&key); h.update(&m);
        assert_eq!(hmac::sign(&k, &m).as_ref(), &h.finalize()[..]);
    }
    // ML-KEM-768 encapsulate
    let dk = kem::DecapsulationKey::generate(&kem::ML_KEM_768).unwrap();
    let ek_bytes = dk.encapsulation_key().unwrap().key_bytes().unwrap().as_ref().to_vec();
    time("mlkem768 encaps (incl. key parse) aws-lc", 0, || {
        let ek = kem::EncapsulationKey::new(&kem::ML_KEM_768, &ek_bytes).unwrap(); let r = ek.encapsulate().unwrap(); bb(r);
    });
    let ekarr: [u8; 1184] = ek_bytes.clone().try_into().unwrap();
    time("mlkem768 encaps (incl. validate) libcrux", 0, || {
        let pk = libcrux_ml_kem::mlkem768::MlKem768PublicKey::from(ekarr);
        assert!(libcrux_ml_kem::mlkem768::validate_public_key(&pk));
        let mut r = [0u8; 32]; rng.fill(&mut r).unwrap();
        let x = libcrux_ml_kem::mlkem768::encapsulate(&pk, r); bb(x);
    });
    // X25519
    let peer = agreement::PrivateKey::generate(&agreement::X25519).unwrap().compute_public_key().unwrap().as_ref().to_vec();
    time("x25519 keygen+agree aws-lc", 0, || {
        let k = agreement::EphemeralPrivateKey::generate(&agreement::X25519, &rng).unwrap();
        let p = k.compute_public_key().unwrap(); bb(p.as_ref());
        agreement::agree_ephemeral(k, agreement::UnparsedPublicKey::new(&agreement::X25519, &peer), (), |s| { bb(s); Ok(()) }).unwrap();
    });
    let peer32: [u8; 32] = peer.clone().try_into().unwrap();
    time("x25519 keygen+agree libcrux", 0, || {
        let mut sk = [0u8; 32]; rng.fill(&mut sk).unwrap(); libcrux_curve25519::clamp(&mut sk);
        let mut pk = [0u8; 32]; libcrux_curve25519::secret_to_public(&mut pk, &sk); bb(&pk);
        let mut ss = [0u8; 32]; assert!(libcrux_curve25519::ecdh(&mut ss, &peer32, &sk).is_ok()); bb(&ss);
    });
    // P-256 ECDH
    let ppeer = agreement::PrivateKey::generate(&agreement::ECDH_P256).unwrap().compute_public_key().unwrap().as_ref().to_vec();
    time("p256 ecdh keygen+agree aws-lc", 0, || {
        let k = agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();
        let p = k.compute_public_key().unwrap(); bb(p.as_ref());
        agreement::agree_ephemeral(k, agreement::UnparsedPublicKey::new(&agreement::ECDH_P256, &ppeer), (), |s| { bb(s); Ok(()) }).unwrap();
    });
    time("p256 ecdh keygen+agree libcrux", 0, || {
        let mut sk = [0u8; 32]; loop { rng.fill(&mut sk).unwrap(); if libcrux_p256::validate_private_key(&sk) { break; } }
        let mut pk = [0u8; 64]; assert!(libcrux_p256::dh_initiator(&mut pk, &sk)); bb(&pk);
        let mut raw = [0u8; 64]; assert!(libcrux_p256::uncompressed_to_raw(&ppeer, &mut raw));
        let mut ss = [0u8; 64]; assert!(libcrux_p256::dh_responder(&mut ss, &raw, &sk)); bb(&ss);
    });
    // Ed25519
    let msg = vec![0x20u8; 130];
    let seed = [9u8; 32];
    let ek = signature::Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
    time("ed25519 sign aws-lc", 0, || { bb(ek.sign(&msg)); });
    time("ed25519 sign libcrux", 0, || { bb(libcrux_ed25519::sign(&msg, &seed).unwrap()); });
    let esig = ek.sign(&msg).as_ref().to_vec(); let epk = ek.public_key().as_ref().to_vec();
    time("ed25519 verify aws-lc", 0, || { signature::UnparsedPublicKey::new(&signature::ED25519, &epk).verify(&msg, &esig).unwrap(); });
    let epk32: [u8; 32] = epk.clone().try_into().unwrap(); let esig64: [u8; 64] = esig.clone().try_into().unwrap();
    time("ed25519 verify libcrux", 0, || { libcrux_ed25519::verify(&msg, &epk32, &esig64).unwrap(); });
    // ECDSA P-256
    let pkcs8 = signature::EcdsaKeyPair::generate_pkcs8(&signature::ECDSA_P256_SHA256_FIXED_SIGNING, &rng).unwrap();
    let kp = signature::EcdsaKeyPair::from_pkcs8(&signature::ECDSA_P256_SHA256_ASN1_SIGNING, pkcs8.as_ref()).unwrap();
    time("ecdsa p256 sign aws-lc", 0, || { bb(kp.sign(&rng, &msg).unwrap()); });
    let sig = kp.sign(&rng, &msg).unwrap().as_ref().to_vec(); let ppk = kp.public_key().as_ref().to_vec();
    time("ecdsa p256 verify aws-lc", 0, || { signature::UnparsedPublicKey::new(&signature::ECDSA_P256_SHA256_ASN1, &ppk).verify(&msg, &sig).unwrap(); });
    let sk = { let mut s = [0u8;32]; loop { rng.fill(&mut s).unwrap(); if libcrux_p256::validate_private_key(&s) { break; } } s };
    let mut lpk = [0u8; 64]; assert!(libcrux_p256::dh_initiator(&mut lpk, &sk));
    time("ecdsa p256 sign libcrux", 0, || {
        let mut nonce = [0u8;32]; loop { rng.fill(&mut nonce).unwrap(); if libcrux_p256::validate_private_key(&nonce) { break; } }
        let mut s = [0u8; 64]; assert!(libcrux_p256::ecdsa_sign_p256_sha2(&mut s, msg.len() as u32, &msg, &sk, &nonce)); bb(&s);
    });
    let mut nonce = [3u8;32]; nonce[0]=1; let mut ls = [0u8;64]; assert!(libcrux_p256::ecdsa_sign_p256_sha2(&mut ls, msg.len() as u32, &msg, &sk, &nonce));
    let (r, s): ([u8;32],[u8;32]) = (ls[..32].try_into().unwrap(), ls[32..].try_into().unwrap());
    time("ecdsa p256 verify libcrux", 0, || { assert!(libcrux_p256::ecdsa_verif_p256_sha2(msg.len() as u32, &msg, &lpk, &r, &s)); });
}

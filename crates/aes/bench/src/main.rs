//! AES-GCM seal and open: verilith-aes, aws-lc, RustCrypto. Best of 7 runs
//! of 200 ms each.
use aes_gcm::aead::{AeadInPlace, KeyInit};
use aws_lc_rs::aead;
use std::hint::black_box as bb;
use std::time::Instant;

fn time<F: FnMut()>(name: &str, bytes: usize, mut f: F) -> f64 {
    for _ in 0..50 {
        f();
    }
    let mut best = f64::MAX;
    for _ in 0..7 {
        let mut n = 0u64;
        let t = Instant::now();
        while t.elapsed().as_millis() < 200 {
            f();
            n += 1;
        }
        let per = t.elapsed().as_secs_f64() / n as f64;
        if per < best {
            best = per;
        }
    }
    println!("{name}\t{:.3} us\t{:.2} GB/s", best * 1e6, bytes as f64 / best / 1e9);
    best
}

fn main() {
    let filter: Vec<String> = std::env::args().skip(1).collect();
    let nonce = [1u8; 12];
    let aad = [0x17u8, 3, 3, 0x40, 0x11];
    for klen in [16usize, 32] {
        let key = vec![7u8; klen];
        let alg = if klen == 16 { &aead::AES_128_GCM } else { &aead::AES_256_GCM };
        let a = aead::LessSafeKey::new(aead::UnboundKey::new(alg, &key).unwrap());
        let v = verilith_aes::AesGcm::new(&key).unwrap();
        let r128 = aes_gcm::Aes128Gcm::new_from_slice(&vec![7u8; 16]).unwrap();
        let r256 = aes_gcm::Aes256Gcm::new_from_slice(&vec![7u8; 32]).unwrap();
        for &len in &[16384usize, 1200, 256, 64] {
            if !filter.is_empty() && !filter.iter().any(|f| len.to_string() == *f) {
                continue;
            }
            let name = format!("aes-{}-gcm seal {len}B", klen * 8);
            let mut buf = vec![0u8; len];
            time(&format!("{name} aws-lc"), len, || {
                let t = a.seal_in_place_separate_tag(aead::Nonce::assume_unique_for_key(nonce), aead::Aad::from(aad), &mut buf).unwrap();
                bb(t);
            });
            let mut buf = vec![0u8; len];
            let mut tag = [0u8; 16];
            time(&format!("{name} verilith"), len, || {
                assert!(v.seal(&nonce, &aad, &mut buf, &mut tag));
                bb(&tag);
            });
            let mut buf = vec![0u8; len];
            time(&format!("{name} rustcrypto"), len, || {
                let t = if klen == 16 {
                    r128.encrypt_in_place_detached((&nonce).into(), &aad, &mut buf).unwrap()
                } else {
                    r256.encrypt_in_place_detached((&nonce).into(), &aad, &mut buf).unwrap()
                };
                bb(t);
            });
            // Open: decrypt a valid record each time (seal it once, then
            // undo each open with a seal is not possible, so open a copy).
            let pt = vec![0u8; len];
            let mut ct = pt.clone();
            let mut tag = [0u8; 16];
            v.seal(&nonce, &aad, &mut ct, &mut tag);
            let mut sealed = ct.clone();
            sealed.extend_from_slice(&tag);
            let mut b = sealed.clone();
            time(&format!("aes-{}-gcm open {len}B aws-lc (incl. a copy)", klen * 8), len, || {
                b.copy_from_slice(&sealed);
                let r = a.open_in_place(aead::Nonce::assume_unique_for_key(nonce), aead::Aad::from(aad), &mut b).unwrap().len();
                bb(r);
            });
            let mut b = ct.clone();
            time(&format!("aes-{}-gcm open {len}B verilith (incl. a copy)", klen * 8), len, || {
                b.copy_from_slice(&ct);
                assert!(v.open(&nonce, &aad, &mut b, &tag));
                bb(&b);
            });
        }
    }
}

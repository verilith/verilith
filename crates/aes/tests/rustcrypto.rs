//! AES-GCM against RustCrypto's `aes-gcm`, an independent implementation,
//! on random keys, IVs, additional data and texts of every length up to
//! 600 bytes and a few long ones.
use aes_gcm::aead::{AeadInPlace, KeyInit};
use aes_gcm::{Aes128Gcm, Aes256Gcm, Nonce};
use verilith_aes::AesGcm;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
}

fn reference(key: &[u8], iv: &[u8; 12], aad: &[u8], pt: &[u8]) -> (Vec<u8>, [u8; 16]) {
    let mut buf = pt.to_vec();
    let tag = if key.len() == 16 {
        Aes128Gcm::new_from_slice(key).unwrap().encrypt_in_place_detached(Nonce::from_slice(iv), aad, &mut buf).unwrap()
    } else {
        Aes256Gcm::new_from_slice(key).unwrap().encrypt_in_place_detached(Nonce::from_slice(iv), aad, &mut buf).unwrap()
    };
    (buf, tag.into())
}

fn check(rng: &mut Rng, klen: usize, alen: usize, plen: usize) {
    let key = rng.bytes(klen);
    let iv: [u8; 12] = rng.bytes(12).try_into().unwrap();
    let aad = rng.bytes(alen);
    let pt = rng.bytes(plen);
    let (ct, tag) = reference(&key, &iv, &aad, &pt);
    let k = AesGcm::new(&key).expect("AES-NI");
    let mut buf = pt.clone();
    let mut t = [0u8; 16];
    assert!(k.seal(&iv, &aad, &mut buf, &mut t));
    assert_eq!(buf, ct, "ciphertext, key {klen} aad {alen} text {plen}");
    assert_eq!(t, tag, "tag, key {klen} aad {alen} text {plen}");
    assert!(k.open(&iv, &aad, &mut buf, &t));
    assert_eq!(buf, pt);
    // A changed tag, text or additional data is refused, and zeroes the text.
    let mut bad = t;
    bad[(plen + alen) % 16] ^= 1 << (plen % 8);
    let mut buf = ct.clone();
    assert!(!k.open(&iv, &aad, &mut buf, &bad));
    assert!(buf.iter().all(|&b| b == 0));
    if plen > 0 {
        let mut buf = ct.clone();
        buf[plen / 2] ^= 0x80;
        assert!(!k.open(&iv, &aad, &mut buf, &t));
    }
    if alen > 0 {
        let mut a = aad.clone();
        a[alen - 1] ^= 1;
        let mut buf = ct.clone();
        assert!(!k.open(&iv, &a, &mut buf, &t));
    }
}

#[test]
fn every_length() {
    if !std::is_x86_feature_detected!("aes") {
        return;
    }
    let mut rng = Rng(0x9e3779b97f4a7c15);
    for klen in [16, 32] {
        for plen in 0..600 {
            check(&mut rng, klen, plen % 37, plen);
        }
        for alen in 0..300 {
            check(&mut rng, klen, alen, 64);
        }
        for plen in [1024, 4096, 16384, 16384 + 17, 65536 + 5] {
            check(&mut rng, klen, 13, plen);
        }
    }
}

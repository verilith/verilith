//! Record protection with aws-lc's AEADs, checked against the AEAD called
//! directly with the nonce §5.3 gives.
use aws_lc_rs::aead::{self, Aad, LessSafeKey, Nonce, UnboundKey};
use verilith_tls::crypto::Provider;
use verilith_tls::keys::Secret;
use verilith_tls::protect::{Protect, RecErr};
use verilith_tls_aws_lc::*;

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

fn alg(suite: u16) -> &'static aead::Algorithm {
    match suite {
        TLS_AES_128_GCM_SHA256 => &aead::AES_128_GCM,
        TLS_AES_256_GCM_SHA384 => &aead::AES_256_GCM,
        _ => &aead::CHACHA20_POLY1305,
    }
}

fn nonce(iv: &[u8], seq: u64) -> [u8; 12] {
    let mut n = [0u8; 12];
    n.copy_from_slice(iv);
    for (i, b) in seq.to_be_bytes().iter().enumerate() {
        n[4 + i] ^= b;
    }
    n
}

#[test]
fn seal_and_open() {
    let mut rng = Rng(0x9e3779b97f4a7c15);
    let p = AwsLc::new(None);
    for &suite in &SUITES {
        let klen = if suite == TLS_AES_128_GCM_SHA256 { 16 } else { 32 };
        let key = rng.bytes(klen);
        let iv = rng.bytes(12);
        let ivs = Secret::from_slice(&iv, 12);
        let mut tx = Protect::new(p.aead_key(suite, &key), &ivs);
        let mut rx = Protect::new(p.aead_key(suite, &key), &ivs);
        let raw = LessSafeKey::new(UnboundKey::new(alg(suite), &key).unwrap());
        for seq in 0..200u64 {
            let n = (rng.next() % 3000) as usize + if seq == 7 { 16384 - 3000 } else { 0 };
            let content = rng.bytes(n);
            let ct = [21u8, 22, 23][(seq % 3) as usize];
            let mut out = vec![0xaa; 3];
            assert!(tx.seal(ct, &content, &mut out));
            assert_eq!(&out[..3], &[0xaa; 3]);
            let rec = &out[3..];
            let len = n + 1 + 16;
            assert_eq!(&rec[..5], &[23, 3, 3, (len >> 8) as u8, len as u8]);
            let mut body = rec[5..].to_vec();
            let hdr: [u8; 5] = rec[..5].try_into().unwrap();
            let pt = raw
                .open_in_place(Nonce::assume_unique_for_key(nonce(&iv, seq)), Aad::from(&hdr), &mut body.clone())
                .unwrap()
                .to_vec();
            assert_eq!(&pt[..n], &content[..]);
            assert_eq!(pt[n], ct);
            let (t, m) = rx.open(&hdr, &mut body).ok().unwrap();
            assert_eq!((t, &body[..m]), (ct, &content[..]));
        }
    }
}

/// Seals `inner` (a whole TLSInnerPlaintext) directly, as a peer that pads.
fn raw_record(raw: &LessSafeKey, iv: &[u8], seq: u64, inner: &[u8]) -> ([u8; 5], Vec<u8>) {
    let len = inner.len() + 16;
    let hdr = [23, 3, 3, (len >> 8) as u8, len as u8];
    let mut body = inner.to_vec();
    raw.seal_in_place_append_tag(Nonce::assume_unique_for_key(nonce(iv, seq)), Aad::from(&hdr), &mut body)
        .unwrap();
    (hdr, body)
}

#[test]
fn padding_and_errors() {
    let p = AwsLc::new(None);
    let key = [7u8; 16];
    let iv = [9u8; 12];
    let raw = LessSafeKey::new(UnboundKey::new(&aead::AES_128_GCM, &key).unwrap());
    let mut rx = Protect::new(p.aead_key(TLS_AES_128_GCM_SHA256, &key), &Secret::from_slice(&iv, 12));

    // Padded: the content type is the last non-zero byte.
    let (h, mut b) = raw_record(&raw, &iv, 0, b"hello\x17\0\0\0\0");
    assert_eq!(rx.open(&h, &mut b).ok().map(|(t, n)| (t, b[..n].to_vec())), Some((23, b"hello".to_vec())));
    // Content type only.
    let (h, mut b) = raw_record(&raw, &iv, 1, b"\x16\0");
    assert_eq!(rx.open(&h, &mut b).ok().map(|(t, n)| (t, n)), Some((22, 0)));
    // All zeros: no type.
    let (h, mut b) = raw_record(&raw, &iv, 2, &[0u8; 40]);
    assert!(matches!(rx.open(&h, &mut b), Err(RecErr::NoType)));
    // A refused record does not advance the sequence number: the next
    // one is still seq 2.
    let (h, mut b) = raw_record(&raw, &iv, 2, b"x\x17");
    assert!(rx.open(&h, &mut b).is_ok());
    // Wrong sequence number, flipped bit, changed header.
    let (h, mut b) = raw_record(&raw, &iv, 9, b"x\x17");
    assert!(matches!(rx.open(&h, &mut b), Err(RecErr::BadMac)));
    let (h, mut b) = raw_record(&raw, &iv, 3, b"x\x17");
    b[0] ^= 1;
    assert!(matches!(rx.open(&h, &mut b), Err(RecErr::BadMac)));
    let (mut h, mut b) = raw_record(&raw, &iv, 3, b"x\x17");
    h[2] = 1;
    assert!(matches!(rx.open(&h, &mut b), Err(RecErr::BadMac)));
    // Inner plaintext of 2^14 + 2 bytes: record_overflow.
    let (h, mut b) = raw_record(&raw, &iv, 3, &vec![1u8; 16386]);
    assert!(matches!(rx.open(&h, &mut b), Err(RecErr::Overflow)));
    // Ciphertext over 2^14 + 256: overflow before decrypting.
    let mut b = vec![0u8; 16641];
    assert!(matches!(rx.open(&[23, 3, 3, 0x41, 0x01], &mut b), Err(RecErr::Overflow)));
}

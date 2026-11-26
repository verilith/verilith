//! QUIC packet protection (`verilith_tls::quic_packet`): RFC 9001's
//! ChaCha20-Poly1305 short header example (Appendix A.5), and for every
//! suite, packets sealed by `Aead::seal` compared with a reference built
//! directly on aws-lc, then unmasked and opened back.
use aws_lc_rs::aead::quic::{HeaderProtectionKey, AES_128, AES_256, CHACHA20};
use aws_lc_rs::aead::{Aad, LessSafeKey, Nonce, UnboundKey};
use verilith_tls::keys::{quic_keys_x, Secret};
use verilith_tls::quic_packet::{keys, unmask, update};
use verilith_tls::spec_keys::HashAlg;
use verilith_tls_aws_lc::*;

fn hex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn decode_pn(largest: u64, truncated: u64, bits: u32) -> u64 {
    // RFC 9000 Appendix A.3.
    let expected = largest + 1;
    let win = 1u64 << bits;
    let hwin = win / 2;
    let mask = win - 1;
    let cand = (expected & !mask) | truncated;
    if cand + hwin <= expected && cand < (1 << 62) - win {
        cand + win
    } else if cand > expected + hwin && cand >= win {
        cand - win
    } else {
        cand
    }
}

#[test]
fn rfc9001_a5_chacha20_short_header() {
    let prov = AwsLc::new(None);
    let secret = Secret::from_slice(&hex("9ac312a7f877468ebe69422748ad00a15443f18203a07d6060f688f30f21632b"), 32);
    let (aead, hp) = keys(&prov, TLS_CHACHA20_POLY1305_SHA256, &secret);
    let pn = 654_360_564u64;
    let mut buf = hex("4200bff401");
    aead.seal(&hp, pn, &mut buf, 0, 1, 4);
    assert_eq!(buf, hex("4cfe4189655e5cd55c41f69080575d7999c25a5bfb"));
    let (n, t) = unmask(&hp, &mut buf, 1).unwrap();
    assert_eq!((n, t), (3, 0xbff4));
    assert_eq!(decode_pn(654_360_563, t as u64, 24), pn);
    let len = aead.open(pn, &mut buf, 4).unwrap();
    assert_eq!(&buf[4..4 + len], &[0x01]);
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// The reference: RFC 9001 §5.3 and §5.4 written directly on aws-lc.
fn reference(suite: u16, secret: &Secret, pn: u64, header: &[u8], pn_off: usize, payload: &[u8]) -> Vec<u8> {
    let kl = if suite == TLS_AES_128_GCM_SHA256 { 16 } else { 32 };
    let h = if suite == TLS_AES_256_GCM_SHA384 { HashAlg::Sha384 } else { HashAlg::Sha256 };
    let (k, iv, hpk) = quic_keys_x(h, secret, kl);
    let (alg, halg) = match suite {
        TLS_AES_128_GCM_SHA256 => (&aws_lc_rs::aead::AES_128_GCM, &AES_128),
        TLS_AES_256_GCM_SHA384 => (&aws_lc_rs::aead::AES_256_GCM, &AES_256),
        _ => (&aws_lc_rs::aead::CHACHA20_POLY1305, &CHACHA20),
    };
    let key = LessSafeKey::new(UnboundKey::new(alg, k.as_slice()).unwrap());
    let mut nonce = [0u8; 12];
    nonce.copy_from_slice(iv.as_slice());
    for (i, b) in pn.to_be_bytes().iter().enumerate() {
        nonce[4 + i] ^= b;
    }
    let mut body = payload.to_vec();
    key.seal_in_place_append_tag(Nonce::assume_unique_for_key(nonce), Aad::from(header), &mut body).unwrap();
    let mut pkt = [header, &body[..]].concat();
    let mask = HeaderProtectionKey::new(halg, hpk.as_slice()).unwrap().new_mask(&pkt[pn_off + 4..pn_off + 20]).unwrap();
    pkt[0] ^= mask[0] & if pkt[0] & 0x80 != 0 { 0x0f } else { 0x1f };
    for i in 0..header.len() - pn_off {
        pkt[pn_off + i] ^= mask[1 + i];
    }
    pkt
}

#[test]
fn every_suite_against_reference() {
    let prov = AwsLc::new(None);
    let mut rng = Rng(0x1234_5678_9abc_def1);
    for &suite in &SUITES {
        let hl = if suite == TLS_AES_256_GCM_SHA384 { 48 } else { 32 };
        for _ in 0..300 {
            let sb: Vec<u8> = (0..hl).map(|_| rng.next() as u8).collect();
            let secret = Secret::from_slice(&sb, hl);
            let (aead, hp) = keys(&prov, suite, &secret);
            let pn = rng.next() % (1 << 40);
            let pn_len = 1 + (rng.next() % 4) as usize;
            let long = rng.next() % 2 == 0;
            // A long header's fixed part, or a short header with an 8-byte
            // connection ID; then the packet number.
            let mut header = if long { hex("c300000001088394c8f03e5157080000449e") } else { hex("4083_94c8f03e515708".replace('_', "").as_str()) };
            header[0] = (header[0] & !3) | (pn_len as u8 - 1);
            let pn_off = header.len();
            header.extend_from_slice(&pn.to_be_bytes()[8 - pn_len..]);
            let plen = (4 - pn_len) + (rng.next() % 1300) as usize;
            let payload: Vec<u8> = (0..plen).map(|_| rng.next() as u8).collect();
            // Seal after some coalesced packet already in the buffer.
            let prefix: Vec<u8> = (0..(rng.next() % 50)).map(|_| rng.next() as u8).collect();
            let mut buf = [&prefix[..], &header, &payload].concat();
            aead.seal(&hp, pn, &mut buf, prefix.len(), prefix.len() + pn_off, prefix.len() + header.len());
            let want = reference(suite, &secret, pn, &header, pn_off, &payload);
            assert_eq!(&buf[..prefix.len()], &prefix[..]);
            assert_eq!(&buf[prefix.len()..], &want[..], "suite {suite:#x}");
            // And back.
            let mut pkt = buf[prefix.len()..].to_vec();
            let (n, t) = unmask(&hp, &mut pkt, pn_off).unwrap();
            assert_eq!(n, pn_len);
            assert_eq!(&pkt[..header.len()], &header[..]);
            let full = decode_pn(pn.saturating_sub(1), t as u64, 8 * n as u32);
            assert_eq!(full, pn);
            let len = aead.open(full, &mut pkt, header.len()).unwrap();
            assert_eq!(&pkt[header.len()..header.len() + len], &payload[..]);
            // A flipped bit anywhere fails to open.
            let mut bad = buf[prefix.len()..].to_vec();
            let i = (rng.next() as usize) % bad.len();
            bad[i] ^= 1 << (rng.next() % 8);
            if let Some((n2, t2)) = unmask(&hp, &mut bad, pn_off) {
                let hl2 = pn_off + n2;
                let full2 = decode_pn(pn.saturating_sub(1), t2 as u64, 8 * n2 as u32);
                assert!(aead.open(full2, &mut bad, hl2).is_none());
            }
        }
    }
}

#[test]
fn key_update_changes_keys_not_header_protection() {
    let prov = AwsLc::new(None);
    let secret = Secret::from_slice(&[7u8; 32], 32);
    let (aead, hp) = keys(&prov, TLS_AES_128_GCM_SHA256, &secret);
    let (next, aead2) = update(&prov, TLS_AES_128_GCM_SHA256, &secret);
    assert_ne!(next.as_slice(), secret.as_slice());
    let header = hex("4083_94c8f03e51570801".replace('_', "").as_str());
    let mut a = [&header[..], &[0u8; 20][..]].concat();
    let mut b = a.clone();
    aead.seal(&hp, 1, &mut a, 0, 9, 10);
    aead2.seal(&hp, 1, &mut b, 0, 9, 10);
    assert_ne!(a, b);
    let mut b2 = b.clone();
    unmask(&hp, &mut b2, 9).unwrap();
    assert!(aead.open(1, &mut b2.clone(), 10).is_none());
    assert!(aead2.open(1, &mut b2, 10).is_some());
}

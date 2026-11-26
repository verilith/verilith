//! The key schedule against RFC 8448's values and against RustCrypto's
//! HKDF, written independently of this crate.
use hkdf::Hkdf;
use hmac::{Hmac, Mac};
use sha2::{Digest, Sha256, Sha384};
use verilith_tls::keys::*;
use verilith_tls::spec_keys::HashAlg;
use vstd::prelude::Ghost;

fn g<T>() -> Ghost<T> {
    Ghost::assume_new()
}

fn hex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn label(l: usize, lab: &str, ctx: &[u8]) -> Vec<u8> {
    let mut v = vec![(l >> 8) as u8, l as u8, (6 + lab.len()) as u8];
    v.extend(b"tls13 ");
    v.extend(lab.as_bytes());
    v.push(ctx.len() as u8);
    v.extend(ctx);
    v
}

/// A reference key schedule from RustCrypto's HKDF.
struct Ref {
    a: HashAlg,
}

impl Ref {
    fn hl(&self) -> usize {
        if self.a == HashAlg::Sha256 { 32 } else { 48 }
    }
    fn hash(&self, m: &[u8]) -> Vec<u8> {
        match self.a {
            HashAlg::Sha256 => Sha256::digest(m).to_vec(),
            HashAlg::Sha384 => Sha384::digest(m).to_vec(),
        }
    }
    fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        match self.a {
            HashAlg::Sha256 => Hkdf::<Sha256>::extract(Some(salt), ikm).0.to_vec(),
            HashAlg::Sha384 => Hkdf::<Sha384>::extract(Some(salt), ikm).0.to_vec(),
        }
    }
    fn expand_label(&self, secret: &[u8], lab: &str, ctx: &[u8], l: usize) -> Vec<u8> {
        let info = label(l, lab, ctx);
        let mut out = vec![0u8; l];
        match self.a {
            HashAlg::Sha256 => Hkdf::<Sha256>::from_prk(secret).unwrap().expand(&info, &mut out).unwrap(),
            HashAlg::Sha384 => Hkdf::<Sha384>::from_prk(secret).unwrap().expand(&info, &mut out).unwrap(),
        }
        out
    }
    fn derive(&self, secret: &[u8], lab: &str, msgs: &[u8]) -> Vec<u8> {
        self.expand_label(secret, lab, &self.hash(msgs), self.hl())
    }
    fn hmac(&self, k: &[u8], m: &[u8]) -> Vec<u8> {
        match self.a {
            HashAlg::Sha256 => {
                let mut h = Hmac::<Sha256>::new_from_slice(k).unwrap();
                h.update(m);
                h.finalize().into_bytes().to_vec()
            }
            HashAlg::Sha384 => {
                let mut h = Hmac::<Sha384>::new_from_slice(k).unwrap();
                h.update(m);
                h.finalize().into_bytes().to_vec()
            }
        }
    }
}

#[test]
fn rfc8448_early_and_derived() {
    // RFC 8448 §3: the early secret with no PSK, and "derived" from it.
    let early = hmac_x(HashAlg::Sha256, &[0; 32], &[0; 32]);
    assert_eq!(early.as_slice(), &hex("33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a")[..]);
    let eh = Transcript::new(HashAlg::Sha256).hash();
    let d = expand_label_x(HashAlg::Sha256, early.as_slice(), b"derived", eh.as_slice(), 32);
    assert_eq!(d.as_slice(), &hex("6f2615a108c702c5678f54fc9dbab69716c076189c48250cebeac3576c3611ba")[..]);
}

#[test]
fn schedule_matches_rustcrypto() {
    let mut seed = 0x1234_5678_9abc_def0u64;
    let mut rnd = move |n: usize| -> Vec<u8> {
        (0..n)
            .map(|_| {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                seed as u8
            })
            .collect()
    };
    for a in [HashAlg::Sha256, HashAlg::Sha384] {
        let r = Ref { a };
        let hl = r.hl();
        for round in 0..50 {
            let dhe = rnd(if round % 2 == 0 { 32 } else { 64 });
            let msgs1 = rnd(100 + round * 37);
            let msgs2 = [msgs1.clone(), rnd(3000)].concat();
            let msgs3 = [msgs2.clone(), rnd(50)].concat();

            // Reference.
            let early = r.extract(&vec![0; hl], &vec![0; hl]);
            let hs = r.extract(&r.derive(&early, "derived", b""), &dhe);
            let ms = r.extract(&r.derive(&hs, "derived", b""), &vec![0; hl]);
            let c_hs = r.derive(&hs, "c hs traffic", &msgs1);
            let s_hs = r.derive(&hs, "s hs traffic", &msgs1);
            let c_ap = r.derive(&ms, "c ap traffic", &msgs2);
            let s_ap = r.derive(&ms, "s ap traffic", &msgs2);
            let exp = r.derive(&ms, "exp master", &msgs2);
            let res = r.derive(&ms, "res master", &msgs3);
            let fin = r.hmac(&r.expand_label(&s_hs, "finished", b"", hl), &r.hash(&msgs2));
            let key = r.expand_label(&s_ap, "key", b"", 16);
            let iv = r.expand_label(&s_ap, "iv", b"", 12);
            let upd = r.expand_label(&c_ap, "traffic upd", b"", hl);

            // Ours, with a running transcript.
            let mut t = Transcript::new(a);
            t.update(&msgs1);
            let th1 = t.hash();
            t.update(&msgs2[msgs1.len()..]);
            let th2 = t.hash();
            t.update(&msgs3[msgs2.len()..]);
            let th3 = t.hash();
            let our_hs = handshake_secret_x(a, Secret::zeros_of(a).as_slice(), &dhe);
            assert_eq!(our_hs.as_slice(), &hs[..]);
            let our_ms = master_secret_x(a, &our_hs, g(), g());
            assert_eq!(our_ms.as_slice(), &ms[..]);
            let (c, s) = hs_traffic_x(a, &our_hs, &th1, g(), g(), g());
            assert_eq!((c.as_slice(), s.as_slice()), (&c_hs[..], &s_hs[..]));
            let (c2, s2, e2) = ap_traffic_x(a, &our_ms, &th2, g(), g(), g());
            assert_eq!((c2.as_slice(), s2.as_slice(), e2.as_slice()), (&c_ap[..], &s_ap[..], &exp[..]));
            assert_eq!(resumption_master_x(a, &our_ms, &th3, g(), g(), g()).as_slice(), &res[..]);
            assert_eq!(verify_data_x(a, &s, &th2, g()).as_slice(), &fin[..]);
            let (k, v) = traffic_keys_x(a, &s2, 16);
            assert_eq!((k.as_slice(), v.as_slice()), (&key[..], &iv[..]));
            assert_eq!(next_traffic_secret_x(a, &c2).as_slice(), &upd[..]);
        }
    }
}

#[test]
fn nonces() {
    let iv: [u8; 12] = core::array::from_fn(|i| (i as u8).wrapping_mul(37) ^ 0xa5);
    for seq in [0u64, 1, 255, 256, 0x0102_0304_0506_0708, u64::MAX] {
        let mut want = iv;
        for (i, b) in seq.to_be_bytes().iter().enumerate() {
            want[4 + i] ^= b;
        }
        assert_eq!(record_nonce_x(&iv, seq), want, "{seq:x}");
    }
}

//! RustCrypto's `digest` traits (`--features digest,digest010,oid`): the
//! hashers through `Digest` and `DynDigest`, generic code written for
//! RustCrypto's `sha2`, RustCrypto's own `SimpleHmac` over these hashers,
//! and the MACs through `Mac`, all against RustCrypto.

/// xorshift64*: reproducible bytes.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
}

mod v011 {
    use super::Rng;
    use ::hmac::SimpleHmac;
    use verilith_sha2::digest::const_oid::AssociatedOid;
    use verilith_sha2::digest::{Digest, DynDigest, KeyInit, Mac};

    /// Generic code as written against RustCrypto's `sha2`.
    fn generic<D: Digest>(d: &[u8]) -> Vec<u8> {
        let mut h = D::new();
        let (a, b) = d.split_at(d.len() / 3);
        h.update(a);
        Digest::update(&mut h, b);
        h.finalize().to_vec()
    }

    fn generic_mac<M: Mac + KeyInit>(k: &[u8], d: &[u8]) -> Vec<u8> {
        let mut m = <M as KeyInit>::new_from_slice(k).unwrap();
        Mac::update(&mut m, d);
        m.finalize().into_bytes().to_vec()
    }

    macro_rules! case {
        ($name:ident, $ours:ident, $theirs:ident, $hm:ident) => {
            #[test]
            fn $name() {
                use verilith_sha2::$ours as Ours;
                let mut r = Rng(0x1234_5678 ^ stringify!($name).len() as u64);
                assert_eq!(Ours::OID, sha2::$theirs::OID);
                assert_eq!(<Ours as Digest>::output_size(), <sha2::$theirs as Digest>::output_size());
                for n in (0..600).chain([4096, 65537]) {
                    let d = r.bytes(n);
                    let want = sha2::$theirs::digest(&d).to_vec();
                    assert_eq!(generic::<Ours>(&d), want);
                    assert_eq!(Ours::digest(&d).to_vec(), want);
                    // finalize_reset leaves a fresh hasher.
                    let mut h = <Ours as Digest>::new();
                    Digest::update(&mut h, &d);
                    assert_eq!(Digest::finalize_reset(&mut h).to_vec(), want);
                    Digest::update(&mut h, &d);
                    assert_eq!(Digest::finalize(h).to_vec(), want);
                    // Through a trait object.
                    let mut dy: Box<dyn DynDigest> = Box::new(<Ours as Digest>::new());
                    dy.update(&d);
                    let c = dy.box_clone();
                    assert_eq!(&dy.finalize()[..], &want[..]);
                    assert_eq!(&c.finalize()[..], &want[..]);
                    // RustCrypto's HMAC over our hasher, our HMAC through `Mac`.
                    let kl = (r.next() % 300) as usize;
                    let k = r.bytes(kl);
                    let want = generic_mac::<SimpleHmac<sha2::$theirs>>(&k, &d);
                    assert_eq!(generic_mac::<SimpleHmac<Ours>>(&k, &d), want);
                    assert_eq!(generic_mac::<verilith_sha2::$hm>(&k, &d), want);
                    let mut m = <verilith_sha2::$hm as KeyInit>::new_from_slice(&k).unwrap();
                    Mac::update(&mut m, &d);
                    assert!(m.clone().verify_slice(&want).is_ok());
                    assert!(m.clone().verify_slice(&want[1..]).is_err());
                    assert_eq!(Mac::finalize_reset(&mut m).into_bytes().to_vec(), want);
                    Mac::update(&mut m, &d);
                    assert!(m.verify_slice(&want).is_ok());
                }
            }
        };
    }

    case!(sha224, Sha224, Sha224, HmacSha224);
    case!(sha256, Sha256, Sha256, HmacSha256);
    case!(sha384, Sha384, Sha384, HmacSha384);
    case!(sha512, Sha512, Sha512, HmacSha512);
    case!(sha512_224, Sha512_224, Sha512_224, HmacSha512_224);
    case!(sha512_256, Sha512_256, Sha512_256, HmacSha512_256);
}

mod v010 {
    use super::Rng;
    use hmac012::SimpleHmac;
    use verilith_sha2::digest010::{Digest, KeyInit, Mac};

    macro_rules! case {
        ($name:ident, $ours:ident, $theirs:ident, $hm:ident) => {
            #[test]
            fn $name() {
                use verilith_sha2::$ours as Ours;
                let mut r = Rng(0x8765_4321 ^ stringify!($name).len() as u64);
                for n in (0..300).chain([4096]) {
                    let d = r.bytes(n);
                    let want = sha2_010::$theirs::digest(&d).to_vec();
                    assert_eq!(<Ours as Digest>::digest(&d).to_vec(), want);
                    let kl = (r.next() % 300) as usize;
                    let k = r.bytes(kl);
                    let mut t = <SimpleHmac<sha2_010::$theirs> as KeyInit>::new_from_slice(&k).unwrap();
                    Mac::update(&mut t, &d);
                    let want = t.finalize().into_bytes().to_vec();
                    let mut o = <SimpleHmac<Ours> as KeyInit>::new_from_slice(&k).unwrap();
                    Mac::update(&mut o, &d);
                    assert_eq!(o.finalize().into_bytes().to_vec(), want);
                    let mut m = <verilith_sha2::$hm as KeyInit>::new_from_slice(&k).unwrap();
                    Mac::update(&mut m, &d);
                    assert!(m.verify_slice(&want).is_ok());
                }
            }
        };
    }

    case!(sha224, Sha224, Sha224, HmacSha224);
    case!(sha256, Sha256, Sha256, HmacSha256);
    case!(sha384, Sha384, Sha384, HmacSha384);
    case!(sha512, Sha512, Sha512, HmacSha512);
    case!(sha512_224, Sha512_224, Sha512_224, HmacSha512_224);
    case!(sha512_256, Sha512_256, Sha512_256, HmacSha512_256);
}

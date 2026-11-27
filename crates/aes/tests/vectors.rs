//! Known answers: the S-box derived again from FIPS 197 §5.1.1, FIPS 197
//! Appendix C's AES-128 and AES-256 examples, and the GCM paper's test
//! cases with 96-bit IVs (McGrew and Viega, "The Galois/Counter Mode of
//! Operation", test cases 1-4 and 13-16), the vectors NIST's GCM
//! validation starts from.
use verilith_aes::spec::SBOX;
use verilith_aes::{Aes, AesGcm};

fn hex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

/// Multiplication in GF(2^8) modulo x^8 + x^4 + x^3 + x + 1.
fn gmul(mut a: u8, mut b: u8) -> u8 {
    let mut p = 0;
    while b != 0 {
        if b & 1 != 0 {
            p ^= a;
        }
        a = (a << 1) ^ if a & 0x80 != 0 { 0x1b } else { 0 };
        b >>= 1;
    }
    p
}

#[test]
fn sbox() {
    for b in 0..=255u8 {
        // The multiplicative inverse (0 for 0), then the affine map.
        let inv = (0..=255u8).find(|&c| gmul(b, c) == 1).unwrap_or(0);
        let s = inv ^ inv.rotate_left(1) ^ inv.rotate_left(2) ^ inv.rotate_left(3) ^ inv.rotate_left(4) ^ 0x63;
        assert_eq!(SBOX[b as usize], s, "S-box entry {b:#04x}");
    }
}

#[test]
fn fips197() {
    for (key, ct) in [
        ("000102030405060708090a0b0c0d0e0f", "69c4e0d86a7b0430d8cdb78070b4c55a"),
        ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f", "8ea2b7ca516745bfeafc49904b496089"),
    ] {
        let Some(k) = Aes::new(&hex(key)) else { return };
        let mut b: [u8; 16] = hex("00112233445566778899aabbccddeeff").try_into().unwrap();
        k.encrypt_block(&mut b);
        assert_eq!(b.to_vec(), hex(ct));
    }
}

const K3: &str = "feffe9928665731c6d6a8f9467308308";
const P3: &str = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255";
const IV3: &str = "cafebabefacedbaddecaf888";
const A4: &str = "feedfacedeadbeeffeedfacedeadbeefabaddad2";

#[test]
fn gcm() {
    let z16 = "00000000000000000000000000000000";
    let z32 = "0000000000000000000000000000000000000000000000000000000000000000";
    let k15 = format!("{K3}{K3}");
    let cases: [(&str, &str, &str, &str, &str, &str); 8] = [
        (z16, "000000000000000000000000", "", "", "", "58e2fccefa7e3061367f1d57a4e7455a"),
        (z16, "000000000000000000000000", z16, "", "0388dace60b6a392f328c2b971b2fe78", "ab6e47d42cec13bdf53a67b21257bddf"),
        (K3, IV3, P3, "", "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985", "4d5c2af327cd64a62cf35abd2ba6fab4"),
        (K3, IV3, &P3[..120], A4, "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091", "5bc94fbc3221a5db94fae95ae7121a47"),
        (z32, "000000000000000000000000", "", "", "", "530f8afbc74536b9a963b4f1c4cb738b"),
        (z32, "000000000000000000000000", z16, "", "cea7403d4d606b6e074ec5d3baf39d18", "d0d1c8a799996bf0265b98b5d48ab919"),
        (&k15, IV3, P3, "", "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad", "b094dac5d93471bdec1a502270e3cc6c"),
        (&k15, IV3, &P3[..120], A4, "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad"[..120].as_ref(), "76fc6ece0f4e1768cddf8853bb2d551b"),
    ];
    for (n, (key, iv, pt, aad, ct, tag)) in cases.iter().enumerate() {
        let Some(k) = AesGcm::new(&hex(key)) else { return };
        let iv: [u8; 12] = hex(iv).try_into().unwrap();
        let mut buf = hex(pt);
        let mut t = [0u8; 16];
        assert!(k.seal(&iv, &hex(aad), &mut buf, &mut t));
        assert_eq!(buf, hex(ct), "case {n}: ciphertext");
        assert_eq!(t.to_vec(), hex(tag), "case {n}: tag");
        let t: [u8; 16] = hex(tag).try_into().unwrap();
        assert!(k.open(&iv, &hex(aad), &mut buf, &t));
        assert_eq!(buf, hex(pt));
    }
}

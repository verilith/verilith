//! Known-answer tests for the verified hashing the validator uses: SHA-1
//! (FIPS 180-4 examples) and NSEC3 hashing (RFC 5155 Appendix A), checked
//! against the vectors and against aws-lc-rs.
mod sec;

use verilith_resolver::nsec::{b32hex_x, ih_x};
use verilith_resolver::sha1::sha1_x;

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

#[test]
fn sha1_vectors() {
    assert_eq!(hex(&sha1_x(b"abc")), "a9993e364706816aba3e25717850c26c9cd0d89d");
    assert_eq!(hex(&sha1_x(b"")), "da39a3ee5e6b4b0d3255bfef95601890afd80709");
    assert_eq!(
        hex(&sha1_x(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")),
        "84983e441c3bd26ebaae4aa1f95129e5e54670f1"
    );
    let mut d = Vec::new();
    for n in 0..300usize {
        let v = sha1_x(&d);
        let w = aws_lc_rs::digest::digest(&aws_lc_rs::digest::SHA1_FOR_LEGACY_USE_ONLY, &d);
        assert_eq!(v.as_slice(), w.as_ref(), "length {n}");
        d.push((n * 7 + 3) as u8);
    }
}

#[test]
fn nsec3_rfc5155_appendix_a() {
    let salt = [0xaa, 0xbb, 0xcc, 0xdd];
    for (name, want) in [
        ("example", "0p9mhaveqvm6t7vbl5lop2u3t2rp3tom"),
        ("a.example", "35mthgpgcu1qg68fab165klnsnk3dpvl"),
        ("ai.example", "gjeqe526plbf1g8mklp59enfd789njgi"),
        ("ns1.example", "2t7b4g4vsa5smi47k61mv5bv1a22bojr"),
        ("w.example", "k8udemvp1j2f7eg6jebps17vp3n8i58h"),
        ("*.w.example", "r53bq7cc2uvmubfu5ocmm6pers9tk9en"),
        ("x.w.example", "b4um86eghhds6nea196smvmlo4ors995"),
        ("xx.example", "t644ebqk9bibcna874givr6joj62mlhv"),
    ] {
        let h = ih_x(&salt, &sec::wire(name), 12);
        assert_eq!(String::from_utf8(b32hex_x(&h)).unwrap(), want, "{name}");
        assert_eq!(sec::base32hex(&sec::nsec3_hash(name, 12, &salt)), want, "{name}, the test signer");
    }
}

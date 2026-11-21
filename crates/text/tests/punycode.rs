//! Punycode against RFC 3492's sample strings and the `idna` crate.
use rand::{Rng, SeedableRng};
use verilith_text::idna::punycode::{decode_str, encode_str};

const RFC_SAMPLES: &[(&str, &str)] = &[
    ("\u{644}\u{64A}\u{647}\u{645}\u{627}\u{628}\u{62A}\u{643}\u{644}\u{645}\u{648}\u{634}\u{639}\u{631}\u{628}\u{64A}\u{61F}", "egbpdaj6bu4bxfgehfvwxn"),
    ("\u{4ED6}\u{4EEC}\u{4E3A}\u{4EC0}\u{4E48}\u{4E0D}\u{8BF4}\u{4E2D}\u{6587}", "ihqwcrb4cv8a8dqg056pqjye"),
    ("Pro\u{10D}prost\u{11B}nemluv\u{ED}\u{10D}esky", "Proprostnemluvesky-uyb24dma41a"),
    ("\u{3072}\u{3068}\u{3064}\u{5C4B}\u{6839}\u{306E}\u{4E0B}2", "2-u9tlzr9756bt3uc0v"),
    ("MajiでKoiする5秒前", "MajiKoi5-783gue6qz075azm5e"),
    ("-> $1.00 <-", "-> $1.00 <--"),
];

#[test]
fn rfc_samples() {
    for &(u, p) in RFC_SAMPLES {
        assert_eq!(encode_str(u).as_deref(), Some(p), "{u}");
        assert_eq!(decode_str(p).as_deref(), Some(u), "{p}");
    }
}

fn random_label(rng: &mut impl Rng) -> String {
    let len = rng.gen_range(0..20);
    (0..len)
        .map(|_| match rng.gen_range(0..6) {
            0 => rng.gen_range(b'a'..=b'z') as char,
            1 => b"-0123456789AZ"[rng.gen_range(0..13)] as char,
            2 => char::from_u32(rng.gen_range(0x80..0x800)).unwrap(),
            3 => char::from_u32(rng.gen_range(0x3000..0xA000)).unwrap(),
            4 => rng.gen::<char>(),
            _ => char::from_u32(rng.gen_range(0xE0..0x180)).unwrap(),
        })
        .collect()
}

#[test]
fn differential() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(7);
    for _ in 0..200_000 {
        let u = random_label(&mut rng);
        let ours = encode_str(&u);
        let theirs = idna::punycode::encode_str(&u);
        assert_eq!(ours, theirs, "encode {u:?}");
        if let Some(p) = &ours {
            assert_eq!(decode_str(p).as_deref(), Some(u.as_str()), "round trip {u:?}");
        }
        // Arbitrary ASCII, to exercise decoding failures.
        let a: String = (0..rng.gen_range(0..16))
            .map(|_| b"abcxyz019-AZ.\x7f"[rng.gen_range(0..14)] as char)
            .collect();
        assert_eq!(decode_str(&a), idna::punycode::decode_to_string(&a), "decode {a:?}");
        // And mutations of valid encodings.
        if let Some(mut p) = ours {
            if !p.is_empty() {
                let k = rng.gen_range(0..p.len());
                let c = b"a9z0-B"[rng.gen_range(0..6)];
                // SAFETY: replacing one ASCII byte keeps UTF-8.
                unsafe { p.as_bytes_mut()[k] = c };
                assert_eq!(decode_str(&p), idna::punycode::decode_to_string(&p), "decode {p:?}");
            }
        }
    }
}

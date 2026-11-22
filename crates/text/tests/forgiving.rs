//! Forgiving base64 against an independent transcription of the WHATWG Infra
//! algorithm, decoding with the `base64` crate, on random and damaged text.
use base64::engine::general_purpose::{GeneralPurpose, GeneralPurposeConfig};
use base64::engine::DecodePaddingMode;
use base64::Engine;
use rand::{Rng, RngExt, SeedableRng};
use verilith_text::base64::forgiving::{decode_forgiving, max_len_exec, B64Error};

fn engine(url: bool) -> GeneralPurpose {
    let cfg = GeneralPurposeConfig::new()
        .with_decode_allow_trailing_bits(true)
        .with_decode_padding_mode(DecodePaddingMode::RequireNone);
    GeneralPurpose::new(if url { &base64::alphabet::URL_SAFE } else { &base64::alphabet::STANDARD }, cfg)
}

/// https://infra.spec.whatwg.org/#forgiving-base64-decode
fn reference(url: bool, s: &[u8]) -> Option<Vec<u8>> {
    let mut d: Vec<u8> = s.iter().copied().filter(|c| !matches!(c, b' ' | b'\t' | b'\n' | 0x0C | b'\r')).collect();
    if d.len() % 4 == 0 {
        if d.ends_with(b"==") {
            d.truncate(d.len() - 2);
        } else if d.ends_with(b"=") {
            d.truncate(d.len() - 1);
        }
    }
    if d.len() % 4 == 1 {
        return None;
    }
    let ok = |c: &u8| c.is_ascii_alphanumeric() || if url { b"-_".contains(c) } else { b"+/".contains(c) };
    if !d.iter().all(ok) {
        return None;
    }
    Some(engine(url).decode(&d).expect("alphabet checked"))
}

fn sample(r: &mut impl Rng, url: bool) -> Vec<u8> {
    let bin: Vec<u8> = (0..r.random_range(0..120)).map(|_| r.random()).collect();
    let pad = r.random_bool(0.5);
    let alpha = if url { &base64::alphabet::URL_SAFE } else { &base64::alphabet::STANDARD };
    let e = GeneralPurpose::new(alpha, GeneralPurposeConfig::new().with_encode_padding(pad));
    let mut s = e.encode(&bin).into_bytes();
    const NOISE: &[u8] = b"AZaz09+/-_= \t\n\r\x0c=.\xff\x00";
    for _ in 0..r.random_range(0..4) {
        match r.random_range(0..5) {
            0 if !s.is_empty() => {
                let i = r.random_range(0..s.len());
                s[i] = NOISE[r.random_range(0..NOISE.len())];
            }
            1 => {
                let i = r.random_range(0..=s.len());
                s.insert(i, b" \t\n\r\x0c"[r.random_range(0..5)]);
            }
            2 if !s.is_empty() => {
                s.truncate(r.random_range(0..s.len()));
            }
            3 => s.extend_from_slice(&b"==  "[..r.random_range(0..4)]),
            _ => {}
        }
    }
    s
}

#[test]
fn against_whatwg() {
    let mut r = rand::rngs::StdRng::seed_from_u64(7);
    for i in 0..300_000 {
        let url = i % 2 == 1;
        let s = sample(&mut r, url);
        let m = max_len_exec(&s);
        let mut out = vec![0u8; m];
        let got = decode_forgiving(url, &s, &mut out);
        match (reference(url, &s), got) {
            (Some(want), Ok(n)) => assert_eq!(&out[..n], &want[..], "{:?}", String::from_utf8_lossy(&s)),
            (None, Err(B64Error::Invalid | B64Error::Remainder)) => {}
            (want, got) => panic!("{:?}: want {:?}, got {:?}", String::from_utf8_lossy(&s), want, got),
        }
        // A buffer one byte short of the output is reported as too small.
        if let Ok(n) = got {
            if n > 0 {
                let mut short = vec![0u8; n - 1];
                assert!(matches!(decode_forgiving(url, &s, &mut short), Err(B64Error::TooSmall)));
            }
        }
    }
}

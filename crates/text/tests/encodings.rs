//! Differential tests of base64, hex and percent-encoding against the
//! base64, hex and percent-encoding crates.
use base64::Engine as _;
use rand::{RngExt, SeedableRng};
use rand::rngs::StdRng;

fn engines() -> [(verilith_text::base64::Engine, base64::engine::GeneralPurpose); 4] {
    use base64::engine::general_purpose as gp;
    [
        (verilith_text::base64::STANDARD, gp::STANDARD),
        (verilith_text::base64::STANDARD_NO_PAD, gp::STANDARD_NO_PAD),
        (verilith_text::base64::URL_SAFE, gp::URL_SAFE),
        (verilith_text::base64::URL_SAFE_NO_PAD, gp::URL_SAFE_NO_PAD),
    ]
}

#[test]
fn base64_encode_matches() {
    let mut rng = StdRng::seed_from_u64(1);
    for len in 0..600 {
        for _ in 0..8 {
            let x: Vec<u8> = (0..len).map(|_| rng.random()).collect();
            for (v, r) in engines() {
                let e = v.encode(&x);
                assert_eq!(e, r.encode(&x), "len {}", len);
                assert_eq!(v.decode(&e).unwrap(), x);
            }
        }
    }
}

/// A random string that is often almost an encoding: characters from the
/// alphabet with padding, and the occasional stray byte.
fn near_base64(rng: &mut StdRng, url: bool) -> Vec<u8> {
    let alpha: &[u8] = if url {
        b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
    } else {
        b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
    };
    let n = rng.random_range(0..80);
    let mut s: Vec<u8> = (0..n).map(|_| alpha[rng.random_range(0..64)]).collect();
    match rng.random_range(0..6) {
        0 => s.push(b'='),
        1 => s.extend_from_slice(b"=="),
        2 => s.extend_from_slice(b"==="),
        3 if n > 0 => {
            let i = rng.random_range(0..n);
            s[i] = rng.random();
        }
        _ => {}
    }
    s
}

#[test]
fn base64_decode_matches() {
    let mut rng = StdRng::seed_from_u64(2);
    let mut accepted = 0;
    for _ in 0..400_000 {
        for (v, r) in engines() {
            let s = near_base64(&mut rng, v == verilith_text::base64::URL_SAFE || v == verilith_text::base64::URL_SAFE_NO_PAD);
            let a = v.decode(&s);
            let b = r.decode(&s);
            assert_eq!(a.is_ok(), b.is_ok(), "{:?}: {:?} vs {:?}", String::from_utf8_lossy(&s), a, b);
            if let (Ok(a), Ok(b)) = (&a, &b) {
                assert_eq!(a, b);
                accepted += 1;
            }
        }
    }
    assert!(accepted > 100_000);
}

/// The same error, with the same offset and byte. base64 0.23 made
/// `InvalidLastSymbol` a struct variant (it adds the symbol's value), so the
/// two types are compared field by field.
fn same_error(a: &verilith_text::base64::DecodeError, b: &base64::DecodeError) -> bool {
    use base64::DecodeError as B;
    use verilith_text::base64::DecodeError as A;
    match (a, b) {
        (A::InvalidByte(i, x), B::InvalidByte(j, y)) => i == j && x == y,
        (A::InvalidLength(n), B::InvalidLength(m)) => n == m,
        (A::InvalidLastSymbol(i, x), B::InvalidLastSymbol { offset, symbol, .. }) => i == offset && x == symbol,
        (A::InvalidPadding, B::InvalidPadding) => true,
        _ => false,
    }
}

#[test]
fn base64_decode_errors_match() {
    let mut rng = StdRng::seed_from_u64(3);
    let mut differ = 0;
    let total = 100_000;
    for _ in 0..total {
        for (v, r) in engines() {
            let s = near_base64(&mut rng, v == verilith_text::base64::URL_SAFE || v == verilith_text::base64::URL_SAFE_NO_PAD);
            if let (Err(a), Err(b)) = (v.decode(&s), r.decode(&s)) {
                if !same_error(&a, &b) {
                    if differ < 10 {
                        eprintln!("{:?}: {:?} vs {:?}", String::from_utf8_lossy(&s), a, b);
                    }
                    differ += 1;
                }
            }
        }
    }
    assert_eq!(differ, 0);
}

#[test]
fn hex_matches() {
    let mut rng = StdRng::seed_from_u64(4);
    for len in 0..300 {
        let x: Vec<u8> = (0..len).map(|_| rng.random()).collect();
        assert_eq!(verilith_text::hex::encode(&x), hex::encode(&x));
        assert_eq!(verilith_text::hex::encode_upper(&x), hex::encode_upper(&x));
        assert_eq!(verilith_text::hex::decode(hex::encode_upper(&x)).unwrap(), x);
    }
    let digits = b"0123456789abcdefABCDEFgG ";
    for _ in 0..200_000 {
        let n = rng.random_range(0..12);
        let s: Vec<u8> = (0..n).map(|_| digits[rng.random_range(0..digits.len())]).collect();
        let a = verilith_text::hex::decode(&s);
        let b = hex::decode(&s);
        assert_eq!(a.is_ok(), b.is_ok());
        assert_eq!(format!("{:?}", a), format!("{:?}", b));
    }
}

#[test]
fn percent_matches() {
    use percent_encoding as pe;
    const SET_V: &verilith_text::percent::AsciiSet = &verilith_text::percent::CONTROLS.add(b' ').add(b'"').add(b'%').add(b'<');
    const SET_R: &pe::AsciiSet = &pe::CONTROLS.add(b' ').add(b'"').add(b'%').add(b'<');
    let mut rng = StdRng::seed_from_u64(5);
    let pool = b"%%%aZ09 \"<>\x7f\x00\xc3\xa9fF/";
    for _ in 0..200_000 {
        let n = rng.random_range(0..20);
        let s: Vec<u8> = (0..n).map(|_| pool[rng.random_range(0..pool.len())]).collect();
        for (sv, sr) in [(SET_V, SET_R), (verilith_text::percent::NON_ALPHANUMERIC, pe::NON_ALPHANUMERIC), (verilith_text::percent::CONTROLS, pe::CONTROLS)] {
            let a = verilith_text::percent::percent_encode(&s, sv).to_string();
            let b = pe::percent_encode(&s, sr).to_string();
            assert_eq!(a, b);
        }
        let a: Vec<u8> = verilith_text::percent::percent_decode(&s).collect();
        let b: Vec<u8> = pe::percent_decode(&s).collect();
        assert_eq!(a, b, "{:?}", String::from_utf8_lossy(&s));
        // The round trip.
        let e = verilith_text::percent::percent_encode(&s, SET_V).to_string();
        let d: Vec<u8> = verilith_text::percent::percent_decode(e.as_bytes()).collect();
        assert_eq!(d, s);
    }
}

/// Long inputs, so the AVX2 kernels run many steps, with one bad byte
/// planted at a random position (or none).
#[test]
fn base64_long_inputs() {
    let mut rng = StdRng::seed_from_u64(6);
    for _ in 0..20_000 {
        let n = rng.random_range(0..400);
        let x: Vec<u8> = (0..n).map(|_| rng.random()).collect();
        for (v, r) in engines() {
            let mut e = r.encode(&x).into_bytes();
            assert_eq!(v.encode(&x).as_bytes(), &e[..]);
            if !e.is_empty() && rng.random_bool(0.5) {
                let i = rng.random_range(0..e.len());
                e[i] = rng.random();
            }
            let a = v.decode(&e);
            let b = r.decode(&e);
            assert_eq!(a, b.map_err(|_| a.clone().unwrap_err()));
        }
    }
}

#[test]
fn hex_long_inputs() {
    let mut rng = StdRng::seed_from_u64(7);
    for _ in 0..20_000 {
        let n = rng.random_range(0..300);
        let x: Vec<u8> = (0..n).map(|_| rng.random()).collect();
        let upper = rng.random_bool(0.5);
        let mut e = if upper { hex::encode_upper(&x) } else { hex::encode(&x) }.into_bytes();
        assert_eq!(if upper { verilith_text::hex::encode_upper(&x) } else { verilith_text::hex::encode(&x) }.as_bytes(), &e[..]);
        if !e.is_empty() && rng.random_bool(0.5) {
            let i = rng.random_range(0..e.len());
            e[i] = rng.random();
        }
        assert_eq!(format!("{:?}", verilith_text::hex::decode(&e)), format!("{:?}", hex::decode(&e)));
    }
}

//! Number conversion for the lazy reader.
//!
//! The verified parser guarantees each number token is an RFC 8259 number
//! lexeme. This module turns the lexeme into an `f64`, correctly rounded:
//!
//! * the lexeme is read by the parser's `ex_number_scan`, which is verified
//!   to give its exact significand and power of ten (`number_value`) when
//!   it has at most 19 significant digits;
//! * `w * 10^q` is converted by `float::to_bits`, which is verified to
//!   return the nearest double, ties to even;
//! * lexemes with more than 19 significant digits, and the cases `to_bits`
//!   leaves undecided (none in testing), fall back to `f64::from_str`.
//!
//! It is tested bit for bit against `f64::from_str` on random lexemes.

/// Parses an RFC 8259 number lexeme.
#[inline]
pub fn parse_f64(lex: &[u8]) -> f64 {
    parse_f64_at(lex, 0, lex.len())
}

/// Parses the number lexeme `src[a..b]`. Reads may look past `b` (but not
/// past `src`), so the byte at `b`, if any, must not be a digit, as is the
/// case after every number the parser accepts.
#[inline]
pub fn parse_f64_at(src: &[u8], a: usize, b: usize) -> f64 {
    // The verified scanner gives the lexeme's exact `number_value` when it
    // has at most 19 significant digits.
    if a < b && b <= src.len() {
        if let Some((e, v, true)) = crate::parser::ex_number_scan(src, a) {
            if e == b {
                if let Some(x) = from_parts(v.neg, v.w, v.q as i64) {
                    return x;
                }
            }
        }
    }
    slow(&src[a..b])
}

/// `w * 10^q`, negated if `neg`, correctly rounded, if the fast algorithms
/// can decide it (`w` must be exact). Otherwise `None`.
#[inline]
pub fn from_parts(neg: bool, w: u64, q: i64) -> Option<f64> {
    // The verified conversion gives the bit pattern of the nearest double;
    // the sign is the top bit.
    let b = crate::float::to_bits(w, q)?;
    Some(f64::from_bits(b | ((neg as u64) << 63)))
}

#[cold]
fn slow(lex: &[u8]) -> f64 {
    // Every RFC 8259 number is accepted by `f64::from_str`.
    match core::str::from_utf8(lex) {
        Ok(t) => t.parse::<f64>().unwrap_or(f64::NAN),
        Err(_) => f64::NAN,
    }
}

/// Parses an integer lexeme (no fraction or exponent) that fits in `i64`.
pub fn parse_i64(lex: &[u8]) -> Option<i64> {
    let (neg, digits) = match lex.first() {
        Some(b'-') => (true, &lex[1..]),
        _ => (false, lex),
    };
    if digits.is_empty() || !digits.iter().all(u8::is_ascii_digit) {
        return None;
    }
    let mut v: i64 = 0;
    for &d in digits {
        let d = (d - b'0') as i64;
        v = v.checked_mul(10)?;
        v = if neg { v.checked_sub(d)? } else { v.checked_add(d)? };
    }
    Some(v)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn agrees_with_std() {
        for s in [
            "0", "-0", "1", "-1", "12345", "1.5", "-0.25", "1e10", "1E-5", "123.456e7",
            "9007199254740993", "0.1", "3.141592653589793", "1e22", "1e23", "1e-22", "1e-23",
            "12345678901234567890", "2.2250738585072014e-308", "1.7976931348623157e308",
            "1e400", "1e-400", "-12.34e+2", "4.9e-324", "2.4703282292062327e-324",
            "2.4703282292062328e-324", "2.2250738585072011e-308", "2.2250738585072012e-308",
            "1.7976931348623158e308", "1.7976931348623159e308", "9007199254740993.0",
            "0.000000000000000000000000000000000000001234567890123456789",
            "123456789012345678901234567890", "1.00000000000000011102230246251565404236316680908203125",
            "7.2057594037927933e16", "0.0", "-0.0e5", "0e400",
        ] {
            let want: f64 = s.parse().unwrap();
            let got = parse_f64(s.as_bytes());
            assert!(want.to_bits() == got.to_bits(), "{s}: {got} != {want}");
        }
    }

    /// The fast path, bit for bit against `f64::from_str`, on
    /// every power of ten it takes and significands of every length,
    /// including the edges `1` and `2^53 - 1`.
    #[test]
    fn clinger_against_std() {
        let mut x: u64 = 0x2545_F491_4F6C_DD1D;
        for q in -22i64..=22 {
            for n in 0..20_000u64 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let w = match n {
                    0 => 1,
                    1 => (1u64 << 53) - 1,
                    _ => (x >> (11 + n % 53)).max(1),
                };
                let want: f64 = format!("{w}e{q}").parse().unwrap();
                assert_eq!(crate::float::clinger(w, q), want.to_bits(), "{w}e{q}");
            }
        }
    }

    /// Random lexemes of every shape, bit for bit against `f64::from_str`.
    #[test]
    fn random_against_std() {
        let mut x: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut rnd = move || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        let mut s = String::new();
        for n in 0..2_000_000 {
            s.clear();
            if rnd() & 1 == 0 {
                s.push('-');
            }
            let r = rnd();
            let int_digits = 1 + (r % 22) as usize;
            if r >> 8 & 7 == 0 {
                s.push('0');
            } else {
                for k in 0..int_digits {
                    let d = (rnd() % 10) as u8;
                    s.push((b'0' + if k == 0 { d.max(1) } else { d }) as char);
                }
            }
            if r >> 12 & 1 == 0 {
                s.push('.');
                for _ in 0..1 + (r >> 16) % 20 {
                    s.push((b'0' + (rnd() % 10) as u8) as char);
                }
            }
            if r >> 24 & 1 == 0 {
                s.push(if r >> 25 & 1 == 0 { 'e' } else { 'E' });
                match r >> 26 & 3 {
                    0 => s.push('-'),
                    1 => s.push('+'),
                    _ => {}
                }
                s.push_str(&((r >> 32) % if n % 3 == 0 { 400 } else { 30 }).to_string());
            }
            let want: f64 = s.parse().unwrap();
            let got = parse_f64(s.as_bytes());
            assert!(want.to_bits() == got.to_bits(), "{s}: {got:e} != {want:e}");
            // Shortest round-trip text of a random double.
            let f = f64::from_bits(rnd() & !(0x7FF << 52) | ((rnd() % 0x7FF) << 52));
            let t = format!("{f:e}");
            assert!(parse_f64(t.as_bytes()).to_bits() == f.to_bits(), "{t}");
        }
    }

    #[test]
    fn integers() {
        assert_eq!(parse_i64(b"0"), Some(0));
        assert_eq!(parse_i64(b"-9223372036854775808"), Some(i64::MIN));
        assert_eq!(parse_i64(b"9223372036854775807"), Some(i64::MAX));
        assert_eq!(parse_i64(b"9223372036854775808"), None);
        assert_eq!(parse_i64(b"1.0"), None);
    }
}

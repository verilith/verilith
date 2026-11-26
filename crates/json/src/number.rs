//! Number conversion for the lazy reader.
//!
//! The verified parser guarantees each number token is an RFC 8259 number
//! lexeme. This module turns the lexeme into an `f64`, correctly rounded:
//!
//! * [`lexeme_bits`] (verified) reads the lexeme with the parser's
//!   `ex_number_scan`, which gives its exact significand and power of ten
//!   (`number_value`) when it has at most 19 significant digits, and
//!   converts `w * 10^q` with `float::to_bits`, which returns the nearest
//!   double, ties to even; it is proven to return those bits, with the
//!   sign, whenever it returns any;
//! * lexemes with more than 19 significant digits, and the cases `to_bits`
//!   leaves undecided (none in testing), fall back to `f64::from_str`.
//!
//! [`parse_i64`] is verified to return the lexeme's value exactly when it
//! is an integer lexeme whose value fits in `i64`.
//!
//! It is all also tested bit for bit against `f64::from_str` on random
//! lexemes.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::float::is_round;
#[cfg(verus_keep_ghost)]
use crate::spec::*;

verus! {

/// The bits of `w * 10^q`, negated if `neg`, correctly rounded, where the
/// verified conversion decides them.
pub fn parts_bits(neg: bool, w: u64, q: i64) -> (r: Option<u64>)
    ensures
        r matches Some(x) ==> is_round(w as int, q as int, (x % 0x8000_0000_0000_0000) as u64) && (x
            >= 0x8000_0000_0000_0000) == neg,
{
    match crate::float::to_bits(w, q) {
        Some(b) => {
            if b < 0x8000_0000_0000_0000 {
                Some(
                    if neg {
                        b + 0x8000_0000_0000_0000
                    } else {
                        b
                    },
                )
            } else {
                None
            }
        },
        None => None,
    }
}

/// The bits of the number lexeme `src[a..b]`, correctly rounded, where
/// the verified scanner and conversion decide them: at most 19
/// significant digits.
pub fn lexeme_bits(src: &[u8], a: usize, b: usize) -> (r: Option<u64>)
    ensures
        r matches Some(x) ==> number_end(src@, a as int) == Some(b as int) && {
            let (neg, w, q) = number_value(src@, a as int);
            &&& is_round(w, q, (x % 0x8000_0000_0000_0000) as u64)
            &&& (x >= 0x8000_0000_0000_0000) == neg
        },
{
    if a < b && b <= src.len() {
        match crate::parser::ex_number_scan(src, a) {
            Some((e, v, exact)) => {
                if exact && e == b {
                    return parts_bits(v.neg, v.w, v.q as i64);
                }
            },
            None => {},
        }
    }
    None
}

/// The value of an integer lexeme, `-?[0-9]+`, if it fits in `i64`.
pub open spec fn i64_lexeme(s: Seq<u8>) -> Option<int> {
    let neg = s.len() > 0 && s[0] == 0x2D;
    let j: int = if neg { 1 } else { 0 };
    if j < s.len() && (forall|k: int| j <= k < s.len() ==> is_digit(#[trigger] s[k])) {
        let m = dval(s, j, s.len() as int);
        let v = if neg { -m } else { m };
        if i64::MIN <= v <= i64::MAX { Some(v) } else { None }
    } else {
        None
    }
}

/// More digits do not make a value smaller.
proof fn lemma_dval_mono(s: Seq<u8>, a: int, b: int, c: int)
    requires
        0 <= a <= b <= c <= s.len(),
        forall|k: int| a <= k < c ==> is_digit(#[trigger] s[k]),
    ensures
        dval(s, a, b) <= dval(s, a, c),
    decreases c - b,
{
    if c > b {
        lemma_dval_mono(s, a, b, c - 1);
        crate::parser::lemma_dval_bound(s, a, c - 1);
        assert(is_digit(s[c - 1]));
    }
}

/// Parses an integer lexeme (no fraction or exponent) that fits in `i64`.
pub fn parse_i64(lex: &[u8]) -> (r: Option<i64>)
    ensures
        r matches Some(v) ==> i64_lexeme(lex@) == Some(v as int),
        r is None ==> i64_lexeme(lex@) is None,
{
    let n = lex.len();
    let neg = n > 0 && lex[0] == 0x2D;
    let j: usize = if neg { 1 } else { 0 };
    if j >= n {
        return None;
    }
    // The magnitude, up to 2^63 (i64::MIN's).
    let mut m: u64 = 0;
    let mut k = j;
    while k < n
        invariant
            n == lex@.len(),
            neg == (lex@.len() > 0 && lex@[0] == 0x2D),
            j as int == (if neg { 1int } else { 0int }),
            j <= k <= n,
            forall|t: int| j <= t < k ==> is_digit(#[trigger] lex@[t]),
            m as int == dval(lex@, j as int, k as int),
            m <= 0x8000_0000_0000_0000,
        decreases n - k,
    {
        let c = lex[k];
        if !(0x30 <= c && c <= 0x39) {
            proof {
                let jj: int = j as int;
                assert(!is_digit(lex@[k as int]));
                assert(!(forall|t: int| jj <= t < lex@.len() ==> is_digit(#[trigger] lex@[t])));
                assert(jj == (if lex@.len() > 0 && lex@[0] == 0x2D { 1int } else { 0int }));
            }
            return None;
        }
        let d = (c - 0x30) as u64;
        if m > (0x8000_0000_0000_0000 - d) / 10 {
            // The value is already past 2^63, and more digits only add.
            proof {
                assert(dval(lex@, j as int, k + 1) == m * 10 + d);
                assert(m * 10 + d > 0x8000_0000_0000_0000) by (nonlinear_arith)
                    requires
                        m > (0x8000_0000_0000_0000 - d) / 10,
                        d <= 9,
                ;
                assert(is_digit(lex@[k as int]));
                let jj: int = j as int;
                assert(jj == (if lex@.len() > 0 && lex@[0] == 0x2D { 1int } else { 0int }));
                if forall|t: int| jj <= t < lex@.len() ==> is_digit(#[trigger] lex@[t]) {
                    lemma_dval_mono(lex@, jj, k + 1, n as int);
                    assert(dval(lex@, jj, n as int) > 0x8000_0000_0000_0000);
                }
            }
            return None;
        }
        proof {
            assert(m * 10 + d <= 0x8000_0000_0000_0000) by (nonlinear_arith)
                requires
                    m <= (0x8000_0000_0000_0000 - d) / 10,
                    d <= 9,
            ;
        }
        m = m * 10 + d;
        k = k + 1;
    }
    if neg {
        if m == 0x8000_0000_0000_0000 {
            Some(i64::MIN)
        } else {
            Some(-(m as i64))
        }
    } else if m <= 0x7FFF_FFFF_FFFF_FFFF {
        Some(m as i64)
    } else {
        None
    }
}

} // verus!

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
    match lexeme_bits(src, a, b) {
        Some(x) => f64::from_bits(x),
        None => slow(&src[a..b]),
    }
}

/// `w * 10^q`, negated if `neg`, correctly rounded, if the fast algorithms
/// can decide it (`w` must be exact). Otherwise `None`.
#[inline]
pub fn from_parts(neg: bool, w: u64, q: i64) -> Option<f64> {
    // The verified conversion gives the bit pattern of the nearest double,
    // with the sign as the top bit.
    parts_bits(neg, w, q).map(f64::from_bits)
}

#[cold]
fn slow(lex: &[u8]) -> f64 {
    // Every RFC 8259 number is accepted by `f64::from_str`.
    match core::str::from_utf8(lex) {
        Ok(t) => t.parse::<f64>().unwrap_or(f64::NAN),
        Err(_) => f64::NAN,
    }
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
        assert_eq!(parse_i64(b"-9223372036854775809"), None);
        assert_eq!(parse_i64(b"-"), None);
        assert_eq!(parse_i64(b""), None);
        assert_eq!(parse_i64(b"-00012"), Some(-12));
        assert_eq!(parse_i64(b"00000000000000000000000000009"), Some(9));
        assert_eq!(parse_i64(b"99999999999999999999999999999"), None);
        // Against `i64::from_str` on random lexemes of every length, near
        // the bounds, signed and not.
        let mut x: u64 = 0x2545_F491_4F6C_DD1D;
        for n in 0..200_000u64 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let mag = match n % 4 {
                0 => (x % 40).to_string(),
                1 => format!("{}", x >> (n % 64)),
                2 => format!("{}{}", 9223372036854775800u64 + x % 16, if n % 8 == 2 { "" } else { "0" }),
                _ => format!("{}", x as u128 * 7),
            };
            let s = if x >> 63 == 1 { format!("-{mag}") } else { mag };
            assert_eq!(parse_i64(s.as_bytes()), s.parse::<i64>().ok(), "{s}");
        }
    }
}

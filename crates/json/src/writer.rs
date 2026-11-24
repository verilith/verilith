//! Writing JSON.
//!
//! [`Writer`] builds a JSON text one value at a time. Strings go through
//! the verified escaper in `crate::write`, which is proven to round-trip
//! through the parser, and numbers through the verified number grammar, so
//! no string or number can break out of its place in the output. The
//! nesting state machine here (which brackets, commas and colons go where)
//! is ordinary Rust: it refuses calls out of order, and the tests parse
//! what it writes back.
use crate::value::{Document, Type, Value};
use crate::write::{is_number, write_string};
use std::fmt;

/// Why a write was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum WriteError {
    /// A value where an object member name was expected, a name where a
    /// value was expected, a close that does not match the open, or a
    /// second top-level value.
    OutOfOrder,
    /// `finish` before the top-level value was complete.
    Incomplete,
    /// NaN or an infinity, which JSON cannot represent.
    NonFinite,
    /// A number string that is not a JSON number.
    InvalidNumber,
    /// Nesting deeper than the parser accepts (1000 levels).
    TooDeep,
}

impl fmt::Display for WriteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            WriteError::OutOfOrder => "JSON value written out of order",
            WriteError::Incomplete => "JSON value not complete",
            WriteError::NonFinite => "NaN and infinities are not JSON numbers",
            WriteError::InvalidNumber => "not a JSON number",
            WriteError::TooDeep => "nesting deeper than 1000",
        })
    }
}

impl std::error::Error for WriteError {}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Frame {
    Array { empty: bool },
    /// `key` is true right after a member name, when the value is next.
    Object { empty: bool, key: bool },
}

/// Writes a JSON text.
///
/// ```
/// let mut w = verilith_json::Writer::new();
/// w.begin_object().unwrap();
/// w.key("name").unwrap();
/// w.string("vjson \"v1\"").unwrap();
/// w.key("tags").unwrap();
/// w.begin_array().unwrap();
/// w.i64(1).unwrap();
/// w.f64(2.5).unwrap();
/// w.end_array().unwrap();
/// w.end_object().unwrap();
/// assert_eq!(w.finish().unwrap(), br#"{"name":"vjson \"v1\"","tags":[1,2.5]}"#);
/// ```
pub struct Writer {
    out: Vec<u8>,
    stack: Vec<Frame>,
    done: bool,
    indent: Option<usize>,
}

impl Default for Writer {
    fn default() -> Writer {
        Writer::new()
    }
}

impl Writer {
    /// A writer of compact JSON, with no whitespace.
    pub fn new() -> Writer {
        Writer { out: Vec::new(), stack: Vec::new(), done: false, indent: None }
    }

    /// A writer that puts each element and member on its own line,
    /// indented by `indent` spaces per level.
    pub fn pretty(indent: usize) -> Writer {
        Writer { indent: Some(indent), ..Writer::new() }
    }

    /// The bytes written so far.
    pub fn as_bytes(&self) -> &[u8] {
        &self.out
    }

    /// The finished text.
    pub fn finish(self) -> Result<Vec<u8>, WriteError> {
        if !self.done {
            return Err(WriteError::Incomplete);
        }
        Ok(self.out)
    }

    fn newline(&mut self) {
        if let Some(n) = self.indent {
            self.out.push(b'\n');
            self.out.resize(self.out.len() + n * self.stack.len(), b' ');
        }
    }

    /// Writes what comes before a value, and checks one may go here.
    fn before_value(&mut self) -> Result<(), WriteError> {
        match self.stack.last_mut() {
            None if self.done => Err(WriteError::OutOfOrder),
            None => Ok(()),
            Some(Frame::Object { key: false, .. }) => Err(WriteError::OutOfOrder),
            Some(Frame::Object { key, .. }) => {
                *key = false;
                Ok(())
            }
            Some(Frame::Array { empty }) => {
                let first = *empty;
                *empty = false;
                if !first {
                    self.out.push(b',');
                }
                self.newline();
                Ok(())
            }
        }
    }

    fn after_value(&mut self) {
        if self.stack.is_empty() {
            self.done = true;
        }
    }

    /// `null`.
    pub fn null(&mut self) -> Result<(), WriteError> {
        self.before_value()?;
        self.out.extend_from_slice(b"null");
        self.after_value();
        Ok(())
    }

    /// `true` or `false`.
    pub fn bool(&mut self, b: bool) -> Result<(), WriteError> {
        self.before_value()?;
        self.out.extend_from_slice(if b { b"true" } else { b"false" });
        self.after_value();
        Ok(())
    }

    /// A string. Quotes, backslashes and control characters are escaped.
    pub fn string(&mut self, s: &str) -> Result<(), WriteError> {
        self.before_value()?;
        write_string(&mut self.out, s.as_bytes());
        self.after_value();
        Ok(())
    }

    /// A number given as text, which must follow the JSON number grammar.
    pub fn number_str(&mut self, s: &str) -> Result<(), WriteError> {
        self.number_bytes(s.as_bytes())
    }

    fn number_bytes(&mut self, s: &[u8]) -> Result<(), WriteError> {
        // Every number is checked against the verified grammar, before any
        // separator is written.
        if !is_number(s) {
            return Err(WriteError::InvalidNumber);
        }
        self.before_value()?;
        self.out.extend_from_slice(s);
        self.after_value();
        Ok(())
    }

    /// An integer.
    pub fn i64(&mut self, n: i64) -> Result<(), WriteError> {
        self.number_bytes(itoa(n < 0, n.unsigned_abs(), &mut [0; 24]))
    }

    /// An unsigned integer.
    pub fn u64(&mut self, n: u64) -> Result<(), WriteError> {
        self.number_bytes(itoa(false, n, &mut [0; 24]))
    }

    /// A finite `f64`, in the shortest form that reads back as the same
    /// value.
    pub fn f64(&mut self, x: f64) -> Result<(), WriteError> {
        if !x.is_finite() {
            return Err(WriteError::NonFinite);
        }
        self.number_str(float_text(x, &mut zmij::Buffer::new()))
    }

    /// Starts an array.
    pub fn begin_array(&mut self) -> Result<(), WriteError> {
        self.open(Frame::Array { empty: true }, b'[')
    }

    /// Starts an object.
    pub fn begin_object(&mut self) -> Result<(), WriteError> {
        self.open(Frame::Object { empty: true, key: false }, b'{')
    }

    fn open(&mut self, f: Frame, c: u8) -> Result<(), WriteError> {
        if self.stack.len() >= crate::spec::MAX_DEPTH {
            return Err(WriteError::TooDeep);
        }
        self.before_value()?;
        self.out.push(c);
        self.stack.push(f);
        Ok(())
    }

    /// Ends the array that is open.
    pub fn end_array(&mut self) -> Result<(), WriteError> {
        match self.stack.last() {
            Some(&Frame::Array { empty }) => self.close(empty, b']'),
            _ => Err(WriteError::OutOfOrder),
        }
    }

    /// Ends the object that is open.
    pub fn end_object(&mut self) -> Result<(), WriteError> {
        match self.stack.last() {
            Some(&Frame::Object { empty, key: false }) => self.close(empty, b'}'),
            _ => Err(WriteError::OutOfOrder),
        }
    }

    fn close(&mut self, empty: bool, c: u8) -> Result<(), WriteError> {
        self.stack.pop();
        if !empty {
            self.newline();
        }
        self.out.push(c);
        self.after_value();
        Ok(())
    }

    /// An object member's name. The member's value comes next.
    pub fn key(&mut self, k: &str) -> Result<(), WriteError> {
        let Some(Frame::Object { empty, key }) = self.stack.last_mut() else {
            return Err(WriteError::OutOfOrder);
        };
        if *key {
            return Err(WriteError::OutOfOrder);
        }
        let first = *empty;
        *empty = false;
        *key = true;
        if !first {
            self.out.push(b',');
        }
        self.newline();
        write_string(&mut self.out, k.as_bytes());
        self.out.push(b':');
        if self.indent.is_some() {
            self.out.push(b' ');
        }
        Ok(())
    }

    /// A value from a parsed document, as it was (numbers keep their text).
    pub fn value(&mut self, v: Value<'_>) -> Result<(), WriteError> {
        match v.kind() {
            Type::Null => self.null(),
            Type::Bool => self.bool(v.as_bool().unwrap_or(false)),
            Type::Number => self.number_str(v.as_number_str().unwrap_or("0")),
            Type::String => self.string(&v.as_str().unwrap_or_default()),
            Type::Array => {
                self.begin_array()?;
                for e in v.elements().into_iter().flatten() {
                    self.value(e)?;
                }
                self.end_array()
            }
            Type::Object => {
                self.begin_object()?;
                for (k, e) in v.members().into_iter().flatten() {
                    self.key(&k.as_str().unwrap_or_default())?;
                    self.value(e)?;
                }
                self.end_object()
            }
        }
    }
}

/// A finite float's text: the shortest form that reads back as the same
/// value, as serde_json writes it. `number_bytes` checks it against the
/// verified grammar, so a formatter bug cannot produce invalid JSON.
pub(crate) fn float_text<F: zmij::Float>(x: F, buf: &mut zmij::Buffer) -> &str {
    buf.format_finite(x)
}

const PAIRS: &[u8; 200] = b"0001020304050607080910111213141516171819\
2021222324252627282930313233343536373839\
4041424344454647484950515253545556575859\
6061626364656667686970717273747576777879\
8081828384858687888990919293949596979899";

/// Decimal digits of `m`, with a `-` if `neg`, at the end of `buf`.
fn itoa(neg: bool, mut m: u64, buf: &mut [u8; 24]) -> &[u8] {
    let mut i = buf.len();
    while m >= 100 {
        let r = (m % 100) as usize * 2;
        m /= 100;
        i -= 2;
        buf[i..i + 2].copy_from_slice(&PAIRS[r..r + 2]);
    }
    if m >= 10 {
        let r = m as usize * 2;
        i -= 2;
        buf[i..i + 2].copy_from_slice(&PAIRS[r..r + 2]);
    } else {
        i -= 1;
        buf[i] = b'0' + m as u8;
    }
    if neg {
        i -= 1;
        buf[i] = b'-';
    }
    &buf[i..]
}

impl Document<'_> {
    /// The document written back out compactly.
    pub fn to_vec(&self) -> Vec<u8> {
        let mut w = Writer::new();
        w.value(self.root()).expect("a parsed document is well formed");
        w.out
    }

    /// The document written back out with each element and member on its
    /// own line.
    pub fn to_vec_pretty(&self, indent: usize) -> Vec<u8> {
        let mut w = Writer::pretty(indent);
        w.value(self.root()).expect("a parsed document is well formed");
        w.out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn misuse_is_refused() {
        let mut w = Writer::new();
        assert_eq!(w.key("a"), Err(WriteError::OutOfOrder));
        w.begin_object().unwrap();
        assert_eq!(w.null(), Err(WriteError::OutOfOrder));
        assert_eq!(w.end_array(), Err(WriteError::OutOfOrder));
        w.key("a").unwrap();
        assert_eq!(w.key("b"), Err(WriteError::OutOfOrder));
        assert_eq!(w.end_object(), Err(WriteError::OutOfOrder));
        assert_eq!(w.f64(f64::NAN), Err(WriteError::NonFinite));
        assert_eq!(w.number_str("01"), Err(WriteError::InvalidNumber));
        w.number_str("-1.5e3").unwrap();
        w.end_object().unwrap();
        assert_eq!(w.null(), Err(WriteError::OutOfOrder));
        assert_eq!(w.finish().unwrap(), br#"{"a":-1.5e3}"#);
        assert_eq!(Writer::new().finish(), Err(WriteError::Incomplete));
    }

    #[test]
    fn numbers() {
        for x in [0.0, -0.0, 1.0, 0.1, 1e300, -2.5e-300, f64::MAX, f64::MIN_POSITIVE, 5e-324] {
            let mut w = Writer::new();
            w.f64(x).unwrap();
            let out = w.finish().unwrap();
            let d = crate::parse(&out).unwrap();
            assert_eq!(d.root().as_f64().unwrap().to_bits(), x.to_bits(), "{}", String::from_utf8_lossy(&out));
        }
        for n in [0, -1, i64::MIN, i64::MAX] {
            let mut w = Writer::new();
            w.i64(n).unwrap();
            assert_eq!(crate::parse(&w.finish().unwrap()).unwrap().root().as_i64(), Some(n));
        }
        let mut w = Writer::new();
        w.u64(u64::MAX).unwrap();
        assert_eq!(w.finish().unwrap(), u64::MAX.to_string().as_bytes());
    }

    #[test]
    fn pretty() {
        let d = crate::parse(br#"{"a":[1,{},[]],"b":{"c":null}}"#).unwrap();
        let p = d.to_vec_pretty(2);
        assert_eq!(
            String::from_utf8(p.clone()).unwrap(),
            "{\n  \"a\": [\n    1,\n    {},\n    []\n  ],\n  \"b\": {\n    \"c\": null\n  }\n}"
        );
        assert_eq!(crate::parse(&p).unwrap().to_vec(), br#"{"a":[1,{},[]],"b":{"c":null}}"#);
    }

    /// Every string round-trips, whatever it holds.
    #[test]
    fn strings_round_trip() {
        let mut x: u64 = 0x9E3779B97F4A7C15;
        let pool: Vec<char> = "\"\\/\u{0}\u{1}\u{8}\u{9}\u{a}\u{c}\u{d}\u{1f}\u{7f} aZ\u{e9}\u{20ac}\u{1F600}\u{FFFF}".chars().collect();
        for _ in 0..100_000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let n = (x % 40) as usize;
            let s: String = (0..n).map(|k| pool[((x >> (k % 50)) as usize + k * 7) % pool.len()]).collect();
            let mut w = Writer::new();
            w.begin_array().unwrap();
            w.string(&s).unwrap();
            w.end_array().unwrap();
            let out = w.finish().unwrap();
            let d = crate::parse(&out).unwrap();
            assert_eq!(d.root().at(0).unwrap().as_str().unwrap(), s);
        }
    }

    /// Writing a parsed document and parsing the result gives the same
    /// document, for every accepted JSONTestSuite file.
    #[test]
    fn documents_round_trip() {
        let Ok(dir) = std::env::var("JSON_TEST_SUITE") else { return };
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            let data = std::fs::read(&path).unwrap();
            let Ok(d) = crate::parse(&data) else { continue };
            let once = d.to_vec();
            let d2 = crate::parse(&once).unwrap_or_else(|e| panic!("{path:?}: {e}"));
            assert_eq!(d2.to_vec(), once, "{path:?}");
            assert_eq!(format!("{d:?}"), format!("{d2:?}"), "{path:?}");
        }
    }
}

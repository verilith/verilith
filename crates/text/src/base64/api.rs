//! The public interface, shaped like the base64 crate's `Engine`
//! (`STANDARD.encode(..)`, `STANDARD.decode(..)`) with base64-simd's method
//! names as aliases. Unverified glue: it allocates the output, calls the
//! verified codec, and on a rejection runs a diagnostic pass that only
//! picks the error to report (the rejection itself is the verified one).
use super::scalar;
use super::spec::Config;
use std::fmt;

/// An encoding configuration; the four constants below are the base64
/// crate's `general_purpose` engines.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Engine {
    url: bool,
    pad: bool,
}

pub const STANDARD: Engine = Engine { url: false, pad: true };
pub const STANDARD_NO_PAD: Engine = Engine { url: false, pad: false };
pub const URL_SAFE: Engine = Engine { url: true, pad: true };
pub const URL_SAFE_NO_PAD: Engine = Engine { url: true, pad: false };

/// Why a string was rejected, with the base64 crate's variants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
    /// A byte outside the alphabet, or padding in the wrong place.
    InvalidByte(usize, u8),
    /// The number of data characters cannot come from an encoding.
    InvalidLength(usize),
    /// The last character has nonzero bits the encoding never sets.
    InvalidLastSymbol(usize, u8),
    /// Padding is missing, or present where it is not allowed.
    InvalidPadding,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::InvalidByte(i, b) => write!(f, "Invalid symbol {}, offset {}.", b, i),
            Self::InvalidLength(n) => write!(f, "Invalid input length: {}", n),
            Self::InvalidLastSymbol(i, b) => write!(f, "Invalid last symbol {}, offset {}.", b, i),
            Self::InvalidPadding => write!(f, "Invalid padding"),
        }
    }
}

impl std::error::Error for DecodeError {}

/// The output slice is too small.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SliceTooSmall;

impl Engine {
    fn cfg(&self) -> Config {
        Config { url: self.url, pad: self.pad }
    }

    /// The length of the encoding of `n` bytes.
    pub fn encoded_len(&self, n: usize) -> usize {
        assert!(n <= usize::MAX / 2, "input too large");
        scalar::enc_len(n, self.pad)
    }

    /// Writes the encoding of `input` to the front of `out`; returns its
    /// length.
    pub fn encode_slice(&self, input: impl AsRef<[u8]>, out: &mut [u8]) -> Result<usize, SliceTooSmall> {
        let x = input.as_ref();
        let n = self.encoded_len(x.len());
        if out.len() < n {
            return Err(SliceTooSmall);
        }
        super::encode_into(self.cfg(), x, &mut out[..n]);
        Ok(n)
    }

    pub fn encode(&self, input: impl AsRef<[u8]>) -> String {
        let x = input.as_ref();
        let mut out = vec![0u8; self.encoded_len(x.len())];
        super::encode_into(self.cfg(), x, &mut out);
        // SAFETY: every byte of an encoding is an ASCII character
        // (`sym` and `PAD`), so `out` is UTF-8.
        unsafe { String::from_utf8_unchecked(out) }
    }

    pub fn encode_string(&self, input: impl AsRef<[u8]>, out: &mut String) {
        out.push_str(&self.encode(input));
    }

    pub fn encode_to_string(&self, input: impl AsRef<[u8]>) -> String {
        self.encode(input)
    }

    /// The decoded length of `s` if it decodes, else an upper bound.
    pub fn decoded_len_estimate(&self, n: usize) -> usize {
        (n + 3) / 4 * 3
    }

    pub fn decode(&self, input: impl AsRef<[u8]>) -> Result<Vec<u8>, DecodeError> {
        let s = input.as_ref();
        let m = scalar::body_len_exec(self.cfg(), s);
        let mut out = vec![0u8; scalar::dec_len(m)];
        if super::decode_into(self.cfg(), s, &mut out) {
            Ok(out)
        } else {
            Err(self.diagnose(s))
        }
    }

    pub fn decode_to_vec(&self, input: impl AsRef<[u8]>) -> Result<Vec<u8>, DecodeError> {
        self.decode(input)
    }

    pub fn decode_vec(&self, input: impl AsRef<[u8]>, out: &mut Vec<u8>) -> Result<(), DecodeError> {
        out.extend_from_slice(&self.decode(input)?);
        Ok(())
    }

    /// Decodes into the front of `out`; returns the number of bytes.
    pub fn decode_slice(&self, input: impl AsRef<[u8]>, out: &mut [u8]) -> Result<usize, DecodeError> {
        let s = input.as_ref();
        let m = scalar::body_len_exec(self.cfg(), s);
        let n = scalar::dec_len(m);
        if out.len() < n {
            // Still report a bad input as such.
            let v = self.decode(s)?;
            assert!(out.len() >= v.len(), "output slice too small");
        }
        if super::decode_into(self.cfg(), s, &mut out[..n]) {
            Ok(n)
        } else {
            Err(self.diagnose(s))
        }
    }

    /// Picks the error the base64 crate reports for a rejected `s`, by
    /// following its decoder's order of checks.
    fn diagnose(&self, s: &[u8]) -> DecodeError {
        let valid = |c: u8| {
            c.is_ascii_alphanumeric() || c == if self.url { b'-' } else { b'+' } || c == if self.url { b'_' } else { b'/' }
        };
        let n = s.len();
        let rem = n % 4;
        if rem == 1 && s[n - 1] != b'=' && !valid(s[n - 1]) {
            return DecodeError::InvalidByte(n - 1, s[n - 1]);
        }
        let q = n.saturating_sub(rem).saturating_sub(if rem == 0 { 4 } else { 0 });
        for (i, &c) in s[..q].iter().enumerate() {
            if !valid(c) {
                return DecodeError::InvalidByte(i, c);
            }
        }
        // The final one to four characters.
        let mut morsels = 0;
        let mut pads = 0;
        let mut first_pad = 0;
        let mut last = 0u8;
        for (k, &c) in s[q..].iter().enumerate() {
            if c == b'=' {
                if k < 2 {
                    return DecodeError::InvalidByte(q + k, c);
                }
                if pads == 0 {
                    first_pad = k;
                }
                pads += 1;
                continue;
            }
            if pads > 0 {
                return DecodeError::InvalidByte(q + first_pad, b'=');
            }
            if !valid(c) {
                return DecodeError::InvalidByte(q + k, c);
            }
            last = c;
            morsels += 1;
        }
        if n > 0 && morsels < 2 {
            return DecodeError::InvalidLength(q + morsels);
        }
        if self.pad {
            if (pads + morsels) % 4 != 0 {
                return DecodeError::InvalidPadding;
            }
        } else if pads > 0 {
            return DecodeError::InvalidPadding;
        }
        if morsels > 0 {
            return DecodeError::InvalidLastSymbol(q + morsels - 1, last);
        }
        DecodeError::InvalidPadding
    }
}

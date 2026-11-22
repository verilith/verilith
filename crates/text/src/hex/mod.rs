//! Hexadecimal: `codec` has the spec, the round trip and the verified
//! codec; this module is the public interface, shaped like the hex crate's.
pub mod avx2;
pub mod codec;

use codec::{decode_into, encode_into};

// ---------------------------------------------------------------------------

/// Why a string was rejected, with the hex crate's variants.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FromHexError {
    InvalidHexCharacter { c: char, index: usize },
    OddLength,
    InvalidStringLength,
}

impl core::fmt::Display for FromHexError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Self::InvalidHexCharacter { c, index } => write!(f, "Invalid character {:?} at position {}", c, index),
            Self::OddLength => write!(f, "Odd number of digits"),
            Self::InvalidStringLength => write!(f, "Invalid string length"),
        }
    }
}

impl std::error::Error for FromHexError {}

fn encode_with(upper: bool, x: &[u8]) -> String {
    let mut out = vec![0u8; x.len().checked_mul(2).expect("input too large")];
    encode_into(upper, x, &mut out);
    // SAFETY: every byte is a digit (`digit`), so `out` is ASCII.
    unsafe { String::from_utf8_unchecked(out) }
}

/// Lowercase hex of `data`.
pub fn encode<T: AsRef<[u8]>>(data: T) -> String {
    encode_with(false, data.as_ref())
}

/// Uppercase hex of `data`.
pub fn encode_upper<T: AsRef<[u8]>>(data: T) -> String {
    encode_with(true, data.as_ref())
}

fn diagnose(s: &[u8]) -> FromHexError {
    // The hex crate reports odd length first, then the first bad digit.
    if s.len() % 2 != 0 {
        return FromHexError::OddLength;
    }
    for (i, &c) in s.iter().enumerate() {
        if !c.is_ascii_hexdigit() {
            return FromHexError::InvalidHexCharacter { c: c as char, index: i };
        }
    }
    FromHexError::OddLength
}

pub fn decode<T: AsRef<[u8]>>(data: T) -> Result<Vec<u8>, FromHexError> {
    let s = data.as_ref();
    let mut out = vec![0u8; s.len() / 2];
    if decode_into(s, &mut out) {
        Ok(out)
    } else {
        Err(diagnose(s))
    }
}

/// Decodes into `out`, which must be exactly half as long as `data`.
pub fn decode_to_slice<T: AsRef<[u8]>>(data: T, out: &mut [u8]) -> Result<(), FromHexError> {
    let s = data.as_ref();
    if s.len() % 2 != 0 {
        return Err(FromHexError::OddLength);
    }
    if s.len() / 2 != out.len() {
        return Err(FromHexError::InvalidStringLength);
    }
    if decode_into(s, out) {
        Ok(())
    } else {
        Err(diagnose(s))
    }
}

/// Encodes into `out`, which must be exactly twice as long as `data`.
pub fn encode_to_slice<T: AsRef<[u8]>>(data: T, out: &mut [u8]) -> Result<(), FromHexError> {
    let x = data.as_ref();
    if x.len().checked_mul(2) != Some(out.len()) {
        return Err(FromHexError::InvalidStringLength);
    }
    encode_into(false, x, out);
    Ok(())
}

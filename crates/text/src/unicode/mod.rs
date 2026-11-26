//! Unicode normalization (NFC, NFD, NFKC, NFKD), verified against the
//! algorithm of UAX #15 over the Unicode 18.0 data.
//!
//! The functions here are the unverified glue: each passes a `&str` to
//! the verified entry points in [`strs`] (which prove, from vstd's model of
//! `str`, that its bytes are the UTF-8 encoding of its scalars, the
//! normalizer's precondition), and turns the result back into a `String`,
//! which is UTF-8 by their postconditions.
pub mod data;
pub mod norm;
pub mod spec;
pub mod strs;
/// The normalization data (generated; trusted, and checked by `tests/unicode_data.rs`).
pub mod tables;

use std::borrow::Cow;

/// The forms, as `(compose, compat)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Form {
    /// Canonical composition.
    Nfc,
    /// Canonical decomposition.
    Nfd,
    /// Compatibility composition.
    Nfkc,
    /// Compatibility decomposition.
    Nfkd,
}

impl Form {
    fn flags(self) -> (bool, bool) {
        match self {
            Form::Nfc => (true, false),
            Form::Nfd => (false, false),
            Form::Nfkc => (true, true),
            Form::Nfkd => (false, true),
        }
    }
}

/// Appends the normal form of `s` to `out`.
pub fn normalize_to(s: &str, form: Form, out: &mut String) {
    let (compose, compat) = form.flags();
    // SAFETY: `normalize_into_str` appends the UTF-8 encoding of scalars.
    let v = unsafe { out.as_mut_vec() };
    strs::normalize_into_str(s, compose, compat, v);
}

/// The normal form of `s`; borrowed when `s` is already normalized as far
/// as the quick check can tell.
pub fn normalize(s: &str, form: Form) -> Cow<'_, str> {
    let (compose, compat) = form.flags();
    if strs::quick_check_str(s, compose, compat) {
        return Cow::Borrowed(s);
    }
    let mut out = String::with_capacity(s.len() + s.len() / 4);
    normalize_to(s, form, &mut out);
    Cow::Owned(out)
}

/// Whether `s` is in the normal form.
pub fn is_normalized(s: &str, form: Form) -> bool {
    let (compose, compat) = form.flags();
    strs::quick_check_str(s, compose, compat) || normalize(s, form) == s
}

/// `s` in NFC.
pub fn nfc(s: &str) -> Cow<'_, str> {
    normalize(s, Form::Nfc)
}

/// `s` in NFD.
pub fn nfd(s: &str) -> Cow<'_, str> {
    normalize(s, Form::Nfd)
}

/// `s` in NFKC.
pub fn nfkc(s: &str) -> Cow<'_, str> {
    normalize(s, Form::Nfkc)
}

/// `s` in NFKD.
pub fn nfkd(s: &str) -> Cow<'_, str> {
    normalize(s, Form::Nfkd)
}

/// Whether `s` is in NFC.
pub fn is_nfc(s: &str) -> bool {
    is_normalized(s, Form::Nfc)
}

/// Whether `s` is in NFD.
pub fn is_nfd(s: &str) -> bool {
    is_normalized(s, Form::Nfd)
}

/// Whether `s` is in NFKC.
pub fn is_nfkc(s: &str) -> bool {
    is_normalized(s, Form::Nfkc)
}

/// Whether `s` is in NFKD.
pub fn is_nfkd(s: &str) -> bool {
    is_normalized(s, Form::Nfkd)
}

/// The normal form of `s` computed as one segment, without the fast path.
/// Slow; the tests use it as a reference.
pub fn normalize_reference(s: &str, form: Form) -> String {
    let (compose, compat) = form.flags();
    let mut v = Vec::new();
    strs::normalize_slow_str(s, compose, compat, &mut v);
    // SAFETY: `normalize_slow_str` produces the UTF-8 encoding of scalars.
    unsafe { String::from_utf8_unchecked(v) }
}

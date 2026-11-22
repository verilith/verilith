//! Unicode normalization (NFC, NFD, NFKC, NFKD), verified against the
//! algorithm of UAX #15 over the Unicode 18.0 data.
//!
//! The functions here are the unverified glue: each passes the bytes of a
//! `&str` to the verified [`norm::normalize_into`], whose precondition (the
//! bytes are the UTF-8 encoding of some scalars) is what `&str` guarantees,
//! and turns the result back into a `String`, which is UTF-8 by its
//! postcondition.
pub mod data;
pub mod norm;
pub mod spec;
pub mod tables;

use std::borrow::Cow;
use vstd::prelude::Ghost;

/// The forms, as `(compose, compat)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Form {
    Nfc,
    Nfd,
    Nfkc,
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
    // SAFETY: `normalize_into` appends the UTF-8 encoding of scalars.
    let v = unsafe { out.as_mut_vec() };
    norm::normalize_into(s.as_bytes(), compose, compat, v, Ghost::assume_new());
}

/// The normal form of `s`; borrowed when `s` is already normalized as far
/// as the quick check can tell.
pub fn normalize(s: &str, form: Form) -> Cow<'_, str> {
    let (compose, compat) = form.flags();
    if norm::quick_check(s.as_bytes(), compose, compat, Ghost::assume_new()) {
        return Cow::Borrowed(s);
    }
    let mut out = String::with_capacity(s.len() + s.len() / 4);
    normalize_to(s, form, &mut out);
    Cow::Owned(out)
}

/// Whether `s` is in the normal form.
pub fn is_normalized(s: &str, form: Form) -> bool {
    let (compose, compat) = form.flags();
    norm::quick_check(s.as_bytes(), compose, compat, Ghost::assume_new()) || normalize(s, form) == s
}

pub fn nfc(s: &str) -> Cow<'_, str> {
    normalize(s, Form::Nfc)
}

pub fn nfd(s: &str) -> Cow<'_, str> {
    normalize(s, Form::Nfd)
}

pub fn nfkc(s: &str) -> Cow<'_, str> {
    normalize(s, Form::Nfkc)
}

pub fn nfkd(s: &str) -> Cow<'_, str> {
    normalize(s, Form::Nfkd)
}

pub fn is_nfc(s: &str) -> bool {
    is_normalized(s, Form::Nfc)
}

pub fn is_nfd(s: &str) -> bool {
    is_normalized(s, Form::Nfd)
}

pub fn is_nfkc(s: &str) -> bool {
    is_normalized(s, Form::Nfkc)
}

pub fn is_nfkd(s: &str) -> bool {
    is_normalized(s, Form::Nfkd)
}

/// The normal form of `s` computed as one segment, without the fast path.
/// Slow; the tests use it as a reference.
pub fn normalize_reference(s: &str, form: Form) -> String {
    let (compose, compat) = form.flags();
    let mut v = Vec::new();
    norm::normalize_slow(s.as_bytes(), compose, compat, &mut v, Ghost::assume_new());
    // SAFETY: `normalize_slow` produces the UTF-8 encoding of scalars.
    unsafe { String::from_utf8_unchecked(v) }
}

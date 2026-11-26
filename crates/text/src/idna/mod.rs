//! IDNA: Punycode (RFC 3492) and UTS #46 processing, verified against
//! transliterations of the two specifications.
//!
//! The functions here are the unverified glue: each passes a `&str` to a
//! verified entry point in [`strs`], which proves from vstd's model of
//! `str` that its bytes encode its scalars (the precondition of the
//! function of [`uts46`] it calls), and turns the result into a `String`.
pub mod data;
pub mod punycode;
pub mod spec;
pub mod strs;
/// The UTS #46 data (generated; trusted, and checked by `tests/idna_data.rs`).
pub mod tables;
pub mod uts46;

pub use spec::Options;
use std::borrow::Cow;

/// UTS #46 processing failed; the specification records only that there
/// was an error.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Errors;

impl std::fmt::Display for Errors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("IDNA processing error")
    }
}

impl std::error::Error for Errors {}

impl Options {
    /// The flags of the URL Standard's domain to ASCII without beStrict:
    /// CheckBidi and CheckJoiners only.
    pub const URL: Options = Options {
        check_hyphens: false,
        check_bidi: true,
        check_joiners: true,
        use_std3_ascii_rules: false,
        transitional: false,
        verify_dns_length: false,
    };

    /// The URL Standard's flags with beStrict, which are also the
    /// conformance flags of UTS #46: everything checked, nontransitional.
    pub const STRICT: Options = Options {
        check_hyphens: true,
        check_bidi: true,
        check_joiners: true,
        use_std3_ascii_rules: true,
        transitional: false,
        verify_dns_length: true,
    };
}

fn chars_to_string(v: &[u32]) -> String {
    // `process_exec` returns scalars.
    v.iter().map(|&c| char::from_u32(c).unwrap()).collect()
}

/// UTS #46 ToASCII.
pub fn to_ascii(s: &str, o: Options) -> Result<String, Errors> {
    to_ascii_cow(s, o).map(Cow::into_owned)
}

/// UTS #46 ToASCII, borrowing `s` when it is its own result.
pub fn to_ascii_cow(s: &str, o: Options) -> Result<Cow<'_, str>, Errors> {
    if strs::ascii_unchanged_str(s, o) {
        return Ok(Cow::Borrowed(s));
    }
    if let Some(b) = strs::to_ascii_fast_str(s, o) {
        // ToASCII's result is ASCII.
        return Ok(Cow::Owned(String::from_utf8(b).unwrap()));
    }
    match strs::to_ascii_str(s, o) {
        // ToASCII's result is ASCII.
        Some(b) => Ok(Cow::Owned(String::from_utf8(b).unwrap())),
        None => Err(Errors),
    }
}

/// UTS #46 ToUnicode: the result, which is meaningful even when there were
/// errors, and whether there were.
pub fn to_unicode(s: &str, o: Options) -> (String, Result<(), Errors>) {
    to_unicode_cow(s, o)
        .map(|(c, r)| (c.into_owned(), r))
        .unwrap()
}

/// UTS #46 ToUnicode, borrowing `s` when it is its own result.
pub fn to_unicode_cow(s: &str, o: Options) -> Option<(Cow<'_, str>, Result<(), Errors>)> {
    if strs::ascii_unchanged_str(s, o) {
        return Some((Cow::Borrowed(s), Ok(())));
    }
    if let Some(b) = strs::to_ascii_fast_str(s, o) {
        // The ToUnicode result is `b`'s bytes as characters, all ASCII.
        return Some((Cow::Owned(String::from_utf8(b).unwrap()), Ok(())));
    }
    let (v, err) = strs::process_str(s, o);
    Some((Cow::Owned(chars_to_string(&v)), if err { Err(Errors) } else { Ok(()) }))
}

/// The URL Standard's host parser step for domains, beStrict false: an
/// ASCII domain is lowercased (it is not checked against UTS #46, even with
/// `xn--` labels), and any other goes through ToASCII with
/// [`Options::URL`]. The empty string, which the host parser rejects after
/// this step, is returned as is.
pub fn domain_to_ascii(domain: &str) -> Result<String, Errors> {
    domain_to_ascii_cow(domain).map(Cow::into_owned)
}

/// [`domain_to_ascii`], borrowing `domain` when it is its own result.
pub fn domain_to_ascii_cow(domain: &str) -> Result<Cow<'_, str>, Errors> {
    // Lowercasing changes nothing in ASCII without capital letters.
    if domain.bytes().all(|b| b < 0x80 && !b.is_ascii_uppercase()) {
        return Ok(Cow::Borrowed(domain));
    }
    match strs::url_domain_to_ascii_str(domain, Options::URL) {
        // The result is ASCII.
        Some(b) => Ok(Cow::Owned(String::from_utf8(b).unwrap())),
        None => Err(Errors),
    }
}

/// The URL Standard's domain to ASCII, beStrict true.
pub fn domain_to_ascii_strict(domain: &str) -> Result<String, Errors> {
    to_ascii(domain, Options::STRICT)
}

/// The URL Standard's domain to Unicode, beStrict false.
pub fn domain_to_unicode(domain: &str) -> (String, Result<(), Errors>) {
    to_unicode(domain, Options::URL)
}

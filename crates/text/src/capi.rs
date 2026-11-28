//! A C API shaped like ICU4C's `unorm2.h` and `uidna.h` (the UTS #46 part).
//!
//! Each function is exported as `vtext_<icu name>`, or under ICU's own
//! (unversioned) name with the `icu-abi` feature, so that a program built
//! with `U_DISABLE_RENAMING=1` links against vtext in place of ICU.
//!
//! This is plain Rust glue outside the proofs. It converts between UTF-16 or
//! UTF-8 and the verified functions' input, and follows ICU's conventions
//! for lengths (-1 for NUL-terminated input), preflighting, NUL termination
//! and `UErrorCode`. What it computes is the verified result:
//! normalization is `unicode::normalize_utf16_to` (the verified UTF-16
//! normalizer in `unicode::norm16`), and an IDNA call reports no error
//! exactly when the verified UTS #46 processing (with ICU's fixed flags, see
//! `idna_options`) reports none. Which `UIDNA_ERROR_*` bits are set when there
//! is an error is worked out here, by rerunning the processing with single
//! checks turned on, and is best effort.
#![allow(clippy::missing_safety_doc, non_camel_case_types)]
#![allow(unsafe_op_in_unsafe_fn)]

use crate::idna::{self, Options};
use crate::unicode::{self, Form};
use std::borrow::Cow;
use core::ffi::c_char;

pub type UChar = u16;
pub type UErrorCode = i32;
pub type UBool = i8;

pub const U_ZERO_ERROR: UErrorCode = 0;
pub const U_ILLEGAL_ARGUMENT_ERROR: UErrorCode = 1;
pub const U_INVALID_CHAR_FOUND: UErrorCode = 10;
pub const U_BUFFER_OVERFLOW_ERROR: UErrorCode = 15;
pub const U_STRING_NOT_TERMINATED_WARNING: UErrorCode = -124;

/// An opaque normalizer: one of four static instances.
#[repr(C)]
pub struct UNormalizer2 {
    form: Form,
}

static NFC: UNormalizer2 = UNormalizer2 { form: Form::Nfc };
static NFD: UNormalizer2 = UNormalizer2 { form: Form::Nfd };
static NFKC: UNormalizer2 = UNormalizer2 { form: Form::Nfkc };
static NFKD: UNormalizer2 = UNormalizer2 { form: Form::Nfkd };

pub const UNORM_NO: i32 = 0;
pub const UNORM_YES: i32 = 1;

pub const UIDNA_USE_STD3_RULES: u32 = 2;
pub const UIDNA_CHECK_BIDI: u32 = 4;
pub const UIDNA_CHECK_CONTEXTJ: u32 = 8;
pub const UIDNA_NONTRANSITIONAL_TO_ASCII: u32 = 0x10;
pub const UIDNA_NONTRANSITIONAL_TO_UNICODE: u32 = 0x20;

pub const UIDNA_ERROR_EMPTY_LABEL: u32 = 1;
pub const UIDNA_ERROR_LABEL_TOO_LONG: u32 = 2;
pub const UIDNA_ERROR_DOMAIN_NAME_TOO_LONG: u32 = 4;
pub const UIDNA_ERROR_LEADING_HYPHEN: u32 = 8;
pub const UIDNA_ERROR_TRAILING_HYPHEN: u32 = 0x10;
pub const UIDNA_ERROR_HYPHEN_3_4: u32 = 0x20;
pub const UIDNA_ERROR_LEADING_COMBINING_MARK: u32 = 0x40;
pub const UIDNA_ERROR_DISALLOWED: u32 = 0x80;
pub const UIDNA_ERROR_PUNYCODE: u32 = 0x100;
pub const UIDNA_ERROR_LABEL_HAS_DOT: u32 = 0x200;
pub const UIDNA_ERROR_INVALID_ACE_LABEL: u32 = 0x400;
pub const UIDNA_ERROR_BIDI: u32 = 0x800;
pub const UIDNA_ERROR_CONTEXTJ: u32 = 0x1000;

/// An opaque UTS #46 processor: its options.
#[repr(C)]
pub struct UIDNA {
    options: u32,
}

/// ICU's `UIDNAInfo`.
#[repr(C)]
pub struct UIDNAInfo {
    pub size: i16,
    pub is_transitional_different: UBool,
    pub reserved_b3: UBool,
    pub errors: u32,
    pub reserved_i2: i32,
    pub reserved_i3: i32,
}

macro_rules! export {
    ($vtext:ident, $icu:literal, fn($($a:ident: $t:ty),*) -> $r:ty $body:block) => {
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $vtext($($a: $t),*) -> $r $body

        const _: () = {
            #[cfg(feature = "icu-abi")]
            #[unsafe(export_name = $icu)]
            unsafe extern "C" fn icu($($a: $t),*) -> $r {
                $vtext($($a),*)
            }
        };
    };
}

/// Whether `*err` already holds a failure (ICU's `U_FAILURE`).
unsafe fn failed(err: *mut UErrorCode) -> bool {
    err.is_null() || *err > U_ZERO_ERROR
}

unsafe fn slice<'a, T: Copy + PartialEq + Default>(p: *const T, len: i32) -> Option<&'a [T]> {
    if p.is_null() {
        return if len == 0 { Some(&[]) } else { None };
    }
    let n = if len < 0 {
        let mut n = 0;
        while *p.add(n) != T::default() {
            n += 1;
        }
        n
    } else {
        len as usize
    };
    Some(core::slice::from_raw_parts(p, n))
}

/// Writes `v` to `dest` ICU-style: the full length is returned; it is an
/// overflow error if it does not fit, and a warning if it fits without the
/// NUL.
unsafe fn write_out<T: Copy + Default>(v: &[T], dest: *mut T, capacity: i32, err: *mut UErrorCode) -> i32 {
    write_out2(v, &[], dest, capacity, err)
}

/// `write_out` of `a` followed by `b`.
unsafe fn write_out2<T: Copy + Default>(a: &[T], b: &[T], dest: *mut T, capacity: i32, err: *mut UErrorCode) -> i32 {
    let n = a.len() + b.len();
    if n > i32::MAX as usize {
        *err = U_ILLEGAL_ARGUMENT_ERROR;
        return 0;
    }
    let cap = capacity.max(0) as usize;
    if n > cap {
        *err = U_BUFFER_OVERFLOW_ERROR;
    } else {
        // `dest` may be null when nothing is written.
        if !a.is_empty() {
            core::ptr::copy_nonoverlapping(a.as_ptr(), dest, a.len());
        }
        if !b.is_empty() {
            core::ptr::copy_nonoverlapping(b.as_ptr(), dest.add(a.len()), b.len());
        }
        if n < cap {
            *dest.add(n) = T::default();
        } else if *err == U_ZERO_ERROR {
            *err = U_STRING_NOT_TERMINATED_WARNING;
        }
    }
    n as i32
}

/// Writes ASCII `s` lowercased, as `write_out` would. `ascii_checked`
/// proves this is the ToASCII and ToUnicode result.
unsafe fn write_lower<T: Copy + Default + Into<u32> + From<u8>>(s: &[T], dest: *mut T, capacity: i32, err: *mut UErrorCode) -> i32 {
    let n = s.len();
    if n > i32::MAX as usize {
        *err = U_ILLEGAL_ARGUMENT_ERROR;
        return 0;
    }
    let cap = capacity.max(0) as usize;
    if n > cap {
        *err = U_BUFFER_OVERFLOW_ERROR;
    } else {
        for (k, &c) in s.iter().enumerate() {
            let c: u32 = c.into();
            *dest.add(k) = T::from(if (0x41..=0x5A).contains(&c) { c as u8 + 0x20 } else { c as u8 });
        }
        if n < cap {
            *dest.add(n) = T::default();
        } else if *err == U_ZERO_ERROR {
            *err = U_STRING_NOT_TERMINATED_WARNING;
        }
    }
    n as i32
}

unsafe fn bad_dest<T>(dest: *mut T, capacity: i32) -> bool {
    capacity < 0 || (dest.is_null() && capacity != 0)
}

// ---------------------------------------------------------------------------
// unorm2
// ---------------------------------------------------------------------------

export!(vtext_unorm2_getNFCInstance, "unorm2_getNFCInstance", fn(err: *mut UErrorCode) -> *const UNormalizer2 {
    if failed(err) { core::ptr::null() } else { &NFC }
});
export!(vtext_unorm2_getNFDInstance, "unorm2_getNFDInstance", fn(err: *mut UErrorCode) -> *const UNormalizer2 {
    if failed(err) { core::ptr::null() } else { &NFD }
});
export!(vtext_unorm2_getNFKCInstance, "unorm2_getNFKCInstance", fn(err: *mut UErrorCode) -> *const UNormalizer2 {
    if failed(err) { core::ptr::null() } else { &NFKC }
});
export!(vtext_unorm2_getNFKDInstance, "unorm2_getNFKDInstance", fn(err: *mut UErrorCode) -> *const UNormalizer2 {
    if failed(err) { core::ptr::null() } else { &NFKD }
});

/// Below this code unit, a character is its own normal form, has canonical
/// combining class 0, and is never the second character of a composition,
/// so nothing before it changes it or is changed by it. Text is split before
/// such a character without changing its normal form (`lemma_nf_split`), and
/// a run of them is copied. `tests/capi.rs` checks these facts against the
/// data for every such character.
pub fn stable_below(form: Form) -> u16 {
    match form {
        Form::Nfc => 0x300,
        Form::Nfd => 0xC0,
        Form::Nfkc | Form::Nfkd => 0xA0,
    }
}

/// Where `s` may first differ from its normal form: just before the first
/// unit at or above `stable_below`, or `s.len()` if there is none.
fn stable_prefix(s: &[u16], form: Form) -> usize {
    let b = stable_below(form);
    match s.iter().position(|&u| u >= b) {
        // The character before may combine with the one at `p`.
        Some(p) => p.saturating_sub(1),
        None => s.len(),
    }
}

std::thread_local! {
    static SCRATCH: core::cell::RefCell<Vec<u16>> = const { core::cell::RefCell::new(Vec::new()) };
}

/// Where `s` may first differ from its normal form: `stable_prefix`, then
/// `unicode::normalized_prefix_utf16` from there.
fn normalized_prefix(s: &[u16], form: Form) -> usize {
    let q = stable_prefix(s, form);
    q + unicode::normalized_prefix_utf16(&s[q..], form)
}

/// Writes the normal form of `s` to `dest`, as `write_out` does. The text
/// before `normalized_prefix` is its own normal form and is copied as it
/// is; the rest is normalized by `unicode::normalize_utf16_to` (the verified
/// UTF-16 normalizer) into a scratch buffer kept per thread.
unsafe fn normalize_out(s: &[u16], form: Form, dest: *mut UChar, capacity: i32, err: *mut UErrorCode) -> i32 {
    let p = normalized_prefix(s, form);
    if p == s.len() {
        return write_out(s, dest, capacity, err);
    }
    SCRATCH.with(|cell| {
        let mut fresh = Vec::new();
        let mut guard = cell.try_borrow_mut();
        let out = match guard {
            Ok(ref mut v) => &mut **v,
            Err(_) => &mut fresh,
        };
        out.clear();
        unicode::normalize_utf16_to(&s[p..], form, out);
        let n = write_out2(&s[..p], out, dest, capacity, err);
        if out.capacity() > 1 << 20 {
            *out = Vec::new();
        }
        n
    })
}

fn is_normalized_utf16(s: &[u16], form: Form) -> bool {
    unicode::is_normalized_utf16(&s[normalized_prefix(s, form)..], form)
}

export!(vtext_unorm2_normalize, "unorm2_normalize", fn(
    norm2: *const UNormalizer2,
    src: *const UChar,
    length: i32,
    dest: *mut UChar,
    capacity: i32,
    err: *mut UErrorCode
) -> i32 {
    if failed(err) {
        return 0;
    }
    let Some(s) = slice(src, length) else {
        *err = U_ILLEGAL_ARGUMENT_ERROR;
        return 0;
    };
    if norm2.is_null() || bad_dest(dest, capacity) || (!dest.is_null() && core::ptr::eq(src, dest)) {
        *err = U_ILLEGAL_ARGUMENT_ERROR;
        return 0;
    }
    normalize_out(s, (*norm2).form, dest, capacity, err)
});

export!(vtext_unorm2_isNormalized, "unorm2_isNormalized", fn(
    norm2: *const UNormalizer2,
    src: *const UChar,
    length: i32,
    err: *mut UErrorCode
) -> UBool {
    if failed(err) {
        return 0;
    }
    let Some(s) = slice(src, length) else {
        *err = U_ILLEGAL_ARGUMENT_ERROR;
        return 0;
    };
    if norm2.is_null() {
        *err = U_ILLEGAL_ARGUMENT_ERROR;
        return 0;
    }
    is_normalized_utf16(s, (*norm2).form) as UBool
});

// Always a definite answer: `UNORM_YES` or `UNORM_NO`, never `UNORM_MAYBE`.
export!(vtext_unorm2_quickCheck, "unorm2_quickCheck", fn(
    norm2: *const UNormalizer2,
    src: *const UChar,
    length: i32,
    err: *mut UErrorCode
) -> i32 {
    if vtext_unorm2_isNormalized(norm2, src, length, err) != 0 { UNORM_YES } else { UNORM_NO }
});

// ---------------------------------------------------------------------------
// uidna
// ---------------------------------------------------------------------------

export!(vtext_uidna_openUTS46, "uidna_openUTS46", fn(options: u32, err: *mut UErrorCode) -> *mut UIDNA {
    if failed(err) {
        return core::ptr::null_mut();
    }
    Box::into_raw(Box::new(UIDNA { options }))
});

export!(vtext_uidna_close, "uidna_close", fn(idna: *mut UIDNA) -> () {
    if !idna.is_null() {
        drop(Box::from_raw(idna));
    }
});

/// The UTS #46 flags of an ICU processor: ICU always checks hyphens and,
/// in ToASCII, lengths.
fn idna_options(options: u32, to_ascii: bool) -> Options {
    Options {
        check_hyphens: true,
        check_bidi: options & UIDNA_CHECK_BIDI != 0,
        check_joiners: options & UIDNA_CHECK_CONTEXTJ != 0,
        use_std3_ascii_rules: options & UIDNA_USE_STD3_RULES != 0,
        transitional: options
            & if to_ascii { UIDNA_NONTRANSITIONAL_TO_ASCII } else { UIDNA_NONTRANSITIONAL_TO_UNICODE }
            == 0,
        verify_dns_length: to_ascii,
    }
}

/// The `UIDNA_ERROR_*` bits for `name`, which has an error under `o`: each
/// label of the processed name is checked on its own, with one check at a
/// time.
fn error_bits(name: &str, o: Options) -> u32 {
    let base = Options { check_hyphens: false, check_bidi: false, check_joiners: false, verify_dns_length: false, ..o };
    let (u, _) = idna::to_unicode(name, base);
    let mut bits = 0;
    if has_empty_label(&u) {
        bits |= UIDNA_ERROR_EMPTY_LABEL;
    }
    let mut ascii_len = 0;
    let labels: Vec<&str> = name.split(['.', '\u{3002}', '\u{FF0E}', '\u{FF61}']).collect();
    for (i, &l) in labels.iter().enumerate() {
        if l.is_empty() {
            continue;
        }
        let (d, e) = idna::to_unicode(l, base);
        let lower = l.to_ascii_lowercase();
        let l = lower.as_str();
        if e.is_err() {
            bits |= if let Some(p) = l.strip_prefix("xn--") {
                if idna::punycode::decode_str(p).is_none() { UIDNA_ERROR_PUNYCODE } else { UIDNA_ERROR_INVALID_ACE_LABEL }
            } else if l.chars().next().is_some_and(is_mark) {
                UIDNA_ERROR_LEADING_COMBINING_MARK
            } else {
                UIDNA_ERROR_DISALLOWED
            };
        }
        // ICU checks hyphens in the ASCII label when that is xn--.
        let h = if l.starts_with("xn--") { l } else { &d };
        if h.starts_with('-') {
            bits |= UIDNA_ERROR_LEADING_HYPHEN;
        }
        if h.ends_with('-') {
            bits |= UIDNA_ERROR_TRAILING_HYPHEN;
        }
        if !h.starts_with("xn--") && h.chars().skip(2).take(2).eq("--".chars()) {
            bits |= UIDNA_ERROR_HYPHEN_3_4;
        }
        if o.check_joiners && idna::to_unicode(l, Options { check_joiners: true, ..base }).1.is_err() && e.is_ok() {
            bits |= UIDNA_ERROR_CONTEXTJ;
        }
        if o.verify_dns_length {
            let n = idna::to_ascii(l, base).map_or(l.len(), |a| a.len());
            if n > 63 {
                bits |= UIDNA_ERROR_LABEL_TOO_LONG;
            }
            if !(i + 1 == labels.len() && labels.len() > 1 && l.is_empty()) {
                ascii_len += n + 1;
            }
        }
    }
    if o.verify_dns_length && ascii_len > 254 {
        bits |= UIDNA_ERROR_DOMAIN_NAME_TOO_LONG;
    }
    if o.check_bidi && bits == 0 && idna::to_unicode(name, Options { check_bidi: true, ..base }).1.is_err() {
        bits |= UIDNA_ERROR_BIDI;
    }
    if bits == 0 { UIDNA_ERROR_DISALLOWED } else { bits }
}

/// A combining mark (general category M), as UTS #46 criterion 6 reads it.
fn is_mark(c: char) -> bool {
    idna::data::iword_of(c as u32) & 8 != 0
}

/// ToASCII or ToUnicode of `name`: the output (ICU writes one even when
/// there are errors) and the info.
fn idna_process(idna: &UIDNA, name: &str, to_ascii: bool) -> (String, u32, bool) {
    let o = idna_options(idna.options, to_ascii);
    let (out, ok) = if to_ascii {
        // ICU allows a final root label under VerifyDnsLength, which UTS #46
        // does not: on an error, check the name without it and put the dot
        // back.
        match idna::to_ascii(name, o) {
            Ok(a) => (a, true),
            Err(_) => {
                let stripped = name
                    .rfind(['.', '\u{3002}', '\u{FF0E}', '\u{FF61}'])
                    .filter(|&p| p > 0 && idna::to_unicode(&name[p..], o).0 == ".")
                    .and_then(|p| idna::to_ascii(&name[..p], o).ok());
                match stripped {
                    Some(a) => (a + ".", true),
                    None => (idna::to_unicode(name, o).0, false),
                }
            }
        }
    } else {
        let (u, e) = idna::to_unicode(name, o);
        (u, e.is_ok())
    };
    let mut errors = if ok { 0 } else { error_bits(name, o) };
    // ICU reports an empty label other than the root in ToUnicode too.
    if !to_ascii && has_empty_label(&out) {
        errors |= UIDNA_ERROR_EMPTY_LABEL;
        errors &= !(UIDNA_ERROR_DISALLOWED * (ok as u32));
    }
    // Only the deviation characters (and U+1E9E, which maps to one) are
    // processed differently.
    let differs = name.contains(['\u{DF}', '\u{3C2}', '\u{200C}', '\u{200D}', '\u{1E9E}'])
        && idna::to_unicode(name, Options { transitional: true, ..o }).0
            != idna::to_unicode(name, Options { transitional: false, ..o }).0;
    (out, errors, differs)
}

/// Whether a processed name has an empty label, other than a final root
/// label after at least one other.
fn has_empty_label(u: &str) -> bool {
    let labels: Vec<&str> = u.split('.').collect();
    let n = if labels.len() > 1 && labels[labels.len() - 1].is_empty() { labels.len() - 1 } else { labels.len() };
    labels[..n].iter().any(|l| l.is_empty())
}

unsafe fn fill_info(info: *mut UIDNAInfo, errors: u32, differs: bool) -> bool {
    if info.is_null() || ((*info).size as usize) < core::mem::size_of::<UIDNAInfo>() {
        return false;
    }
    (*info).errors = errors;
    (*info).is_transitional_different = differs as UBool;
    true
}

unsafe fn idna_utf8(
    idna: *const UIDNA,
    name: *const c_char,
    length: i32,
    dest: *mut c_char,
    capacity: i32,
    info: *mut UIDNAInfo,
    err: *mut UErrorCode,
    to_ascii: bool,
) -> i32 {
    if failed(err) {
        return 0;
    }
    let Some(s) = slice(name as *const u8, length) else {
        *err = U_ILLEGAL_ARGUMENT_ERROR;
        return 0;
    };
    if idna.is_null() || bad_dest(dest, capacity) || info.is_null() {
        *err = U_ILLEGAL_ARGUMENT_ERROR;
        return 0;
    }
    // An ASCII name that passes every check is only lowercased, which
    // `to_ascii_fast` proves for both ToASCII and ToUnicode.
    // `ascii_checked_bytes` is false unless the bytes are ASCII, so the
    // `from_utf8_unchecked` below is of ASCII.
    if idna::strs::ascii_checked_bytes(s, idna_options((*idna).options, to_ascii))
        && (to_ascii || !has_empty_label(core::str::from_utf8_unchecked(s)))
    {
        if !fill_info(info, 0, false) {
            *err = U_ILLEGAL_ARGUMENT_ERROR;
            return 0;
        }
        return write_lower(s, dest as *mut u8, capacity, err);
    }
    // Ill-formed UTF-8 is replaced by U+FFFD, which is disallowed, so it is
    // an error as in ICU.
    let name = String::from_utf8_lossy(s);
    let (out, errors, differs) = idna_process(&*idna, &name, to_ascii);
    if !fill_info(info, errors, differs) {
        *err = U_ILLEGAL_ARGUMENT_ERROR;
        return 0;
    }
    write_out(out.as_bytes(), dest as *mut u8, capacity, err)
}

unsafe fn idna_utf16(
    idna: *const UIDNA,
    name: *const UChar,
    length: i32,
    dest: *mut UChar,
    capacity: i32,
    info: *mut UIDNAInfo,
    err: *mut UErrorCode,
    to_ascii: bool,
) -> i32 {
    if failed(err) {
        return 0;
    }
    let Some(s) = slice(name, length) else {
        *err = U_ILLEGAL_ARGUMENT_ERROR;
        return 0;
    };
    if idna.is_null() || bad_dest(dest, capacity) || info.is_null() {
        *err = U_ILLEGAL_ARGUMENT_ERROR;
        return 0;
    }
    if s.len() <= 256 && s.iter().all(|&u| u < 0x80) {
        let mut b = [0u8; 256];
        for (d, &u) in b.iter_mut().zip(s) {
            *d = u as u8;
        }
        let b = &b[..s.len()];
        if idna::strs::ascii_checked_bytes(b, idna_options((*idna).options, to_ascii))
            && (to_ascii || !has_empty_label(core::str::from_utf8_unchecked(b)))
        {
            if !fill_info(info, 0, false) {
                *err = U_ILLEGAL_ARGUMENT_ERROR;
                return 0;
            }
            return write_lower(s, dest, capacity, err);
        }
    }
    let name = String::from_utf16_lossy(s);
    let (out, errors, differs) = idna_process(&*idna, &name, to_ascii);
    if !fill_info(info, errors, differs) {
        *err = U_ILLEGAL_ARGUMENT_ERROR;
        return 0;
    }
    let v: Vec<u16> = out.encode_utf16().collect();
    write_out(&v, dest, capacity, err)
}

export!(vtext_uidna_nameToASCII_UTF8, "uidna_nameToASCII_UTF8", fn(
    idna: *const UIDNA,
    name: *const c_char,
    length: i32,
    dest: *mut c_char,
    capacity: i32,
    info: *mut UIDNAInfo,
    err: *mut UErrorCode
) -> i32 {
    idna_utf8(idna, name, length, dest, capacity, info, err, true)
});

export!(vtext_uidna_nameToUnicodeUTF8, "uidna_nameToUnicodeUTF8", fn(
    idna: *const UIDNA,
    name: *const c_char,
    length: i32,
    dest: *mut c_char,
    capacity: i32,
    info: *mut UIDNAInfo,
    err: *mut UErrorCode
) -> i32 {
    idna_utf8(idna, name, length, dest, capacity, info, err, false)
});

export!(vtext_uidna_nameToASCII, "uidna_nameToASCII", fn(
    idna: *const UIDNA,
    name: *const UChar,
    length: i32,
    dest: *mut UChar,
    capacity: i32,
    info: *mut UIDNAInfo,
    err: *mut UErrorCode
) -> i32 {
    idna_utf16(idna, name, length, dest, capacity, info, err, true)
});

export!(vtext_uidna_nameToUnicode, "uidna_nameToUnicode", fn(
    idna: *const UIDNA,
    name: *const UChar,
    length: i32,
    dest: *mut UChar,
    capacity: i32,
    info: *mut UIDNAInfo,
    err: *mut UErrorCode
) -> i32 {
    idna_utf16(idna, name, length, dest, capacity, info, err, false)
});

// Unused today; keeps the constant in the header's vocabulary.
const _: UErrorCode = U_INVALID_CHAR_FOUND;

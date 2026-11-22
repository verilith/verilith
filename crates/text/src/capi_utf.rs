//! A C API for the transcoders and forgiving base64, with simdutf's
//! semantics: the functions Node.js calls (`vtext_<simdutf name>`), which
//! `include/vtext_utf.h` declares and vbind's `simdutf.h` wraps in
//! simdutf's C++ API.
//!
//! This is plain Rust glue outside the proofs. It turns pointers and
//! lengths into slices and calls the verified functions, which compute every
//! result: validity, converted text, lengths, and decoded bytes. Output
//! slices are exactly as long as simdutf's documented output size for the
//! input (`utf16_length_from_utf8` and so on), which is what callers
//! allocate; the converters are proven never to write past that.
//!
//! Two things are worked out here, unverified: which simdutf error code and
//! position describe an invalid input (`utf8_error`, a transliteration of
//! simdutf's scalar validator, run only once the verified validator has
//! said the input is invalid), and the error position for base64.
#![allow(clippy::missing_safety_doc)]
#![allow(unsafe_op_in_unsafe_fn)]

use crate::base64::forgiving::{decode_forgiving, max_len_exec, B64Error};
use crate::base64::scalar::{enc_len, encode_into};

use crate::base64::spec::Config;
use crate::utf::conv;
use crate::utf::valid8::utf8_valid;
use core::ffi::c_char;

// simdutf::error_code.
pub const SUCCESS: i32 = 0;
pub const HEADER_BITS: i32 = 1;
pub const TOO_SHORT: i32 = 2;
pub const TOO_LONG: i32 = 3;
pub const OVERLONG: i32 = 4;
pub const TOO_LARGE: i32 = 5;
pub const SURROGATE: i32 = 6;
pub const INVALID_BASE64_CHARACTER: i32 = 7;
pub const BASE64_INPUT_REMAINDER: i32 = 8;
pub const BASE64_EXTRA_BITS: i32 = 9;
pub const OUTPUT_BUFFER_TOO_SMALL: i32 = 10;
pub const OTHER: i32 = 11;

// simdutf::base64_options bits.
pub const BASE64_URL: u64 = 1;
pub const BASE64_REVERSE_PADDING: u64 = 2;

unsafe fn bytes<'a>(p: *const c_char, n: usize) -> &'a [u8] {
    assert!(n < conv::MAX_LEN);
    if n == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(p as *const u8, n)
    }
}

unsafe fn units<'a>(p: *const u16, n: usize) -> &'a [u16] {
    assert!(n < conv::MAX_LEN);
    if n == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(p, n)
    }
}

unsafe fn bytes_mut<'a>(p: *mut c_char, n: usize) -> &'a mut [u8] {
    if n == 0 {
        &mut []
    } else {
        core::slice::from_raw_parts_mut(p as *mut u8, n)
    }
}

unsafe fn units_mut<'a>(p: *mut u16, n: usize) -> &'a mut [u16] {
    if n == 0 {
        &mut []
    } else {
        core::slice::from_raw_parts_mut(p, n)
    }
}

unsafe fn put(p: *mut usize, v: usize) {
    if !p.is_null() {
        *p = v;
    }
}

/// simdutf's error code and position for invalid UTF-8 (its scalar
/// `validate_with_errors`).
pub fn utf8_error(d: &[u8]) -> (i32, usize) {
    let len = d.len();
    let mut pos = 0;
    while pos < len {
        let b = d[pos];
        if b < 0x80 {
            pos += 1;
            continue;
        }
        let cont = |i: usize| i < len && d[i] & 0xC0 == 0x80;
        let next;
        if b & 0xE0 == 0xC0 {
            next = pos + 2;
            if next > len || !cont(pos + 1) {
                return (TOO_SHORT, pos);
            }
            let c = ((b as u32 & 0x1F) << 6) | (d[pos + 1] as u32 & 0x3F);
            if !(0x80..=0x7FF).contains(&c) {
                return (OVERLONG, pos);
            }
        } else if b & 0xF0 == 0xE0 {
            next = pos + 3;
            if next > len || !cont(pos + 1) || !cont(pos + 2) {
                return (TOO_SHORT, pos);
            }
            let c = ((b as u32 & 0x0F) << 12) | ((d[pos + 1] as u32 & 0x3F) << 6) | (d[pos + 2] as u32 & 0x3F);
            if !(0x800..=0xFFFF).contains(&c) {
                return (OVERLONG, pos);
            }
            if (0xD800..0xE000).contains(&c) {
                return (SURROGATE, pos);
            }
        } else if b & 0xF8 == 0xF0 {
            next = pos + 4;
            if next > len || !cont(pos + 1) || !cont(pos + 2) || !cont(pos + 3) {
                return (TOO_SHORT, pos);
            }
            let c = ((b as u32 & 0x07) << 18)
                | ((d[pos + 1] as u32 & 0x3F) << 12)
                | ((d[pos + 2] as u32 & 0x3F) << 6)
                | (d[pos + 3] as u32 & 0x3F);
            if c <= 0xFFFF {
                return (OVERLONG, pos);
            }
            if c > 0x10FFFF {
                return (TOO_LARGE, pos);
            }
        } else if b & 0xC0 == 0x80 {
            return (TOO_LONG, pos);
        } else {
            return (HEADER_BITS, pos);
        }
        pos = next;
    }
    // Not reached for input the verified validator rejected.
    (OTHER, len)
}

// ---------------------------------------------------------------------------
// Validation and sizes
// ---------------------------------------------------------------------------

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_validate_utf8(p: *const c_char, n: usize) -> bool {
    utf8_valid(bytes(p, n))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_validate_utf8_with_errors(p: *const c_char, n: usize, count: *mut usize) -> i32 {
    let s = bytes(p, n);
    if utf8_valid(s) {
        put(count, n);
        return SUCCESS;
    }
    let (e, at) = utf8_error(s);
    put(count, at);
    e
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_validate_ascii(p: *const c_char, n: usize) -> bool {
    conv::ascii_prefix(bytes(p, n)) == n
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_validate_ascii_with_errors(p: *const c_char, n: usize, count: *mut usize) -> i32 {
    let k = conv::ascii_prefix(bytes(p, n));
    put(count, k);
    if k == n {
        SUCCESS
    } else {
        TOO_LARGE
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_utf8_length_from_latin1(p: *const c_char, n: usize) -> usize {
    conv::count_latin1_utf8(bytes(p, n))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_utf16_length_from_utf8(p: *const c_char, n: usize) -> usize {
    conv::count_utf8(bytes(p, n), false)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_latin1_length_from_utf8(p: *const c_char, n: usize) -> usize {
    conv::count_utf8(bytes(p, n), true)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_utf8_length_from_utf16(p: *const u16, n: usize) -> usize {
    conv::count_utf16(units(p, n))
}

// ---------------------------------------------------------------------------
// Conversions
// ---------------------------------------------------------------------------

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_convert_latin1_to_utf8(p: *const c_char, n: usize, out: *mut c_char) -> usize {
    let s = bytes(p, n);
    let m = conv::count_latin1_utf8(s);
    conv::latin1_to_utf8(s, bytes_mut(out, m))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_convert_latin1_to_utf8_safe(
    p: *const c_char,
    n: usize,
    out: *mut c_char,
    cap: usize,
) -> usize {
    conv::latin1_to_utf8_safe(bytes(p, n), bytes_mut(out, cap)).1
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_convert_latin1_to_utf16(p: *const c_char, n: usize, out: *mut u16) -> usize {
    conv::latin1_to_utf16(bytes(p, n), units_mut(out, n));
    n
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_convert_utf8_to_utf16(p: *const c_char, n: usize, out: *mut u16) -> usize {
    let s = bytes(p, n);
    let m = conv::count_utf8(s, false);
    conv::utf8_to_utf16(s, units_mut(out, m)).unwrap_or(0)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_convert_utf16_to_utf8(p: *const u16, n: usize, out: *mut c_char) -> usize {
    let s = units(p, n);
    let m = conv::count_utf16(s);
    conv::utf16_to_utf8(s, bytes_mut(out, m)).unwrap_or(0)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_convert_utf16_to_latin1(p: *const u16, n: usize, out: *mut c_char) -> usize {
    if conv::utf16_to_latin1(units(p, n), bytes_mut(out, n)) {
        n
    } else {
        0
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_convert_utf8_to_latin1_with_errors(
    p: *const c_char,
    n: usize,
    out: *mut c_char,
    count: *mut usize,
) -> i32 {
    let s = bytes(p, n);
    let m = conv::count_utf8(s, true);
    match conv::utf8_to_latin1(s, bytes_mut(out, m)) {
        Some(w) => {
            put(count, w);
            SUCCESS
        }
        None => {
            let (e, at) = latin1_error(s);
            put(count, at);
            e
        }
    }
}

/// simdutf's error for UTF-8 that is not Latin-1 text: the first lead byte
/// of three or four bytes is TOO_LARGE whatever follows it, as is a two-byte
/// character above U+00FF (a transliteration of simdutf's scalar
/// `utf8_to_latin1::convert_with_errors`).
fn latin1_error(d: &[u8]) -> (i32, usize) {
    let mut i = 0;
    while i < d.len() {
        let b = d[i];
        if b < 0x80 {
            i += 1;
        } else if b & 0xE0 == 0xC0 {
            if i + 1 >= d.len() || d[i + 1] & 0xC0 != 0x80 {
                return (TOO_SHORT, i);
            }
            let c = ((b as u32 & 0x1F) << 6) | (d[i + 1] as u32 & 0x3F);
            if c < 0x80 {
                return (OVERLONG, i);
            }
            if c > 0xFF {
                return (TOO_LARGE, i);
            }
            i += 2;
        } else if b & 0xF0 == 0xE0 || b & 0xF8 == 0xF0 {
            return (TOO_LARGE, i);
        } else if b & 0xC0 == 0x80 {
            return (TOO_LONG, i);
        } else {
            return (HEADER_BITS, i);
        }
    }
    (SUCCESS, d.len())
}

// ---------------------------------------------------------------------------
// Base64
// ---------------------------------------------------------------------------

fn config(options: u64) -> Config {
    let url = options & BASE64_URL != 0;
    // Padded by default for the standard alphabet and not for URL;
    // `base64_reverse_padding` swaps that.
    let pad = !url ^ (options & BASE64_REVERSE_PADDING != 0);
    Config { url, pad }
}

#[unsafe(no_mangle)]
pub extern "C" fn vtext_base64_length_from_binary(n: usize, options: u64) -> usize {
    assert!(n <= usize::MAX / 2);
    enc_len(n, config(options).pad)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_binary_to_base64(p: *const c_char, n: usize, out: *mut c_char, options: u64) -> usize {
    let cfg = config(options);
    let m = enc_len(n, cfg.pad);
    encode_into(cfg, bytes(p, n), bytes_mut(out, m));
    m
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_maximal_binary_length_from_base64(p: *const c_char, n: usize) -> usize {
    max_len_exec(bytes(p, n))
}

/// UTF-16 base64 as bytes: units above 0xFF become 0xFF, which is neither
/// whitespace, padding nor in either alphabet, as simdutf treats them.
fn narrow(s: &[u16]) -> Vec<u8> {
    s.iter().map(|&u| if u > 0xFF { 0xFF } else { u as u8 }).collect()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_maximal_binary_length_from_base64_utf16(p: *const u16, n: usize) -> usize {
    let s = units(p, n);
    // As for bytes: the decoded size of what precedes the `=` it ends with.
    let eq = |i: usize| s[i] == b'=' as u16;
    let p = if n >= 1 && eq(n - 1) { if n >= 2 && eq(n - 2) { 2 } else { 1 } } else { 0 };
    crate::base64::scalar::dec_len(n - p)
}

/// The first position simdutf would report for an invalid text: the first
/// character that is neither whitespace nor in the alphabet, else the end.
fn b64_error_pos(s: &[u8], url: bool) -> usize {
    let ok = |c: u8| {
        c.is_ascii_alphanumeric()
            || matches!(c, b' ' | b'\t' | b'\n' | b'\r' | 0x0C)
            || if url { c == b'-' || c == b'_' } else { c == b'+' || c == b'/' }
    };
    s.iter().position(|&c| !ok(c)).unwrap_or(s.len())
}

fn b64_code(e: B64Error) -> i32 {
    match e {
        B64Error::Invalid => INVALID_BASE64_CHARACTER,
        B64Error::Remainder => BASE64_INPUT_REMAINDER,
        B64Error::TooSmall => OUTPUT_BUFFER_TOO_SMALL,
    }
}

unsafe fn b64_decode(s: &[u8], out: *mut c_char, options: u64, count: *mut usize) -> i32 {
    let url = options & BASE64_URL != 0;
    let m = max_len_exec(s);
    match decode_forgiving(url, s, bytes_mut(out, m)) {
        Ok(w) => {
            put(count, w);
            SUCCESS
        }
        Err(e) => {
            put(count, b64_error_pos(s, url));
            b64_code(e)
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_base64_to_binary(
    p: *const c_char,
    n: usize,
    out: *mut c_char,
    options: u64,
    count: *mut usize,
) -> i32 {
    b64_decode(bytes(p, n), out, options, count)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_base64_to_binary_utf16(
    p: *const u16,
    n: usize,
    out: *mut c_char,
    options: u64,
    count: *mut usize,
) -> i32 {
    b64_decode(&narrow(units(p, n)), out, options, count)
}

unsafe fn b64_decode_safe(s: &[u8], out: *mut c_char, outlen: *mut usize, options: u64, count: *mut usize) -> i32 {
    let url = options & BASE64_URL != 0;
    let cap = *outlen;
    let dst = bytes_mut(out, cap);
    match decode_forgiving(url, s, dst) {
        Ok(w) => {
            *outlen = w;
            put(count, s.len());
            SUCCESS
        }
        Err(B64Error::TooSmall) => {
            // As simdutf does, fill the buffer with the whole groups that fit.
            let mut full = vec![0u8; max_len_exec(s)];
            let w = decode_forgiving(url, s, &mut full).unwrap_or(0);
            let k = (cap / 3 * 3).min(w);
            dst[..k].copy_from_slice(&full[..k]);
            *outlen = k;
            put(count, 0);
            OUTPUT_BUFFER_TOO_SMALL
        }
        Err(e) => {
            *outlen = 0;
            put(count, b64_error_pos(s, url));
            b64_code(e)
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_base64_to_binary_safe(
    p: *const c_char,
    n: usize,
    out: *mut c_char,
    outlen: *mut usize,
    options: u64,
    count: *mut usize,
) -> i32 {
    b64_decode_safe(bytes(p, n), out, outlen, options, count)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_base64_to_binary_safe_utf16(
    p: *const u16,
    n: usize,
    out: *mut c_char,
    outlen: *mut usize,
    options: u64,
    count: *mut usize,
) -> i32 {
    b64_decode_safe(&narrow(units(p, n)), out, outlen, options, count)
}

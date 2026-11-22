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
//! Some things are worked out here, unverified:
//!
//! * which simdutf error code and position describe an invalid input
//!   (`utf8_error`, a transliteration of simdutf's scalar validator, run
//!   only once the verified validator has said the input is invalid);
//! * base64 that the verified forgiving decoder does not decode: the
//!   `strict` and `stop_before_partial` last-chunk modes of
//!   `Uint8Array.fromBase64`, input the forgiving decoder rejects, and
//!   output buffers too small for the whole text. Those go through
//!   `b64_details`, a transliteration of simdutf's scalar decoder, which
//!   also gives simdutf's error code and position. A `loose` decode of valid
//!   text into a large enough buffer, which is every base64 decode Node's
//!   Buffer and `atob` make, is the verified decoder's;
//! * the UTF-16 well-formedness functions (`validate_utf16`,
//!   `to_well_formed_utf16`, `utf8_length_from_utf16_with_replacement`) and
//!   `convert_utf32_to_utf8`, which are short loops over code units.
#![allow(clippy::missing_safety_doc)]
#![allow(unsafe_op_in_unsafe_fn)]

use crate::base64::forgiving::{decode_forgiving, max_len_exec};
use crate::base64::scalar::{dec_tab, enc_len, encode_into};

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

// simdutf::last_chunk_handling_options.
pub const LOOSE: u64 = 0;
pub const STRICT: u64 = 1;
pub const STOP_BEFORE_PARTIAL: u64 = 2;

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
// UTF-16 well-formedness (unverified)
// ---------------------------------------------------------------------------

fn is_high(u: u16) -> bool {
    u & 0xFC00 == 0xD800
}

fn is_low(u: u16) -> bool {
    u & 0xFC00 == 0xDC00
}

/// The index of the first surrogate that is not half of a pair.
fn utf16_error(s: &[u16]) -> Option<usize> {
    let mut i = 0;
    while i < s.len() {
        let u = s[i];
        if u & 0xF800 != 0xD800 {
            i += 1;
        } else if is_high(u) && i + 1 < s.len() && is_low(s[i + 1]) {
            i += 2;
        } else {
            return Some(i);
        }
    }
    None
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_validate_utf16(p: *const u16, n: usize) -> bool {
    utf16_error(units(p, n)).is_none()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_validate_utf16_with_errors(p: *const u16, n: usize, count: *mut usize) -> i32 {
    match utf16_error(units(p, n)) {
        None => {
            put(count, n);
            SUCCESS
        }
        Some(at) => {
            put(count, at);
            SURROGATE
        }
    }
}

/// Copies `n` units to `out` with every unpaired surrogate replaced by
/// U+FFFD. `out` may be the input itself, so this works on pointers.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_to_well_formed_utf16(p: *const u16, n: usize, out: *mut u16) {
    let mut i = 0;
    while i < n {
        let u = *p.add(i);
        if u & 0xF800 != 0xD800 {
            *out.add(i) = u;
            i += 1;
        } else if is_high(u) && i + 1 < n && is_low(*p.add(i + 1)) {
            let v = *p.add(i + 1);
            *out.add(i) = u;
            *out.add(i + 1) = v;
            i += 2;
        } else {
            *out.add(i) = 0xFFFD;
            i += 1;
        }
    }
}

/// The UTF-8 length of the text with unpaired surrogates read as U+FFFD,
/// through `count`. Returns SURROGATE when the text has any surrogate,
/// paired or not, as simdutf does.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_utf8_length_from_utf16_with_replacement(
    p: *const u16,
    n: usize,
    count: *mut usize,
) -> i32 {
    let s = units(p, n);
    let mut len = 0usize;
    let mut any = false;
    let mut i = 0;
    while i < s.len() {
        let u = s[i];
        if u < 0x80 {
            len += 1;
        } else if u < 0x800 {
            len += 2;
        } else if u & 0xF800 != 0xD800 {
            len += 3;
        } else {
            any = true;
            if is_high(u) && i + 1 < s.len() && is_low(s[i + 1]) {
                len += 4;
                i += 1;
            } else {
                len += 3;
            }
        }
        i += 1;
    }
    put(count, len);
    if any {
        SURROGATE
    } else {
        SUCCESS
    }
}

/// UTF-32 to UTF-8; 0 if a unit is not a scalar value. `out` holds four
/// bytes per unit.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_convert_utf32_to_utf8(p: *const u32, n: usize, out: *mut c_char) -> usize {
    let mut w = 0;
    for i in 0..n {
        let Some(c) = char::from_u32(*p.add(i)) else { return 0 };
        let mut b = [0u8; 4];
        let e = c.encode_utf8(&mut b);
        core::ptr::copy_nonoverlapping(e.as_ptr(), out.add(w) as *mut u8, e.len());
        w += e.len();
    }
    w
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
pub unsafe extern "C" fn vtext_convert_utf8_to_utf16_with_errors(
    p: *const c_char,
    n: usize,
    out: *mut u16,
    count: *mut usize,
) -> i32 {
    let s = bytes(p, n);
    let m = conv::count_utf8(s, false);
    match conv::utf8_to_utf16(s, units_mut(out, m)) {
        Some(w) => {
            put(count, w);
            SUCCESS
        }
        None => {
            let (e, at) = utf8_error(s);
            put(count, at);
            e
        }
    }
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

// What follows is a transliteration of simdutf 7's scalar base64 decoder
// (`find_end`, `base64_tail_decode_impl`, `patch_tail_result` and
// `base64_to_binary_details_safe_impl`), without its accept-garbage options.
// It is unverified. It runs only when the verified forgiving decoder cannot
// give the answer: see the module comment.

/// simdutf's `full_result`.
struct Full {
    error: i32,
    input: usize,
    output: usize,
    padding_error: bool,
}

fn full(error: i32, input: usize, output: usize) -> Full {
    Full { error, input, output, padding_error: false }
}

/// simdutf's `to_base64` tables: the value of an alphabet character, 64 for
/// the whitespace base64 ignores, more for anything else.
fn b64_class(url: bool, c: u8) -> u8 {
    let v = dec_tab(url)[c as usize];
    if v < 64 {
        v
    } else if matches!(c, b' ' | b'\t' | b'\n' | b'\r' | 0x0C) {
        64
    } else {
        255
    }
}

fn b64_tail(dst: &mut [u8], s: &[u8], pad: usize, url: bool, last: u64) -> Full {
    let partial = last == STOP_BEFORE_PARTIAL;
    let (mut src, mut d) = (0usize, 0usize);
    loop {
        let cur = src;
        let mut idx = 0;
        let mut buf = [0u8; 4];
        while idx < 4 && src < s.len() {
            let code = b64_class(url, s[src]);
            if code <= 63 {
                buf[idx] = code;
                idx += 1;
            } else if code > 64 {
                return full(INVALID_BASE64_CHARACTER, src, d);
            }
            src += 1;
        }
        let triple = ((buf[0] as u32) << 18) | ((buf[1] as u32) << 12) | ((buf[2] as u32) << 6) | buf[3] as u32;
        if idx == 4 {
            if dst.len() - d < 3 {
                return full(OUTPUT_BUFFER_TOO_SMALL, cur, d);
            }
            dst[d] = (triple >> 16) as u8;
            dst[d + 1] = (triple >> 8) as u8;
            dst[d + 2] = triple as u8;
            d += 3;
            continue;
        }
        if idx + pad > 4 {
            return Full { error: INVALID_BASE64_CHARACTER, input: src, output: d, padding_error: true };
        }
        if last == LOOSE && idx >= 2 && pad > 0 && (idx + pad) & 3 != 0 {
            return Full { error: INVALID_BASE64_CHARACTER, input: src, output: d, padding_error: true };
        }
        if last == STRICT && idx >= 2 && (idx + pad) & 3 != 0 {
            return Full { error: BASE64_INPUT_REMAINDER, input: src, output: d, padding_error: true };
        }
        if partial && pad + idx < 4 && idx != 0 && (idx >= 2 || pad == 0) {
            // The partial chunk is not consumed.
            return full(SUCCESS, cur, d);
        }
        if idx == 2 {
            if last == STRICT && triple & 0xFFFF != 0 {
                return full(BASE64_EXTRA_BITS, src, d);
            }
            if dst.len() - d < 1 {
                return full(OUTPUT_BUFFER_TOO_SMALL, cur, d);
            }
            dst[d] = (triple >> 16) as u8;
            d += 1;
        } else if idx == 3 {
            if last == STRICT && triple & 0xFF != 0 {
                return full(BASE64_EXTRA_BITS, src, d);
            }
            if dst.len() - d < 2 {
                return full(OUTPUT_BUFFER_TOO_SMALL, cur, d);
            }
            dst[d] = (triple >> 16) as u8;
            dst[d + 1] = (triple >> 8) as u8;
            d += 2;
        } else if idx == 1 && (!partial || pad > 0) {
            return full(BASE64_INPUT_REMAINDER, src, d);
        } else if idx == 0 && pad > 0 {
            return Full { error: INVALID_BASE64_CHARACTER, input: src, output: d, padding_error: true };
        }
        return full(SUCCESS, src, d);
    }
}

/// Decodes `s` into `dst`, stopping at its end. `slow` is simdutf's
/// `slow_base64_to_binary_safe_impl`, which it runs for a caller that wants
/// the bytes before an invalid character: the same decoding, with the
/// position left where the decoder stopped.
fn b64_details(s: &[u8], dst: &mut [u8], url: bool, last: u64, slow: bool) -> Full {
    let partial = last == STOP_BEFORE_PARTIAL;
    let ws = |i: usize| b64_class(url, s[i]) == 64;
    let whole = s.len();
    let mut n = whole;
    while n > 0 && ws(n - 1) {
        n -= 1;
    }
    let (mut eq_at, mut eqs) = (n, 0);
    if n > 0 && s[n - 1] == b'=' {
        n -= 1;
        eq_at = n;
        eqs = 1;
        while n > 0 && ws(n - 1) {
            n -= 1;
        }
        if n > 0 && s[n - 1] == b'=' {
            n -= 1;
            eq_at = n;
            eqs = 2;
        }
    }
    if n == 0 {
        if eqs > 0 {
            return full(INVALID_BASE64_CHARACTER, eq_at, 0);
        }
        return full(SUCCESS, if slow { 0 } else { whole }, 0);
    }
    let mut r = b64_tail(dst, &s[..n], eqs, url, last);
    if r.padding_error {
        r.input = eq_at;
    }
    if r.error == SUCCESS && (!partial || r.output % 3 != 0) {
        r.input = whole;
    }
    if !partial && r.error == SUCCESS && eqs > 0 && (r.output % 3 == 0 || r.output % 3 + 1 + eqs != 4) {
        r.error = INVALID_BASE64_CHARACTER;
        if !slow {
            r.input = eq_at;
        }
        return r;
    }
    // A decode that stops before a partial chunk ends at the end of the
    // text, or else right after a character that is not whitespace.
    if !slow && partial && r.error == SUCCESS && r.input < whole {
        while r.input < whole && ws(r.input) {
            r.input += 1;
        }
        if r.input < whole {
            while r.input > 0 && ws(r.input - 1) {
                r.input -= 1;
            }
        }
    }
    r
}

unsafe fn b64_decode(s: &[u8], out: *mut c_char, options: u64, last: u64, count: *mut usize) -> i32 {
    let url = options & BASE64_URL != 0;
    let dst = bytes_mut(out, max_len_exec(s));
    if last == LOOSE {
        if let Ok(w) = decode_forgiving(url, s, dst) {
            put(count, w);
            return SUCCESS;
        }
    }
    let r = b64_details(s, dst, url, last, false);
    put(count, if r.error == SUCCESS { r.output } else { r.input });
    r.error
}

/// `last` is a simdutf::last_chunk_handling_options value.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_base64_to_binary(
    p: *const c_char,
    n: usize,
    out: *mut c_char,
    options: u64,
    last: u64,
    count: *mut usize,
) -> i32 {
    b64_decode(bytes(p, n), out, options, last, count)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_base64_to_binary_utf16(
    p: *const u16,
    n: usize,
    out: *mut c_char,
    options: u64,
    last: u64,
    count: *mut usize,
) -> i32 {
    b64_decode(&narrow(units(p, n)), out, options, last, count)
}

unsafe fn b64_decode_safe(
    s: &[u8],
    out: *mut c_char,
    outlen: *mut usize,
    options: u64,
    last: u64,
    up_to_bad_char: bool,
    count: *mut usize,
) -> i32 {
    let url = options & BASE64_URL != 0;
    let dst = bytes_mut(out, *outlen);
    if last == LOOSE {
        if let Ok(w) = decode_forgiving(url, s, dst) {
            *outlen = w;
            put(count, s.len());
            return SUCCESS;
        }
    }
    let mut r = b64_details(s, dst, url, last, false);
    if up_to_bad_char && r.error == INVALID_BASE64_CHARACTER {
        r = b64_details(s, dst, url, last, true);
    }
    *outlen = r.output;
    put(count, r.input);
    r.error
}

/// `count` receives the number of input units read, on success too.
/// `up_to_bad_char` is simdutf's `decode_up_to_bad_char`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_base64_to_binary_safe(
    p: *const c_char,
    n: usize,
    out: *mut c_char,
    outlen: *mut usize,
    options: u64,
    last: u64,
    up_to_bad_char: bool,
    count: *mut usize,
) -> i32 {
    b64_decode_safe(bytes(p, n), out, outlen, options, last, up_to_bad_char, count)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vtext_base64_to_binary_safe_utf16(
    p: *const u16,
    n: usize,
    out: *mut c_char,
    outlen: *mut usize,
    options: u64,
    last: u64,
    up_to_bad_char: bool,
    count: *mut usize,
) -> i32 {
    b64_decode_safe(&narrow(units(p, n)), out, outlen, options, last, up_to_bad_char, count)
}

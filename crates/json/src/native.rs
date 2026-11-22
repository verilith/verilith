//! The native C API (`include/vjson.h`), behind the `capi` feature.
//!
//! This is the Rust API of `value.rs` with C types: a reusable parser, and
//! values that are two-word views into its tape. Nothing is copied out and
//! nothing is allocated per value, which is what the cJSON-compatible ABI
//! (`ffi.rs`) cannot avoid.
//!
//! This layer is NOT verified. It is kept mechanical: every function checks
//! its pointers and the value's index, then calls the method of the same
//! name in `value.rs`. All syntax decisions are made by the verified parser.
#![allow(non_camel_case_types)]
#![allow(clippy::missing_safety_doc)]

use crate::error::ErrorKind;
use crate::value::{Elements, Members, Parser, Value, View};
use core::ffi::{c_char, c_int, c_void};
use std::borrow::Cow;
use std::sync::Mutex;

pub const VJSON_INVALID: c_int = 0;
pub const VJSON_NULL: c_int = 1;
pub const VJSON_BOOL: c_int = 2;
pub const VJSON_NUMBER: c_int = 3;
pub const VJSON_STRING: c_int = 4;
pub const VJSON_ARRAY: c_int = 5;
pub const VJSON_OBJECT: c_int = 6;

const EMPTY: View<'static> = View { src: &[], toks: &[], aux: &[], strs: &[] };

/// A parser and the document it last parsed. `view` is first, so that a
/// value's `doc` pointer reads it directly.
#[repr(C)]
pub struct vjson_parser {
    /// The last document's buffers: the caller's input and this parser's
    /// tape. Empty before the first parse and after a failed one.
    view: View<'static>,
    parser: Parser,
    /// Strings decoded on request. The parser decodes every escaped string
    /// while parsing, so this stays empty; it is here so that the accessors
    /// are correct even if a string was left undecoded.
    spill: Mutex<Vec<Box<[u8]>>>,
}

/// A value of the last document `doc` parsed.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct vjson_value {
    doc: *const c_void,
    idx: usize,
}

/// A position in an array or object.
#[repr(C)]
pub struct vjson_iter {
    doc: *const c_void,
    idx: usize,
}

#[repr(C)]
pub struct vjson_error {
    /// 0 for no error, otherwise one of the `VJSON_E_*` codes.
    pub code: c_int,
    /// The offending byte, for `VJSON_E_UNEXPECTED_BYTE` and
    /// `VJSON_E_CONTROL_CHARACTER`.
    pub byte: u8,
    pub offset: usize,
    /// 1-based.
    pub line: usize,
    /// 1-based, in bytes.
    pub column: usize,
}

fn code(k: ErrorKind) -> (c_int, u8) {
    match k {
        ErrorKind::UnexpectedEnd => (1, 0),
        ErrorKind::UnterminatedString => (2, 0),
        ErrorKind::UnexpectedByte(c) => (3, c),
        ErrorKind::ControlCharacter(c) => (4, c),
        ErrorKind::InvalidEscape => (5, 0),
        ErrorKind::InvalidNumber => (6, 0),
        ErrorKind::InvalidLiteral => (7, 0),
        ErrorKind::TooDeep => (8, 0),
        ErrorKind::TrailingData => (9, 0),
        ErrorKind::InvalidUtf8 => (10, 0),
        ErrorKind::TooLarge => (11, 0),
    }
}

/// A new parser. Free it with `vjson_parser_free`.
#[no_mangle]
pub extern "C" fn vjson_parser_new() -> *mut vjson_parser {
    Box::into_raw(Box::new(vjson_parser { view: EMPTY, parser: Parser::new(), spill: Mutex::new(Vec::new()) }))
}

/// # Safety
/// `p` is null or came from `vjson_parser_new` and was not freed.
#[no_mangle]
pub unsafe extern "C" fn vjson_parser_free(p: *mut vjson_parser) {
    if !p.is_null() {
        drop(Box::from_raw(p));
    }
}

/// Parses `len` bytes at `json` as one complete JSON text.
///
/// # Safety
/// `p` is a live parser no other thread is using, `json` points to `len`
/// readable bytes that stay unchanged while the document's values are in
/// use, and `root` and `err` are null or valid for writes.
#[no_mangle]
pub unsafe extern "C" fn vjson_parse(
    p: *mut vjson_parser,
    json: *const c_char,
    len: usize,
    root: *mut vjson_value,
    err: *mut vjson_error,
) -> c_int {
    if !err.is_null() {
        *err = vjson_error { code: 0, byte: 0, offset: 0, line: 0, column: 0 };
    }
    if !root.is_null() {
        *root = vjson_value { doc: core::ptr::null(), idx: 0 };
    }
    if p.is_null() || (json.is_null() && len != 0) {
        return -1;
    }
    // The previous document ends here: its tape is about to be reused.
    (*p).view = EMPTY;
    if let Ok(mut s) = (*p).spill.lock() {
        s.clear();
    }
    let input: &'static [u8] = if len == 0 { &[] } else { core::slice::from_raw_parts(json as *const u8, len) };
    // SAFETY: the document borrows the parser's tape. Its view is kept in
    // `*p` and dropped (set to `EMPTY`, above) before the parser is used
    // again or freed, so the borrow never outlives the buffers.
    let parser: &'static mut Parser = &mut *core::ptr::addr_of_mut!((*p).parser);
    match parser.parse(input) {
        Ok(doc) => {
            (*p).view = doc.view();
            if !root.is_null() {
                *root = vjson_value { doc: p as *const c_void, idx: 0 };
            }
            0
        }
        Err(e) => {
            let (code, byte) = code(e.kind);
            if !err.is_null() {
                *err = vjson_error { code, byte, offset: e.offset, line: e.line, column: e.column };
            }
            code
        }
    }
}

/// A short description of an error code.
#[no_mangle]
pub extern "C" fn vjson_error_message(code: c_int) -> *const c_char {
    let s: &'static [u8] = match code {
        0 => b"no error\0",
        1 => b"unexpected end of input\0",
        2 => b"unterminated string\0",
        3 => b"unexpected byte\0",
        4 => b"control character in string\0",
        5 => b"invalid escape in string\0",
        6 => b"invalid number\0",
        7 => b"invalid literal (expected true, false or null)\0",
        8 => b"nesting too deep\0",
        9 => b"data after the JSON value\0",
        10 => b"invalid UTF-8\0",
        11 => b"input of 4 GiB or more\0",
        _ => b"invalid argument\0",
    };
    s.as_ptr() as *const c_char
}

#[inline(always)]
fn type_of(x: &Value<'_>) -> c_int {
    match x.kind() {
        crate::Type::Null => VJSON_NULL,
        crate::Type::Bool => VJSON_BOOL,
        crate::Type::Number => VJSON_NUMBER,
        crate::Type::String => VJSON_STRING,
        crate::Type::Array => VJSON_ARRAY,
        crate::Type::Object => VJSON_OBJECT,
    }
}

/// The value `v` names, if it is one of its document's.
#[inline(always)]
unsafe fn view<'a>(doc: *const c_void) -> Option<&'a View<'a>> {
    if doc.is_null() {
        return None;
    }
    // SAFETY: `doc` is a `vjson_parser`, whose first field is the view.
    Some(&*(doc as *const View<'a>))
}

#[inline(always)]
unsafe fn val<'a>(v: vjson_value) -> Option<Value<'a>> {
    let view = view(v.doc)?;
    // `Value` reads its token unchecked.
    if v.idx >= view.toks.len() {
        return None;
    }
    Some(Value { v: view, idx: v.idx })
}

/// Writes out a string's bytes. Decoded strings live in the tape; one
/// that is not there is decoded into the parser's spill list.
#[inline(always)]
unsafe fn put_bytes(doc: *const c_void, b: Cow<'_, [u8]>, s: *mut *const c_char, len: *mut usize) {
    let (p, n) = match b {
        Cow::Borrowed(b) => (b.as_ptr(), b.len()),
        Cow::Owned(v) => spill(doc, v),
    };
    if !s.is_null() {
        *s = p as *const c_char;
    }
    if !len.is_null() {
        *len = n;
    }
}

#[cold]
unsafe fn spill(doc: *const c_void, v: Vec<u8>) -> (*const u8, usize) {
    let b = v.into_boxed_slice();
    let r = (b.as_ptr(), b.len());
    match (*(doc as *const vjson_parser)).spill.lock() {
        Ok(mut l) => l.push(b),
        // Unreachable (nothing panics while holding the lock); keep the
        // bytes alive regardless.
        Err(_) => core::mem::forget(b),
    }
    r
}

/// # Safety
/// For every function below: a `vjson_value` or `vjson_iter` came from this
/// API, its parser is live and has not parsed again since, and out
/// pointers are null or valid for writes.
#[no_mangle]
pub unsafe extern "C" fn vjson_type(v: vjson_value) -> c_int {
    match val(v) {
        None => VJSON_INVALID,
        Some(x) => type_of(&x),
    }
}

#[no_mangle]
pub unsafe extern "C" fn vjson_is_null(v: vjson_value) -> bool {
    val(v).is_some_and(|x| x.is_null())
}

#[no_mangle]
pub unsafe extern "C" fn vjson_get_bool(v: vjson_value, out: *mut bool) -> bool {
    match val(v).and_then(|x| x.as_bool()) {
        Some(b) => {
            if !out.is_null() {
                *out = b;
            }
            true
        }
        None => false,
    }
}

#[no_mangle]
pub unsafe extern "C" fn vjson_get_double(v: vjson_value, out: *mut f64) -> bool {
    match val(v).and_then(|x| x.as_f64()) {
        Some(d) => {
            if !out.is_null() {
                *out = d;
            }
            true
        }
        None => false,
    }
}

#[no_mangle]
pub unsafe extern "C" fn vjson_get_int64(v: vjson_value, out: *mut i64) -> bool {
    match val(v).and_then(|x| x.as_i64()) {
        Some(i) => {
            if !out.is_null() {
                *out = i;
            }
            true
        }
        None => false,
    }
}

/// A number's source text (not NUL-terminated).
#[no_mangle]
pub unsafe extern "C" fn vjson_get_number_text(v: vjson_value, s: *mut *const c_char, len: *mut usize) -> bool {
    match val(v).and_then(|x| x.as_number_str()) {
        Some(t) => {
            put_bytes(v.doc, Cow::Borrowed(t.as_bytes()), s, len);
            true
        }
        None => false,
    }
}

/// A string's decoded UTF-8 bytes (not NUL-terminated; it may contain NUL).
#[no_mangle]
pub unsafe extern "C" fn vjson_get_string(v: vjson_value, s: *mut *const c_char, len: *mut usize) -> bool {
    match val(v).and_then(|x| x.as_bytes()) {
        Some(b) => {
            put_bytes(v.doc, b, s, len);
            true
        }
        None => false,
    }
}

/// The number of elements of an array or members of an object. This walks
/// the container.
#[no_mangle]
pub unsafe extern "C" fn vjson_length(v: vjson_value, out: *mut usize) -> bool {
    match val(v).and_then(|x| x.len()) {
        Some(n) => {
            if !out.is_null() {
                *out = n;
            }
            true
        }
        None => false,
    }
}

/// Starts iterating over an array.
#[no_mangle]
pub unsafe extern "C" fn vjson_array_iter(v: vjson_value, it: *mut vjson_iter) -> bool {
    match val(v).and_then(|x| x.elements()) {
        Some(e) if !it.is_null() => {
            *it = vjson_iter { doc: v.doc, idx: e.idx };
            true
        }
        _ => false,
    }
}

/// The next element: its type, or 0 (`VJSON_INVALID`) at the end of the
/// array.
#[no_mangle]
pub unsafe extern "C" fn vjson_array_next(it: *mut vjson_iter, out: *mut vjson_value) -> c_int {
    if it.is_null() {
        return 0;
    }
    let Some(view) = view((*it).doc) else { return 0 };
    let mut e = Elements { v: view, idx: (*it).idx };
    match e.next() {
        Some(x) => {
            (*it).idx = e.idx;
            if !out.is_null() {
                *out = vjson_value { doc: (*it).doc, idx: x.idx };
            }
            type_of(&x)
        }
        None => 0,
    }
}

/// Starts iterating over an object.
#[no_mangle]
pub unsafe extern "C" fn vjson_object_iter(v: vjson_value, it: *mut vjson_iter) -> bool {
    match val(v).and_then(|x| x.members()) {
        Some(m) if !it.is_null() => {
            *it = vjson_iter { doc: v.doc, idx: m.idx };
            true
        }
        _ => false,
    }
}

/// The next member, in document order (duplicates included): its value's
/// type, or 0 at the end of the object. The key is decoded UTF-8, not
/// NUL-terminated.
#[no_mangle]
pub unsafe extern "C" fn vjson_object_next(
    it: *mut vjson_iter,
    key: *mut *const c_char,
    key_len: *mut usize,
    out: *mut vjson_value,
) -> c_int {
    if it.is_null() {
        return 0;
    }
    let Some(view) = view((*it).doc) else { return 0 };
    let mut m = Members { v: view, idx: (*it).idx };
    match m.next() {
        Some((k, x)) => {
            (*it).idx = m.idx;
            if !key.is_null() || !key_len.is_null() {
                put_bytes((*it).doc, k.as_bytes(), key, key_len);
            }
            if !out.is_null() {
                *out = vjson_value { doc: (*it).doc, idx: x.idx };
            }
            type_of(&x)
        }
        None => 0,
    }
}

/// The first member of an object named `key`.
#[no_mangle]
pub unsafe extern "C" fn vjson_object_get(
    v: vjson_value,
    key: *const c_char,
    key_len: usize,
    out: *mut vjson_value,
) -> bool {
    if key.is_null() && key_len != 0 {
        return false;
    }
    let key: &[u8] = if key_len == 0 { &[] } else { core::slice::from_raw_parts(key as *const u8, key_len) };
    let found = val(v).and_then(|x| x.members()).and_then(|mut m| m.find(|(k, _)| k.eq_bytes(key)));
    match found {
        Some((_, x)) => {
            if !out.is_null() {
                *out = vjson_value { doc: v.doc, idx: x.idx };
            }
            true
        }
        None => false,
    }
}

/// The `index`th element of an array. This walks the array.
#[no_mangle]
pub unsafe extern "C" fn vjson_array_at(v: vjson_value, index: usize, out: *mut vjson_value) -> bool {
    match val(v).and_then(|x| x.at(index)) {
        Some(x) => {
            if !out.is_null() {
                *out = vjson_value { doc: v.doc, idx: x.idx };
            }
            true
        }
        None => false,
    }
}

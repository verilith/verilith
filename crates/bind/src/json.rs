//! A C API over vjson documents: the verified parser's tape, handed out as
//! a flat token array, plus string, number and raw-text accessors.
//!
//! A `vbind_json_doc` is reused across parses, like simdjson's parser: the
//! tokens, decoded strings and raw spans it hands out stay valid until the
//! next parse into it or until it is freed. The input is borrowed, not
//! copied, and must outlive the parse's results.
#![allow(unsafe_op_in_unsafe_fn)]
use core::ptr;
use verilith_json::parser::{ex_decode, Kind};
use verilith_json::{ErrorKind, Parser};

/// One token, in document order. `kind` is a [`Kind`] as `u8`:
/// 0 null, 1 true, 2 false, 3 number, 4 string, 5 key, 6 `[`, 7 `]`,
/// 8 `{`, 9 `}`.
///
/// * number, string, key: `a..b` is the byte range of the number, or of
///   the string's body between its quotes; `escaped` says whether the body
///   has a backslash escape.
/// * `[` and `{`: `a` is the index of the matching `]` or `}` token.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Tok {
    pub kind: u8,
    pub escaped: u8,
    pub pad: u16,
    pub a: u32,
    pub b: u32,
}

/// Parse results, as returned by [`parse`]. Mirrors [`ErrorKind`].
pub const OK: i32 = 0;
pub const E_UNEXPECTED_END: i32 = 1;
pub const E_UNTERMINATED_STRING: i32 = 2;
pub const E_UNEXPECTED_BYTE: i32 = 3;
pub const E_CONTROL_CHARACTER: i32 = 4;
pub const E_INVALID_ESCAPE: i32 = 5;
pub const E_INVALID_NUMBER: i32 = 6;
pub const E_INVALID_LITERAL: i32 = 7;
pub const E_TOO_DEEP: i32 = 8;
pub const E_TRAILING_DATA: i32 = 9;
pub const E_INVALID_UTF8: i32 = 10;
pub const E_TOO_LARGE: i32 = 11;
pub const E_EMPTY: i32 = 12;

/// Accessor results.
pub const GET_OK: i32 = 0;
pub const GET_WRONG_TYPE: i32 = 1;
pub const GET_OUT_OF_RANGE: i32 = 2;

pub struct Doc {
    parser: Parser,
    src: *const u8,
    len: usize,
    toks: Vec<Tok>,
    /// Decoded escaped strings. Each is its own allocation, so pointers to
    /// earlier ones stay valid as more are added.
    strs: Vec<Box<[u8]>>,
    /// Start offset of every token, computed the first time raw text is
    /// asked for.
    pos: Vec<u32>,
}

impl Doc {
    fn src(&self) -> &[u8] {
        if self.src.is_null() {
            &[]
        } else {
            // SAFETY: the caller keeps the input alive while it uses the doc.
            unsafe { core::slice::from_raw_parts(self.src, self.len) }
        }
    }

    fn tok(&self, i: usize) -> Option<Tok> {
        self.toks.get(i).copied()
    }

    /// Start offsets of every token. The parser accepted the text, so it is
    /// enough to step over whitespace, commas, colons and a leading BOM.
    fn positions(&mut self) -> &[u32] {
        if self.pos.len() != self.toks.len() {
            let s = self.src();
            let mut pos = Vec::with_capacity(self.toks.len());
            let mut p = if s.starts_with(b"\xEF\xBB\xBF") { 3 } else { 0 };
            for t in &self.toks {
                while p < s.len() && matches!(s[p], b' ' | b'\t' | b'\n' | b'\r' | b',' | b':') {
                    p += 1;
                }
                pos.push(p as u32);
                p = match t.kind {
                    k if k == Kind::Num as u8 => t.b as usize,
                    k if k == Kind::Str as u8 || k == Kind::Key as u8 => t.b as usize + 1,
                    k if k == Kind::True as u8 || k == Kind::Null as u8 => p + 4,
                    k if k == Kind::False as u8 => p + 5,
                    _ => p + 1,
                };
            }
            self.pos = pos;
        }
        &self.pos
    }
}

fn error_code(k: ErrorKind) -> i32 {
    match k {
        ErrorKind::UnexpectedEnd => E_UNEXPECTED_END,
        ErrorKind::UnterminatedString => E_UNTERMINATED_STRING,
        ErrorKind::UnexpectedByte(_) => E_UNEXPECTED_BYTE,
        ErrorKind::ControlCharacter(_) => E_CONTROL_CHARACTER,
        ErrorKind::InvalidEscape => E_INVALID_ESCAPE,
        ErrorKind::InvalidNumber => E_INVALID_NUMBER,
        ErrorKind::InvalidLiteral => E_INVALID_LITERAL,
        ErrorKind::TooDeep => E_TOO_DEEP,
        ErrorKind::TrailingData => E_TRAILING_DATA,
        ErrorKind::InvalidUtf8 => E_INVALID_UTF8,
        ErrorKind::TooLarge => E_TOO_LARGE,
        _ => E_UNEXPECTED_BYTE,
    }
}

unsafe fn doc<'a>(d: *mut Doc) -> Option<&'a mut Doc> {
    d.as_mut()
}

unsafe fn out<T>(p: *mut T, v: T) {
    if !p.is_null() {
        *p = v;
    }
}

fn is_blank(s: &[u8]) -> bool {
    let s = s.strip_prefix(b"\xEF\xBB\xBF").unwrap_or(s);
    s.iter().all(|c| matches!(c, b' ' | b'\t' | b'\n' | b'\r'))
}

#[unsafe(no_mangle)]
pub extern "C" fn vbind_json_doc_new() -> *mut Doc {
    Box::into_raw(Box::new(Doc {
        parser: Parser::lazy(),
        src: ptr::null(),
        len: 0,
        toks: Vec::new(),
        strs: Vec::new(),
        pos: Vec::new(),
    }))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vbind_json_doc_free(d: *mut Doc) {
    if !d.is_null() {
        drop(Box::from_raw(d));
    }
}

/// Parses `input` with the verified parser into `d`, replacing what `d`
/// held. Returns `OK` or one of the `E_*` codes, with the error's byte
/// offset in `*err_offset`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vbind_json_doc_parse(d: *mut Doc, input: *const u8, length: usize, err_offset: *mut usize) -> i32 {
    let Some(d) = doc(d) else { return E_UNEXPECTED_END };
    d.toks.clear();
    d.strs.clear();
    d.pos.clear();
    d.src = input;
    d.len = if input.is_null() { 0 } else { length };
    let s: &[u8] = if input.is_null() { &[] } else { core::slice::from_raw_parts(input, length) };
    // This ABI's tokens (and the simdjson.h shim built on it) hold 32-bit
    // positions, like simdjson's own: past that the positions would not fit.
    if s.len() > u32::MAX as usize {
        out(err_offset, 0);
        d.src = ptr::null();
        d.len = 0;
        return E_TOO_LARGE;
    }
    match d.parser.parse(s) {
        Ok(document) => {
            d.toks.extend(document.tape().iter().map(|t| Tok {
                kind: t.kind as u8,
                escaped: t.escaped as u8,
                pad: 0,
                a: t.start() as u32,
                b: t.end() as u32,
            }));
            OK
        }
        Err(e) => {
            out(err_offset, e.offset);
            d.src = ptr::null();
            d.len = 0;
            if is_blank(s) {
                E_EMPTY
            } else {
                error_code(e.kind)
            }
        }
    }
}

/// The tokens of the last successful parse.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vbind_json_doc_tokens(d: *const Doc, n: *mut usize) -> *const Tok {
    match d.as_ref() {
        Some(d) => {
            out(n, d.toks.len());
            d.toks.as_ptr()
        }
        None => {
            out(n, 0);
            ptr::null()
        }
    }
}

/// The decoded bytes of string or key token `i`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vbind_json_doc_string(d: *mut Doc, i: usize, p: *mut *const u8, n: *mut usize) -> i32 {
    let Some(d) = doc(d) else { return GET_WRONG_TYPE };
    let Some(t) = d.tok(i) else { return GET_WRONG_TYPE };
    if t.kind != Kind::Str as u8 && t.kind != Kind::Key as u8 {
        return GET_WRONG_TYPE;
    }
    let (a, b) = (t.a as usize, t.b as usize);
    if t.escaped == 0 {
        out(p, d.src.add(a));
        out(n, b - a);
    } else {
        let mut v = Vec::with_capacity(b - a);
        ex_decode(d.src(), a, b, &mut v);
        let s = v.into_boxed_slice();
        out(p, s.as_ptr());
        out(n, s.len());
        d.strs.push(s);
    }
    GET_OK
}

/// The source text of value `i`: a whole array or object, a string with
/// its quotes, a number or a literal, followed (as in simdjson) by any
/// whitespace up to the next token.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vbind_json_doc_raw(d: *mut Doc, i: usize, p: *mut *const u8, n: *mut usize) -> i32 {
    let Some(d) = doc(d) else { return GET_WRONG_TYPE };
    let Some(t) = d.tok(i) else { return GET_WRONG_TYPE };
    let pos = d.positions();
    let start = pos[i] as usize;
    let end = match t.kind {
        k if k == Kind::ArrStart as u8 || k == Kind::ObjStart as u8 => pos[t.a as usize] as usize + 1,
        k if k == Kind::Num as u8 => t.b as usize,
        k if k == Kind::Str as u8 || k == Kind::Key as u8 => t.b as usize + 1,
        k if k == Kind::True as u8 || k == Kind::Null as u8 => start + 4,
        k if k == Kind::False as u8 => start + 5,
        _ => start + 1,
    };
    let s = d.src();
    let mut end = end;
    while end < s.len() && matches!(s[end], b' ' | b'\t' | b'\n' | b'\r') {
        end += 1;
    }
    out(p, d.src.add(start));
    out(n, end - start);
    GET_OK
}

fn number<'a>(d: &'a Doc, i: usize) -> Option<&'a [u8]> {
    let t = d.tok(i)?;
    (t.kind == Kind::Num as u8).then(|| &d.src()[t.a as usize..t.b as usize])
}

fn is_integer(lex: &[u8]) -> bool {
    !lex.iter().any(|c| matches!(c, b'.' | b'e' | b'E'))
}

/// Number token `i` as the nearest `f64`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vbind_json_doc_f64(d: *mut Doc, i: usize, v: *mut f64) -> i32 {
    let Some(d) = doc(d) else { return GET_WRONG_TYPE };
    match number(d, i) {
        Some(lex) => {
            out(v, verilith_json::number::parse_f64(lex));
            GET_OK
        }
        None => GET_WRONG_TYPE,
    }
}

/// Number token `i` as an `i64`, if it is an integer that fits.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vbind_json_doc_i64(d: *mut Doc, i: usize, v: *mut i64) -> i32 {
    let Some(d) = doc(d) else { return GET_WRONG_TYPE };
    match number(d, i) {
        Some(lex) if !is_integer(lex) => GET_WRONG_TYPE,
        Some(lex) => match verilith_json::number::parse_i64(lex) {
            Some(x) => {
                out(v, x);
                GET_OK
            }
            None => GET_OUT_OF_RANGE,
        },
        None => GET_WRONG_TYPE,
    }
}

/// Number token `i` as a `u64`, if it is a non-negative integer that fits.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vbind_json_doc_u64(d: *mut Doc, i: usize, v: *mut u64) -> i32 {
    let Some(d) = doc(d) else { return GET_WRONG_TYPE };
    match number(d, i) {
        Some(lex) if !is_integer(lex) => GET_WRONG_TYPE,
        Some(lex) if lex.first() == Some(&b'-') => GET_OUT_OF_RANGE,
        Some(lex) => {
            let mut x: u64 = 0;
            for &c in lex {
                match x.checked_mul(10).and_then(|x| x.checked_add((c - b'0') as u64)) {
                    Some(y) => x = y,
                    None => return GET_OUT_OF_RANGE,
                }
            }
            out(v, x);
            GET_OK
        }
        None => GET_WRONG_TYPE,
    }
}

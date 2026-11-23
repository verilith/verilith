//! The Rust API: a parsed document and borrowed views of its values.
//!
//! Parsing is done by the verified parser (`crate::parser`). This module is
//! safe Rust over its tape, which is a flat list of tokens. Strings borrow
//! from the input unless they contain escapes, and numbers keep their
//! source text until a conversion is asked for.
//!
//! ```
//! let doc = verilith_json::parse(br#"{"name": "vjson", "tags": ["fast", "verified"], "n": 2}"#).unwrap();
//! let root = doc.root();
//! assert_eq!(root.get("name").unwrap().as_str().as_deref(), Some("vjson"));
//! assert_eq!(root.get("n").unwrap().as_i64(), Some(2));
//! let tags: Vec<_> = root.get("tags").unwrap().elements().unwrap()
//!     .map(|v| v.as_str().unwrap().into_owned())
//!     .collect();
//! assert_eq!(tags, ["fast", "verified"]);
//! ```
use crate::parser::{ex_decode, parse_document, parse_into, EagerTape, Kind, Tape, Tok, NO};
use crate::stage2::{parse2_eager_into, parse2_into};
use std::borrow::Cow;
use std::fmt;

pub use crate::error::{Error, ErrorKind};

/// Parses a complete JSON text (RFC 8259). Only whitespace may follow the
/// value. A leading UTF-8 byte order mark is skipped.
pub fn parse(input: &[u8]) -> Result<Document<'_>, Error> {
    parse_mode(input, true)
}

/// `parse`, storing values while parsing (`eager`) or leaving them to be
/// converted when read.
pub(crate) fn parse_mode(input: &[u8], eager: bool) -> Result<Document<'_>, Error> {
    let mut tape = Tape::with_capacity(input.len() / 8 + 4);
    let mut idx = Vec::new();
    match parse_tape(input, &mut tape, &mut idx, eager) {
        Ok(_) => Ok(Document::new(input, Cow::Owned(tape))),
        Err(_) => Err(error_at(input, &mut tape)),
    }
}

/// The verified two-pass parser, in the lazy or the eager mode.
#[inline]
fn parse_tape(input: &[u8], tape: &mut Tape, idx: &mut Vec<u32>, eager: bool) -> Result<usize, usize> {
    if !eager {
        return parse2_into(input, tape, idx);
    }
    // Moving a tape moves only its buffers' headers.
    let mut e = EagerTape { tape: std::mem::replace(tape, Tape::with_capacity(0)) };
    let r = parse2_eager_into(input, &mut e, idx);
    *tape = e.tape;
    r
}

/// A reusable parser. It keeps its token buffer between documents, so
/// parsing many documents does not allocate (or fault in fresh pages) each
/// time.
///
/// ```
/// let mut p = verilith_json::Parser::new();
/// for text in [&b"[1, 2]"[..], b"{\"a\": true}"] {
///     let doc = p.parse(text).unwrap();
///     assert!(doc.root().len().unwrap() > 0);
/// }
/// ```
pub struct Parser {
    tape: Option<Tape>,
    idx: Vec<u32>,
    eager: bool,
}

impl Default for Parser {
    fn default() -> Parser {
        Parser::new()
    }
}

impl Parser {
    pub fn new() -> Parser {
        Parser { tape: None, idx: Vec::new(), eager: true }
    }

    /// A parser that decodes strings with escapes only when they are read,
    /// rather than while parsing. Faster when most strings are not read.
    pub fn lazy() -> Parser {
        Parser { tape: None, idx: Vec::new(), eager: false }
    }

    /// Switches between lazy and eager string decoding (see [`lazy`]),
    /// keeping this parser's buffers.
    pub fn set_lazy(&mut self, lazy: bool) {
        self.eager = !lazy;
    }

    /// Like [`parse`], reusing this parser's buffer. The document borrows
    /// the parser until it is dropped.
    pub fn parse<'p>(&'p mut self, input: &'p [u8]) -> Result<Document<'p>, Error> {
        let tape = self.tape.get_or_insert_with(|| Tape::with_capacity(input.len() / 8 + 4));
        match parse_tape(input, tape, &mut self.idx, self.eager) {
            Ok(_) => Ok(Document::new(input, Cow::Borrowed(tape))),
            Err(_) => Err(error_at(input, tape)),
        }
    }
}

/// The two-pass parser does not track where it failed, so rerun the
/// one-pass parser for a precise error offset. This costs time only on
/// invalid input.
#[cold]
fn error_at(input: &[u8], tape: &mut Tape) -> Error {
    let p = parse_into(input, true, tape).err().unwrap_or(0);
    crate::error::diagnose(input, true, p)
}

/// Parses one JSON value at the start of `input` (after whitespace and an
/// optional BOM) and returns it with the offset just past it. Any bytes may
/// follow.
pub fn parse_prefix(input: &[u8]) -> Result<(Document<'_>, usize), Error> {
    match parse_document(input, false) {
        Ok((tape, end)) => Ok((Document::new(input, Cow::Owned(tape)), end)),
        Err(p) => Err(crate::error::diagnose(input, false, p)),
    }
}

/// A parsed JSON document. It borrows the input (and, from
/// [`Parser::parse`], the parser).
pub struct Document<'a> {
    tape: Cow<'a, Tape>,
    view: View<'a>,
}

/// What values read: the input and the tape's buffers, as plain slices, so
/// that a `Value` is two words and reaches them without going through the
/// `Cow`. For an owned tape the slices point into its heap buffers, which
/// stay put when the document moves and are never changed or freed while
/// it lives; `Document` hands out a view only for as long as it is
/// borrowed.
#[derive(Clone, Copy)]
pub(crate) struct View<'a> {
    pub(crate) src: &'a [u8],
    pub(crate) toks: &'a [Tok],
    pub(crate) aux: &'a [u64],
    pub(crate) strs: &'a [u8],
}

impl<'a> Document<'a> {
    fn new(src: &'a [u8], tape: Cow<'a, Tape>) -> Document<'a> {
        let t: &Tape = &tape;
        // SAFETY: see `View`. The buffers outlive every borrow of the view.
        let view = unsafe {
            View {
                src,
                toks: std::slice::from_raw_parts(t.toks.as_ptr(), t.toks.len()),
                aux: std::slice::from_raw_parts(t.aux.as_ptr(), t.aux.len()),
                strs: std::slice::from_raw_parts(t.strs.as_ptr(), t.strs.len()),
            }
        };
        Document { tape, view }
    }
}

impl<'a> Clone for Document<'a> {
    fn clone(&self) -> Document<'a> {
        let tape = match &self.tape {
            Cow::Borrowed(t) => Cow::Borrowed(*t),
            Cow::Owned(t) => Cow::Owned(t.clone()),
        };
        Document::new(self.view.src, tape)
    }
}

impl Clone for Tape {
    fn clone(&self) -> Tape {
        Tape {
            toks: self.toks.clone(),
            aux: self.aux.clone(),
            strs: self.strs.clone(),
            err_pos: self.err_pos,
        }
    }
}

impl<'a> Document<'a> {
    /// The top-level value.
    #[inline]
    pub fn root(&self) -> Value<'_> {
        Value { v: &self.view, idx: 0 }
    }

    /// The input this document was parsed from.
    pub fn source(&self) -> &'a [u8] {
        self.view.src
    }

    /// The verified parser's tape.
    pub fn tape(&self) -> &[Tok] {
        &self.tape.toks
    }

    /// The slices values read through (for the C API, which keeps a copy
    /// next to the parser that owns the buffers).
    #[cfg(feature = "capi")]
    pub(crate) fn view(&self) -> View<'a> {
        self.view
    }
}

impl fmt::Debug for Document<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.root().fmt(f)
    }
}

/// The type of a JSON value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    Null,
    Bool,
    Number,
    String,
    Array,
    Object,
}

/// A borrowed view of one value in a `Document`.
#[derive(Clone, Copy)]
pub struct Value<'d> {
    pub(crate) v: &'d View<'d>,
    pub(crate) idx: usize,
}

impl<'d> Value<'d> {
    #[inline]
    fn tok(&self) -> &'d Tok {
        debug_assert!(self.idx < self.v.toks.len());
        // SAFETY: `idx` is in bounds. Every tape a `Document` holds is
        // accepted by `document`, so it is not empty and does not end with a
        // key (`lemmas::ends_value`, in the parsers' `ensures`). A `Value` is
        // the root (index 0), an element at an index `Elements` checked, or
        // the token after a key at an index `Members` checked, and a key is
        // never the last token.
        unsafe { self.v.toks.get_unchecked(self.idx) }
    }

    /// Index of the token after this value (and all of its children). A
    /// container's start token links to its end token: this is in the spec
    /// (`STok::ArrStart { end }`), and every parser's `ensures` states
    /// `lemmas::links_from(t, 0)`, so `t.a` is a later end token of the
    /// tape.
    #[inline]
    fn next_idx(&self) -> usize {
        let t = self.tok();
        match t.kind {
            Kind::ArrStart | Kind::ObjStart => t.start() + 1,
            _ => self.idx + 1,
        }
    }

    #[inline]
    pub fn kind(&self) -> Type {
        match self.tok().kind {
            Kind::Null => Type::Null,
            Kind::True | Kind::False => Type::Bool,
            Kind::Num => Type::Number,
            Kind::Str | Kind::Key => Type::String,
            Kind::ArrStart | Kind::ArrEnd => Type::Array,
            Kind::ObjStart | Kind::ObjEnd => Type::Object,
        }
    }

    #[inline]
    pub fn is_null(&self) -> bool {
        self.tok().kind == Kind::Null
    }

    #[inline]
    pub fn as_bool(&self) -> Option<bool> {
        match self.tok().kind {
            Kind::True => Some(true),
            Kind::False => Some(false),
            _ => None,
        }
    }

    /// A number's source text, e.g. `"-1.5e3"`.
    #[inline]
    pub fn as_number_str(&self) -> Option<&'d str> {
        let t = self.tok();
        if t.kind != Kind::Num {
            return None;
        }
        // Number lexemes are ASCII.
        std::str::from_utf8(lexeme(self.v, t)).ok()
    }

    /// A number as the nearest `f64`.
    #[inline]
    pub fn as_f64(&self) -> Option<f64> {
        let t = self.tok();
        if t.kind != Kind::Num {
            return None;
        }
        // The value the parser accumulated, if it is exact.
        if t.x != NO {
            if let Some(&w) = self.v.aux.get(self.idx) {
                let neg = t.x >> 15 != 0;
                if let Some(v) = crate::number::from_parts(neg, w, (t.x & 0x7FFF) as i64 - 0x4000) {
                    return Some(v);
                }
            }
        }
        Some(crate::number::parse_f64_at(self.v.src, t.start(), t.end()))
    }

    /// A number with no fraction or exponent that fits in `i64`.
    #[inline]
    pub fn as_i64(&self) -> Option<i64> {
        self.as_number_str().and_then(|s| crate::number::parse_i64(s.as_bytes()))
    }

    /// A string's decoded bytes. Borrowed unless the string has escapes.
    #[inline]
    pub fn as_bytes(&self) -> Option<Cow<'d, [u8]>> {
        let t = self.tok();
        if t.kind != Kind::Str {
            return None;
        }
        Some(string_bytes(self.v, self.idx, t))
    }

    /// A string as UTF-8 text. `None` if this is not a string. (The parser
    /// checks that the text is UTF-8, and decoding escapes keeps it so.)
    pub fn as_str(&self) -> Option<Cow<'d, str>> {
        cow_str(self.as_bytes()?)
    }

    /// The elements of an array.
    #[inline]
    pub fn elements(&self) -> Option<Elements<'d>> {
        if self.tok().kind != Kind::ArrStart {
            return None;
        }
        Some(Elements { v: self.v, idx: self.idx + 1 })
    }

    /// The members of an object, in document order (duplicates included).
    #[inline]
    pub fn members(&self) -> Option<Members<'d>> {
        if self.tok().kind != Kind::ObjStart {
            return None;
        }
        Some(Members { v: self.v, idx: self.idx + 1 })
    }

    /// The `index`th element of an array.
    pub fn at(&self, index: usize) -> Option<Value<'d>> {
        self.elements()?.nth(index)
    }

    /// The first member of an object whose name equals `key`.
    pub fn get(&self, key: &str) -> Option<Value<'d>> {
        self.members()?.find(|(k, _)| k.eq_bytes(key.as_bytes())).map(|(_, v)| v)
    }

    /// Number of elements or members of an array or object.
    pub fn len(&self) -> Option<usize> {
        match self.tok().kind {
            Kind::ArrStart => Some(self.elements()?.count()),
            Kind::ObjStart => Some(self.members()?.count()),
            _ => None,
        }
    }
}

impl fmt::Debug for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            Type::Null => f.write_str("null"),
            Type::Bool => write!(f, "{}", self.as_bool().unwrap()),
            Type::Number => f.write_str(self.as_number_str().unwrap()),
            Type::String => write!(f, "{:?}", String::from_utf8_lossy(&self.as_bytes().unwrap())),
            Type::Array => f.debug_list().entries(self.elements().unwrap()).finish(),
            Type::Object => f
                .debug_map()
                .entries(self.members().unwrap().map(|(k, v)| (k, v)))
                .finish(),
        }
    }
}

/// An object member's name.
#[derive(Clone, Copy)]
pub struct Key<'d> {
    v: &'d View<'d>,
    idx: usize,
    tok: &'d Tok,
}

impl<'d> Key<'d> {
    #[inline]
    pub fn as_bytes(&self) -> Cow<'d, [u8]> {
        string_bytes(self.v, self.idx, self.tok)
    }

    pub fn as_str(&self) -> Option<Cow<'d, str>> {
        cow_str(self.as_bytes())
    }

    /// Compares the decoded name with `other` without allocating when the
    /// name has no escapes.
    #[inline]
    pub fn eq_bytes(&self, other: &[u8]) -> bool {
        if self.tok.escaped {
            *self.as_bytes() == *other
        } else {
            lexeme(self.v, self.tok) == other
        }
    }
}

impl fmt::Debug for Key<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", String::from_utf8_lossy(&self.as_bytes()))
    }
}

/// Iterator over array elements.
#[derive(Clone)]
pub struct Elements<'d> {
    pub(crate) v: &'d View<'d>,
    pub(crate) idx: usize,
}

impl<'d> Iterator for Elements<'d> {
    type Item = Value<'d>;

    #[inline]
    fn next(&mut self) -> Option<Value<'d>> {
        if self.v.toks.get(self.idx)?.kind == Kind::ArrEnd {
            return None;
        }
        let v = Value { v: self.v, idx: self.idx };
        self.idx = v.next_idx();
        Some(v)
    }
}

/// Iterator over object members.
#[derive(Clone)]
pub struct Members<'d> {
    pub(crate) v: &'d View<'d>,
    pub(crate) idx: usize,
}

impl<'d> Iterator for Members<'d> {
    type Item = (Key<'d>, Value<'d>);

    #[inline]
    fn next(&mut self) -> Option<(Key<'d>, Value<'d>)> {
        let k = self.v.toks.get(self.idx)?;
        if k.kind != Kind::Key {
            return None;
        }
        let key = Key { v: self.v, idx: self.idx, tok: k };
        let v = Value { v: self.v, idx: self.idx + 1 };
        self.idx = v.next_idx();
        Some((key, v))
    }
}

/// The input bytes of a number token or of a string token's raw body.
#[inline(always)]
fn lexeme<'d>(v: &View<'d>, t: &Tok) -> &'d [u8] {
    debug_assert!(t.start() <= t.end() && t.end() <= v.src.len());
    // SAFETY: every tape a `Document` holds was returned by a parser that
    // is verified to return only tapes accepted by `document`, and every
    // such tape lies within the input (`lemmas::in_bounds`, proved in
    // `lemmas::lemma_document_in_bounds` and stated in the parsers'
    // `ensures`): `t.a <= t.b <= src.len()` for every number, string and
    // key token. `t` is one of the tape's tokens and `v.src` that input.
    unsafe { v.src.get_unchecked(t.start()..t.end()) }
}

#[inline(always)]
fn string_bytes<'d>(v: &View<'d>, idx: usize, t: &Tok) -> Cow<'d, [u8]> {
    if t.escaped {
        escaped_bytes(v, idx, t)
    } else {
        Cow::Borrowed(lexeme(v, t))
    }
}

#[inline(never)]
fn escaped_bytes<'d>(v: &View<'d>, idx: usize, t: &Tok) -> Cow<'d, [u8]> {
    let src = v.src;
    // Decoded while parsing.
    if t.x != NO {
        if let Some(&r) = v.aux.get(idx) {
            if let Some(d) = v.strs.get(r as u32 as usize..(r >> 32) as usize) {
                return Cow::Borrowed(d);
            }
        }
    }
    let (a, b) = (t.start(), t.end());
    let mut out = Vec::with_capacity(b - a);
    ex_decode(src, a, b, &mut out);
    Cow::Owned(out)
}

fn cow_str(b: Cow<'_, [u8]>) -> Option<Cow<'_, str>> {
    match b {
        Cow::Borrowed(b) => std::str::from_utf8(b).ok().map(Cow::Borrowed),
        Cow::Owned(v) => String::from_utf8(v).ok().map(Cow::Owned),
    }
}

//! The Rust API: `parse`, and borrowed views of the verified tape.
//!
//! This file is ordinary Rust. It decides nothing about the input: the
//! verified parser (`enc::ex_parse`) has accepted the document and written
//! its tape, the verified decoders (`decode`) give character data and
//! attribute values their meaning, and the verified `content::ex_ent_content`
//! parses an entity's replacement text when a reference to it is read.
//! What is here is navigation over tokens, the tables built from the DTD's
//! tokens (attribute defaults and declared types), and error positions.
use crate::decode::{ex_att_norm, ex_eol};
use crate::dtd::DtdOut;
use crate::lex::{ex_find_ent, XEnv};
use crate::tape::{Kind, Tape, Tok};
use std::borrow::Cow;
use std::cell::OnceCell;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[cfg(feature = "expat-abi")]
mod expat;
#[cfg(feature = "libxml2-abi")]
// libxml2's tables of codes and struct fields are kept whole, used or not.
#[allow(dead_code)]
mod libxml2;

/// Why a document was rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// The input is not text in an encoding read here (UTF-8, UTF-16 with
    /// its byte order mark, ISO-8859-1 or US-ASCII, as declared), or holds
    /// a character XML does not allow.
    Encoding,
    /// The text is not a well-formed XML document.
    Syntax,
    /// The text is longer than token positions hold (`tape::MAX_POS`):
    /// over 2^48 - 1 bytes (256 TiB) as UTF-8 on a 64-bit target, more
    /// than any address space gives a process today. (A 32-bit target's
    /// limit, 2^32 - 1, is past the largest slice it can have.)
    TooLarge,
}

/// A rejected document: why, and where. `offset` is a byte offset into
/// the text as UTF-8 (the input itself, unless it was in another
/// encoding); `line` and `column` count from 1, the column in bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Error {
    pub kind: ErrorKind,
    pub offset: usize,
    pub line: usize,
    pub column: usize,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let what = match self.kind {
            ErrorKind::Encoding => "not text in a known encoding, or a character XML does not allow",
            ErrorKind::Syntax => "not well-formed",
            ErrorKind::TooLarge => "longer than token positions hold",
        };
        write!(f, "{what} at line {} column {} (byte {})", self.line, self.column, self.offset)
    }
}

impl std::error::Error for Error {}

fn error_at(kind: ErrorKind, text: &[u8], offset: usize) -> Error {
    let offset = offset.min(text.len());
    let before = &text[..offset];
    let line = 1 + before.iter().filter(|&&c| c == b'\n').count();
    let column = 1 + before.iter().rev().take_while(|&&c| c != b'\n').count();
    Error { kind, offset, line, column }
}

/// Where the first character that is not allowed is (diagnostic only).
fn bad_char_at(s: &[u8]) -> usize {
    let mut i = 0;
    while i < s.len() {
        let b = s[i];
        if b < 0x80 {
            if b < 0x20 && b != 0x09 && b != 0x0A && b != 0x0D {
                return i;
            }
            i += 1;
        } else {
            match crate::chars::ex_cp_at_hi(s, i) {
                Some((c, l)) if crate::lex::ex_is_char(c) => i += l,
                _ => return i,
            }
        }
    }
    i
}

/// An attribute definition from the internal subset that applies.
#[derive(Clone, Copy, Debug)]
struct AttDef {
    name: (usize, usize),
    ty: u8,
    kind: u8,
    value: (usize, usize),
}

/// The declarations a document's content refers to: its own, or those of
/// a stream's prolog (`Document::chunk`).
enum Dtd<'a> {
    Own(DtdOut),
    Prolog(&'a DtdOut),
}

impl std::ops::Deref for Dtd<'_> {
    type Target = DtdOut;

    fn deref(&self) -> &DtdOut {
        match self {
            Dtd::Own(d) => d,
            Dtd::Prolog(d) => d,
        }
    }
}

/// A parsed document.
pub struct Document<'a> {
    input: &'a [u8],
    owned: Option<Vec<u8>>,
    tape: Tape,
    dtd: Dtd<'a>,
    /// The text the declarations' positions are in, where it is not the
    /// document's own: a stream's prolog.
    pro: Option<&'a [u8]>,
    /// The XML declaration says `standalone="yes"`.
    standalone: bool,
    ent_tapes: Vec<OnceCell<Option<Tape>>>,
    defs: Vec<AttDef>,
    /// `defs` by (element type, attribute name), and by element type.
    def_index: HashMap<Box<[u8]>, HashMap<Box<[u8]>, usize>>,
    defs_of: HashMap<Box<[u8]>, Vec<usize>>,
    root: usize,
}

impl fmt::Debug for Document<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Document({} bytes, {} tokens)", self.text().len(), self.tape.toks.len())
    }
}

/// Parses `input`, a document in UTF-8 (or UTF-16 with its byte order
/// mark, or ISO-8859-1 or US-ASCII as its declaration says).
pub fn parse(input: &[u8]) -> Result<Document<'_>, Error> {
    let mut tape = Tape::new();
    match crate::enc::ex_parse(input, &mut tape) {
        Some((owned, dtd)) => Ok(Document::new(input, owned, tape, dtd)),
        None => Err(diagnose(input, &tape)),
    }
}

fn diagnose(input: &[u8], tape: &Tape) -> Error {
    let enc = crate::enc::ex_input_enc(input);
    let decoded = match crate::enc::ex_decode_input(input, enc) {
        None => return error_at(ErrorKind::Encoding, input, 0),
        Some(d) => d,
    };
    let text: &[u8] = decoded.as_deref().unwrap_or(input);
    if text.len() as u64 > crate::tape::MAX_POS {
        return error_at(ErrorKind::TooLarge, text, 0);
    }
    if !crate::chars::ex_doc_chars(text) {
        return error_at(ErrorKind::Encoding, text, bad_char_at(text));
    }
    // The tape of the failed run is the decoded text's when the input was
    // already UTF-8; otherwise run it again on the decoded text.
    let err = if decoded.is_none() {
        tape.err
    } else {
        let mut t = Tape::new();
        let _ = crate::doc::ex_document(text, &mut t, enc);
        t.err
    };
    error_at(ErrorKind::Syntax, text, err)
}

fn utf8(b: &[u8]) -> &str {
    // The text was checked to be UTF-8 and every span ends where an ASCII
    // delimiter or the end of a name is, which is a character boundary.
    std::str::from_utf8(b).unwrap_or("")
}

fn cow_utf8(c: Cow<'_, [u8]>) -> Cow<'_, str> {
    match c {
        Cow::Borrowed(b) => Cow::Borrowed(utf8(b)),
        Cow::Owned(v) => Cow::Owned(String::from_utf8(v).unwrap_or_default()),
    }
}

/// A buffer of the document: the text itself, or the replacement text
/// of the internal entity at an index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Src {
    Doc,
    Ent(usize),
    /// The text of the declarations (the document's own, but for a
    /// stream: its prolog).
    Pro,
}

impl Src {
    /// In the document's text (or its prolog's), not in an entity's
    /// replacement text: line ends are not yet normalized.
    fn raw(self) -> bool {
        !matches!(self, Src::Ent(_))
    }
}

impl<'a> Document<'a> {
    fn new(input: &'a [u8], owned: Option<Vec<u8>>, tape: Tape, dtd: DtdOut) -> Self {
        let n = dtd.ents.len();
        let standalone = tape.toks.first().map_or(false, |t| t.kind == Kind::XmlDecl && t.f == 1);
        let mut d = Document {
            input,
            owned,
            tape,
            dtd: Dtd::Own(dtd),
            pro: None,
            standalone,
            ent_tapes: (0..n).map(|_| OnceCell::new()).collect(),
            defs: Vec::new(),
            def_index: HashMap::new(),
            defs_of: HashMap::new(),
            root: 0,
        };
        d.root = d.tape.toks.iter().position(|t| t.kind == Kind::STag).unwrap_or(0) as usize;
        let toks = std::mem::take(&mut d.tape.toks);
        d.att_defs(&toks, None);
        d.tape.toks = toks;
        d
    }

    /// A stream's document, read a chunk at a time (`set_chunk`): its
    /// content refers to the declarations `dtd`, at positions in `pro`,
    /// whose tokens are `ptoks` (the prolog's).
    pub(crate) fn chunk(dtd: &'a DtdOut, pro: &'a [u8], ptoks: &[Tok], standalone: bool) -> Self {
        let n = dtd.ents.len();
        let mut d = Document {
            input: &[],
            owned: None,
            tape: Tape::new(),
            dtd: Dtd::Prolog(dtd),
            pro: Some(pro),
            standalone,
            ent_tapes: (0..n).map(|_| OnceCell::new()).collect(),
            defs: Vec::new(),
            def_index: HashMap::new(),
            defs_of: HashMap::new(),
            root: 0,
        };
        d.att_defs(ptoks, Some(pro));
        d
    }

    /// The next chunk of a stream's document: the window's text, and the
    /// tokens read in it. The tokens of the last chunk come back.
    pub(crate) fn set_chunk(&mut self, text: &'a [u8], tape: Tape) -> Tape {
        self.input = text;
        std::mem::replace(&mut self.tape, tape)
    }

    /// The XML declaration says `standalone="yes"`.
    pub(crate) fn standalone(&self) -> bool {
        self.standalone
    }

    /// The text the declarations' positions are in.
    fn dtd_text(&self) -> &[u8] {
        match self.pro {
            Some(p) => p,
            None => self.text(),
        }
    }

    /// The text of the document in UTF-8.
    pub fn text(&self) -> &[u8] {
        self.owned.as_deref().unwrap_or(self.input)
    }

    /// The verified tape: one token per item of the document.
    pub fn tokens(&self) -> &[Tok] {
        &self.tape.toks
    }

    /// Whether declarations this processor did not read may bear on the
    /// document: it has an external subset, or a parameter entity
    /// reference in its internal subset, and is not standalone. Then a
    /// reference to an entity that was not declared is not an error
    /// (§4.1, WFC: Entity Declared): content shows it as
    /// `Child::Unexpanded`, and an attribute value keeps it as written.
    pub fn has_unread_declarations(&self) -> bool {
        !self.dtd.wfc
    }

    /// The root element.
    pub fn root(&self) -> Element<'_> {
        Element { doc: self, src: Src::Doc, idx: self.root }
    }

    /// The name in the document type declaration, if there is one.
    pub fn doctype_name(&self) -> Option<&str> {
        let t = self.tape.toks.iter().find(|t| t.kind == Kind::Doctype)?;
        Some(utf8(&self.text()[t.a()..t.b()]))
    }

    /// The processing instructions outside the root element, before it
    /// (those in the internal subset among them, in order) and after it,
    /// as (target, data).
    pub fn outer_pis(&self) -> (Vec<(&str, Cow<'_, str>)>, Vec<(&str, Cow<'_, str>)>) {
        let toks = &self.tape.toks;
        let close = toks[self.root as usize].c();
        let mut before = Vec::new();
        let mut after = Vec::new();
        for (i, t) in toks.iter().enumerate() {
            if t.kind == Kind::PI && (i < self.root as usize || i > close) {
                let d = toks[i + 1];
                let p = (utf8(self.span(Src::Doc, t.a(), t.b())), self.text_of(Src::Doc, d));
                if i < self.root as usize {
                    before.push(p)
                } else {
                    after.push(p)
                }
            }
        }
        (before, after)
    }

    /// The text of a token's span, line ends normalized where it is in
    /// the document itself (an entity's replacement text already is).
    fn text_of(&self, src: Src, t: Tok) -> Cow<'_, str> {
        let raw = self.span(src, t.a(), t.b());
        if src.raw() && raw.contains(&b'\r') {
            let mut out = Vec::with_capacity(raw.len());
            ex_eol(self.buf(src), t.a(), t.b(), &mut out);
            cow_utf8(Cow::Owned(out))
        } else {
            Cow::Borrowed(utf8(raw))
        }
    }

    /// The notations declared in the internal subset: name, public id,
    /// system id.
    pub fn notations(&self) -> Vec<(&str, Option<&str>, Option<&str>)> {
        let toks = &self.tape.toks;
        let mut out = Vec::new();
        for (i, t) in toks.iter().enumerate() {
            if t.kind != Kind::NotationDecl {
                continue;
            }
            let mut p = None;
            let mut s = None;
            for u in &toks[i + 1..] {
                match u.kind {
                    Kind::PubId => p = Some(utf8(self.span(Src::Doc, u.a(), u.b()))),
                    Kind::SysId => s = Some(utf8(self.span(Src::Doc, u.a(), u.b()))),
                    _ => break,
                }
            }
            out.push((utf8(self.span(Src::Doc, t.a(), t.b())), p, s));
        }
        out
    }

    fn env(&self) -> XEnv<'_> {
        XEnv {
            doc: self.dtd_text(),
            ents: &self.dtd.ents,
            wfc: self.dtd.wfc,
            oka: &self.dtd.oka,
            okc: &self.dtd.okc,
            idx: &self.dtd.idx,
        }
    }

    fn buf(&self, src: Src) -> &[u8] {
        match src {
            Src::Doc => self.text(),
            Src::Ent(k) => &self.dtd.rts[k as usize],
            Src::Pro => self.dtd_text(),
        }
    }

    fn span(&self, src: Src, a: usize, b: usize) -> &[u8] {
        &self.buf(src)[a as usize..b as usize]
    }

    fn toks(&self, src: Src) -> &[Tok] {
        match src {
            Src::Doc => &self.tape.toks,
            Src::Ent(k) => match self.ent_tape(k as usize) {
                Some(t) => &t.toks,
                None => &[],
            },
            Src::Pro => &[],
        }
    }

    /// The tape of the replacement text of entity `k`, parsed as content
    /// the first time it is asked for.
    fn ent_tape(&self, k: usize) -> Option<&Tape> {
        self.ent_tapes[k]
            .get_or_init(|| {
                let mut t = Tape::new();
                let env = self.env();
                if crate::content::ex_ent_content(&self.dtd.rts[k], &mut t, &env) {
                    Some(t)
                } else {
                    None
                }
            })
            .as_ref()
    }

    /// The entity a reference names, if it was declared: its index, and
    /// whether it is internal.
    fn entity(&self, src: Src, a: usize, b: usize) -> Option<(usize, bool)> {
        let env = self.env();
        let buf = self.buf(src);
        let j = ex_find_ent(&env, self.dtd.ents.len(), buf, a as usize, b as usize)?;
        Some((j, self.dtd.ents[j].kind == 0))
    }

    /// The attribute definitions that apply: those of the ATTLIST
    /// declarations that were processed (all before the first parameter
    /// entity reference that was not read, unless the document is
    /// standalone, §5.1), the first one binding for each attribute (§3.3).
    fn att_defs(&mut self, toks: &[Tok], pro: Option<&[u8]>) {
        let text: &[u8] = match pro {
            Some(p) => p,
            None => self.owned.as_deref().unwrap_or(self.input),
        };
        let standalone = self.standalone;
        let mut skip = false;
        let mut elem = (0, 0);
        let mut i = 0;
        while i < toks.len() {
            let t = toks[i];
            match t.kind {
                Kind::PERef if !standalone => skip = true,
                Kind::AttlistDecl => elem = (t.a(), t.b()),
                Kind::AttDef if !skip => {
                    let d = toks[i + 1];
                    let e: Box<[u8]> = text[elem.0 as usize..elem.1 as usize].into();
                    let n: Box<[u8]> = text[t.a()..t.b()].into();
                    let by_name = self.def_index.entry(e.clone()).or_default();
                    if !by_name.contains_key(&n) {
                        let k = self.defs.len();
                        self.defs.push(AttDef { name: (t.a(), t.b()), ty: t.f, kind: d.f, value: (d.a(), d.b()) });
                        by_name.insert(n, k);
                        self.defs_of.entry(e).or_default().push(k);
                    }
                    i += 1;
                }
                Kind::DoctypeEnd => break,
                _ => {}
            }
            i += 1;
        }
    }

    /// The normalized value (§3.3.3) of the raw attribute value
    /// `src[a..b]`, collapsed for a declared type other than CDATA.
    /// `Err` if it would grow past `limit` bytes by entity expansion.
    fn value(&self, src: Src, a: usize, b: usize, plain: bool, ty: u8, limit: usize) -> Result<Cow<'_, [u8]>, ()> {
        let v: Cow<'_, [u8]> = if plain {
            Cow::Borrowed(self.span(src, a, b))
        } else {
            let mut out = Vec::with_capacity((b - a) as usize);
            let env = self.env();
            let r = ex_att_norm(
                self.buf(src),
                a as usize,
                b as usize,
                src.raw(),
                &env,
                &self.dtd.rts,
                self.dtd.ents.len(),
                &mut out,
                limit,
            );
            if r != 0 {
                return Err(());
            }
            Cow::Owned(out)
        };
        if ty <= 1 {
            return Ok(v);
        }
        // A type other than CDATA: no leading or trailing spaces, and one
        // space between tokens.
        let collapsed: Vec<u8> = v
            .split(|&c| c == b' ')
            .filter(|w| !w.is_empty())
            .collect::<Vec<_>>()
            .join(&b' ');
        if collapsed.len() == v.len() {
            Ok(v)
        } else {
            Ok(Cow::Owned(collapsed))
        }
    }

    fn def_for(&self, elem: &[u8], name: &[u8]) -> Option<&AttDef> {
        if self.defs.is_empty() {
            return None;
        }
        let k = self.def_index.get(elem)?.get(name)?;
        Some(&self.defs[*k])
    }

    /// The indices in `defs` of the definitions for the element type `elem`.
    fn defs_for(&self, elem: &[u8]) -> &[usize] {
        if self.defs.is_empty() {
            return &[];
        }
        self.defs_of.get(elem).map_or(&[], |v| v.as_slice())
    }
}

/// An element: a start tag in the document or in an entity's replacement
/// text.
#[derive(Clone, Copy)]
pub struct Element<'d> {
    doc: &'d Document<'d>,
    src: Src,
    idx: usize,
}

/// An attribute, with its normalized value.
#[derive(Clone, Debug)]
pub struct Attribute<'d> {
    pub name: &'d str,
    pub value: Cow<'d, str>,
    /// The value came from the DTD's default, not from the start tag.
    pub defaulted: bool,
}

/// What an element contains, in order, entity references to internal
/// entities expanded in place.
#[derive(Clone, Debug)]
pub enum Child<'d> {
    Element(Element<'d>),
    /// Character data, line ends normalized; a character reference is a
    /// child of its own.
    Text(Cow<'d, str>),
    /// The text of a CDATA section.
    CData(Cow<'d, str>),
    Comment(Cow<'d, str>),
    /// A processing instruction: target and data.
    PI(&'d str, Cow<'d, str>),
    /// A reference to an entity that is not read: an external entity, or
    /// one whose declaration may be in an external subset.
    Unexpanded(&'d str),
}

impl fmt::Debug for Element<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<{}>", self.name())
    }
}

impl<'d> Element<'d> {
    fn tok(&self) -> Tok {
        self.doc.toks(self.src)[self.idx as usize]
    }

    /// The element type's name.
    pub fn name(&self) -> &'d str {
        let t = self.tok();
        utf8(self.doc.span(self.src, t.a(), t.b()))
    }

    /// The name, as bytes.
    pub fn name_bytes(&self) -> &'d [u8] {
        let t = self.tok();
        self.doc.span(self.src, t.a(), t.b())
    }

    /// The attributes: those in the start tag, in order, then the DTD's
    /// defaults for the ones not given. Values are their whole normalized
    /// value, however long entity references make it: a "billion laughs"
    /// value is gigabytes. For untrusted input, `try_attributes` with a
    /// limit.
    pub fn attributes(&self) -> Vec<Attribute<'d>> {
        self.try_attributes(usize::MAX).unwrap_or_default()
    }

    /// `attributes`, or `Err` if a value's entity expansion grows past
    /// `limit` bytes.
    pub fn try_attributes(&self, limit: usize) -> Result<Vec<Attribute<'d>>, ()> {
        let doc = self.doc;
        let toks = doc.toks(self.src);
        let elem = self.name_bytes();
        let mut out = Vec::new();
        let mut i = self.idx as usize + 1;
        while i + 1 < toks.len() && toks[i].kind == Kind::Attr {
            let (n, v) = (toks[i], toks[i + 1]);
            let name = doc.span(self.src, n.a(), n.b());
            let ty = doc.def_for(elem, name).map_or(1, |d| d.ty);
            let value = doc.value(self.src, v.a(), v.b(), v.f != 0, ty, limit)?;
            out.push(Attribute { name: utf8(name), value: cow_utf8(value), defaulted: false });
            i += 2;
        }
        let text = doc.dtd_text();
        let given: HashSet<&[u8]> = out.iter().map(|a| a.name.as_bytes()).collect();
        for &k in doc.defs_for(elem) {
            let d = &doc.defs[k];
            if d.kind < 3 {
                continue;
            }
            let name = &text[d.name.0 as usize..d.name.1 as usize];
            if given.contains(name) {
                continue;
            }
            let value = doc.value(Src::Pro, d.value.0, d.value.1, false, d.ty, limit)?;
            out.push(Attribute { name: utf8(name), value: cow_utf8(value), defaulted: true });
        }
        Ok(out)
    }

    /// The value of the attribute `name`, if it has one.
    pub fn attribute(&self, name: &str) -> Option<Cow<'d, str>> {
        self.attributes().into_iter().find(|a| a.name == name).map(|a| a.value)
    }

    /// The children, entity references expanded.
    pub fn children(&self) -> Children<'d> {
        let toks = self.doc.toks(self.src);
        let close = toks[self.idx as usize].c();
        let mut i = self.idx as usize + 1;
        while i < close && matches!(toks[i].kind, Kind::Attr | Kind::AttVal) {
            i += 1;
        }
        Children { doc: self.doc, cur: (self.src, i as usize, close as usize), outer: Vec::new() }
    }

    /// The attributes, without allocating: those in the start tag, then
    /// the DTD's defaults (as `attributes`), whole values, however long.
    pub fn attrs(&self) -> Attrs<'d> {
        Attrs { e: *self, i: self.idx as usize + 1, d: 0 }
    }

    /// The child elements.
    pub fn elements(&self) -> impl Iterator<Item = Element<'d>> + use<'d> {
        self.children().filter_map(|c| match c {
            Child::Element(e) => Some(e),
            _ => None,
        })
    }

    /// All the character data inside, CDATA sections included, in order.
    pub fn text(&self) -> String {
        let mut s = String::new();
        self.push_text(&mut s);
        s
    }

    fn push_text(&self, s: &mut String) {
        for c in self.children() {
            match c {
                Child::Text(t) | Child::CData(t) => s.push_str(&t),
                Child::Element(e) => e.push_text(s),
                _ => {}
            }
        }
    }
}

/// The attributes of an element (`Element::attrs`).
pub struct Attrs<'d> {
    e: Element<'d>,
    i: usize,
    d: usize,
}

impl<'d> Iterator for Attrs<'d> {
    type Item = Attribute<'d>;

    fn next(&mut self) -> Option<Attribute<'d>> {
        let doc = self.e.doc;
        let toks = doc.toks(self.e.src);
        if self.i + 1 < toks.len() && toks[self.i].kind == Kind::Attr {
            let (n, v) = (toks[self.i], toks[self.i + 1]);
            self.i += 2;
            let name = doc.span(self.e.src, n.a(), n.b());
            let ty = if doc.defs.is_empty() { 1 } else { doc.def_for(self.e.name_bytes(), name).map_or(1, |d| d.ty) };
            let value = doc.value(self.e.src, v.a(), v.b(), v.f != 0, ty, usize::MAX).unwrap_or(Cow::Borrowed(&[]));
            return Some(Attribute { name: utf8(name), value: cow_utf8(value), defaulted: false });
        }
        let text = doc.dtd_text();
        let mine = doc.defs_for(self.e.name_bytes());
        while self.d < mine.len() {
            let d = doc.defs[mine[self.d]];
            self.d += 1;
            if d.kind < 3 {
                continue;
            }
            let name = &text[d.name.0 as usize..d.name.1 as usize];
            // Whether the start tag gives it: the definition for a given
            // attribute is found by its name, so look the tag's names up.
            let given = toks[self.e.idx as usize + 1..]
                .chunks(2)
                .take_while(|p| p[0].kind == Kind::Attr)
                .any(|p| doc.span(self.e.src, p[0].a(), p[0].b()) == name);
            if given {
                continue;
            }
            let value = doc.value(Src::Pro, d.value.0, d.value.1, false, d.ty, usize::MAX).unwrap_or(Cow::Borrowed(&[]));
            return Some(Attribute { name: utf8(name), value: cow_utf8(value), defaulted: true });
        }
        None
    }
}

/// The children of an element (`Element::children`): the token range
/// being read, and those of the entities being expanded around it.
pub struct Children<'d> {
    doc: &'d Document<'d>,
    cur: (Src, usize, usize),
    outer: Vec<(Src, usize, usize)>,
}

impl<'d> Iterator for Children<'d> {
    type Item = Child<'d>;

    fn next(&mut self) -> Option<Child<'d>> {
        loop {
            let (src, i, end) = self.cur;
            if i >= end {
                self.cur = self.outer.pop()?;
                continue;
            }
            let doc = self.doc;
            let toks = doc.toks(src);
            let t = toks[i as usize];
            self.cur.1 = i + 1;
            return Some(match t.kind {
                Kind::STag => {
                    self.cur.1 = t.c() + 1;
                    Child::Element(Element { doc, src, idx: i })
                }
                Kind::Text | Kind::CData => {
                    let v: Cow<'d, [u8]> = if src.raw() && t.f & 1 != 0 {
                        let mut out = Vec::with_capacity(t.b() - t.a());
                        ex_eol(doc.buf(src), t.a(), t.b(), &mut out);
                        Cow::Owned(out)
                    } else {
                        Cow::Borrowed(doc.span(src, t.a(), t.b()))
                    };
                    let v = cow_utf8(v);
                    if t.kind == Kind::Text {
                        Child::Text(v)
                    } else {
                        Child::CData(v)
                    }
                }
                Kind::CharRef => Child::Text(Cow::Owned(char::from_u32(t.b() as u32).map(String::from).unwrap_or_default())),
                Kind::Comment => Child::Comment(doc.text_of(src, t)),
                Kind::PI => {
                    let d = toks[i as usize + 1];
                    self.cur.1 = i + 2;
                    Child::PI(utf8(doc.span(src, t.a(), t.b())), doc.text_of(src, d))
                }
                Kind::EntRef => match doc.entity(src, t.a(), t.b()) {
                    Some((k, true)) => {
                        let n = doc.ent_tape(k).map_or(0, |t| t.toks.len());
                        self.outer.push(self.cur);
                        self.cur = (Src::Ent(k as usize), 0, n as usize);
                        continue;
                    }
                    _ => Child::Unexpanded(utf8(doc.span(src, t.a(), t.b()))),
                },
                _ => continue,
            });
        }
    }
}

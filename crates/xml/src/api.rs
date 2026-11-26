//! The Rust API: `parse`, and borrowed views of the verified tape.
//!
//! This file is ordinary Rust. It decides nothing about the input: the
//! verified parser (`enc::ex_parse`) has accepted the document and written
//! its tape, the verified decoders (`decode`) give character data and
//! attribute values their meaning, and the verified `content::ex_ent_content`
//! parses an entity's replacement text when a reference to it is read.
//! The verified `atts` module builds the table of attribute definitions
//! from the DTD's tokens and decides which defaults an element gets and
//! how a value of a declared type is collapsed. What is here is
//! navigation over tokens and error positions.
use crate::atts::{ex_collapse, AttTable};
use crate::decode::{ex_att_norm, ex_eol};
use crate::dtd::DtdOut;
use crate::lex::{ex_find_ent, XEnv};
use crate::tape::{Kind, Tape, Tok};
use std::borrow::Cow;
use std::cell::OnceCell;
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
    /// Reading the DTD whole (its parameter entities expanded, its
    /// external subset loaded) takes more than the budget allows
    /// (`pe::FLAT_FUEL` steps), as a "billion laughs" made of parameter
    /// entities does.
    Limit,
}

/// A rejected document: why, and where. `offset` is a byte offset into
/// the text as UTF-8 (the input itself, unless it was in another
/// encoding); `line` and `column` count from 1, the column in bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Error {
    /// What is wrong.
    pub kind: ErrorKind,
    /// The byte offset where it was found.
    pub offset: usize,
    /// The line, from 1.
    pub line: usize,
    /// The column, from 1, in bytes.
    pub column: usize,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let what = match self.kind {
            ErrorKind::Encoding => "not text in a known encoding, or a character XML does not allow",
            ErrorKind::Syntax => "not well-formed",
            ErrorKind::TooLarge => "longer than token positions hold",
            ErrorKind::Limit => "its DTD expands past the budget for reading it",
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

/// The declarations a document's content refers to: its own, or those of
/// a stream's prolog (`Document::chunk`).
#[cfg_attr(not(any(feature = "expat-abi", feature = "libxml2-abi")), allow(dead_code))]
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
    /// The text of each external parsed entity that was read: decoded,
    /// with its text declaration left out and line ends normalized, and
    /// checked to be content (`content::ex_ent_content`).
    ext_rts: Vec<OnceCell<Vec<u8>>>,
    /// Where each parameter entity's text begins and ends in the
    /// flattened DTD (`pe::Loader::note_push`).
    trace: Vec<(usize, Option<Vec<u8>>, Vec<u8>)>,
    /// The flattened DTD (`pe_spec::flat`) and its tape, when the DTD was
    /// read whole: the declarations' positions are in it.
    flat: Option<(Vec<u8>, Tape)>,
    /// The attribute definitions that apply (`atts::decls`), indexed.
    atts: AttTable,
    root: usize,
}

impl fmt::Debug for Document<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Document({} bytes, {} tokens)", self.text().len(), self.tape.toks.len())
    }
}

/// Parses `input`, a document in UTF-8 (or UTF-16 with its byte order
/// mark, or ISO-8859-1 or US-ASCII as its declaration says). Parameter
/// entities declared in the internal subset are expanded; external
/// entities are not read (see `parse_with`).
pub fn parse(input: &[u8]) -> Result<Document<'_>, Error> {
    parse_x(input, false, &mut crate::pe::Loader::none(), false)
}

/// `parse`, reading the external subset and external parameter entities
/// with `loader` (`pe::Loader::new`), which is asked for each once. What
/// it gives is checked like the document: decoded by its byte order mark
/// or text declaration, with every declaration in it well-formed.
pub fn parse_with<'a>(input: &'a [u8], loader: &mut crate::pe::Loader) -> Result<Document<'a>, Error> {
    parse_x(input, true, loader, true)
}

/// `parse_with`, reading the external subset and external parameter
/// entities but not external general entities (libxml2's
/// XML_PARSE_DTDLOAD).
#[cfg_attr(not(any(feature = "expat-abi", feature = "libxml2-abi")), allow(dead_code))]
pub(crate) fn parse_dtd_with<'a>(input: &'a [u8], loader: &mut crate::pe::Loader) -> Result<Document<'a>, Error> {
    parse_x(input, true, loader, false)
}

fn parse_x<'a>(input: &'a [u8], load: bool, loader: &mut crate::pe::Loader, general: bool) -> Result<Document<'a>, Error> {
    use crate::pe::{XDocRes, XDtdRes};
    let mut tape = Tape::new();
    loader.trace.clear();
    let doc = match crate::pe::ex_parse_x(input, &mut tape, load, loader, crate::pe::FLAT_FUEL) {
        Some((owned, XDocRes::Ok(XDtdRes::Own(dtd)))) => Document::new(input, owned, tape, dtd, None),
        Some((owned, XDocRes::Ok(XDtdRes::Flat { text, tape: ft, out }))) => {
            let mut d = Document::new(input, owned, tape, out, Some((text, ft)));
            d.trace = std::mem::take(&mut loader.trace);
            d
        }
        Some((owned, XDocRes::Limit)) => {
            let text: &[u8] = owned.as_deref().unwrap_or(input);
            return Err(error_at(ErrorKind::Limit, text, doctype_at(&tape)));
        }
        Some((owned, _)) => {
            let e = diagnose(input, &tape);
            if e.kind == ErrorKind::Syntax && e.offset == 0 {
                // Rejected for what the DTD read whole holds: at the
                // document type declaration.
                let text: &[u8] = owned.as_deref().unwrap_or(input);
                return Err(error_at(ErrorKind::Syntax, text, doctype_at(&tape)));
            }
            return Err(e);
        }
        None => return Err(diagnose(input, &tape)),
    };
    if general {
        doc.read_external(loader)?;
    }
    Ok(doc)
}

/// At most this many external entities are read for a document, and at
/// most this many bytes of them in all.
const MAX_EXT_ENTITIES: usize = 1 << 12;
const MAX_EXT_BYTES: usize = 1 << 28;

/// Where the document type declaration's name is, on a tape (0 if none).
fn doctype_at(tape: &Tape) -> usize {
    tape.toks.iter().find(|t| t.kind == Kind::Doctype).map_or(0, |t| t.a())
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
pub(crate) enum Src {
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
    fn new(input: &'a [u8], owned: Option<Vec<u8>>, tape: Tape, dtd: DtdOut, flat: Option<(Vec<u8>, Tape)>) -> Self {
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
            ext_rts: (0..n).map(|_| OnceCell::new()).collect(),
            trace: Vec::new(),
            flat,
            atts: AttTable::build(&[], &[], false),
            root: 0,
        };
        d.root = d.tape.toks.iter().position(|t| t.kind == Kind::STag).unwrap_or(0) as usize;
        if let Some((ft, fk)) = d.flat.take() {
            d.att_defs(&fk.toks, Some(&ft));
            d.flat = Some((ft, fk));
        } else {
            let toks = std::mem::take(&mut d.tape.toks);
            d.att_defs(&toks, None);
            d.tape.toks = toks;
        }
        d
    }

    /// A stream's document, read a chunk at a time (`set_chunk`): its
    /// content refers to the declarations `dtd`, at positions in `pro`,
    /// whose tokens are `ptoks` (the prolog's).
    #[cfg_attr(not(any(feature = "expat-abi", feature = "libxml2-abi")), allow(dead_code))]
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
            ext_rts: (0..n).map(|_| OnceCell::new()).collect(),
            trace: Vec::new(),
            flat: None,
            atts: AttTable::build(&[], &[], false),
            root: 0,
        };
        d.att_defs(ptoks, Some(pro));
        d
    }

    /// The next chunk of a stream's document: the window's text, and the
    /// tokens read in it. The tokens of the last chunk come back.
    #[cfg_attr(not(any(feature = "expat-abi", feature = "libxml2-abi")), allow(dead_code))]
    pub(crate) fn set_chunk(&mut self, text: &'a [u8], tape: Tape) -> Tape {
        self.input = text;
        std::mem::replace(&mut self.tape, tape)
    }

    /// The XML declaration says `standalone="yes"`.
    #[cfg_attr(not(any(feature = "expat-abi", feature = "libxml2-abi")), allow(dead_code))]
    pub(crate) fn standalone(&self) -> bool {
        self.standalone
    }

    /// The text the declarations' positions are in.
    fn dtd_text(&self) -> &[u8] {
        if let Some((t, _)) = &self.flat {
            return t;
        }
        match self.pro {
            Some(p) => p,
            None => self.text(),
        }
    }

    /// Where each parameter entity's text begins (its name) and ends
    /// (`None`) in the flattened DTD.
    #[cfg_attr(not(any(feature = "expat-abi", feature = "libxml2-abi")), allow(dead_code))]
    pub(crate) fn pe_trace(&self) -> &[(usize, Option<Vec<u8>>, Vec<u8>)] {
        &self.trace
    }

    /// The document's tape.
    pub(crate) fn into_tape(self) -> Tape {
        self.tape
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
        let (src, toks) = self.dtd_toks();
        let mut out = Vec::new();
        for (i, t) in toks.iter().enumerate() {
            if t.kind != Kind::NotationDecl {
                continue;
            }
            let mut p = None;
            let mut s = None;
            for u in &toks[i + 1..] {
                match u.kind {
                    Kind::PubId => p = Some(utf8(self.span(src, u.a(), u.b()))),
                    Kind::SysId => s = Some(utf8(self.span(src, u.a(), u.b()))),
                    _ => break,
                }
            }
            out.push((utf8(self.span(src, t.a(), t.b())), p, s));
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
            Src::Ent(k) => self.ent_text(k),
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
            Src::Pro => match &self.flat {
                Some((_, t)) => &t.toks,
                None => &[],
            },
        }
    }

    /// The tokens of the declarations and the text they are in: the
    /// flattened DTD's (`Src::Pro`) if the DTD was read whole, else the
    /// document's own.
    #[cfg_attr(not(any(feature = "expat-abi", feature = "libxml2-abi")), allow(dead_code))]
    pub(crate) fn dtd_toks(&self) -> (Src, &[Tok]) {
        match &self.flat {
            Some((_, t)) => (Src::Pro, &t.toks),
            None => (Src::Doc, &self.tape.toks),
        }
    }

    /// The DTD was read whole: its declarations are in `dtd_toks`, over
    /// `buf(Src::Pro)`.
    #[cfg_attr(not(any(feature = "expat-abi", feature = "libxml2-abi")), allow(dead_code))]
    pub(crate) fn flattened(&self) -> bool {
        self.flat.is_some()
    }

    /// The tape of the replacement text of entity `k`, parsed as content
    /// the first time it is asked for.
    fn ent_tape(&self, k: usize) -> Option<&Tape> {
        self.ent_tapes[k]
            .get_or_init(|| {
                let mut t = Tape::new();
                let env = self.env();
                if crate::content::ex_ent_content(self.ent_text(k), &mut t, &env) {
                    Some(t)
                } else {
                    None
                }
            })
            .as_ref()
    }

    /// The replacement text of entity `k`: an internal entity's, or an
    /// external parsed entity's that was read (empty if not).
    fn ent_text(&self, k: usize) -> &[u8] {
        if self.dtd.ents[k].kind == 0 {
            &self.dtd.rts[k]
        } else {
            self.ext_rts[k].get().map_or(&[], |v| v.as_slice())
        }
    }

    /// Whether entity `k`'s replacement text is known: it is internal, or
    /// an external parsed entity that was read.
    #[cfg_attr(not(any(feature = "expat-abi", feature = "libxml2-abi")), allow(dead_code))]
    pub(crate) fn expandable(&self, k: usize) -> bool {
        self.dtd.ents[k].kind == 0 || self.ext_rts[k].get().is_some()
    }

    /// The declaration of the external entity `k`: its system and public
    /// identifiers, and the base URI they are relative to ("" for the
    /// document entity).
    pub(crate) fn ext_ids(&self, k: usize) -> Option<(&[u8], &[u8], &[u8])> {
        let e = &self.dtd.ents[k];
        if e.kind != 1 {
            return None;
        }
        let (_, toks) = self.dtd_toks();
        let text = self.dtd_text();
        let i = toks.iter().position(|t| t.kind == Kind::EntityDecl && t.f == 0 && t.a() == e.a && t.b() == e.b)?;
        let (mut sys, mut pubid): (&[u8], &[u8]) = (&[], &[]);
        for u in &toks[i + 1..] {
            match u.kind {
                Kind::SysId => sys = &text[u.a()..u.b()],
                Kind::PubId => pubid = &text[u.a()..u.b()],
                Kind::NData => return None,
                _ => break,
            }
        }
        // The base: that of the innermost entity whose text holds the
        // declaration.
        let mut stack: Vec<&[u8]> = Vec::new();
        for (pos, name, base) in &self.trace {
            if *pos > e.a {
                break;
            }
            match name {
                Some(_) => stack.push(base),
                None => {
                    stack.pop();
                }
            }
        }
        Some((sys, pubid, stack.last().copied().unwrap_or(&[])))
    }

    /// Takes `bytes` as the text of the external parsed entity `k`: decoded
    /// by its byte order mark or text declaration (`pe::ex_ext_text`), and
    /// checked to be content (`content::ex_ent_content`). False if it is
    /// not (and nothing is kept), or the entity was read already.
    #[cfg_attr(not(any(feature = "expat-abi", feature = "libxml2-abi")), allow(dead_code))]
    pub(crate) fn set_ext(&self, k: usize, bytes: Vec<u8>) -> bool {
        if self.dtd.ents[k].kind != 1 || self.ext_rts[k].get().is_some() {
            return false;
        }
        let Some((t, q)) = crate::pe::ex_ext_text(bytes) else { return false };
        let mut r = Vec::with_capacity(t.len() - q);
        ex_eol(&t, q, t.len(), &mut r);
        let mut tape = Tape::new();
        if !crate::content::ex_ent_content(&r, &mut tape, &self.env()) {
            return false;
        }
        let _ = self.ext_rts[k].set(r);
        let _ = self.ent_tapes[k].set(Some(tape));
        true
    }

    /// Reads, with `loader`, each external parsed entity the content refers
    /// to (in the document, or in the text of an entity it refers to), and
    /// checks it (`set_ext`) and that no entity refers to itself.
    fn read_external(&self, loader: &mut crate::pe::Loader) -> Result<(), Error> {
        // 0: not seen, 1: being read, 2: done.
        let mut state = vec![0u8; self.dtd.ents.len()];
        let toks = &self.tape.toks;
        let mut i = self.root;
        while i < toks.len() {
            if toks[i].kind == Kind::EntRef {
                if let Some((k, _)) = self.entity(Src::Doc, toks[i].a(), toks[i].b()) {
                    self.read_from(k, &mut state, loader).map_err(|kind| error_at(kind, self.text(), toks[i].a()))?;
                }
            }
            i += 1;
        }
        Ok(())
    }

    fn read_from(&self, k: usize, state: &mut [u8], loader: &mut crate::pe::Loader) -> Result<(), ErrorKind> {
        match state[k] {
            1 => return Err(ErrorKind::Syntax),
            2 => return Ok(()),
            _ => {}
        }
        if self.dtd.ents[k].kind == 1 && self.ext_rts[k].get().is_none() {
            let Some((sys, pubid, base)) = self.ext_ids(k) else { return Ok(()) };
            if loader.count >= MAX_EXT_ENTITIES {
                return Err(ErrorKind::Limit);
            }
            if let Some((bytes, _)) = loader.fetch(base, sys, pubid) {
                if loader.bytes > MAX_EXT_BYTES {
                    return Err(ErrorKind::Limit);
                }
                if !self.set_ext(k, bytes) {
                    return Err(ErrorKind::Syntax);
                }
            }
        }
        if !self.expandable(k) {
            state[k] = 2;
            return Ok(());
        }
        state[k] = 1;
        let n = self.ent_tape(k).map_or(0, |t| t.toks.len());
        for j in 0..n {
            let t = self.ent_tape(k).unwrap().toks[j];
            if t.kind == Kind::EntRef {
                if let Some((m, _)) = self.entity(Src::Ent(k), t.a(), t.b()) {
                    self.read_from(m, state, loader)?;
                }
            }
        }
        state[k] = 2;
        Ok(())
    }

    /// The entity a reference names, if it was declared: its index, and
    /// whether it is internal.
    fn entity(&self, src: Src, a: usize, b: usize) -> Option<(usize, bool)> {
        let env = self.env();
        let buf = self.buf(src);
        let j = ex_find_ent(&env, self.dtd.ents.len(), buf, a as usize, b as usize)?;
        Some((j, self.dtd.ents[j].kind == 0))
    }

    /// The attribute definitions that apply (`atts::decls`): those of the
    /// ATTLIST declarations that were processed (all before the first
    /// parameter entity reference that was not read, unless the document
    /// is standalone, §5.1), the first one binding for each attribute
    /// (§3.3).
    fn att_defs(&mut self, toks: &[Tok], pro: Option<&[u8]>) {
        let text: &[u8] = match pro {
            Some(p) => p,
            None => self.owned.as_deref().unwrap_or(self.input),
        };
        self.atts = AttTable::build(text, toks, self.standalone);
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
        // A type other than CDATA (§3.3.3).
        let collapsed = ex_collapse(&v);
        if collapsed[..] == v[..] {
            Ok(v)
        } else {
            Ok(Cow::Owned(collapsed))
        }
    }

    /// Whether any attribute definition applies.
    #[cfg_attr(not(any(feature = "expat-abi", feature = "libxml2-abi")), allow(dead_code))]
    pub(crate) fn has_defs(&self) -> bool {
        !self.atts.decls.is_empty()
    }

    /// The binding definition of the attribute `name` of the element type
    /// `elem` (`AttTable::def_for`).
    pub(crate) fn def_for(&self, elem: &[u8], name: &[u8]) -> Option<&crate::atts::ADecl> {
        if self.atts.decls.is_empty() {
            return None;
        }
        let k = self.atts.def_for(self.dtd_text(), elem, 0, elem.len(), name, 0, name.len())?;
        Some(&self.atts.decls[k])
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
    /// The attribute's name.
    pub name: &'d str,
    /// Its value, normalized (references replaced, white space as the attribute's type says).
    pub value: Cow<'d, str>,
    /// The value came from the DTD's default, not from the start tag.
    pub defaulted: bool,
}

/// What an element contains, in order, entity references to internal
/// entities expanded in place.
#[derive(Clone, Debug)]
pub enum Child<'d> {
    /// A child element.
    Element(Element<'d>),
    /// Character data, line ends normalized; a character reference is a
    /// child of its own.
    Text(Cow<'d, str>),
    /// The text of a CDATA section.
    CData(Cow<'d, str>),
    /// A comment's text.
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
        if doc.atts.decls.is_empty() {
            return Ok(out);
        }
        let text = doc.dtd_text();
        let t = self.tok();
        for k in doc.atts.ex_defaults(text, doc.buf(self.src), toks, self.idx + 1, t.a(), t.b()) {
            let d = doc.atts.decls[k];
            let name = &text[d.na..d.nb];
            let value = doc.value(Src::Pro, d.va, d.vb, false, d.ty, limit)?;
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
        Attrs { e: *self, i: self.idx as usize + 1, g: None, k: 0 }
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
    /// The element type's group of definitions, once the start tag's
    /// attributes are read (`Some(None)`: there is none), and where in its
    /// binding definitions to go on.
    g: Option<Option<usize>>,
    k: usize,
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
            let ty = doc.def_for(self.e.name_bytes(), name).map_or(1, |d| d.ty);
            let value = doc.value(self.e.src, v.a(), v.b(), v.f != 0, ty, usize::MAX).unwrap_or(Cow::Borrowed(&[]));
            return Some(Attribute { name: utf8(name), value: cow_utf8(value), defaulted: false });
        }
        if doc.atts.decls.is_empty() {
            return None;
        }
        let text = doc.dtd_text();
        let buf = doc.buf(self.e.src);
        let t = self.e.tok();
        let g = *self.g.get_or_insert_with(|| doc.atts.group_of(text, buf, t.a(), t.b()));
        let (k, next) = doc.atts.next_default(text, buf, toks, self.e.idx + 1, t.a(), t.b(), g?, self.k)?;
        self.k = next;
        let d = doc.atts.decls[k];
        let name = &text[d.na..d.nb];
        let value = doc.value(Src::Pro, d.va, d.vb, false, d.ty, usize::MAX).unwrap_or(Cow::Borrowed(&[]));
        Some(Attribute { name: utf8(name), value: cow_utf8(value), defaulted: true })
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
                    Some((k, _)) if doc.expandable(k) => {
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

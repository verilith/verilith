//! A recovering XML parser: libxml2 2.15.4's `parser.c` document path,
//! ported.
//!
//! The verified parser (`doc`, `content`, `dtd`, ...) decides whether a
//! document is well-formed, and that verdict is the one this library
//! reports. A drop-in for libxml2 must also say *what* is wrong the way
//! libxml2 says it: libxml2 keeps parsing after a well-formedness error,
//! reports every error it finds (up to its limits), and with
//! `XML_PARSE_RECOVER` builds a tree from what it read. This module does
//! that, and only for documents the verified parser rejected: it reads the
//! input as libxml2 does, function for function, and makes its reports and
//! SAX calls through a [`Sink`], which the libxml2 ABI layer
//! (`api/libxml2/recover.rs`) implements over the parser context.
//!
//! The reading is libxml2's, including its buffering where that shows in
//! what is reported: the input is a NUL-terminated buffer that grows by
//! `INPUT_CHUNK`, decoded from the input's encoding in libxml2's chunks,
//! with the line and column kept as libxml2 keeps them.
//!
//! Every read of a buffer is through [`at`], which answers 0 past the end
//! (libxml2's buffers end in a NUL), so no index can be out of bounds;
//! counters saturate; every loop either consumes input or is bounded.
#![allow(clippy::too_many_arguments, clippy::collapsible_if, clippy::collapsible_else_if)]

pub mod tables;
mod enc;
mod names;
mod nsdb;
mod dtd;
pub mod refs;
mod content;
mod doc;
pub use doc::parse;

pub use enc::{lookup_encoding, Enc};

// --- constants (parser.h, parserInternals.h, parser.c) -------------------------

pub const PARSE_RECOVER: u32 = 1 << 0;
pub const PARSE_NOENT: u32 = 1 << 1;
pub const PARSE_DTDLOAD: u32 = 1 << 2;
pub const PARSE_DTDATTR: u32 = 1 << 3;
pub const PARSE_DTDVALID: u32 = 1 << 4;
pub const PARSE_PEDANTIC: u32 = 1 << 7;
pub const PARSE_NOBLANKS: u32 = 1 << 8;
pub const PARSE_SAX1: u32 = 1 << 9;
pub const PARSE_NSCLEAN: u32 = 1 << 13;
pub const PARSE_NOCDATA: u32 = 1 << 14;
pub const PARSE_OLD10: u32 = 1 << 17;
pub const PARSE_HUGE: u32 = 1 << 19;
pub const PARSE_OLDSAX: u32 = 1 << 20;
pub const PARSE_IGNORE_ENC: u32 = 1 << 21;
pub const PARSE_NO_XXE: u32 = 1 << 23;

pub const INPUT_CHUNK: usize = 250;
pub const LINE_LEN: usize = 80;
pub const MINLEN: usize = 4000;
pub const MAX_TEXT_LENGTH: usize = 10_000_000;
pub const MAX_HUGE_LENGTH: usize = 1_000_000_000;
pub const MAX_NAME_LENGTH: usize = 50_000;
pub const MAX_LOOKUP_LIMIT: usize = 10_000_000;
pub const MAX_NAMELEN: usize = 100;
pub const PARSER_BUFFER_SIZE: usize = 100;
pub const PARSER_BIG_BUFFER_SIZE: usize = 300;
pub const ENT_FIXED_COST: u64 = 20;
pub const PARSER_ALLOWED_EXPANSION: u64 = 1_000_000;
pub const INVALID_CHAR: u32 = 0x200000;

/// `xmlParserInput.flags`.
pub const INPUT_HAS_ENCODING: u32 = 1 << 0;
pub const INPUT_AUTO_ENCODING: u32 = 7 << 1;
pub const INPUT_AUTO_UTF8: u32 = 1 << 1;
pub const INPUT_AUTO_UTF16LE: u32 = 2 << 1;
pub const INPUT_AUTO_UTF16BE: u32 = 3 << 1;
pub const INPUT_AUTO_OTHER: u32 = 4 << 1;
pub const INPUT_USES_ENC_DECL: u32 = 1 << 4;
pub const INPUT_ENCODING_ERROR: u32 = 1 << 5;
pub const INPUT_MARKUP_DECL: u32 = 1 << 7;

/// `xmlEntity.flags`.
pub const ENT_PARSED: u32 = 1 << 0;
pub const ENT_CHECKED: u32 = 1 << 1;
pub const ENT_VALIDATED: u32 = 1 << 2;
pub const ENT_EXPANDING: u32 = 1 << 3;

/// `xmlEntityType`.
pub const INTERNAL_GENERAL_ENTITY: i32 = 1;
pub const EXTERNAL_GENERAL_PARSED_ENTITY: i32 = 2;
pub const EXTERNAL_GENERAL_UNPARSED_ENTITY: i32 = 3;
pub const INTERNAL_PARAMETER_ENTITY: i32 = 4;
pub const EXTERNAL_PARAMETER_ENTITY: i32 = 5;
pub const INTERNAL_PREDEFINED_ENTITY: i32 = 6;

/// `xmlErrorLevel`.
pub const LEVEL_WARNING: i32 = 1;
pub const LEVEL_ERROR: i32 = 2;
pub const LEVEL_FATAL: i32 = 3;

/// `xmlErrorDomain`.
pub const FROM_PARSER: i32 = 1;
pub const FROM_NAMESPACE: i32 = 3;
pub const FROM_DTD: i32 = 4;
pub const FROM_IO: i32 = 8;

pub mod codes;
use codes::*;

// --- what the parser reports to -------------------------------------------------

/// An entity, as the sink knows it (a pointer to its `xmlEntity`).
pub type Ent = usize;

/// The fields of an `xmlEntity` the parser reads.
#[derive(Clone, Copy, Default)]
pub struct EntInfo {
    pub etype: i32,
    pub flags: u32,
    pub expanded_size: u64,
    /// `content != NULL`.
    pub has_content: bool,
    pub length: usize,
    /// `children != NULL`.
    pub has_children: bool,
    /// `URI != NULL`.
    pub has_uri: bool,
}

/// One error report (`xmlCtxtErr`'s arguments). `msg` is the formatted
/// message; `None` asks for libxml2's message for `code`, formatted as
/// `xmlFatalErr` does: "%s\n", or "%s: %s\n" with `s1`.
pub struct Report<'a> {
    pub domain: i32,
    pub code: i32,
    pub level: i32,
    pub s1: Option<&'a [u8]>,
    pub s2: Option<&'a [u8]>,
    pub s3: Option<&'a [u8]>,
    pub int1: i32,
    pub msg: Option<&'a [u8]>,
}

/// An external resource read for the parser: its bytes, whether they are
/// read in chunks (a file) or are all there, and the input's file name.
pub struct Loaded {
    pub bytes: Vec<u8>,
    pub stream: bool,
    pub filename: Option<Vec<u8>>,
}

/// An input on the stack, as error reports and SAX handlers see it
/// (`ctxt->inputTab[i]`).
pub struct InputView<'a> {
    pub buf: &'a [u8],
    pub base: usize,
    pub cur: usize,
    pub line: i32,
    pub col: i32,
    pub entity: Option<Ent>,
    /// The input's buffer decodes through an encoder.
    pub encoder: bool,
    pub flags: u32,
    /// `input->filename`, when the parser knows it.
    pub filename: Option<&'a [u8]>,
}

/// An attribute passed to `startElementNs`: localname, prefix, URI, value.
pub struct NsAttr<'a> {
    pub local: &'a [u8],
    pub prefix: Option<&'a [u8]>,
    pub uri: Option<&'a [u8]>,
    pub value: &'a [u8],
}

/// An element content model (`xmlElementContent`), as an arena.
#[derive(Clone, Default)]
pub struct ContentModel {
    pub nodes: Vec<ContentNode>,
    pub root: Option<usize>,
}

/// `xmlElementContentType`: PCDATA 1, ELEMENT 2, SEQ 3, OR 4;
/// `xmlElementContentOccur`: ONCE 1, OPT 2, MULT 3, PLUS 4.
#[derive(Clone, Default)]
pub struct ContentNode {
    pub ctype: i32,
    pub ocur: i32,
    pub name: Option<Vec<u8>>,
    pub prefix: Option<Vec<u8>>,
    pub c1: Option<usize>,
    pub c2: Option<usize>,
    pub parent: Option<usize>,
}

/// How the parser reaches the parser context: its state, the SAX handler
/// and the error channel. The libxml2 ABI layer implements it.
pub trait Sink {
    // the context's settings and state
    fn options(&self) -> u32;
    fn replace_entities(&self) -> bool;
    fn keep_blanks(&self) -> bool;
    fn sax2(&self) -> bool;
    fn validate(&self) -> bool;
    fn recovery(&self) -> bool;
    fn html(&self) -> bool;
    fn max_ampl(&self) -> u32;
    fn disable_sax(&self) -> i32;
    fn well_formed(&self) -> bool;
    fn set_well_formed(&mut self, v: bool);
    fn err_no(&self) -> i32;
    fn set_ns_well_formed(&mut self, v: bool);
    fn set_valid(&mut self, v: bool);
    fn in_subset(&self) -> i32;
    fn set_in_subset(&mut self, v: i32);
    fn set_has_ext_subset(&mut self, v: bool);
    fn has_ext_subset(&self) -> bool;
    fn set_has_perefs(&mut self, v: bool);
    fn has_perefs(&self) -> bool;
    fn set_standalone(&mut self, v: i32);
    fn standalone(&self) -> i32;
    fn set_version(&mut self, v: &[u8]);
    fn set_encoding(&mut self, v: Option<&[u8]>);
    fn set_int_subset(&mut self, name: Option<&[u8]>, ext_id: Option<&[u8]>, sys_id: Option<&[u8]>);
    fn set_instate_eof(&mut self);
    /// Stops the parser (`xmlHaltParser`): `disableSAX = 2`.
    fn halt(&mut self);
    fn stop(&mut self);
    fn mem_error(&mut self);
    /// The input stack changed or moved: what `ctxt->input` and
    /// `ctxt->inputTab` show from now on.
    fn sync(&mut self, inputs: &[InputView<'_>]);
    fn report(&mut self, r: &Report<'_>);
    fn sizeentities(&self) -> u64;
    fn sizeentcopy(&self) -> u64;
    fn set_sizeentcopy(&mut self, v: u64);
    fn add_sizeentities(&mut self, v: u64);

    // SAX
    fn start_document(&mut self);
    fn internal_subset(&mut self, name: Option<&[u8]>, ext_id: Option<&[u8]>, sys_id: Option<&[u8]>);
    /// `xmlSAX2ExternalSubset` up to reading: when the subset is to be
    /// loaded, its DTD node made and its bytes with the way they are read.
    fn external_subset(&mut self, name: Option<&[u8]>, ext_id: Option<&[u8]>, sys_id: Option<&[u8]>) -> Option<Loaded>;
    /// `xmlParseExternalSubset`'s document and internal subset, when none.
    fn ensure_doc_for_subset(&mut self, ext_id: Option<&[u8]>, sys_id: Option<&[u8]>);
    fn end_document(&mut self);
    fn has_external_subset_cb(&mut self) -> bool;
    fn has_internal_subset_cb(&mut self) -> bool;
    fn entity_decl(&mut self, name: &[u8], etype: i32, public_id: Option<&[u8]>, system_id: Option<&[u8]>, content: Option<&[u8]>);
    fn unparsed_entity_decl(&mut self, name: &[u8], public_id: Option<&[u8]>, system_id: Option<&[u8]>, notation: Option<&[u8]>);
    fn has_unparsed_entity_decl(&self) -> bool;
    /// `xmlParseEntityDecl`'s SAX2 compatibility document
    /// (`SAX_COMPAT_MODE`): when there is no document (or it is that one),
    /// the entity is added to it.
    fn compat_entity_decl(&mut self, name: &[u8], etype: i32, public_id: Option<&[u8]>, system_id: Option<&[u8]>, content: Option<&[u8]>);
    /// The entity's `orig`, when it has none yet.
    fn entity_orig(&mut self, is_pe: bool, name: &[u8], orig: &[u8]);
    fn notation_decl(&mut self, name: &[u8], public_id: Option<&[u8]>, system_id: Option<&[u8]>);
    fn attribute_decl(&mut self, elem: &[u8], name: &[u8], atype: i32, def: i32, default: Option<&[u8]>, tree: Option<Vec<Vec<u8>>>);
    fn element_decl(&mut self, name: &[u8], etype: i32, content: &ContentModel);
    fn start_element_ns(&mut self, local: &[u8], prefix: Option<&[u8]>, uri: Option<&[u8]>, nss: &[(Option<&[u8]>, &[u8])], atts: &[NsAttr<'_>], nb_defaulted: usize);
    fn end_element_ns(&mut self, local: &[u8], prefix: Option<&[u8]>, uri: Option<&[u8]>);
    fn start_element(&mut self, name: &[u8], atts: &[(&[u8], Option<&[u8]>)]);
    fn end_element(&mut self, name: &[u8]);
    fn characters(&mut self, s: &[u8]);
    fn ignorable_whitespace(&mut self, s: &[u8]);
    /// Whether `ignorableWhitespace` and `characters` are the same callback.
    fn blanks_same_as_chars(&self) -> bool;
    fn has_characters(&self) -> bool;
    fn cdata_block(&mut self, s: &[u8]);
    fn has_cdata_block(&self) -> bool;
    fn processing_instruction(&mut self, target: &[u8], data: Option<&[u8]>);
    fn comment(&mut self, s: &[u8]);
    fn reference(&mut self, name: &[u8]);
    fn has_reference(&self) -> bool;

    // entities
    fn get_entity(&mut self, name: &[u8]) -> Option<Ent>;
    fn has_get_entity(&self) -> bool;
    fn get_parameter_entity(&mut self, name: &[u8]) -> Option<Ent>;
    fn has_get_parameter_entity(&self) -> bool;
    /// `xmlSAX2GetEntity` (the default handler's lookup), for the SAX1
    /// compatibility path of `xmlParseEntityRefInternal`.
    fn sax2_get_entity(&mut self, name: &[u8]) -> Option<Ent>;
    fn predefined_entity(&mut self, name: &[u8]) -> Option<Ent>;
    fn ent_info(&self, e: Ent) -> EntInfo;
    fn ent_content(&self, e: Ent) -> Vec<u8>;
    fn ent_name(&self, e: Ent) -> Vec<u8>;
    fn ent_set_flags(&mut self, e: Ent, flags: u32);
    fn ent_set_expanded_size(&mut self, e: Ent, v: u64);
    fn ent_truncate_content(&mut self, e: Ent);
    /// An external entity's content, loaded (`xmlLoadResource`), with the
    /// way it is read; `None` when it cannot be (reported by the sink).
    fn load_entity(&mut self, e: Ent) -> Option<Loaded>;
    fn ent_set_content(&mut self, e: Ent, content: Vec<u8>);
    /// The tree side of `xmlParseReference` with entities replaced: the
    /// entity's nodes copied under the current node, its first and last
    /// text passed as characters.
    fn reference_tree(&mut self, e: Ent, first: bool);
    /// The tree side of parsing an entity's content.
    fn ent_tree(&mut self, op: refs::TreeOp, e: Ent);
    /// `ctxt->node != NULL`.
    fn has_node(&self) -> bool;
    /// `ctxt->nodeNr`, and `nodePop`.
    fn node_nr(&self) -> usize;
    fn node_pop(&mut self);
    /// `ctxt->valid &= xmlValidateRoot(...)` when the node just made is
    /// the document's root.
    fn validate_root(&mut self);
    /// `xmlCtxtIsCatastrophicError`.
    fn catastrophic(&self) -> bool;
    /// `areBlanks`'s questions about the tree (from `ctxt->node == NULL`
    /// on), with the two bytes after the text.
    fn blanks_ignorable_in_tree(&mut self, next: [u8; 2]) -> bool;

    // namespaces, mirrored for SAX2's `xmlParserNsLookupSax`
    fn ns_pushed(&mut self, prefix: Option<&[u8]>, uri: &[u8]);
    fn ns_popped(&mut self, n: usize);
    fn ns_min(&mut self, min: usize);
    /// `xmlParseURISafe` on a namespace name: (parsed, has a scheme).
    fn uri_check(&self, uri: &[u8]) -> (bool, bool);
}

// --- the input stack ---------------------------------------------------------------

/// How an input's bytes arrive (`xmlParserInputBuffer`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// All of it, in memory (no read callback).
    Memory,
    /// Read `len` bytes at a time (a file or descriptor).
    Stream,
}

/// The raw side of an input buffer: what is still to be read or decoded.
pub struct Source {
    pub raw: Vec<u8>,
    /// Bytes delivered by the "read callback" so far.
    pub delivered: usize,
    /// Bytes of `raw` already converted (or moved to the buffer).
    pub pos: usize,
    pub mode: Mode,
    pub enc: Option<Enc>,
    /// `buf->error`.
    pub error: i32,
    /// The read callback is exhausted.
    pub eof: bool,
}

pub struct Input {
    /// The text read so far (libxml2's buffer, without its NUL).
    pub buf: Vec<u8>,
    pub base: usize,
    pub cur: usize,
    pub line: i32,
    pub col: i32,
    pub flags: u32,
    /// Bytes read before `buf[0]` (`consumed`, less what shrinking moved).
    pub consumed: u64,
    pub entity: Option<Ent>,
    /// `entity->etype`, kept with it.
    pub etype: i32,
    pub src: Option<Source>,
    /// `input->version`, from a text declaration.
    pub version: Option<Vec<u8>>,
    pub filename: Option<Vec<u8>>,
}

impl Input {
    pub fn from_bytes(b: Vec<u8>) -> Input {
        Input { buf: b, base: 0, cur: 0, line: 1, col: 1, flags: 0, consumed: 0, entity: None, etype: 0, src: None, version: None, filename: None }
    }
}

/// A byte of `b`, 0 past its end (libxml2's buffers are NUL-terminated).
#[inline]
pub fn at(b: &[u8], i: usize) -> u8 {
    if i < b.len() { b[i] } else { 0 }
}

#[inline]
pub fn blank(c: u8) -> bool {
    c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D
}

/// `xmlCopyCharMultiByte`, appended.
pub fn push_char(out: &mut Vec<u8>, c: u32) {
    if c < 0x80 {
        out.push(c as u8);
    } else if c < 0x800 {
        out.push(((c >> 6) | 0xC0) as u8);
        out.push(((c & 0x3F) | 0x80) as u8);
    } else if c < 0x10000 {
        out.push(((c >> 12) | 0xE0) as u8);
        out.push((((c >> 6) & 0x3F) | 0x80) as u8);
        out.push(((c & 0x3F) | 0x80) as u8);
    } else if c < 0x110000 {
        out.push(((c >> 18) | 0xF0) as u8);
        out.push((((c >> 12) & 0x3F) | 0x80) as u8);
        out.push((((c >> 6) & 0x3F) | 0x80) as u8);
        out.push(((c & 0x3F) | 0x80) as u8);
    }
}

/// `xmlStringCurrentChar` over a NUL-terminated string: the character at
/// `i` and its length, (0, 4)-like garbage giving 0.
pub fn string_char(s: &[u8], i: usize) -> (u32, usize) {
    match utf8_char(s, i, 4) {
        Some(r) => r,
        None => (0, 4),
    }
}

/// `xmlGetUTF8Char`: the character at `i` within `avail` bytes.
pub fn utf8_char(s: &[u8], i: usize, avail: usize) -> Option<(u32, usize)> {
    let c = at(s, i) as u32;
    if avail < 1 {
        return None;
    }
    if c < 0x80 {
        return Some((c, 1));
    }
    if avail < 2 || (at(s, i + 1) & 0xC0) != 0x80 {
        return None;
    }
    if c < 0xE0 {
        if c < 0xC2 {
            return None;
        }
        return Some((((c & 0x1F) << 6) | (at(s, i + 1) as u32 & 0x3F), 2));
    }
    if avail < 3 || (at(s, i + 2) & 0xC0) != 0x80 {
        return None;
    }
    if c < 0xF0 {
        let v = ((c & 0xF) << 12) | ((at(s, i + 1) as u32 & 0x3F) << 6) | (at(s, i + 2) as u32 & 0x3F);
        if v < 0x800 || (0xD800..0xE000).contains(&v) {
            return None;
        }
        return Some((v, 3));
    }
    if avail < 4 || (at(s, i + 3) & 0xC0) != 0x80 {
        return None;
    }
    let v = ((c & 0x7) << 18) | ((at(s, i + 1) as u32 & 0x3F) << 12) | ((at(s, i + 2) as u32 & 0x3F) << 6) | (at(s, i + 3) as u32 & 0x3F);
    if !(0x10000..0x110000).contains(&v) {
        return None;
    }
    Some((v, 4))
}

/// `IS_CHAR`.
pub fn is_char(c: u32) -> bool {
    if c < 0x100 {
        c == 0x9 || c == 0xA || c == 0xD || c >= 0x20
    } else {
        (0x100..=0xD7FF).contains(&c) || (0xE000..=0xFFFD).contains(&c) || (0x10000..=0x10FFFF).contains(&c)
    }
}

/// Decimal digits of `v`.
pub fn itoa(v: i64) -> Vec<u8> {
    let mut out = Vec::new();
    let neg = v < 0;
    let mut u: u64 = if neg { (v as i128).unsigned_abs() as u64 } else { v as u64 };
    if u == 0 {
        out.push(b'0');
    }
    while u > 0 {
        out.push(b'0' + (u % 10) as u8);
        u /= 10;
    }
    if neg {
        out.push(b'-');
    }
    out.reverse();
    out
}

pub fn cat(parts: &[&[u8]]) -> Vec<u8> {
    let mut v = Vec::new();
    for p in parts {
        v.extend_from_slice(p);
    }
    v
}

/// `xmlStrcasecmp(a, b) == 0` over ASCII.
pub fn eq_ci(a: &[u8], b: &[u8]) -> bool {
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.to_ascii_lowercase() == y.to_ascii_lowercase())
}

// --- the parser ------------------------------------------------------------------------

/// A default attribute (`xmlDefAttr`).
#[derive(Clone)]
pub struct DefAttr {
    pub prefix: Option<Vec<u8>>,
    pub name: Vec<u8>,
    pub value: Vec<u8>,
    pub external: bool,
    pub expanded_size: u64,
}

pub struct Parser<S: Sink> {
    pub sink: S,
    pub inputs: Vec<Input>,
    pub options: u32,
    /// `ctxt->replaceEntities`, `ctxt->keepBlanks`, `ctxt->sax2`, ...
    pub replace_entities: bool,
    pub keep_blanks: bool,
    pub sax2: bool,
    pub html: bool,
    pub max_ampl: u32,
    pub input_id: i32,
    /// `ctxt->nameTab` with the prefix and URI kept by `nameNsPush`.
    pub names: Vec<NameEntry>,
    /// `ctxt->spaceTab` and `ctxt->spaceNr`.
    pub spaces: Vec<i32>,
    pub space_nr: usize,
    /// `ctxt->maxatts`.
    pub maxatts: usize,
    pub nsdb: nsdb::NsDb,
    /// `ctxt->attsDefault`: (element localname, prefix) → its defaults.
    pub atts_default: Vec<((Vec<u8>, Option<Vec<u8>>), Vec<DefAttr>)>,
    /// `ctxt->attsSpecial`: (element, attribute) → type.
    pub atts_special: Vec<((Vec<u8>, Vec<u8>), i32)>,
    pub int_sub_name: Option<Vec<u8>>,
    pub ext_sub_system: Option<Vec<u8>>,
    pub ext_sub_uri: Option<Vec<u8>>,
    pub version: Option<Vec<u8>>,
    pub encoding: Option<Vec<u8>>,
    /// `ctxt->depth`: entity nesting while parsing entity content.
    pub depth: i32,
    /// `ctxt->nbErrors` as seen through the sink is the sink's; this
    /// keeps nothing of it.
    pub instate_eof: bool,
    /// Steps left before the parser stops: a bound on all its loops.
    pub fuel: u64,
}

/// `ctxt->nameTab[i]` and `ctxt->pushTab[i]`.
#[derive(Clone)]
pub struct NameEntry {
    pub name: Vec<u8>,
    pub prefix: Option<Vec<u8>>,
    pub uri: Option<Vec<u8>>,
    pub line: i32,
    pub ns_nr: usize,
}

impl<S: Sink> Parser<S> {
    pub fn new(sink: S, doc: Input) -> Parser<S> {
        let options = sink.options();
        let replace_entities = sink.replace_entities();
        let keep_blanks = sink.keep_blanks();
        let sax2 = sink.sax2();
        let html = sink.html();
        let max_ampl = sink.max_ampl();
        let mut p = Parser {
            sink,
            inputs: Vec::new(),
            options,
            replace_entities,
            keep_blanks,
            sax2,
            html,
            max_ampl,
            input_id: 1,
            names: Vec::new(),
            spaces: vec![-1],
            space_nr: 0,
            maxatts: 0,
            nsdb: nsdb::NsDb::new(0),
            atts_default: Vec::new(),
            atts_special: Vec::new(),
            int_sub_name: None,
            ext_sub_system: None,
            ext_sub_uri: None,
            version: None,
            encoding: None,
            depth: 0,
            instate_eof: false,
            fuel: 0,
        };
        let total = (doc.buf.len() as u64).saturating_add(doc.src.as_ref().map_or(0, |s| s.raw.len() as u64));
        // Every step consumes input or is one of a bounded number around
        // it; entity expansion is bounded by the amplification limit.
        p.fuel = total.saturating_mul(64).saturating_add(1 << 24);
        p.inputs.push(doc);
        p
    }

    // --- the current input ---

    #[inline]
    pub fn inp(&self) -> &Input {
        let n = self.inputs.len();
        &self.inputs[n - 1]
    }

    #[inline]
    pub fn inp_mut(&mut self) -> &mut Input {
        let n = self.inputs.len();
        &mut self.inputs[n - 1]
    }

    /// `CUR`, `RAW`.
    #[inline]
    pub fn cur(&self) -> u8 {
        let i = self.inp();
        at(&i.buf, i.cur)
    }

    /// `NXT(k)`.
    #[inline]
    pub fn nxt(&self, k: usize) -> u8 {
        let i = self.inp();
        at(&i.buf, i.cur.saturating_add(k))
    }

    /// `CMPn(CUR_PTR, ...)`.
    pub fn cmp(&self, s: &[u8]) -> bool {
        let i = self.inp();
        let mut k = 0;
        while k < s.len() {
            if at(&i.buf, i.cur + k) != s[k] {
                return false;
            }
            k += 1;
        }
        true
    }

    /// `ctxt->input->end - ctxt->input->cur`.
    pub fn avail(&self) -> usize {
        let i = self.inp();
        i.buf.len().saturating_sub(i.cur)
    }

    pub fn at_end(&self) -> bool {
        let i = self.inp();
        i.cur >= i.buf.len()
    }

    pub fn stopped(&self) -> bool {
        self.sink.disable_sax() > 1
    }

    /// `!ctxt->disableSAX`.
    pub fn sax_on(&self) -> bool {
        self.sink.disable_sax() == 0
    }

    /// One step of a loop; false when the bound on the parser's work is
    /// reached (the parser then stops, as on a resource limit).
    pub fn step(&mut self) -> bool {
        if self.fuel == 0 {
            if !self.stopped() {
                self.fatal_msg(ERR_RESOURCE_LIMIT, b"Parser step limit exceeded\n");
                self.sink.halt();
            }
            return false;
        }
        self.fuel -= 1;
        true
    }

    pub fn in_pe(&self) -> bool {
        let i = self.inp();
        i.entity.is_some() && (i.etype == INTERNAL_PARAMETER_ENTITY || i.etype == EXTERNAL_PARAMETER_ENTITY)
    }

    pub fn external(&self) -> bool {
        self.sink.in_subset() == 2 || (self.inp().entity.is_some() && self.inp().etype == EXTERNAL_PARAMETER_ENTITY)
    }

    pub fn max_length(&self, normal: usize) -> usize {
        if self.options & PARSE_HUGE != 0 { MAX_HUGE_LENGTH } else { normal }
    }

    /// Tells the sink where the inputs are.
    pub fn sync(&mut self) {
        let mut views: Vec<InputView<'_>> = Vec::with_capacity(self.inputs.len());
        for i in self.inputs.iter() {
            views.push(InputView {
                buf: &i.buf,
                base: i.base,
                cur: i.cur,
                line: i.line,
                col: i.col,
                entity: i.entity,
                encoder: i.src.as_ref().is_some_and(|s| s.enc.is_some()),
                flags: i.flags,
                filename: i.filename.as_deref(),
            });
        }
        self.sink.sync(&views);
    }

    // --- errors (parser.c's wrappers of xmlCtxtErr) ---

    pub fn report(&mut self, domain: i32, code: i32, level: i32, s1: Option<&[u8]>, s2: Option<&[u8]>, s3: Option<&[u8]>, int1: i32, msg: Option<&[u8]>) {
        self.sync();
        let r = Report { domain, code, level, s1, s2, s3, int1, msg };
        self.sink.report(&r);
    }

    /// `xmlFatalErr`.
    pub fn fatal(&mut self, code: i32, info: Option<&[u8]>) {
        let level = if self.html && code == ERR_UNSUPPORTED_ENCODING { LEVEL_ERROR } else { LEVEL_FATAL };
        self.report(FROM_PARSER, code, level, info, None, None, 0, None);
    }

    /// `xmlFatalErrMsg`.
    pub fn fatal_msg(&mut self, code: i32, msg: &[u8]) {
        self.report(FROM_PARSER, code, LEVEL_FATAL, None, None, None, 0, Some(msg));
    }

    /// `xmlFatalErrMsgStr`: `msg` already holds `val`.
    pub fn fatal_str(&mut self, code: i32, msg: &[u8], val: Option<&[u8]>) {
        self.report(FROM_PARSER, code, LEVEL_FATAL, val, None, None, 0, Some(msg));
    }

    /// `xmlFatalErrMsgInt`.
    pub fn fatal_int(&mut self, code: i32, msg: &[u8], val: i32) {
        self.report(FROM_PARSER, code, LEVEL_FATAL, None, None, None, val, Some(msg));
    }

    /// `xmlFatalErrMsgStrIntStr`.
    pub fn fatal_sis(&mut self, code: i32, msg: &[u8], s1: Option<&[u8]>, val: i32, s2: Option<&[u8]>) {
        self.report(FROM_PARSER, code, LEVEL_FATAL, s1, s2, None, val, Some(msg));
    }

    /// `xmlErrMsgStr`.
    pub fn err_str(&mut self, code: i32, msg: &[u8], val: Option<&[u8]>) {
        self.report(FROM_PARSER, code, LEVEL_ERROR, val, None, None, 0, Some(msg));
    }

    /// `xmlWarningMsg`.
    pub fn warning(&mut self, code: i32, msg: &[u8], s1: Option<&[u8]>, s2: Option<&[u8]>) {
        self.report(FROM_PARSER, code, LEVEL_WARNING, s1, s2, None, 0, Some(msg));
    }

    /// `xmlValidityError`.
    pub fn validity_error(&mut self, code: i32, msg: &[u8], s1: Option<&[u8]>, s2: Option<&[u8]>) {
        self.sink.set_valid(false);
        self.report(FROM_DTD, code, LEVEL_ERROR, s1, s2, None, 0, Some(msg));
    }

    /// `xmlNsErr`.
    pub fn ns_err(&mut self, code: i32, msg: &[u8], s1: Option<&[u8]>, s2: Option<&[u8]>, s3: Option<&[u8]>) {
        self.sink.set_ns_well_formed(false);
        self.report(FROM_NAMESPACE, code, LEVEL_ERROR, s1, s2, s3, 0, Some(msg));
    }

    /// `xmlNsWarn`.
    pub fn ns_warn(&mut self, code: i32, msg: &[u8], s1: Option<&[u8]>, s2: Option<&[u8]>, s3: Option<&[u8]>) {
        self.report(FROM_NAMESPACE, code, LEVEL_WARNING, s1, s2, s3, 0, Some(msg));
    }

    /// `xmlErrAttributeDup`.
    pub fn err_attribute_dup(&mut self, prefix: Option<&[u8]>, local: &[u8]) {
        match prefix {
            None => {
                let m = cat(&[b"Attribute ", local, b" redefined\n"]);
                self.report(FROM_PARSER, ERR_ATTRIBUTE_REDEFINED, LEVEL_FATAL, Some(local), None, None, 0, Some(&m));
            }
            Some(p) => {
                let m = cat(&[b"Attribute ", p, b":", local, b" redefined\n"]);
                self.report(FROM_PARSER, ERR_ATTRIBUTE_REDEFINED, LEVEL_FATAL, Some(p), Some(local), None, 0, Some(&m));
            }
        }
    }

    /// `xmlCtxtErrIO` (no URI).
    pub fn err_io(&mut self, code: i32) {
        let level = if code == IO_ENOENT || code == IO_UNKNOWN {
            if self.sink.validate() { LEVEL_ERROR } else { LEVEL_WARNING }
        } else if code == IO_NETWORK_ATTEMPT {
            LEVEL_ERROR
        } else {
            LEVEL_FATAL
        };
        self.report(FROM_IO, code, level, None, None, None, 0, None);
    }

    /// `xmlParserEntityCheck`: whether expanding `extra` more bytes goes
    /// over the amplification limit (and reports it).
    pub fn entity_check(&mut self, extra: u64) -> bool {
        let (ent, consumed) = {
            let i = self.inp();
            (i.entity, i.consumed.saturating_add(i.cur.saturating_sub(0) as u64))
        };
        if let Some(e) = ent {
            if self.sink.ent_info(e).flags & ENT_CHECKED != 0 {
                return false;
            }
        }
        let consumed = consumed.saturating_add(self.sink.sizeentities());
        let size = match ent {
            Some(e) => {
                let v = self.sink.ent_info(e).expanded_size.saturating_add(extra).saturating_add(ENT_FIXED_COST);
                self.sink.ent_set_expanded_size(e, v);
                v
            }
            None => {
                let v = self.sink.sizeentcopy().saturating_add(extra).saturating_add(ENT_FIXED_COST);
                self.sink.set_sizeentcopy(v);
                v
            }
        };
        if self.max_ampl > 0 && size > PARSER_ALLOWED_EXPANSION && (size == u64::MAX || size / self.max_ampl as u64 > consumed) {
            self.fatal_msg(ERR_RESOURCE_LIMIT, b"Maximum entity amplification factor exceeded, see xmlCtxtSetMaxAmplification.\n");
            return true;
        }
        false
    }

    // --- reading (parserInternals.c and parser.c's macros) ---

    /// `xmlParserGrow`.
    pub fn grow_now(&mut self) -> i32 {
        let huge = self.options & PARSE_HUGE != 0;
        let n = self.inputs.len();
        let input = &mut self.inputs[n - 1];
        let cur_end = input.buf.len().saturating_sub(input.cur);
        let cur_base = input.cur.saturating_sub(input.base);
        let src = match input.src.as_mut() {
            None => return 0,
            Some(s) => s,
        };
        if src.enc.is_none() && src.mode == Mode::Memory {
            return 0;
        }
        if src.error != 0 {
            return -1;
        }
        let max = if huge { MAX_HUGE_LENGTH } else { MAX_LOOKUP_LIMIT };
        if cur_base > max {
            self.fatal(ERR_RESOURCE_LIMIT, Some(b"Buffer size limit exceeded, try XML_PARSE_HUGE\n"));
            return -1;
        }
        if cur_end >= INPUT_CHUNK {
            return 0;
        }
        let ret = enc::buffer_grow(&mut input.buf, src, INPUT_CHUNK);
        if ret < 0 {
            let code = src.error;
            self.err_io(code);
        }
        ret
    }

    /// `GROW`.
    #[inline]
    pub fn grow(&mut self) {
        if self.avail() < INPUT_CHUNK {
            self.grow_now();
        }
    }

    /// `SHRINK` (`xmlParserShrink`).
    pub fn shrink(&mut self) {
        let input = self.inp_mut();
        if input.src.is_none() && input.entity.is_none() && input.buf.is_empty() {
            return;
        }
        let used = input.cur.saturating_sub(input.base);
        if used > LINE_LEN {
            input.base = input.cur - LINE_LEN;
        }
    }

    /// `SKIP(n)`: ASCII only, on the line.
    pub fn skip(&mut self, n: usize) {
        {
            let i = self.inp_mut();
            i.cur = i.cur.saturating_add(n);
            i.col = i.col.saturating_add(n as i32);
        }
        if self.cur() == 0 {
            self.grow_now();
        }
    }

    /// `NEXT1`.
    pub fn next1(&mut self) {
        {
            let i = self.inp_mut();
            i.col = i.col.saturating_add(1);
            i.cur = i.cur.saturating_add(1);
        }
        if self.cur() == 0 {
            self.grow_now();
        }
    }

    /// `NEXTL(l)`.
    pub fn nextl(&mut self, l: usize) {
        let i = self.inp_mut();
        if at(&i.buf, i.cur) == b'\n' {
            i.line = i.line.saturating_add(1);
            i.col = 1;
        } else {
            i.col = i.col.saturating_add(1);
        }
        i.cur = i.cur.saturating_add(l);
    }

    /// `SKIPL(n)`.
    pub fn skipl(&mut self, n: usize) {
        let mut k = 0;
        while k < n {
            let i = self.inp_mut();
            if at(&i.buf, i.cur) == b'\n' {
                i.line = i.line.saturating_add(1);
                i.col = 1;
            } else {
                i.col = i.col.saturating_add(1);
            }
            i.cur = i.cur.saturating_add(1);
            k += 1;
        }
        if self.cur() == 0 {
            self.grow_now();
        }
    }

    /// `xmlNextChar` (`NEXT`).
    pub fn next(&mut self) {
        let mut avail = self.avail();
        if avail < INPUT_CHUNK {
            self.grow_now();
            if self.at_end() {
                return;
            }
            avail = self.avail();
        }
        let i = self.inp_mut();
        let p = i.cur;
        let c = at(&i.buf, p);
        if c < 0x80 {
            if c == b'\n' {
                i.cur += 1;
                i.line = i.line.saturating_add(1);
                i.col = 1;
            } else if c == b'\r' {
                i.cur += if at(&i.buf, p + 1) == b'\n' { 2 } else { 1 };
                i.line = i.line.saturating_add(1);
                i.col = 1;
            } else {
                i.cur += 1;
                i.col = i.col.saturating_add(1);
            }
            return;
        }
        i.col = i.col.saturating_add(1);
        let c1 = at(&i.buf, p + 1);
        let ok = 'chk: {
            if avail < 2 || (c1 & 0xC0) != 0x80 {
                break 'chk 0;
            }
            if c < 0xE0 {
                if c < 0xC2 {
                    break 'chk 0;
                }
                break 'chk 2;
            }
            let val = ((c as u32) << 8) | c1 as u32;
            if avail < 3 || (at(&i.buf, p + 2) & 0xC0) != 0x80 {
                break 'chk 0;
            }
            if c < 0xF0 {
                if val < 0xE0A0 || (0xEDA0..0xEE00).contains(&val) {
                    break 'chk 0;
                }
                break 'chk 3;
            }
            if avail < 4 || (at(&i.buf, p + 3) & 0xC0) != 0x80 {
                break 'chk 0;
            }
            if !(0xF090..0xF490).contains(&val) {
                break 'chk 0;
            }
            4
        };
        if ok > 0 {
            i.cur += ok;
            return;
        }
        if i.flags & INPUT_ENCODING_ERROR == 0 {
            self.err_io(ERR_INVALID_ENCODING);
            self.inp_mut().flags |= INPUT_ENCODING_ERROR;
        }
        let i = self.inp_mut();
        i.cur += 1;
    }

    /// `xmlCurrentChar` (`CUR_CHAR`): the character and its length. On
    /// CR LF it moves past the CR, as libxml2 does.
    pub fn current_char(&mut self) -> (u32, usize) {
        let mut avail = self.avail();
        if avail < INPUT_CHUNK {
            self.grow_now();
            avail = self.avail();
        }
        let (c, p, at_end) = {
            let i = self.inp();
            (at(&i.buf, i.cur) as u32, i.cur, i.cur >= i.buf.len())
        };
        if c < 0x80 {
            if c < 0x20 {
                if c == 0x0D {
                    let i = self.inp_mut();
                    if at(&i.buf, p + 1) == b'\n' {
                        i.cur += 1;
                    }
                    return (0x0A, 1);
                }
                if c == 0 {
                    if at_end {
                        return (0, 0);
                    }
                    self.fatal(ERR_INVALID_CHAR, Some(b"Char 0x0 out of allowed range\n"));
                    return (0, 1);
                }
            }
            return (c, 1);
        }
        let b = |k: usize| -> u32 {
            let i = self.inp();
            at(&i.buf, p + k) as u32
        };
        let r: Result<(u32, usize), bool> = 'dec: {
            if avail < 2 {
                break 'dec Err(false);
            }
            if b(1) & 0xC0 != 0x80 {
                break 'dec Err(true);
            }
            if c < 0xE0 {
                if c < 0xC2 {
                    break 'dec Err(true);
                }
                break 'dec Ok((((c & 0x1F) << 6) | (b(1) & 0x3F), 2));
            }
            if avail < 3 {
                break 'dec Err(false);
            }
            if b(2) & 0xC0 != 0x80 {
                break 'dec Err(true);
            }
            if c < 0xF0 {
                let v = ((c & 0xF) << 12) | ((b(1) & 0x3F) << 6) | (b(2) & 0x3F);
                if v < 0x800 || (0xD800..0xE000).contains(&v) {
                    break 'dec Err(true);
                }
                break 'dec Ok((v, 3));
            }
            if avail < 4 {
                break 'dec Err(false);
            }
            if b(3) & 0xC0 != 0x80 {
                break 'dec Err(true);
            }
            let v = ((c & 0x0F) << 18) | ((b(1) & 0x3F) << 12) | ((b(2) & 0x3F) << 6) | (b(3) & 0x3F);
            if !(0x10000..0x110000).contains(&v) {
                break 'dec Err(true);
            }
            Ok((v, 4))
        };
        match r {
            Ok(x) => x,
            Err(false) => (0, 0),
            Err(true) => {
                if self.inp().flags & INPUT_ENCODING_ERROR == 0 {
                    self.err_io(ERR_INVALID_ENCODING);
                    self.inp_mut().flags |= INPUT_ENCODING_ERROR;
                }
                (INVALID_CHAR, 1)
            }
        }
    }

    /// `xmlCurrentCharRecover`.
    pub fn current_char_recover(&mut self) -> (u32, usize) {
        let (c, l) = self.current_char();
        if c == INVALID_CHAR { (0xFFFD, l) } else { (c, l) }
    }

    /// `xmlUTF8MultibyteLen` at the current position.
    pub fn utf8_multibyte_len(&mut self, p: usize, err_msg: &[u8]) -> usize {
        let (c, c1, c2, c3) = {
            let i = self.inp();
            (at(&i.buf, p), at(&i.buf, p + 1), at(&i.buf, p + 2), at(&i.buf, p + 3))
        };
        let r = 'l: {
            if c1 & 0xC0 != 0x80 {
                break 'l 0;
            }
            if c < 0xE0 {
                if c < 0xC2 {
                    break 'l 0;
                }
                break 'l 2;
            }
            if c2 & 0xC0 != 0x80 {
                break 'l 0;
            }
            if c < 0xF0 {
                if c == 0xE0 {
                    if c1 < 0xA0 {
                        break 'l 0;
                    }
                } else if c == 0xED {
                    if c1 >= 0xA0 {
                        break 'l 0;
                    }
                } else if c == 0xEF && c1 == 0xBF && c2 >= 0xBE {
                    break 'l 33;
                }
                break 'l 3;
            }
            if c3 & 0xC0 != 0x80 {
                break 'l 0;
            }
            if c == 0xF0 {
                if c1 < 0x90 {
                    break 'l 0;
                }
            } else if c >= 0xF4 && (c > 0xF4 || c1 >= 0x90) {
                break 'l 0;
            }
            4
        };
        if r == 33 {
            self.fatal_msg(ERR_INVALID_CHAR, err_msg);
            return 3;
        }
        if r == 0 {
            if self.inp().flags & INPUT_ENCODING_ERROR == 0 {
                self.err_io(ERR_INVALID_ENCODING);
                self.inp_mut().flags |= INPUT_ENCODING_ERROR;
            }
        }
        r
    }

    /// `xmlSkipBlankChars` (`SKIP_BLANKS`).
    pub fn skip_blanks(&mut self) -> usize {
        let mut res: usize = 0;
        loop {
            let c = self.cur();
            if !blank(c) {
                break;
            }
            {
                let i = self.inp_mut();
                if c == b'\n' {
                    i.line = i.line.saturating_add(1);
                    i.col = 1;
                } else {
                    i.col = i.col.saturating_add(1);
                }
                i.cur += 1;
            }
            res = res.saturating_add(1);
            if self.cur() == 0 {
                self.grow_now();
            }
        }
        if res > 4 {
            self.grow();
        }
        res
    }

    /// `xmlCtxtPushInput`.
    pub fn push_input(&mut self, input: Input) -> i32 {
        let max = if self.options & PARSE_HUGE != 0 { 40 } else { 20 };
        if self.inputs.len() >= max {
            self.fatal_msg(ERR_RESOURCE_LIMIT, b"Maximum entity nesting depth exceeded");
            return -1;
        }
        self.inputs.push(input);
        self.input_id = self.input_id.saturating_add(1);
        self.sync();
        (self.inputs.len() - 1) as i32
    }

    /// `xmlCtxtPopInput` and free.
    pub fn pop_input(&mut self) {
        if self.inputs.len() > 1 {
            self.inputs.pop();
            self.sync();
        }
    }

    /// `xmlNewEntityInputStream`.
    pub fn entity_input(&mut self, e: Ent) -> Option<Input> {
        let info = self.sink.ent_info(e);
        let mut input = if info.has_content {
            Input::from_bytes(self.sink.ent_content(e))
        } else if info.has_uri {
            let l = self.sink.load_entity(e)?;
            let mut i = Input::from_bytes(Vec::new());
            i.src = Some(Source { raw: l.bytes, delivered: 0, pos: 0, mode: if l.stream { Mode::Stream } else { Mode::Memory }, enc: None, error: 0, eof: false });
            i.filename = l.filename;
            enc::init_buffer(&mut i);
            i
        } else {
            return None;
        };
        input.entity = Some(e);
        input.etype = info.etype;
        Some(input)
    }

    /// `xmlHaltParser`.
    pub fn halt(&mut self) {
        self.sink.halt();
    }
}

// --- xmlSBuf ----------------------------------------------------------------------

/// `xmlSBuf`: a growing string with a length limit and a sticky error.
pub struct SBuf {
    pub mem: Vec<u8>,
    /// `mem != NULL`: something was added (even nothing).
    pub alloc: bool,
    pub max: usize,
    pub code: i32,
}

impl SBuf {
    pub fn new(max: usize) -> SBuf {
        SBuf { mem: Vec::new(), alloc: false, max, code: codes::ERR_OK }
    }

    fn limit(&mut self) {
        if self.code == codes::ERR_OK {
            self.code = codes::ERR_RESOURCE_LIMIT;
        }
    }

    /// `xmlSBufAddString`.
    pub fn add(&mut self, s: &[u8]) {
        if self.max - self.mem.len() < s.len() {
            self.limit();
            return;
        }
        if s.len() >= (u32::MAX as usize) / 2 - self.mem.len() {
            self.limit();
            return;
        }
        self.alloc = true;
        self.mem.extend_from_slice(s);
    }

    /// `xmlSBufAddChar`.
    pub fn add_char(&mut self, c: u32) {
        if self.max - self.mem.len() < 4 {
            self.limit();
            return;
        }
        self.alloc = true;
        push_char(&mut self.mem, c);
    }

    /// `xmlSBufAddReplChar`.
    pub fn add_repl(&mut self) {
        self.add(b"\xEF\xBF\xBD");
    }
}

impl<S: Sink> Parser<S> {
    /// `xmlSBufReportError`.
    pub fn sbuf_report(&mut self, b: &SBuf, msg: &[u8]) {
        if b.code == codes::ERR_NO_MEMORY {
            self.sink.mem_error();
        } else {
            self.fatal(b.code, Some(msg));
        }
    }

    /// `xmlSBufFinish`.
    pub fn sbuf_finish(&mut self, b: SBuf, msg: &[u8]) -> Option<Vec<u8>> {
        if b.code == codes::ERR_OK {
            return Some(b.mem);
        }
        self.sbuf_report(&b, msg);
        None
    }

    /// `xmlSBufCleanup`.
    pub fn sbuf_cleanup(&mut self, b: SBuf, msg: &[u8]) {
        if b.code != codes::ERR_OK {
            self.sbuf_report(&b, msg);
        }
    }
}

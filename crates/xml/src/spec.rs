//! Executable-free specification of XML 1.0 (Fifth Edition) well-formedness
//! for a document in UTF-8, as Verus spec functions.
//!
//! The grammar is written over the input bytes. A successful parse produces
//! a *tape*: the document's markup in order, one token per item, with byte
//! ranges into the input for every name, value and run of text (nothing is
//! copied). `document` is the whole document; every other function takes a
//! position `i` and returns the tape extended with what it recognized and
//! the position just past it, or `None` if the input does not match the
//! grammar (or breaks a well-formedness constraint) at `i`.
//!
//! The element structure is not recursive: `content` is a loop over items
//! with an explicit stack of the open elements, so the spec, like the
//! parser, has no nesting limit. Each step consumes input, which is the
//! termination measure throughout. A few functions contain a guard of the
//! form `if !(i < e <= s.len()) { None }` before continuing: it never fails
//! (each step moves forward and stays within the input), and is there so
//! that termination is syntactic.
//!
//! Production numbers `[n]` and constraint names (WFC) are those of the
//! XML 1.0 Recommendation, Fifth Edition.
use crate::chars::*;
#[cfg(verus_keep_ghost)]
pub use verilith_core::num::{digits_end, is_digit};
#[cfg(verus_keep_ghost)]
pub use verilith_core::utf8::utf8_encode;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Tape
// ---------------------------------------------------------------------------

/// One item of a document. Spans `start..end` are byte ranges of the input.
pub enum XTok {
    /// `<?xml version="..." ...?>`: the version number's span, and the
    /// standalone declaration (0 absent, 1 `yes`, 2 `no`).
    XmlDecl { start: int, end: int, sd: int },
    /// The encoding name in the XML declaration.
    Encoding { start: int, end: int },
    /// `<!DOCTYPE name`: the root element type's name.
    Doctype { start: int, end: int },
    /// The end of the document type declaration.
    DoctypeEnd,
    /// A public identifier (the literal's contents).
    PubId { start: int, end: int },
    /// A system identifier (the literal's contents).
    SysId { start: int, end: int },
    /// `<!ELEMENT name ...>` (the content model is checked, not recorded).
    ElementDecl { start: int, end: int },
    /// `<!ATTLIST name`: the element type's name; its `AttDef`s follow.
    AttlistDecl { start: int, end: int },
    /// An attribute definition: the name and the type (see `att_type`).
    AttDef { start: int, end: int, ty: int },
    /// The default of the `AttDef` before it: `kind` 1 `#REQUIRED`,
    /// 2 `#IMPLIED`, 3 `#FIXED` value, 4 value; the value's raw span (between
    /// the quotes), and how many general entities were declared before it.
    AttDefault { start: int, end: int, kind: int, nents: int },
    /// `<!ENTITY name` (or `<!ENTITY % name`); its definition follows: an
    /// `EntityValue`, or a `SysId` (after a `PubId`), then perhaps `NData`.
    EntityDecl { start: int, end: int, pe: bool },
    /// The literal entity value, raw (between the quotes).
    EntityValue { start: int, end: int },
    /// `NDATA name`: the entity is unparsed.
    NData { start: int, end: int },
    /// `<!NOTATION name`; a `PubId` and/or a `SysId` follow.
    NotationDecl { start: int, end: int },
    /// `%name;` between declarations of the internal subset (not read).
    PERef { start: int, end: int },
    /// A comment's text, between `<!--` and `-->`.
    Comment { start: int, end: int },
    /// A processing instruction's target; its `PIData` follows.
    PI { start: int, end: int },
    /// A processing instruction's data, after the white space following
    /// the target.
    PIData { start: int, end: int },
    /// A start tag (or an empty-element tag): the element type's name, and
    /// the index in the tape of the `ETag` that closes the element, so a
    /// reader can skip it in one step. Its `Attr`/`AttVal` pairs follow.
    STag { start: int, end: int, close: int },
    /// An attribute's name.
    Attr { start: int, end: int },
    /// An attribute's value, raw (between the quotes). `plain`: it holds no
    /// reference and no tab, line feed or carriage return, so its
    /// normalized value is the raw bytes.
    AttVal { start: int, end: int, plain: bool },
    /// The end of an element (an end tag, or the end of an empty-element
    /// tag).
    ETag,
    /// Character data. `cr`: it holds a carriage return (line-end
    /// normalization changes it).
    Text { start: int, end: int, cr: bool },
    /// The text of a CDATA section.
    CData { start: int, end: int, cr: bool },
    /// A character reference, or a reference to one of the five predefined
    /// entities: where it starts, and the character.
    CharRef { pos: int, cp: int },
    /// Any other entity reference: the entity's name.
    EntRef { start: int, end: int },
}

// ---------------------------------------------------------------------------
// Entities and the environment of the content
// ---------------------------------------------------------------------------

pub enum EKind {
    /// An internal entity: its literal value's raw span.
    Internal { start: int, end: int },
    /// An external parsed entity (not read).
    External,
    /// An unparsed entity (`NDATA`).
    Unparsed,
}

/// A general entity declaration that was processed.
pub struct Ent {
    pub name: Seq<u8>,
    pub kind: EKind,
}

/// The internal subset so far: the general entities processed, in order;
/// the names of the parameter entities declared; whether a parameter
/// entity reference was seen; and whether the document is standalone.
pub struct DtdSt {
    pub ents: Seq<Ent>,
    pub pes: Seq<Seq<u8>>,
    pub pe_seen: bool,
    pub sa: bool,
}

/// What the content of the document is checked against: the general
/// entities, and whether the WFC "Entity Declared" applies (§4.1): in a
/// document without a DTD, or whose DTD is only an internal subset
/// without parameter entity references, or that is standalone.
pub struct Env {
    pub ents: Seq<Ent>,
    pub wfc: bool,
    /// Per entity: a reference to it may appear in an attribute value
    /// (`ent_oka`).
    pub oka: Seq<bool>,
    /// Per entity: a reference to it may appear in content (`ent_okc`).
    pub okc: Seq<bool>,
}

/// The first processed declaration of the general entity `name` (§4.2:
/// the first declaration is binding).
pub open spec fn find_ent(ents: Seq<Ent>, name: Seq<u8>) -> Option<int>
    decreases ents.len(),
{
    if ents.len() == 0 {
        None
    } else {
        match find_ent(ents.drop_last(), name) {
            Some(j) => Some(j),
            None => if ents.last().name == name {
                Some(ents.len() - 1)
            } else {
                None
            },
        }
    }
}

pub open spec fn no_dtd() -> Env {
    Env { ents: Seq::empty(), wfc: true, oka: Seq::empty(), okc: Seq::empty() }
}

pub open spec fn dtd_init(sa: bool) -> DtdSt {
    DtdSt { ents: Seq::empty(), pes: Seq::empty(), pe_seen: false, sa }
}

/// The environment after the internal subset `st`: the entities, whether
/// "Entity Declared" applies, and which entities may be referred to where.
pub open spec fn env_of(s: Seq<u8>, st: DtdSt, ext: bool) -> Env {
    let wfc = (!ext && !st.pe_seen) || st.sa;
    let oka = oka_seq(s, st.ents, wfc, ENT_DEPTH as nat);
    Env { ents: st.ents, wfc, oka, okc: okc_seq(s, st.ents, wfc, oka, ENT_DEPTH as nat) }
}

// ---------------------------------------------------------------------------
// Lexical helpers
// ---------------------------------------------------------------------------

/// `s[i] == c`.
pub open spec fn byte_is(s: Seq<u8>, i: int, c: u8) -> bool {
    0 <= i < s.len() && s[i] == c
}

/// `s[i..]` starts with `lit`.
pub open spec fn has_lit(s: Seq<u8>, i: int, lit: Seq<u8>) -> bool {
    0 <= i && i + lit.len() <= s.len() && s.subrange(i, i + lit.len()) == lit
}

/// The first byte at or after `i` that is not white space.
pub open spec fn ws_end(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_ws(s[i]) {
        ws_end(s, i + 1)
    } else {
        i
    }
}

pub open spec fn quote(c: u8) -> bool {
    c == 0x22 || c == 0x27
}

/// Eq ::= S? '=' S?   [25]
pub open spec fn eq_end(s: Seq<u8>, i: int) -> Option<int> {
    let j = ws_end(s, i);
    if byte_is(s, j, 0x3D) {
        Some(ws_end(s, j + 1))
    } else {
        None
    }
}

/// Whether `s[a..b]` contains a carriage return.
pub open spec fn has_cr(s: Seq<u8>, a: int, b: int) -> bool {
    exists|k: int| a <= k < b && s[k] == 0x0D
}

// Literals.
pub open spec fn lit_xmldecl() -> Seq<u8> { seq![0x3Cu8, 0x3F, 0x78, 0x6D, 0x6C] }  // <?xml
pub open spec fn lit_version() -> Seq<u8> { seq![0x76u8, 0x65, 0x72, 0x73, 0x69, 0x6F, 0x6E] }  // version
pub open spec fn lit_encoding() -> Seq<u8> { seq![0x65u8, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67] }  // encoding
pub open spec fn lit_standalone() -> Seq<u8> { seq![0x73u8, 0x74, 0x61, 0x6E, 0x64, 0x61, 0x6C, 0x6F, 0x6E, 0x65] }  // standalone
pub open spec fn lit_yes() -> Seq<u8> { seq![0x79u8, 0x65, 0x73] }  // yes
pub open spec fn lit_no() -> Seq<u8> { seq![0x6Eu8, 0x6F] }  // no
pub open spec fn lit_pi_end() -> Seq<u8> { seq![0x3Fu8, 0x3E] }  // ?>
pub open spec fn lit_comment() -> Seq<u8> { seq![0x3Cu8, 0x21, 0x2D, 0x2D] }  // <!--
pub open spec fn lit_cdata() -> Seq<u8> { seq![0x3Cu8, 0x21, 0x5B, 0x43, 0x44, 0x41, 0x54, 0x41, 0x5B] }  // <![CDATA[
pub open spec fn lit_cdata_end() -> Seq<u8> { seq![0x5Du8, 0x5D, 0x3E] }  // ]]>
pub open spec fn lit_pi() -> Seq<u8> { seq![0x3Cu8, 0x3F] }  // <?
pub open spec fn lit_empty_end() -> Seq<u8> { seq![0x2Fu8, 0x3E] }  // />
pub open spec fn lit_doctype() -> Seq<u8> { seq![0x3Cu8, 0x21, 0x44, 0x4F, 0x43, 0x54, 0x59, 0x50, 0x45] }  // <!DOCTYPE
pub open spec fn lit_system() -> Seq<u8> { seq![0x53u8, 0x59, 0x53, 0x54, 0x45, 0x4D] }  // SYSTEM
pub open spec fn lit_public() -> Seq<u8> { seq![0x50u8, 0x55, 0x42, 0x4C, 0x49, 0x43] }  // PUBLIC
pub open spec fn lit_element() -> Seq<u8> { seq![0x3Cu8, 0x21, 0x45, 0x4C, 0x45, 0x4D, 0x45, 0x4E, 0x54] }  // <!ELEMENT
pub open spec fn lit_attlist() -> Seq<u8> { seq![0x3Cu8, 0x21, 0x41, 0x54, 0x54, 0x4C, 0x49, 0x53, 0x54] }  // <!ATTLIST
pub open spec fn lit_entity() -> Seq<u8> { seq![0x3Cu8, 0x21, 0x45, 0x4E, 0x54, 0x49, 0x54, 0x59] }  // <!ENTITY
pub open spec fn lit_notation() -> Seq<u8> { seq![0x3Cu8, 0x21, 0x4E, 0x4F, 0x54, 0x41, 0x54, 0x49, 0x4F, 0x4E] }  // <!NOTATION
pub open spec fn lit_ndata() -> Seq<u8> { seq![0x4Eu8, 0x44, 0x41, 0x54, 0x41] }  // NDATA
pub open spec fn lit_empty() -> Seq<u8> { seq![0x45u8, 0x4D, 0x50, 0x54, 0x59] }  // EMPTY
pub open spec fn lit_any() -> Seq<u8> { seq![0x41u8, 0x4E, 0x59] }  // ANY
pub open spec fn lit_pcdata() -> Seq<u8> { seq![0x23u8, 0x50, 0x43, 0x44, 0x41, 0x54, 0x41] }  // #PCDATA
pub open spec fn lit_required() -> Seq<u8> { seq![0x23u8, 0x52, 0x45, 0x51, 0x55, 0x49, 0x52, 0x45, 0x44] }  // #REQUIRED
pub open spec fn lit_implied() -> Seq<u8> { seq![0x23u8, 0x49, 0x4D, 0x50, 0x4C, 0x49, 0x45, 0x44] }  // #IMPLIED
pub open spec fn lit_fixed() -> Seq<u8> { seq![0x23u8, 0x46, 0x49, 0x58, 0x45, 0x44] }  // #FIXED
pub open spec fn lit_cdata_ty() -> Seq<u8> { seq![0x43u8, 0x44, 0x41, 0x54, 0x41] }  // CDATA
pub open spec fn lit_idrefs() -> Seq<u8> { seq![0x49u8, 0x44, 0x52, 0x45, 0x46, 0x53] }  // IDREFS
pub open spec fn lit_idref() -> Seq<u8> { seq![0x49u8, 0x44, 0x52, 0x45, 0x46] }  // IDREF
pub open spec fn lit_id() -> Seq<u8> { seq![0x49u8, 0x44] }  // ID
pub open spec fn lit_entities() -> Seq<u8> { seq![0x45u8, 0x4E, 0x54, 0x49, 0x54, 0x49, 0x45, 0x53] }  // ENTITIES
pub open spec fn lit_entity_ty() -> Seq<u8> { seq![0x45u8, 0x4E, 0x54, 0x49, 0x54, 0x59] }  // ENTITY
pub open spec fn lit_nmtokens() -> Seq<u8> { seq![0x4Eu8, 0x4D, 0x54, 0x4F, 0x4B, 0x45, 0x4E, 0x53] }  // NMTOKENS
pub open spec fn lit_nmtoken() -> Seq<u8> { seq![0x4Eu8, 0x4D, 0x54, 0x4F, 0x4B, 0x45, 0x4E] }  // NMTOKEN
pub open spec fn lit_notation_ty() -> Seq<u8> { seq![0x4Eu8, 0x4F, 0x54, 0x41, 0x54, 0x49, 0x4F, 0x4E] }  // NOTATION

// ---------------------------------------------------------------------------
// References
// ---------------------------------------------------------------------------

pub open spec fn is_hex(c: u8) -> bool {
    (0x30 <= c <= 0x39) || (0x41 <= c <= 0x46) || (0x61 <= c <= 0x66)
}

pub open spec fn hex_val(c: u8) -> int {
    if 0x30 <= c <= 0x39 {
        c - 0x30
    } else if 0x41 <= c <= 0x46 {
        c - 0x41 + 10
    } else {
        c - 0x61 + 10
    }
}

/// The end of the run of hex digits at `i`.
pub open spec fn hex_end(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_hex(s[i]) {
        hex_end(s, i + 1)
    } else {
        i
    }
}

/// The value of the hex digits `s[a..b]`.
pub open spec fn hexv(s: Seq<u8>, a: int, b: int) -> int
    decreases b - a,
{
    if b <= a {
        0
    } else {
        hexv(s, a, b - 1) * 16 + hex_val(s[b - 1])
    }
}

/// The value of the decimal digits `s[a..b]`.
pub open spec fn decv(s: Seq<u8>, a: int, b: int) -> int
    decreases b - a,
{
    if b <= a {
        0
    } else {
        decv(s, a, b - 1) * 10 + (s[b - 1] - 0x30)
    }
}

/// CharRef ::= '&#' [0-9]+ ';' | '&#x' [0-9a-fA-F]+ ';'   [66]
/// with WFC: Legal Character. `s[i..i + 2]` is `&#`. Returns the
/// character and the position after the `;`.
pub open spec fn charref(s: Seq<u8>, i: int) -> Option<(int, int)> {
    if byte_is(s, i + 2, 0x78) {
        let d = hex_end(s, i + 3);
        if d > i + 3 && byte_is(s, d, 0x3B) && is_char(hexv(s, i + 3, d)) {
            Some((hexv(s, i + 3, d), d + 1))
        } else {
            None
        }
    } else {
        let d = digits_end(s, i + 2);
        if d > i + 2 && byte_is(s, d, 0x3B) && is_char(decv(s, i + 2, d)) {
            Some((decv(s, i + 2, d), d + 1))
        } else {
            None
        }
    }
}

/// The predefined entities `lt`, `gt`, `amp`, `apos` and `quot` (§4.6),
/// by the name `s[a..b]`.
pub open spec fn predef(s: Seq<u8>, a: int, b: int) -> Option<int> {
    let n = s.subrange(a, b);
    if n == seq![0x6Cu8, 0x74] {
        Some(0x3C)
    } else if n == seq![0x67u8, 0x74] {
        Some(0x3E)
    } else if n == seq![0x61u8, 0x6D, 0x70] {
        Some(0x26)
    } else if n == seq![0x61u8, 0x70, 0x6F, 0x73] {
        Some(0x27)
    } else if n == seq![0x71u8, 0x75, 0x6F, 0x74] {
        Some(0x22)
    } else {
        None
    }
}

/// Reference ::= EntityRef | CharRef   [67]; EntityRef ::= '&' Name ';'
/// [68]. The syntax only: `s[i]` is `&`; the position after the `;`.
pub open spec fn ref_syntax(s: Seq<u8>, i: int) -> Option<int> {
    if byte_is(s, i + 1, 0x23) {
        match charref(s, i) {
            Some((_, e)) => Some(e),
            None => None,
        }
    } else {
        let n = name_end(s, i + 1);
        if n > i + 1 && byte_is(s, n, 0x3B) {
            Some(n + 1)
        } else {
            None
        }
    }
}

/// A reference in an attribute value at `i` (`s[i]` is `&`). With an
/// environment, the entity must also be declared where the WFC "Entity
/// Declared" applies, not external (WFC: No External Entity References),
/// not unparsed (WFC: Parsed Entity), and, if internal, one whose
/// replacement text may appear in an attribute value (`oka`).
pub open spec fn att_ref(s: Seq<u8>, i: int, env: Option<Env>) -> Option<int> {
    if byte_is(s, i + 1, 0x23) {
        match charref(s, i) {
            Some((_, e)) => Some(e),
            None => None,
        }
    } else {
        let n = name_end(s, i + 1);
        if !(n > i + 1 && byte_is(s, n, 0x3B)) {
            None
        } else if predef(s, i + 1, n) is Some {
            Some(n + 1)
        } else {
            match env {
                None => Some(n + 1),
                Some(env) => match find_ent(env.ents, s.subrange(i + 1, n)) {
                    Some(j) => match env.ents[j].kind {
                        EKind::Internal { .. } => if 0 <= j < env.oka.len() && env.oka[j] {
                            Some(n + 1)
                        } else {
                            None
                        },
                        _ => None,
                    },
                    None => if env.wfc {
                        None
                    } else {
                        Some(n + 1)
                    },
                },
            }
        }
    }
}

/// A reference in content at `i` (`s[i]` is `&`): the token for it and
/// the position after it. WFC: Entity Declared, Parsed Entity; an internal
/// entity's replacement text must be well-formed content (`okc`). An
/// external entity is not read.
pub open spec fn content_ref(s: Seq<u8>, i: int, env: Env) -> Option<(XTok, int)> {
    if byte_is(s, i + 1, 0x23) {
        match charref(s, i) {
            Some((c, e)) => Some((XTok::CharRef { pos: i, cp: c }, e)),
            None => None,
        }
    } else {
        let n = name_end(s, i + 1);
        if !(n > i + 1 && byte_is(s, n, 0x3B)) {
            None
        } else {
            match predef(s, i + 1, n) {
                Some(c) => Some((XTok::CharRef { pos: i, cp: c }, n + 1)),
                None => match find_ent(env.ents, s.subrange(i + 1, n)) {
                    Some(j) => match env.ents[j].kind {
                        EKind::Unparsed => None,
                        EKind::External => Some((XTok::EntRef { start: i + 1, end: n }, n + 1)),
                        EKind::Internal { .. } => if 0 <= j < env.okc.len() && env.okc[j] {
                            Some((XTok::EntRef { start: i + 1, end: n }, n + 1))
                        } else {
                            None
                        },
                    },
                    None => if env.wfc {
                        None
                    } else {
                        Some((XTok::EntRef { start: i + 1, end: n }, n + 1))
                    },
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Literals and attribute values
// ---------------------------------------------------------------------------

/// AttValue ::= '"' ([^<&"] | Reference)* '"' | "'" ([^<&'] | Reference)* "'"
/// [10], from `i` (just past the opening quote `q`) to the closing quote,
/// whose position is returned. WFC: No < in Attribute Values.
pub open spec fn att_chars(s: Seq<u8>, i: int, q: u8, env: Option<Env>) -> Option<int>
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        None
    } else if s[i] == q {
        Some(i)
    } else if s[i] == 0x3C {
        None
    } else if s[i] == 0x26 {
        match att_ref(s, i, env) {
            None => None,
            Some(e) => if i < e <= s.len() {
                att_chars(s, e, q, env)
            } else {
                None
            },
        }
    } else {
        att_chars(s, i + 1, q, env)
    }
}

/// Whether the raw value `s[a..b]` is its own normalized value (§3.3.3): no
/// reference, and no white space other than the space.
pub open spec fn att_plain(s: Seq<u8>, a: int, b: int) -> bool {
    forall|k: int| a <= k < b ==> s[k] != 0x26 && s[k] != 0x09 && s[k] != 0x0A && s[k] != 0x0D
}

/// EntityValue in the internal subset [9], from `i` (just past the opening
/// quote `q`); the position after the closing quote. A `%` is a parameter
/// entity reference, which the internal subset does not allow inside a
/// declaration (WFC: PEs in Internal Subset); references are checked for
/// syntax only (they are bypassed, §4.4.7).
pub open spec fn ent_value_end(s: Seq<u8>, i: int, q: u8) -> Option<int>
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        None
    } else if s[i] == q {
        Some(i + 1)
    } else if s[i] == 0x25 {
        None
    } else if s[i] == 0x26 {
        match ref_syntax(s, i) {
            None => None,
            Some(e) => if i < e <= s.len() {
                ent_value_end(s, e, q)
            } else {
                None
            },
        }
    } else {
        ent_value_end(s, i + 1, q)
    }
}

/// The end of a quoted literal whose contents are any characters but the
/// quote `q` (SystemLiteral [11]); `i` is just past the opening quote.
pub open spec fn lit_end(s: Seq<u8>, i: int, q: u8) -> Option<int>
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        None
    } else if s[i] == q {
        Some(i + 1)
    } else {
        lit_end(s, i + 1, q)
    }
}

/// PubidLiteral ::= '"' PubidChar* '"' | "'" (PubidChar - "'")* "'"   [12]
pub open spec fn pubid_end(s: Seq<u8>, i: int, q: u8) -> Option<int>
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        None
    } else if s[i] == q {
        Some(i + 1)
    } else if pubid_char(s[i]) {
        pubid_end(s, i + 1, q)
    } else {
        None
    }
}

/// A SystemLiteral at `i`: the position after it.
pub open spec fn sys_lit(s: Seq<u8>, i: int) -> Option<int> {
    if 0 <= i < s.len() && quote(s[i]) {
        lit_end(s, i + 1, s[i])
    } else {
        None
    }
}

pub open spec fn pubid_lit(s: Seq<u8>, i: int) -> Option<int> {
    if 0 <= i < s.len() && quote(s[i]) {
        pubid_end(s, i + 1, s[i])
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Comments, processing instructions, CDATA sections, character data
// ---------------------------------------------------------------------------

/// Comment ::= '<!--' ((Char - '-') | ('-' (Char - '-')))* '-->'   [15]
/// From `i`, just past `<!--`: the position after `-->`. A `--` that does
/// not end the comment is an error, and so is a `-` just before `-->`.
pub open spec fn comment_end(s: Seq<u8>, i: int) -> Option<int>
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        None
    } else if s[i] == 0x2D && byte_is(s, i + 1, 0x2D) {
        if byte_is(s, i + 2, 0x3E) {
            Some(i + 3)
        } else {
            None
        }
    } else {
        comment_end(s, i + 1)
    }
}

/// A comment at `i` (`s[i..]` starts with `<!--`).
pub open spec fn comment(s: Seq<u8>, i: int, tape: Seq<XTok>) -> Option<(Seq<XTok>, int)> {
    match comment_end(s, i + 4) {
        Some(e) => Some((tape.push(XTok::Comment { start: i + 4, end: e - 3 }), e)),
        None => None,
    }
}

/// The position after the first `?>` at or after `i`.
pub open spec fn pi_end(s: Seq<u8>, i: int) -> Option<int>
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        None
    } else if s[i] == 0x3F && byte_is(s, i + 1, 0x3E) {
        Some(i + 2)
    } else {
        pi_end(s, i + 1)
    }
}

/// The name `s[a..b]` is `xml` in any case (reserved, [17]).
pub open spec fn xml_name(s: Seq<u8>, a: int, b: int) -> bool {
    b == a + 3 && (s[a] == 0x78 || s[a] == 0x58) && (s[a + 1] == 0x6D || s[a + 1] == 0x4D) && (s[a + 2]
        == 0x6C || s[a + 2] == 0x4C)
}

/// PI ::= '<?' PITarget (S (Char* - (Char* '?>' Char*)))? '?>'   [16]
/// PITarget ::= Name - (('X' | 'x') ('M' | 'm') ('L' | 'l'))   [17]
/// At `i` (`s[i..]` starts with `<?`).
pub open spec fn pi(s: Seq<u8>, i: int, tape: Seq<XTok>) -> Option<(Seq<XTok>, int)> {
    let n = name_end(s, i + 2);
    if n == i + 2 || xml_name(s, i + 2, n) {
        None
    } else if has_lit(s, n, lit_pi_end()) {
        Some((tape.push(XTok::PI { start: i + 2, end: n }).push(XTok::PIData { start: n, end: n }), n + 2))
    } else if 0 <= n < s.len() && is_ws(s[n]) {
        let d = ws_end(s, n);
        match pi_end(s, d) {
            Some(e) => Some(
                (tape.push(XTok::PI { start: i + 2, end: n }).push(XTok::PIData { start: d, end: e - 2 }), e),
            ),
            None => None,
        }
    } else {
        None
    }
}

/// The position after the first `]]>` at or after `i` (CDSect [18]).
pub open spec fn cdata_end(s: Seq<u8>, i: int) -> Option<int>
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        None
    } else if has_lit(s, i, lit_cdata_end()) {
        Some(i + 3)
    } else {
        cdata_end(s, i + 1)
    }
}

/// CharData ::= [^<&]* - ([^<&]* ']]>' [^<&]*)   [14]
/// The end of the character data at `i`, or `None` if it contains `]]>`.
pub open spec fn text_end(s: Seq<u8>, i: int) -> Option<int>
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) || s[i] == 0x3C || s[i] == 0x26 {
        Some(i)
    } else if has_lit(s, i, lit_cdata_end()) {
        None
    } else {
        text_end(s, i + 1)
    }
}

/// Misc ::= Comment | PI | S   [27], repeated: the position after them.
pub open spec fn misc(s: Seq<u8>, i: int, tape: Seq<XTok>) -> Option<(Seq<XTok>, int)>
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if has_lit(s, j, lit_comment()) {
        match comment(s, j, tape) {
            None => None,
            Some((t, e)) => if i < e <= s.len() {
                misc(s, e, t)
            } else {
                None
            },
        }
    } else if has_lit(s, j, lit_pi()) {
        match pi(s, j, tape) {
            None => None,
            Some((t, e)) => if i < e <= s.len() {
                misc(s, e, t)
            } else {
                None
            },
        }
    } else {
        Some((tape, j))
    }
}

// ---------------------------------------------------------------------------
// The XML declaration
// ---------------------------------------------------------------------------

/// VersionInfo ::= S 'version' Eq ("'" VersionNum "'" | '"' VersionNum '"')
/// [24], VersionNum ::= '1.' [0-9]+ [26], from `i`: the end and the
/// number's span.
pub open spec fn version_info(s: Seq<u8>, i: int) -> Option<(int, int, int)> {
    let j = ws_end(s, i);
    if !(j > i && has_lit(s, j, lit_version())) {
        None
    } else {
        match eq_end(s, j + 7) {
            None => None,
            Some(k) => if 0 <= k < s.len() && quote(s[k]) && byte_is(s, k + 1, 0x31) && byte_is(s, k + 2, 0x2E) {
                let d = digits_end(s, k + 3);
                if d > k + 3 && byte_is(s, d, s[k]) {
                    Some((d + 1, k + 1, d))
                } else {
                    None
                }
            } else {
                None
            },
        }
    }
}

/// [A-Za-z0-9._] | '-'
pub open spec fn enc_char(c: u8) -> bool {
    (0x41 <= c <= 0x5A) || (0x61 <= c <= 0x7A) || (0x30 <= c <= 0x39) || c == 0x2E || c == 0x5F || c == 0x2D
}

pub open spec fn enc_rest(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if 0 <= i < s.len() && enc_char(s[i]) {
        enc_rest(s, i + 1)
    } else {
        i
    }
}

/// The encodings this processor reads: the two every processor must
/// (§4.3.3), and the two others expat reads natively.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Enc {
    Utf8,
    Utf16,
    Latin1,
    Ascii,
}

/// ASCII lower case.
pub open spec fn lower(c: u8) -> u8 {
    if 0x41 <= c <= 0x5A {
        (c + 0x20) as u8
    } else {
        c
    }
}

/// `s[a..b]` is `lit`, ignoring ASCII case.
pub open spec fn ci_eq(s: Seq<u8>, a: int, b: int, lit: Seq<u8>) -> bool {
    b - a == lit.len() && forall|k: int| 0 <= k < lit.len() ==> lower(#[trigger] s[a + k]) == lower(lit[k])
}

pub open spec fn lit_utf8() -> Seq<u8> { seq![0x55u8, 0x54, 0x46, 0x2D, 0x38] }  // UTF-8
pub open spec fn lit_utf16() -> Seq<u8> { seq![0x55u8, 0x54, 0x46, 0x2D, 0x31, 0x36] }  // UTF-16
pub open spec fn lit_latin1() -> Seq<u8> { seq![0x49u8, 0x53, 0x4F, 0x2D, 0x38, 0x38, 0x35, 0x39, 0x2D, 0x31] }  // ISO-8859-1
pub open spec fn lit_ascii() -> Seq<u8> { seq![0x55u8, 0x53, 0x2D, 0x41, 0x53, 0x43, 0x49, 0x49] }  // US-ASCII

/// The encoding name `s[a..b]` names `enc`, in any case. A document's
/// declaration must name the encoding it is in (§4.3.3).
pub open spec fn enc_name_ok(s: Seq<u8>, a: int, b: int, enc: Enc) -> bool {
    match enc {
        Enc::Utf8 => ci_eq(s, a, b, lit_utf8()),
        Enc::Utf16 => ci_eq(s, a, b, lit_utf16()),
        Enc::Latin1 => ci_eq(s, a, b, lit_latin1()),
        Enc::Ascii => ci_eq(s, a, b, lit_ascii()),
    }
}

/// EncodingDecl ::= S 'encoding' Eq ('"' EncName '"' | "'" EncName "'")
/// [80], EncName ::= [A-Za-z] ([A-Za-z0-9._] | '-')* [81], at `j` (on
/// `encoding`), whatever the name: the end and the name's span.
pub open spec fn enc_span(s: Seq<u8>, j: int) -> Option<(int, int, int)> {
    match eq_end(s, j + 8) {
        None => None,
        Some(k) => if 0 <= k < s.len() && quote(s[k]) && 0 <= k + 1 < s.len() && ((0x41 <= s[k + 1] <= 0x5A)
            || (0x61 <= s[k + 1] <= 0x7A)) {
            let n = enc_rest(s, k + 2);
            if byte_is(s, n, s[k]) {
                Some((n + 1, k + 1, n))
            } else {
                None
            }
        } else {
            None
        },
    }
}

/// The encoding declaration at `j`, which must name `enc`.
pub open spec fn encoding_decl(s: Seq<u8>, j: int, enc: Enc) -> Option<(int, int, int)> {
    match enc_span(s, j) {
        Some((e, a, b)) => if enc_name_ok(s, a, b, enc) {
            Some((e, a, b))
        } else {
            None
        },
        None => None,
    }
}

/// SDDecl ::= S 'standalone' Eq (("'" ('yes' | 'no') "'") | ('"' ('yes' | 'no') '"'))
/// [32], at `j` (on `standalone`): the end, and 1 for `yes`, 2 for `no`.
pub open spec fn sd_decl(s: Seq<u8>, j: int) -> Option<(int, int)> {
    match eq_end(s, j + 10) {
        None => None,
        Some(k) => if 0 <= k < s.len() && quote(s[k]) {
            if has_lit(s, k + 1, lit_yes()) && byte_is(s, k + 4, s[k]) {
                Some((k + 5, 1))
            } else if has_lit(s, k + 1, lit_no()) && byte_is(s, k + 3, s[k]) {
                Some((k + 4, 2))
            } else {
                None
            }
        } else {
            None
        },
    }
}

/// XMLDecl ::= '<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'   [23]
/// At `i`: the tape, the end and the standalone declaration.
pub open spec fn xmldecl(s: Seq<u8>, i: int, enc: Enc) -> Option<(Seq<XTok>, int, int)> {
    match version_info(s, i + 5) {
        None => None,
        Some((v, va, vb)) => {
            let j = ws_end(s, v);
            let er = if j > v && has_lit(s, j, lit_encoding()) {
                encoding_decl(s, j, enc)
            } else {
                Some((v, -1, -1))
            };
            match er {
                None => None,
                Some((e, ea, eb)) => {
                    let k = ws_end(s, e);
                    let sr = if k > e && has_lit(s, k, lit_standalone()) {
                        sd_decl(s, k)
                    } else {
                        Some((e, 0))
                    };
                    match sr {
                        None => None,
                        Some((d, sd)) => {
                            let m = ws_end(s, d);
                            if has_lit(s, m, lit_pi_end()) {
                                let t = seq![XTok::XmlDecl { start: va, end: vb, sd }];
                                let t2 = if ea >= 0 {
                                    t.push(XTok::Encoding { start: ea, end: eb })
                                } else {
                                    t
                                };
                                Some((t2, m + 2, sd))
                            } else {
                                None
                            }
                        },
                    }
                },
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The document type declaration
// ---------------------------------------------------------------------------

/// ExternalID ::= 'SYSTEM' S SystemLiteral | 'PUBLIC' S PubidLiteral S SystemLiteral
/// [75], at `k`.
pub open spec fn external_id(s: Seq<u8>, k: int, tape: Seq<XTok>) -> Option<(Seq<XTok>, int)> {
    if has_lit(s, k, lit_system()) {
        let j = ws_end(s, k + 6);
        if j == k + 6 {
            None
        } else {
            match sys_lit(s, j) {
                Some(e) => Some((tape.push(XTok::SysId { start: j + 1, end: e - 1 }), e)),
                None => None,
            }
        }
    } else if has_lit(s, k, lit_public()) {
        let j = ws_end(s, k + 6);
        if j == k + 6 {
            None
        } else {
            match pubid_lit(s, j) {
                None => None,
                Some(e) => {
                    let m = ws_end(s, e);
                    if m == e {
                        None
                    } else {
                        match sys_lit(s, m) {
                            Some(f) => Some(
                                (tape.push(XTok::PubId { start: j + 1, end: e - 1 }).push(
                                    XTok::SysId { start: m + 1, end: f - 1 },
                                ), f),
                            ),
                            None => None,
                        }
                    }
                },
            }
        }
    } else {
        None
    }
}

/// `?`, `*` or `+` after a content particle.
pub open spec fn quant_end(s: Seq<u8>, i: int) -> int {
    if 0 <= i < s.len() && (s[i] == 0x3F || s[i] == 0x2A || s[i] == 0x2B) {
        i + 1
    } else {
        i
    }
}

/// children ::= (choice | seq) ('?' | '*' | '+')?   [47]
/// cp ::= (Name | choice | seq) ('?' | '*' | '+')?   [48]
/// choice ::= '(' S? cp ( S? '|' S? cp )+ S? ')'   [49]
/// seq ::= '(' S? cp ( S? ',' S? cp )* S? ')'   [50]
///
/// A loop over the model with a stack of the open groups: each holds 0
/// until its first separator, then that separator (`|` or `,`), which the
/// rest of the group must repeat. `after` says a particle has just ended.
/// The position after the model's closing parenthesis and quantifier.
pub open spec fn cmodel(s: Seq<u8>, i: int, st: Seq<u8>, after: bool) -> Option<int>
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if !(0 <= i <= j < s.len()) {
        None
    } else if !after {
        if s[j] == 0x28 {
            cmodel(s, j + 1, st.push(0), false)
        } else {
            let k = name_end(s, j);
            if k == j {
                None
            } else if j < quant_end(s, k) <= s.len() {
                cmodel(s, quant_end(s, k), st, true)
            } else {
                None
            }
        }
    } else if st.len() == 0 {
        None
    } else if s[j] == 0x29 {
        let k = quant_end(s, j + 1);
        if st.len() == 1 {
            Some(k)
        } else if j < k <= s.len() {
            cmodel(s, k, st.drop_last(), true)
        } else {
            None
        }
    } else if (s[j] == 0x7C || s[j] == 0x2C) && (st.last() == 0 || st.last() == s[j]) {
        cmodel(s, j + 1, st.drop_last().push(s[j]), false)
    } else {
        None
    }
}

/// Mixed ::= '(' S? '#PCDATA' (S? '|' S? Name)* S? ')*' | '(' S? '#PCDATA' S? ')'
/// [51], from `i` (just past `#PCDATA`). `names`: a name was listed.
pub open spec fn mixed(s: Seq<u8>, i: int, names: bool) -> Option<int>
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if byte_is(s, j, 0x29) {
        if byte_is(s, j + 1, 0x2A) {
            Some(j + 2)
        } else if names {
            None
        } else {
            Some(j + 1)
        }
    } else if byte_is(s, j, 0x7C) {
        let k = ws_end(s, j + 1);
        let n = name_end(s, k);
        if n == k {
            None
        } else if i < n <= s.len() {
            mixed(s, n, true)
        } else {
            None
        }
    } else {
        None
    }
}

/// contentspec ::= 'EMPTY' | 'ANY' | Mixed | children   [46], at `b`.
pub open spec fn contentspec(s: Seq<u8>, b: int) -> Option<int> {
    if has_lit(s, b, lit_empty()) {
        Some(b + 5)
    } else if has_lit(s, b, lit_any()) {
        Some(b + 3)
    } else if byte_is(s, b, 0x28) {
        let k = ws_end(s, b + 1);
        if has_lit(s, k, lit_pcdata()) {
            mixed(s, k + 7, false)
        } else {
            cmodel(s, b, Seq::empty(), false)
        }
    } else {
        None
    }
}

/// elementdecl ::= '<!ELEMENT' S Name S contentspec S? '>'   [45], at `j`.
pub open spec fn element_decl(s: Seq<u8>, j: int, tape: Seq<XTok>) -> Option<(Seq<XTok>, int)> {
    let a = ws_end(s, j + 9);
    let n = name_end(s, a);
    let b = ws_end(s, n);
    if a == j + 9 || n == a || b == n {
        None
    } else {
        match contentspec(s, b) {
            None => None,
            Some(c) => {
                let e = ws_end(s, c);
                if byte_is(s, e, 0x3E) {
                    Some((tape.push(XTok::ElementDecl { start: a, end: n }), e + 1))
                } else {
                    None
                }
            },
        }
    }
}

/// `Name (S? '|' S? Name)* S? ')'`, or the same with `Nmtoken`s, from `i`
/// (just past the `(` and white space allowed there): the position after
/// the `)`.
pub open spec fn alt_list(s: Seq<u8>, i: int, nm: bool) -> Option<int>
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    let n = if nm {
        nmtoken_end(s, j)
    } else {
        name_end(s, j)
    };
    if n == j {
        None
    } else {
        let k = ws_end(s, n);
        if byte_is(s, k, 0x29) {
            Some(k + 1)
        } else if byte_is(s, k, 0x7C) {
            if i < k + 1 <= s.len() {
                alt_list(s, k + 1, nm)
            } else {
                None
            }
        } else {
            None
        }
    }
}

/// AttType [54..59], at `k`: its end and a code: 1 CDATA, 2 ID, 3 IDREF,
/// 4 IDREFS, 5 ENTITY, 6 ENTITIES, 7 NMTOKEN, 8 NMTOKENS, 9 NOTATION,
/// 10 an enumeration.
pub open spec fn att_type(s: Seq<u8>, k: int) -> Option<(int, int)> {
    if has_lit(s, k, lit_cdata_ty()) {
        Some((k + 5, 1))
    } else if has_lit(s, k, lit_idrefs()) {
        Some((k + 6, 4))
    } else if has_lit(s, k, lit_idref()) {
        Some((k + 5, 3))
    } else if has_lit(s, k, lit_id()) {
        Some((k + 2, 2))
    } else if has_lit(s, k, lit_entities()) {
        Some((k + 8, 6))
    } else if has_lit(s, k, lit_entity_ty()) {
        Some((k + 6, 5))
    } else if has_lit(s, k, lit_nmtokens()) {
        Some((k + 8, 8))
    } else if has_lit(s, k, lit_nmtoken()) {
        Some((k + 7, 7))
    } else if has_lit(s, k, lit_notation_ty()) {
        // NotationType ::= 'NOTATION' S '(' S? Name (S? '|' S? Name)* S? ')'
        let j = ws_end(s, k + 8);
        if j > k + 8 && byte_is(s, j, 0x28) {
            match alt_list(s, j + 1, false) {
                Some(e) => Some((e, 9)),
                None => None,
            }
        } else {
            None
        }
    } else if byte_is(s, k, 0x28) {
        // Enumeration ::= '(' S? Nmtoken (S? '|' S? Nmtoken)* S? ')'
        match alt_list(s, k + 1, true) {
            Some(e) => Some((e, 10)),
            None => None,
        }
    } else {
        None
    }
}

/// DefaultDecl ::= '#REQUIRED' | '#IMPLIED' | (('#FIXED' S)? AttValue)
/// [60], at `m`: the end, the kind (see `XTok::AttDefault`) and the
/// value's raw span. Values are checked for syntax here; their entity
/// references are checked against the whole internal subset by
/// `defaults_ok`.
pub open spec fn default_decl(s: Seq<u8>, m: int) -> Option<(int, int, int, int)> {
    if has_lit(s, m, lit_required()) {
        Some((m + 9, 1, m, m))
    } else if has_lit(s, m, lit_implied()) {
        Some((m + 8, 2, m, m))
    } else {
        let (v, kind) = if has_lit(s, m, lit_fixed()) {
            (ws_end(s, m + 6), 3int)
        } else {
            (m, 4int)
        };
        if kind == 3 && v == m + 6 {
            None
        } else if 0 <= v < s.len() && quote(s[v]) {
            match att_chars(s, v + 1, s[v], None) {
                Some(q) => Some((q + 1, kind, v + 1, q)),
                None => None,
            }
        } else {
            None
        }
    }
}

/// AttlistDecl ::= '<!ATTLIST' S Name AttDef* S? '>'   [52]
/// AttDef ::= S Name S AttType S DefaultDecl   [53]
/// The definitions, from `i`: the position after the `>`.
pub open spec fn att_defs(s: Seq<u8>, i: int, tape: Seq<XTok>, nents: int) -> Option<(Seq<XTok>, int)>
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if byte_is(s, j, 0x3E) {
        Some((tape, j + 1))
    } else if j == i {
        None
    } else {
        let n = name_end(s, j);
        let k = ws_end(s, n);
        if n == j || k == n {
            None
        } else {
            match att_type(s, k) {
                None => None,
                Some((e, ty)) => {
                    let m = ws_end(s, e);
                    if m == e {
                        None
                    } else {
                        match default_decl(s, m) {
                            None => None,
                            Some((d, kind, va, vb)) => if i < d <= s.len() {
                                att_defs(
                                    s,
                                    d,
                                    tape.push(XTok::AttDef { start: j, end: n, ty }).push(
                                        XTok::AttDefault { start: va, end: vb, kind, nents },
                                    ),
                                    nents,
                                )
                            } else {
                                None
                            },
                        }
                    }
                },
            }
        }
    }
}

pub open spec fn attlist_decl(s: Seq<u8>, j: int, tape: Seq<XTok>, nents: int) -> Option<(Seq<XTok>, int)> {
    let a = ws_end(s, j + 9);
    let n = name_end(s, a);
    if a == j + 9 || n == a {
        None
    } else {
        att_defs(s, n, tape.push(XTok::AttlistDecl { start: a, end: n }), nents)
    }
}

/// EntityDef ::= EntityValue | (ExternalID NDataDecl?)   [73]
/// PEDef ::= EntityValue | ExternalID   [74] (when `!ge`)
/// NDataDecl ::= S 'NDATA' S Name   [76]
/// At `c`: the tape, the end and what kind of entity it declares.
pub open spec fn ent_def(s: Seq<u8>, c: int, tape: Seq<XTok>, ge: bool) -> Option<(Seq<XTok>, int, EKind)> {
    if 0 <= c < s.len() && quote(s[c]) {
        match ent_value_end(s, c + 1, s[c]) {
            Some(e) => Some(
                (tape.push(XTok::EntityValue { start: c + 1, end: e - 1 }), e, EKind::Internal {
                    start: c + 1,
                    end: e - 1,
                }),
            ),
            None => None,
        }
    } else {
        match external_id(s, c, tape) {
            None => None,
            Some((t, e)) => {
                let k = ws_end(s, e);
                if ge && k > e && has_lit(s, k, lit_ndata()) {
                    let m = ws_end(s, k + 5);
                    let n = name_end(s, m);
                    if m == k + 5 || n == m {
                        None
                    } else {
                        Some((t.push(XTok::NData { start: m, end: n }), n, EKind::Unparsed))
                    }
                } else {
                    Some((t, e, EKind::External))
                }
            },
        }
    }
}

/// EntityDecl ::= GEDecl | PEDecl   [70]
/// GEDecl ::= '<!ENTITY' S Name S EntityDef S? '>'   [71]
/// PEDecl ::= '<!ENTITY' S '%' S Name S PEDef S? '>'   [72]
///
/// A general entity's declaration is processed (recorded) unless it comes
/// after a parameter entity reference that was not read, in a document
/// that is not standalone (§5.1).
pub open spec fn entity_decl(s: Seq<u8>, j: int, tape: Seq<XTok>, st: DtdSt) -> Option<(Seq<XTok>, DtdSt, int)> {
    let a = ws_end(s, j + 8);
    if a == j + 8 {
        None
    } else if byte_is(s, a, 0x25) {
        let b = ws_end(s, a + 1);
        let n = name_end(s, b);
        let c = ws_end(s, n);
        if b == a + 1 || n == b || c == n {
            None
        } else {
            match ent_def(s, c, tape.push(XTok::EntityDecl { start: b, end: n, pe: true }), false) {
                None => None,
                Some((t, e, _)) => {
                    let f = ws_end(s, e);
                    if byte_is(s, f, 0x3E) {
                        Some((t, DtdSt { ents: st.ents, pes: st.pes.push(s.subrange(b, n)), pe_seen: st.pe_seen, sa: st.sa }, f + 1))
                    } else {
                        None
                    }
                },
            }
        }
    } else {
        let n = name_end(s, a);
        let c = ws_end(s, n);
        if n == a || c == n {
            None
        } else {
            match ent_def(s, c, tape.push(XTok::EntityDecl { start: a, end: n, pe: false }), true) {
                None => None,
                Some((t, e, kind)) => {
                    let f = ws_end(s, e);
                    if byte_is(s, f, 0x3E) {
                        let st2 = if !st.pe_seen || st.sa {
                            DtdSt { ents: st.ents.push(Ent { name: s.subrange(a, n), kind }), pes: st.pes, pe_seen: st.pe_seen, sa: st.sa }
                        } else {
                            st
                        };
                        Some((t, st2, f + 1))
                    } else {
                        None
                    }
                },
            }
        }
    }
}

/// NotationDecl ::= '<!NOTATION' S Name S (ExternalID | PublicID) S? '>'
/// [82], PublicID ::= 'PUBLIC' S PubidLiteral [83], at `j`.
pub open spec fn notation_decl(s: Seq<u8>, j: int, tape: Seq<XTok>) -> Option<(Seq<XTok>, int)> {
    let a = ws_end(s, j + 10);
    let n = name_end(s, a);
    let b = ws_end(s, n);
    if a == j + 10 || n == a || b == n {
        None
    } else {
        let t1 = tape.push(XTok::NotationDecl { start: a, end: n });
        let r = if has_lit(s, b, lit_public()) {
            let p = ws_end(s, b + 6);
            if p == b + 6 {
                None
            } else {
                match pubid_lit(s, p) {
                    None => None,
                    Some(e) => {
                        let t2 = t1.push(XTok::PubId { start: p + 1, end: e - 1 });
                        let k = ws_end(s, e);
                        if k > e && 0 <= k < s.len() && quote(s[k]) {
                            match sys_lit(s, k) {
                                Some(f) => Some((t2.push(XTok::SysId { start: k + 1, end: f - 1 }), f)),
                                None => None,
                            }
                        } else {
                            Some((t2, e))
                        }
                    },
                }
            }
        } else {
            external_id(s, b, t1)
        };
        match r {
            None => None,
            Some((t, e)) => {
                let f = ws_end(s, e);
                if byte_is(s, f, 0x3E) {
                    Some((t, f + 1))
                } else {
                    None
                }
            },
        }
    }
}

/// PEReference ::= '%' Name ';'   [69], between declarations (DeclSep
/// [28a]), at `j`. It is not read. In a standalone document the
/// parameter entity must have been declared (WFC: Entity Declared).
pub open spec fn pe_ref(s: Seq<u8>, j: int, tape: Seq<XTok>, st: DtdSt) -> Option<(Seq<XTok>, DtdSt, int)> {
    let n = name_end(s, j + 1);
    if n == j + 1 || !byte_is(s, n, 0x3B) {
        None
    } else if st.sa && !st.pes.contains(s.subrange(j + 1, n)) {
        None
    } else {
        Some((tape.push(XTok::PERef { start: j + 1, end: n }), DtdSt { ents: st.ents, pes: st.pes, pe_seen: true, sa: st.sa }, n + 1))
    }
}

/// markupdecl ::= elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment
/// [29], or a PEReference, at `j`.
pub open spec fn decl(s: Seq<u8>, j: int, tape: Seq<XTok>, st: DtdSt) -> Option<(Seq<XTok>, DtdSt, int)> {
    if byte_is(s, j, 0x25) {
        pe_ref(s, j, tape, st)
    } else if has_lit(s, j, lit_element()) {
        match element_decl(s, j, tape) {
            Some((t, e)) => Some((t, st, e)),
            None => None,
        }
    } else if has_lit(s, j, lit_attlist()) {
        match attlist_decl(s, j, tape, st.ents.len() as int) {
            Some((t, e)) => Some((t, st, e)),
            None => None,
        }
    } else if has_lit(s, j, lit_entity()) {
        entity_decl(s, j, tape, st)
    } else if has_lit(s, j, lit_notation()) {
        match notation_decl(s, j, tape) {
            Some((t, e)) => Some((t, st, e)),
            None => None,
        }
    } else if has_lit(s, j, lit_comment()) {
        match comment(s, j, tape) {
            Some((t, e)) => Some((t, st, e)),
            None => None,
        }
    } else if has_lit(s, j, lit_pi()) {
        match pi(s, j, tape) {
            Some((t, e)) => Some((t, st, e)),
            None => None,
        }
    } else {
        None
    }
}

/// intSubset ::= (markupdecl | DeclSep)*   [28b], from `i`: the tape, the
/// state, and the position of the `]` that ends it.
pub open spec fn int_subset(s: Seq<u8>, i: int, tape: Seq<XTok>, st: DtdSt) -> Option<(Seq<XTok>, DtdSt, int)>
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if !(0 <= j < s.len()) {
        None
    } else if s[j] == 0x5D {
        Some((tape, st, j))
    } else {
        match decl(s, j, tape, st) {
            None => None,
            Some((t, st2, e)) => if i < e <= s.len() {
                int_subset(s, e, t, st2)
            } else {
                None
            },
        }
    }
}

/// doctypedecl ::= '<!DOCTYPE' S Name (S ExternalID)? S? ('[' intSubset ']' S?)? '>'
/// [28], at `i`. External subsets are not read (§5.1).
pub open spec fn doctype(s: Seq<u8>, i: int, tape: Seq<XTok>, sa: bool) -> Option<(Seq<XTok>, int, Env)> {
    let j = ws_end(s, i + 9);
    let n = name_end(s, j);
    if j == i + 9 || n == j {
        None
    } else {
        let t1 = tape.push(XTok::Doctype { start: j, end: n });
        let k = ws_end(s, n);
        let er = if k > n && (has_lit(s, k, lit_system()) || has_lit(s, k, lit_public())) {
            match external_id(s, k, t1) {
                Some((t, e)) => Some((t, e, true)),
                None => None,
            }
        } else {
            Some((t1, n, false))
        };
        match er {
            None => None,
            Some((t2, e, ext)) => {
                let m = ws_end(s, e);
                if byte_is(s, m, 0x5B) {
                    match int_subset(s, m + 1, t2, dtd_init(sa)) {
                        None => None,
                        Some((t3, st, q)) => {
                            let r = ws_end(s, q + 1);
                            if byte_is(s, r, 0x3E) {
                                Some((t3.push(XTok::DoctypeEnd), r + 1, env_of(s, st, ext)))
                            } else {
                                None
                            }
                        },
                    }
                } else if byte_is(s, m, 0x3E) {
                    Some((t2.push(XTok::DoctypeEnd), m + 1, env_of(s, dtd_init(sa), ext)))
                } else {
                    None
                }
            },
        }
    }
}

/// The references in the default values of attribute definitions (WFC:
/// Entity Declared, No External Entity References, Parsed Entity): checked
/// once the whole internal subset is known, since whether a reference must
/// be declared depends on all of it; each against the entities declared
/// before the definition. (The span and the count are always in range;
/// the guard keeps the spec total.)
pub open spec fn defaults_ok(s: Seq<u8>, tape: Seq<XTok>, env: Env) -> bool {
    forall|k: int|
        0 <= k < tape.len() ==> match #[trigger] tape[k] {
            XTok::AttDefault { start, end, kind, nents } => kind < 3 || (0 <= start <= end < s.len() && 0 <= nents
                <= env.ents.len() && att_chars(
                s,
                start,
                s[end],
                Some(Env { ents: env.ents.subrange(0, nents), wfc: env.wfc, oka: env.oka, okc: env.okc }),
            ) is Some),
            _ => true,
        }
}

// ---------------------------------------------------------------------------
// Elements
// ---------------------------------------------------------------------------

/// The attribute names in `t[first..]` are all different (WFC: Unique Att
/// Spec).
pub open spec fn attrs_distinct(s: Seq<u8>, t: Seq<XTok>, first: int) -> bool {
    forall|j: int, k: int|
        first <= j < k < t.len() && #[trigger] t[j] is Attr && #[trigger] t[k] is Attr ==> s.subrange(
            t[j]->Attr_start,
            t[j]->Attr_end,
        ) != s.subrange(t[k]->Attr_start, t[k]->Attr_end)
}

/// (S Attribute)* S? ('>' | '/>'), with Attribute ::= Name Eq AttValue
/// [41], from `i`: the tape, the position after the tag, and whether it
/// was an empty-element tag.
pub open spec fn attrs(s: Seq<u8>, i: int, tape: Seq<XTok>, env: Env) -> Option<(Seq<XTok>, int, bool)>
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if byte_is(s, j, 0x3E) {
        Some((tape, j + 1, false))
    } else if has_lit(s, j, lit_empty_end()) {
        Some((tape, j + 2, true))
    } else if j == i {
        None
    } else {
        let n = name_end(s, j);
        if n == j {
            None
        } else {
            match eq_end(s, n) {
                None => None,
                Some(v) => if 0 <= v < s.len() && quote(s[v]) {
                    match att_chars(s, v + 1, s[v], Some(env)) {
                        None => None,
                        Some(q) => if i < q + 1 <= s.len() {
                            attrs(
                                s,
                                q + 1,
                                tape.push(XTok::Attr { start: j, end: n }).push(
                                    XTok::AttVal { start: v + 1, end: q, plain: att_plain(s, v + 1, q) },
                                ),
                                env,
                            )
                        } else {
                            None
                        },
                    }
                } else {
                    None
                },
            }
        }
    }
}

/// STag ::= '<' Name (S Attribute)* S? '>'   [40]
/// EmptyElemTag ::= '<' Name (S Attribute)* S? '/>'   [44]
/// At `i`: the tape, the position after the tag, and whether it was an
/// empty-element tag.
pub open spec fn stag(s: Seq<u8>, i: int, tape: Seq<XTok>, env: Env) -> Option<(Seq<XTok>, int, bool)> {
    let n = name_end(s, i + 1);
    if n == i + 1 {
        None
    } else {
        let t = tape.push(XTok::STag { start: i + 1, end: n, close: 0 });
        match attrs(s, n, t, env) {
            None => None,
            Some((t2, e, empty)) => if attrs_distinct(s, t2, t.len() as int) {
                Some((t2, e, empty))
            } else {
                None
            },
        }
    }
}

/// `t` with the start tag at `k` linked to `t`'s last token, the `ETag`
/// that closes it.
pub open spec fn close_at(t: Seq<XTok>, k: int) -> Seq<XTok> {
    t.update(
        k,
        match t[k] {
            XTok::STag { start, end, .. } => XTok::STag { start, end, close: t.len() - 1 },
            x => x,
        },
    )
}

/// An open element: its name's span and the index of its start tag.
pub type Open = (int, int, int);

/// One item of content at `i`, inside the open elements `stack`: content ::= CharData? ((element | Reference | CDSect | PI
/// | Comment) CharData?)* [43], with ETag ::= '</' Name S? '>' [42] closing
/// the innermost element (WFC: Element Type Match). An end tag with no
/// element open is an error (in an entity's replacement text: elements
/// must start and end in the same entity, §4.3.2).
pub open spec fn item(s: Seq<u8>, i: int, stack: Seq<Open>, tape: Seq<XTok>, env: Env) -> Option<
    (Seq<Open>, Seq<XTok>, int),
> {
    if s[i] == 0x3C {
        if byte_is(s, i + 1, 0x2F) {
            let top = stack.last();
            if stack.len() == 0 {
                None
            } else {
                let n = name_end(s, i + 2);
                if s.subrange(i + 2, n) != s.subrange(top.0, top.1) {
                    None
                } else {
                    let e = ws_end(s, n);
                    if byte_is(s, e, 0x3E) {
                        Some((stack.drop_last(), close_at(tape.push(XTok::ETag), top.2), e + 1))
                    } else {
                        None
                    }
                }
            }
        } else if has_lit(s, i, lit_comment()) {
            match comment(s, i, tape) {
                Some((t, e)) => Some((stack, t, e)),
                None => None,
            }
        } else if has_lit(s, i, lit_cdata()) {
            match cdata_end(s, i + 9) {
                Some(e) => Some(
                    (stack, tape.push(XTok::CData { start: i + 9, end: e - 3, cr: has_cr(s, i + 9, e - 3) }), e),
                ),
                None => None,
            }
        } else if byte_is(s, i + 1, 0x3F) {
            match pi(s, i, tape) {
                Some((t, e)) => Some((stack, t, e)),
                None => None,
            }
        } else {
            match stag(s, i, tape, env) {
                None => None,
                Some((t, e, empty)) => if empty {
                    Some((stack, close_at(t.push(XTok::ETag), tape.len() as int), e))
                } else {
                    Some((stack.push((i + 1, name_end(s, i + 1), tape.len() as int)), t, e))
                },
            }
        }
    } else if s[i] == 0x26 {
        match content_ref(s, i, env) {
            Some((x, e)) => Some((stack, tape.push(x), e)),
            None => None,
        }
    } else {
        match text_end(s, i) {
            Some(e) => Some((stack, tape.push(XTok::Text { start: i, end: e, cr: has_cr(s, i, e) }), e)),
            None => None,
        }
    }
}

/// The content of the open elements `stack`, from `i`, up to and
/// including the end tag that closes the outermost: the tape and the
/// position after that end tag.
pub open spec fn content(s: Seq<u8>, i: int, stack: Seq<Open>, tape: Seq<XTok>, env: Env) -> Option<
    (Seq<XTok>, int),
>
    decreases s.len() - i,
{
    if stack.len() == 0 {
        Some((tape, i))
    } else if !(0 <= i < s.len()) {
        None
    } else {
        match item(s, i, stack, tape, env) {
            None => None,
            Some((st2, t2, e)) => if i < e <= s.len() {
                content(s, e, st2, t2, env)
            } else {
                None
            },
        }
    }
}

/// element ::= EmptyElemTag | STag content ETag   [39], at `i`.
pub open spec fn element(s: Seq<u8>, i: int, tape: Seq<XTok>, env: Env) -> Option<(Seq<XTok>, int)> {
    if !byte_is(s, i, 0x3C) {
        None
    } else {
        match stag(s, i, tape, env) {
            None => None,
            Some((t, e, empty)) => if empty {
                Some((close_at(t.push(XTok::ETag), tape.len() as int), e))
            } else {
                content(s, e, seq![(i + 1, name_end(s, i + 1), tape.len() as int)], t, env)
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Entities' replacement text
// ---------------------------------------------------------------------------

/// The replacement text of the internal entity whose literal value is
/// `s[a..b]` (§4.5): each character reference replaced by its character,
/// in UTF-8; the rest, entity references included, as written (they are
/// bypassed, §4.4.7), after line-end normalization (§2.11: the literal
/// is part of the document, whose line ends are normalized before it is
/// parsed, so a carriage return in the replacement text can only come
/// from a character reference). The internal subset has no parameter
/// entity references inside declarations.
pub open spec fn repl(s: Seq<u8>, a: int, b: int) -> Seq<u8>
    decreases b - a,
{
    if !(0 <= a < b <= s.len()) {
        Seq::empty()
    } else if s[a] == 0x26 && byte_is(s, a + 1, 0x23) {
        match charref(s, a) {
            Some((c, e)) => if a < e <= b {
                utf8_encode(c as u32) + repl(s, e, b)
            } else {
                Seq::empty()
            },
            None => Seq::empty(),
        }
    } else if s[a] == 0x0D {
        if a + 1 < b && s[a + 1] == 0x0A {
            seq![0x0Au8] + repl(s, a + 2, b)
        } else {
            seq![0x0Au8] + repl(s, a + 1, b)
        }
    } else {
        seq![s[a]] + repl(s, a + 1, b)
    }
}

/// The replacement text `r`, from `i`, as part of an attribute value
/// (§3.3.3: references in it are processed in turn): no `<` (WFC: No < in
/// Attribute Values), and each reference allowed in an attribute value.
pub open spec fn att_text(r: Seq<u8>, i: int, env: Env) -> bool
    decreases r.len() - i,
{
    if !(0 <= i < r.len()) {
        true
    } else if r[i] == 0x3C {
        false
    } else if r[i] == 0x26 {
        match att_ref(r, i, Some(env)) {
            None => false,
            Some(e) => if i < e <= r.len() {
                att_text(r, e, env)
            } else {
                false
            },
        }
    } else {
        att_text(r, i + 1, env)
    }
}

/// The replacement text `r`, from `i`, as content (§4.3.2: an internal
/// entity is well-formed if its replacement text matches `content`), with
/// the open elements `stack`, which must all close before the end.
pub open spec fn ent_content(r: Seq<u8>, i: int, stack: Seq<Open>, tape: Seq<XTok>, env: Env) -> Option<Seq<XTok>>
    decreases r.len() - i,
{
    if !(0 <= i < r.len()) {
        if stack.len() == 0 {
            Some(tape)
        } else {
            None
        }
    } else {
        match item(r, i, stack, tape, env) {
            None => None,
            Some((st2, t2, e)) => if i < e <= r.len() {
                ent_content(r, e, st2, t2, env)
            } else {
                None
            },
        }
    }
}

/// How deep references to internal entities may nest, counting through
/// their replacement texts. A reference cycle nests without end, so this
/// bound is also what rejects recursion (WFC: No Recursion). libxml2's
/// default bound is 40.
pub const ENT_DEPTH: usize = 64;

/// Entity `k` may be referred to in an attribute value, given which
/// entities may be (`prev`) at one level less.
pub open spec fn ent_oka(s: Seq<u8>, ents: Seq<Ent>, wfc: bool, prev: Seq<bool>, k: int) -> bool {
    match ents[k].kind {
        EKind::Internal { start, end } => att_text(
            repl(s, start, end),
            0,
            Env { ents, wfc, oka: prev, okc: Seq::empty() },
        ),
        _ => false,
    }
}

/// `ent_oka` for each entity, with references nesting at most `d` deep.
pub open spec fn oka_seq(s: Seq<u8>, ents: Seq<Ent>, wfc: bool, d: nat) -> Seq<bool>
    decreases d,
{
    if d == 0 {
        Seq::new(ents.len(), |k: int| false)
    } else {
        let prev = oka_seq(s, ents, wfc, (d - 1) as nat);
        Seq::new(ents.len(), |k: int| ent_oka(s, ents, wfc, prev, k))
    }
}

/// Entity `k` may be referred to in content: its replacement text is
/// content in which every element that starts also ends, and whose own
/// references are allowed, given which entities may be referred to in
/// content at one level less (`prev`) and in attribute values (`oka`).
pub open spec fn ent_okc(s: Seq<u8>, ents: Seq<Ent>, wfc: bool, oka: Seq<bool>, prev: Seq<bool>, k: int) -> bool {
    match ents[k].kind {
        EKind::Internal { start, end } => ent_content(
            repl(s, start, end),
            0,
            Seq::empty(),
            Seq::empty(),
            Env { ents, wfc, oka, okc: prev },
        ) is Some,
        _ => false,
    }
}

/// `ent_okc` for each entity, with references nesting at most `d` deep.
pub open spec fn okc_seq(s: Seq<u8>, ents: Seq<Ent>, wfc: bool, oka: Seq<bool>, d: nat) -> Seq<bool>
    decreases d,
{
    if d == 0 {
        Seq::new(ents.len(), |k: int| false)
    } else {
        let prev = okc_seq(s, ents, wfc, oka, (d - 1) as nat);
        Seq::new(ents.len(), |k: int| ent_okc(s, ents, wfc, oka, prev, k))
    }
}

// ---------------------------------------------------------------------------
// Documents
// ---------------------------------------------------------------------------

/// The position after a UTF-8 byte order mark at the start, if any.
pub open spec fn bom_end(s: Seq<u8>) -> int {
    if has_lit(s, 0, seq![0xEFu8, 0xBB, 0xBF]) {
        3
    } else {
        0
    }
}

/// The byte order mark and the XML declaration, if any: the tape, the
/// position after them, and the standalone declaration.
pub open spec fn decl_head(s: Seq<u8>, enc: Enc) -> Option<(Seq<XTok>, int, int)> {
    let p0 = bom_end(s);
    if has_lit(s, p0, lit_xmldecl()) && 0 <= p0 + 5 < s.len() && is_ws(s[p0 + 5]) {
        xmldecl(s, p0, enc)
    } else {
        Some((Seq::empty(), p0, 0))
    }
}

/// The document type declaration at `p`, if there is one there: the
/// tape, the position after it, and the environment of the content.
pub open spec fn doctype_opt(s: Seq<u8>, p: int, t: Seq<XTok>, sd: int) -> Option<(Seq<XTok>, int, Env)> {
    if has_lit(s, p, lit_doctype()) {
        doctype(s, p, t, sd == 1)
    } else {
        Some((t, p, no_dtd()))
    }
}

/// The prolog, up to the root element: prolog ::= XMLDecl? Misc*
/// (doctypedecl Misc*)? [22]. The tape, the position of the root element,
/// and the environment of its content.
pub open spec fn prolog(s: Seq<u8>, enc: Enc) -> Option<(Seq<XTok>, int, Env)> {
    match decl_head(s, enc) {
        None => None,
        Some((t0, p1, sd)) => match misc(s, p1, t0) {
            None => None,
            Some((t1, p2)) => match doctype_opt(s, p2, t1, sd) {
                None => None,
                Some((t2, p3, env)) => match misc(s, p3, t2) {
                    None => None,
                    Some((t3, p4)) => if defaults_ok(s, t3, env) {
                        Some((t3, p4, env))
                    } else {
                        None
                    },
                },
            },
        },
    }
}

/// document ::= prolog element Misc*   [1], in UTF-8 (with an optional
/// byte order mark), every character a `Char` [2], read from a document in
/// the encoding `enc`. The whole input must be the document.
pub open spec fn document(s: Seq<u8>, enc: Enc) -> Option<Seq<XTok>> {
    if !doc_chars(s) {
        None
    } else {
        match prolog(s, enc) {
            None => None,
            Some((t, p, env)) => match element(s, p, t, env) {
                None => None,
                Some((t2, e)) => match misc(s, e, t2) {
                    None => None,
                    Some((t3, f)) => if f == s.len() {
                        Some(t3)
                    } else {
                        None
                    },
                },
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Encodings (§4.3.3, Appendix F)
// ---------------------------------------------------------------------------

/// The encoding name in an XML declaration at the start of `b` (after a
/// UTF-8 byte order mark), read as ASCII: its span. This only chooses how
/// to decode `b`; `document` then checks the whole declaration, the name
/// included, on the decoded text.
pub open spec fn declared_enc(b: Seq<u8>) -> Option<(int, int)> {
    let p0 = bom_end(b);
    if has_lit(b, p0, lit_xmldecl()) && 0 <= p0 + 5 < b.len() && is_ws(b[p0 + 5]) {
        match version_info(b, p0 + 5) {
            None => None,
            Some((v, _, _)) => {
                let j = ws_end(b, v);
                if j > v && has_lit(b, j, lit_encoding()) {
                    match enc_span(b, j) {
                        Some((_, x, y)) => Some((x, y)),
                        None => None,
                    }
                } else {
                    None
                }
            },
        }
    } else {
        None
    }
}

/// The encoding `b` is in: UTF-16 when it starts with a UTF-16 byte order
/// mark (which UTF-16 requires, Appendix F); otherwise what the XML
/// declaration names, if it is ISO-8859-1 or US-ASCII; otherwise UTF-8.
pub open spec fn input_enc(b: Seq<u8>) -> Enc {
    if has_lit(b, 0, seq![0xFEu8, 0xFF]) || has_lit(b, 0, seq![0xFFu8, 0xFE]) {
        Enc::Utf16
    } else {
        match declared_enc(b) {
            Some((x, y)) => if ci_eq(b, x, y, lit_latin1()) {
                Enc::Latin1
            } else if ci_eq(b, x, y, lit_ascii()) {
                Enc::Ascii
            } else {
                Enc::Utf8
            },
            None => Enc::Utf8,
        }
    }
}

/// The 16-bit code unit at `i` (little-endian when `le`).
pub open spec fn unit16(b: Seq<u8>, i: int, le: bool) -> int {
    if le {
        b[i] + b[i + 1] * 256
    } else {
        b[i] * 256 + b[i + 1]
    }
}

/// UTF-16 from `i` to the end, in UTF-8: `None` if it is cut short or has
/// a surrogate that is not half of a pair.
pub open spec fn utf16_dec(b: Seq<u8>, i: int, le: bool) -> Option<Seq<u8>>
    decreases b.len() - i,
{
    if !(0 <= i < b.len()) {
        Some(Seq::empty())
    } else if i + 2 > b.len() {
        None
    } else {
        let u = unit16(b, i, le);
        if 0xD800 <= u <= 0xDBFF {
            if i + 4 <= b.len() && 0xDC00 <= unit16(b, i + 2, le) <= 0xDFFF {
                let c = 0x10000 + (u - 0xD800) * 1024 + (unit16(b, i + 2, le) - 0xDC00);
                match utf16_dec(b, i + 4, le) {
                    Some(r) => Some(utf8_encode(c as u32) + r),
                    None => None,
                }
            } else {
                None
            }
        } else if 0xDC00 <= u <= 0xDFFF {
            None
        } else {
            match utf16_dec(b, i + 2, le) {
                Some(r) => Some(utf8_encode(u as u32) + r),
                None => None,
            }
        }
    }
}

/// ISO-8859-1 from `i` to the end, in UTF-8: each byte is the code point
/// of the same value.
pub open spec fn latin1_dec(b: Seq<u8>, i: int) -> Seq<u8>
    decreases b.len() - i,
{
    if !(0 <= i < b.len()) {
        Seq::empty()
    } else {
        utf8_encode(b[i] as u32) + latin1_dec(b, i + 1)
    }
}

/// `b` decoded to UTF-8 (US-ASCII must have no byte above 0x7F).
pub open spec fn decode_input(b: Seq<u8>) -> Option<Seq<u8>> {
    match input_enc(b) {
        Enc::Utf16 => utf16_dec(b, 0, b[0] == 0xFF),
        Enc::Latin1 => Some(latin1_dec(b, 0)),
        Enc::Ascii => if forall|k: int| 0 <= k < b.len() ==> b[k] < 0x80 {
            Some(b)
        } else {
            None
        },
        Enc::Utf8 => Some(b),
    }
}

/// An XML document in any encoding read here: the text in UTF-8, and its
/// tape.
pub open spec fn parse(b: Seq<u8>) -> Option<(Seq<u8>, Seq<XTok>)> {
    match decode_input(b) {
        None => None,
        Some(u) => match document(u, input_enc(b)) {
            None => None,
            Some(t) => Some((u, t)),
        },
    }
}

} // verus!

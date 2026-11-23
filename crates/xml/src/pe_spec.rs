//! The document type declaration read whole: parameter entities expanded
//! (§4.4.8, §4.4.5), the external subset and external parameter entities
//! read when a loader is given (§5.1), conditional sections resolved
//! (§3.4), as Verus spec functions.
//!
//! `flat` turns the internal subset, then the external subset, into one
//! text of markup declarations with no parameter entity reference left in
//! it but those that were not read: the *flattened DTD*. It reads the
//! texts the way §4.4 says a parameter entity reference is treated where
//! it is recognized:
//!
//! * between declarations (DeclSep [28a]) and, in external text, inside a
//!   declaration: *included as PE*, its replacement text with one space
//!   before and one after (§4.4.8);
//! * in an entity value in external text: *included in literal*, with no
//!   spaces, and a quote in it does not end the literal (§4.4.5);
//! * in a comment, a processing instruction, a system or public literal,
//!   an attribute value, an ignored section, and inside a declaration of
//!   the internal subset: not recognized (the last is the WFC "PEs in
//!   Internal Subset", so the text is left as it is, and the flattened DTD
//!   is rejected where it holds a `%`).
//!
//! Its well-formedness constraints are checked as it goes: PE Between
//! Declarations [28a] (a replacement text referred to between
//! declarations holds whole declarations: it ends between declarations),
//! No Recursion (§4.1), the text declaration of each external parsed
//! entity [77], and that comments, processing instructions, literals and
//! ignored sections end in the entity they begin in. The flattened DTD is
//! then parsed as an internal subset by the verified parser (`spec::
//! int_subset`), which checks every declaration in it; the document's
//! content is checked against what it declares (`doc_x`).
//!
//! What is read stops at the first reference to a parameter entity that is
//! not read (one not declared, or external with no loader or whose loader
//! gives nothing), unless the document is standalone (§5.1): the reference
//! stays in the flattened DTD, where the verified parser stops processing
//! declarations after it, and external text after it is not read.
//!
//! The loader is a function from (the URI of the entity holding the
//! declaration, the system identifier, the public identifier) to the bytes
//! of the entity and its URI (`Cfg::ld`); what the loader returned is all
//! that is trusted about it. A budget of steps (`fuel`) bounds the work
//! and the size of the flattened DTD: "billion laughs" through parameter
//! entities runs out of it and is refused.
use crate::chars::*;
use crate::spec::*;
use crate::tape::MAX_POS;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

/// A text being read: the internal subset, the external subset, or the
/// replacement text of a parameter entity.
pub struct Frame {
    pub text: Seq<u8>,
    pub pos: int,
    /// External text: the external subset, an external parameter entity,
    /// or a replacement text referred to from external text. Parameter
    /// entity references are recognized inside declarations, and
    /// conditional sections are allowed.
    pub ext: bool,
    /// The parameter entity whose replacement text this is (an index into
    /// `Fl::pes`), or -1.
    pub pe: int,
    /// Included in a literal (§4.4.5).
    pub lit: bool,
    /// Referred to between declarations: it must end between declarations
    /// (WFC: PE Between Declarations).
    pub sep: bool,
    /// The URI of the external entity the text is in ("" for the document).
    pub base: Seq<u8>,
}

/// What is being read.
pub enum Mode {
    /// Between declarations.
    Sep,
    /// In a comment.
    Comment,
    /// In a processing instruction.
    Pi,
    /// In a markup declaration that begins at `start` in the output, in the
    /// entity whose URI is `base`. `q` is the quote of the literal being
    /// read (0 outside literals), `ev` whether that literal is an entity
    /// value, and `ld` how many frames were open when it began.
    Decl { start: int, q: u8, ev: bool, ld: int, base: Seq<u8> },
    /// In the keyword of a conditional section that begins at `start` in
    /// the output.
    Cond { start: int },
    /// In an ignored section, `depth` sections deep.
    Ignore { depth: int },
}

/// A parameter entity declaration that was processed: internal with its
/// replacement text, or external with its identifiers and the URI of the
/// entity its declaration is in.
pub struct PeDef {
    pub name: Seq<u8>,
    pub internal: bool,
    pub rt: Seq<u8>,
    pub sys: Seq<u8>,
    pub pubid: Seq<u8>,
    pub base: Seq<u8>,
}

/// The loader's model: the bytes and the URI of the entity with these
/// (base URI, system identifier, public identifier), if it gives them.
pub type LoadFn = spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<(Seq<u8>, Seq<u8>)>;

/// What does not change while flattening: whether the document is
/// standalone, whether there is a loader and its model, and the external
/// subset's identifiers (`has_ext`: the document type declaration has an
/// external identifier).
pub struct Cfg {
    pub sa: bool,
    pub load: bool,
    pub ld: LoadFn,
    pub has_ext: bool,
    pub ext_sys: Seq<u8>,
    pub ext_pub: Seq<u8>,
}

pub struct Fl {
    pub frames: Seq<Frame>,
    pub out: Seq<u8>,
    pub mode: Mode,
    pub pes: Seq<PeDef>,
    /// A parameter entity that was not read was referred to, in a document
    /// that is not standalone: nothing more is processed (§5.1).
    pub stop: bool,
    /// Open INCLUDE sections.
    pub incl: int,
    /// The external subset is still to be read.
    pub ext_todo: bool,
}

pub enum Step {
    Next(Fl),
    Done(Seq<u8>),
    Bad,
}

pub enum FlatRes {
    Ok(Seq<u8>),
    /// Not well-formed.
    Bad,
    /// The budget ran out.
    Limit,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// A parameter entity reference `%Name;` at `i` in `t`: the end of the
/// name (the position of the `;`).
pub open spec fn pe_ref_at(t: Seq<u8>, i: int) -> Option<int> {
    let n = name_end(t, i + 1);
    if byte_is(t, i, 0x25) && n > i + 1 && byte_is(t, n, 0x3B) {
        Some(n)
    } else {
        None
    }
}

/// The first processed declaration of the parameter entity `name`.
pub open spec fn find_pe(pes: Seq<PeDef>, name: Seq<u8>) -> Option<int>
    decreases pes.len(),
{
    if pes.len() == 0 {
        None
    } else {
        match find_pe(pes.drop_last(), name) {
            Some(j) => Some(j),
            None => if pes.last().name == name {
                Some(pes.len() - 1)
            } else {
                None
            },
        }
    }
}

/// The parameter entity `k` is being read (WFC: No Recursion).
pub open spec fn on_stack(frames: Seq<Frame>, k: int) -> bool {
    exists|i: int| 0 <= i < frames.len() && #[trigger] frames[i].pe == k
}

/// The first external frame (`frames.len()` if none).
pub open spec fn first_ext(frames: Seq<Frame>) -> int
    decreases frames.len(),
{
    if frames.len() == 0 {
        0
    } else {
        let k = first_ext(frames.drop_last());
        if k < frames.len() - 1 {
            k
        } else if frames.last().ext {
            frames.len() - 1
        } else {
            frames.len() as int
        }
    }
}

/// The literal about to begin is an entity value: the declaration so far
/// (`out[start..]`) is `<!ENTITY S Name S` or `<!ENTITY S % S Name S`.
pub open spec fn is_ev(out: Seq<u8>, start: int) -> bool {
    let a = ws_end(out, start + 8);
    if !has_lit(out, start, lit_entity()) || a == start + 8 {
        false
    } else if byte_is(out, a, 0x25) {
        let b = ws_end(out, a + 1);
        let n = name_end(out, b);
        let c = ws_end(out, n);
        b > a + 1 && n > b && c > n && c == out.len()
    } else {
        let n = name_end(out, a);
        let c = ws_end(out, n);
        n > a && c > n && c == out.len()
    }
}

pub open spec fn lit_include() -> Seq<u8> { seq![0x49u8, 0x4E, 0x43, 0x4C, 0x55, 0x44, 0x45] }  // INCLUDE
pub open spec fn lit_ignore() -> Seq<u8> { seq![0x49u8, 0x47, 0x4E, 0x4F, 0x52, 0x45] }  // IGNORE
pub open spec fn lit_cond() -> Seq<u8> { seq![0x3Cu8, 0x21, 0x5B] }  // <![
pub open spec fn lit_cond_end() -> Seq<u8> { seq![0x5Du8, 0x5D, 0x3E] }  // ]]>
pub open spec fn lit_comment_end() -> Seq<u8> { seq![0x2Du8, 0x2D, 0x3E] }  // -->
pub open spec fn lit_decl() -> Seq<u8> { seq![0x3Cu8, 0x21] }  // <!

/// The keyword of a conditional section `out[start..]` (`<![ S? kw S?`),
/// at its `[`: 1 INCLUDE, 2 IGNORE, 0 neither (§3.4 [61]-[63]).
pub open spec fn cond_kw(out: Seq<u8>, start: int) -> int {
    let j = ws_end(out, start + 3);
    if has_lit(out, j, lit_include()) && ws_end(out, j + 7) == out.len() {
        1
    } else if has_lit(out, j, lit_ignore()) && ws_end(out, j + 6) == out.len() {
        2
    } else {
        0
    }
}

/// The quote `q` written as a character reference.
pub open spec fn esc_quote(q: u8) -> Seq<u8> {
    if q == 0x22 {
        seq![0x26u8, 0x23, 0x33, 0x34, 0x3B]  // &#34;
    } else {
        seq![0x26u8, 0x23, 0x33, 0x39, 0x3B]  // &#39;
    }
}

/// The parameter entity declared by the tokens `t` of a declaration in
/// `out`, in the entity whose URI is `base` (`entity_decl`'s tape: the
/// `EntityDecl`, then an `EntityValue`, or a `PubId` and a `SysId`, or a
/// `SysId`). (The spans are in the output; the guards keep the spec
/// total.)
pub open spec fn pe_def(out: Seq<u8>, t: Seq<XTok>, base: Seq<u8>) -> Option<PeDef> {
    if t.len() < 2 {
        None
    } else {
        match t[0] {
            XTok::EntityDecl { start: na, end: nb, pe } => if !pe || !(0 <= na <= nb <= out.len()) {
                None
            } else {
                let name = out.subrange(na, nb);
                match t[1] {
                    XTok::EntityValue { start: va, end: vb } => if 0 <= va <= vb <= out.len() {
                        Some(
                            PeDef {
                                name,
                                internal: true,
                                rt: repl(out, va, vb),
                                sys: Seq::empty(),
                                pubid: Seq::empty(),
                                base,
                            },
                        )
                    } else {
                        None
                    },
                    XTok::SysId { start: sa, end: sb } => if 0 <= sa <= sb <= out.len() {
                        Some(
                            PeDef {
                                name,
                                internal: false,
                                rt: Seq::empty(),
                                sys: out.subrange(sa, sb),
                                pubid: Seq::empty(),
                                base,
                            },
                        )
                    } else {
                        None
                    },
                    XTok::PubId { start: pa, end: pb } => if t.len() >= 3 && 0 <= pa <= pb <= out.len() {
                        match t[2] {
                            XTok::SysId { start: sa, end: sb } => if 0 <= sa <= sb <= out.len() {
                                Some(
                                    PeDef {
                                        name,
                                        internal: false,
                                        rt: Seq::empty(),
                                        sys: out.subrange(sa, sb),
                                        pubid: out.subrange(pa, pb),
                                        base,
                                    },
                                )
                            } else {
                                None
                            },
                            _ => None,
                        }
                    } else {
                        None
                    },
                    _ => None,
                }
            },
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// External parsed entities: encoding and text declaration
// ---------------------------------------------------------------------------

/// The encoding an external entity's text declaration names, read as
/// ASCII (after a UTF-8 byte order mark): its span. `<?xml` S
/// VersionInfo? EncodingDecl.
pub open spec fn ext_declared_enc(b: Seq<u8>) -> Option<(int, int)> {
    let p0 = bom_end(b);
    if has_lit(b, p0, lit_xmldecl()) && 0 <= p0 + 5 < b.len() && is_ws(b[p0 + 5]) {
        let v = match version_info(b, p0 + 5) {
            Some((v, _, _)) => v,
            None => p0 + 5,
        };
        let j = ws_end(b, v);
        if j > v && has_lit(b, j, lit_encoding()) {
            match enc_span(b, j) {
                Some((_, x, y)) => Some((x, y)),
                None => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// The encoding an external entity is in (as `input_enc`, from its text
/// declaration).
pub open spec fn ext_enc(b: Seq<u8>) -> Enc {
    if has_lit(b, 0, seq![0xFEu8, 0xFF]) || has_lit(b, 0, seq![0xFFu8, 0xFE]) {
        Enc::Utf16
    } else {
        match ext_declared_enc(b) {
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

/// `b` decoded from `enc` to UTF-8 (as `decode_input`).
pub open spec fn decode_as(b: Seq<u8>, enc: Enc) -> Option<Seq<u8>> {
    match enc {
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

/// TextDecl ::= '<?xml' VersionInfo? EncodingDecl S? '?>'   [77], with
/// version 1.0 if any, at the
/// start of the decoded text `t` (after a byte order mark), read as being
/// in `enc`: where the entity's text begins.
pub open spec fn text_decl(t: Seq<u8>, enc: Enc) -> Option<int> {
    let p0 = bom_end(t);
    if has_lit(t, p0, lit_xmldecl()) && 0 <= p0 + 5 < t.len() && is_ws(t[p0 + 5]) {
        let j0 = ws_end(t, p0 + 5);
        let vr = if has_lit(t, j0, lit_version()) {
            match version_info(t, p0 + 5) {
                // An entity of a 1.0 document is 1.0 (erratum E38).
                Some((v, a, b)) => if b == a + 3 && t[a + 2] == 0x30 {
                    Some(v)
                } else {
                    None
                },
                None => None,
            }
        } else {
            Some(p0 + 5)
        };
        match vr {
            None => None,
            Some(v) => {
                let j = ws_end(t, v);
                if j > v && has_lit(t, j, lit_encoding()) {
                    match encoding_decl(t, j, enc) {
                        Some((e, _, _)) => {
                            let m = ws_end(t, e);
                            if has_lit(t, m, lit_pi_end()) {
                                Some(m + 2)
                            } else {
                                None
                            }
                        },
                        None => None,
                    }
                } else {
                    None
                }
            },
        }
    } else {
        Some(p0)
    }
}

/// An external entity's bytes read as text: decoded, every character a
/// `Char`; the text and where it begins after its text declaration. A
/// text longer than token positions hold (`MAX_POS`) is refused.
pub open spec fn ext_text(b: Seq<u8>) -> Option<(Seq<u8>, int)> {
    let enc = ext_enc(b);
    if b.len() == 0 {
        Some((Seq::empty(), 0))
    } else if b.len() > MAX_POS {
        None
    } else {
        match decode_as(b, enc) {
            None => None,
            Some(t) => if t.len() > MAX_POS || !doc_chars(t) {
                None
            } else {
                match text_decl(t, enc) {
                    Some(p) => Some((t, p)),
                    None => None,
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// One step
// ---------------------------------------------------------------------------

/// `st` with the top frame at `pos`.
pub open spec fn at(st: Fl, pos: int) -> Fl {
    let f = st.frames.last();
    Fl { frames: st.frames.update(st.frames.len() - 1, Frame { pos, ..f }), ..st }
}

/// Copy `n` bytes of the top frame to the output.
pub open spec fn copy(st: Fl, n: int) -> Fl {
    let f = st.frames.last();
    Fl { out: st.out + f.text.subrange(f.pos, f.pos + n), ..at(st, f.pos + n) }
}

/// Copy `n` bytes, then read in mode `m`.
pub open spec fn copy_to(st: Fl, n: int, m: Mode) -> Fl {
    Fl { mode: m, ..copy(st, n) }
}

/// A reference to a parameter entity that is not read, at `a..e` (`%` to
/// `;` included) of the top frame. In a standalone document it is left as
/// it is (where it is not allowed, the flattened DTD is rejected). Else
/// nothing more is processed: in the internal subset the rest is read
/// with references left as they are; in external text, the declaration
/// it is in is dropped, the reference is left between declarations, and
/// the rest of the external text is not read.
pub open spec fn unread(st: Fl, sa: bool, e: int) -> Fl {
    let f = st.frames.last();
    if sa {
        copy(st, e - f.pos)
    } else {
        let k = first_ext(st.frames);
        if k == st.frames.len() {
            Fl { stop: true, ..copy(st, e - f.pos) }
        } else {
            let keep = match st.mode {
                Mode::Decl { start, .. } => start,
                Mode::Cond { start } => start,
                _ => st.out.len() as int,
            };
            let r = f.text.subrange(f.pos, e);
            Fl {
                frames: st.frames.subrange(0, k),
                out: st.out.subrange(0, keep) + seq![0x20u8] + r + seq![0x20u8],
                mode: Mode::Sep,
                stop: true,
                ..st
            }
        }
    }
}

/// Push the text `t` (from `p`) of the parameter entity `k`, referred to
/// in mode `lit` / `sep`, after the reference that ends at `e` in the top
/// frame.
pub open spec fn push(st: Fl, t: Seq<u8>, p: int, ext: bool, k: int, lit: bool, sep: bool, base: Seq<u8>, e: int) -> Fl {
    let s2 = at(st, e);
    Fl {
        frames: s2.frames.push(Frame { text: t, pos: p, ext, pe: k, lit, sep, base }),
        out: if lit {
            st.out
        } else {
            st.out.push(0x20u8)
        },
        ..s2
    }
}

/// A reference `%Name;` to a parameter entity, whose name ends at `n` in
/// the top frame, recognized in a literal (`lit`) or between declarations
/// (`sep`) or elsewhere.
pub open spec fn peref(st: Fl, cfg: Cfg, n: int, lit: bool, sep: bool) -> Step {
    let f = st.frames.last();
    let e = n + 1;
    if st.stop {
        Step::Next(copy(st, e - f.pos))
    } else {
        match find_pe(st.pes, f.text.subrange(f.pos + 1, n)) {
            None => Step::Next(unread(st, cfg.sa, e)),
            Some(k) => {
                let d = st.pes[k];
                if on_stack(st.frames, k) {
                    Step::Bad
                } else if d.internal {
                    Step::Next(push(st, d.rt, 0, f.ext, k, lit, sep, d.base, e))
                } else if !cfg.load {
                    Step::Next(unread(st, cfg.sa, e))
                } else {
                    match (cfg.ld)(d.base, d.sys, d.pubid) {
                        None => Step::Next(unread(st, cfg.sa, e)),
                        Some((b, uri)) => match ext_text(b) {
                            None => Step::Bad,
                            Some((t, p)) => Step::Next(push(st, t, p, true, k, lit, sep, uri, e)),
                        },
                    }
                }
            },
        }
    }
}

/// The end of the top frame.
pub open spec fn pop(st: Fl) -> Step {
    let f = st.frames.last();
    let bad = match st.mode {
        Mode::Comment => true,
        Mode::Pi => true,
        Mode::Ignore { .. } => true,
        Mode::Decl { q, ld, .. } => q != 0 && ld == st.frames.len(),
        _ => false,
    };
    if bad || (f.sep && !(st.mode is Sep)) {
        Step::Bad
    } else {
        Step::Next(
            Fl {
                frames: st.frames.drop_last(),
                out: if f.pe >= 0 && !f.lit {
                    st.out.push(0x20u8)
                } else {
                    st.out
                },
                ..st
            },
        )
    }
}

/// No frame is open: read the external subset, or end.
pub open spec fn next_root(st: Fl, cfg: Cfg) -> Step {
    if st.ext_todo {
        let s2 = Fl { ext_todo: false, ..st };
        if cfg.has_ext && cfg.load && !st.stop {
            match (cfg.ld)(Seq::empty(), cfg.ext_sys, cfg.ext_pub) {
                None => Step::Next(s2),
                Some((b, uri)) => match ext_text(b) {
                    None => Step::Bad,
                    Some((t, p)) => Step::Next(
                        Fl {
                            frames: seq![Frame { text: t, pos: p, ext: true, pe: -1, lit: false, sep: true, base: uri }],
                            ..s2
                        },
                    ),
                },
            }
        } else {
            Step::Next(s2)
        }
    } else if st.mode is Sep && st.incl == 0 {
        Step::Done(st.out)
    } else {
        Step::Bad
    }
}

/// Between declarations.
pub open spec fn step_sep(st: Fl, cfg: Cfg) -> Step {
    let f = st.frames.last();
    let t = f.text;
    let i = f.pos;
    match pe_ref_at(t, i) {
        Some(n) => peref(st, cfg, n, false, true),
        None => if has_lit(t, i, lit_comment()) {
            Step::Next(copy_to(st, 4, Mode::Comment))
        } else if has_lit(t, i, lit_pi()) {
            Step::Next(copy_to(st, 2, Mode::Pi))
        } else if f.ext && has_lit(t, i, lit_cond()) {
            Step::Next(copy_to(st, 3, Mode::Cond { start: st.out.len() as int }))
        } else if f.ext && st.incl > 0 && has_lit(t, i, lit_cond_end()) {
            Step::Next(Fl { incl: st.incl - 1, ..at(st, i + 3) })
        } else if has_lit(t, i, lit_decl()) {
            Step::Next(
                copy_to(st, 2, Mode::Decl { start: st.out.len() as int, q: 0, ev: false, ld: 0, base: f.base }),
            )
        } else {
            Step::Next(copy(st, 1))
        },
    }
}

/// The end of a markup declaration at `start` in the output (just copied
/// its `>`): a parameter entity declaration is processed.
pub open spec fn end_decl(st: Fl, start: int, base: Seq<u8>) -> Step {
    let s2 = Fl { mode: Mode::Sep, ..st };
    if st.stop || !has_lit(st.out, start, lit_entity()) {
        Step::Next(s2)
    } else {
        match entity_decl(st.out, start, Seq::empty(), dtd_init(false)) {
            None => Step::Bad,
            Some((t, _, e)) => if e != st.out.len() {
                Step::Bad
            } else {
                match pe_def(st.out, t, base) {
                    Some(d) => Step::Next(Fl { pes: st.pes.push(d), ..s2 }),
                    None => Step::Next(s2),
                }
            },
        }
    }
}

/// In a markup declaration.
pub open spec fn step_decl(st: Fl, cfg: Cfg, start: int, q: u8, ev: bool, ld: int, base: Seq<u8>) -> Step {
    let f = st.frames.last();
    let t = f.text;
    let i = f.pos;
    let c = t[i];
    if q == 0 {
        if c == 0x3E {
            end_decl(copy(st, 1), start, base)
        } else if quote(c) {
            Step::Next(
                copy_to(st, 1, Mode::Decl { start, q: c, ev: is_ev(st.out, start), ld: st.frames.len() as int, base }),
            )
        } else if f.ext && pe_ref_at(t, i) is Some {
            peref(st, cfg, pe_ref_at(t, i).unwrap(), false, false)
        } else {
            Step::Next(copy(st, 1))
        }
    } else if c == q && ld == st.frames.len() {
        Step::Next(copy_to(st, 1, Mode::Decl { start, q: 0, ev: false, ld: 0, base }))
    } else if c == q {
        Step::Next(Fl { out: st.out + esc_quote(q), ..at(st, i + 1) })
    } else if ev && f.ext && pe_ref_at(t, i) is Some {
        peref(st, cfg, pe_ref_at(t, i).unwrap(), true, false)
    } else {
        Step::Next(copy(st, 1))
    }
}

/// In a conditional section's keyword.
pub open spec fn step_cond(st: Fl, cfg: Cfg, start: int) -> Step {
    let f = st.frames.last();
    let t = f.text;
    let i = f.pos;
    if t[i] == 0x5B {
        let kw = cond_kw(st.out, start);
        let s2 = Fl { out: st.out.subrange(0, start), ..at(st, i + 1) };
        if kw == 1 {
            Step::Next(Fl { mode: Mode::Sep, incl: st.incl + 1, ..s2 })
        } else if kw == 2 {
            Step::Next(Fl { mode: Mode::Ignore { depth: 1 }, ..s2 })
        } else {
            Step::Bad
        }
    } else if pe_ref_at(t, i) is Some {
        peref(st, cfg, pe_ref_at(t, i).unwrap(), false, false)
    } else {
        Step::Next(copy(st, 1))
    }
}

/// In an ignored section: nothing is recognized but the beginnings and
/// ends of sections (ignoreSectContents [64]).
pub open spec fn step_ignore(st: Fl, depth: int) -> Step {
    let f = st.frames.last();
    let t = f.text;
    let i = f.pos;
    if has_lit(t, i, lit_cond()) {
        Step::Next(Fl { mode: Mode::Ignore { depth: depth + 1 }, ..at(st, i + 3) })
    } else if has_lit(t, i, lit_cond_end()) {
        Step::Next(
            Fl {
                mode: if depth <= 1 {
                    Mode::Sep
                } else {
                    Mode::Ignore { depth: depth - 1 }
                },
                ..at(st, i + 3)
            },
        )
    } else {
        Step::Next(at(st, i + 1))
    }
}

pub open spec fn step(st: Fl, cfg: Cfg) -> Step {
    if st.frames.len() == 0 {
        next_root(st, cfg)
    } else {
        let f = st.frames.last();
        if !(0 <= f.pos < f.text.len()) {
            pop(st)
        } else {
            match st.mode {
                Mode::Sep => step_sep(st, cfg),
                Mode::Comment => if has_lit(f.text, f.pos, lit_comment_end()) {
                    Step::Next(copy_to(st, 3, Mode::Sep))
                } else {
                    Step::Next(copy(st, 1))
                },
                Mode::Pi => if has_lit(f.text, f.pos, lit_pi_end()) {
                    Step::Next(copy_to(st, 2, Mode::Sep))
                } else {
                    Step::Next(copy(st, 1))
                },
                Mode::Decl { start, q, ev, ld, base } => step_decl(st, cfg, start, q, ev, ld, base),
                Mode::Cond { start } => step_cond(st, cfg, start),
                Mode::Ignore { depth } => step_ignore(st, depth),
            }
        }
    }
}

/// At most `fuel` steps from `st`, while the output is shorter than
/// token positions hold.
pub open spec fn run(st: Fl, cfg: Cfg, fuel: nat) -> FlatRes
    decreases fuel,
{
    if fuel == 0 || st.out.len() >= MAX_POS {
        FlatRes::Limit
    } else {
        match step(st, cfg) {
            Step::Next(s2) => run(s2, cfg, (fuel - 1) as nat),
            Step::Done(o) => FlatRes::Ok(o),
            Step::Bad => FlatRes::Bad,
        }
    }
}

/// The start: the internal subset `sub` (the text between `[` and `]`).
pub open spec fn init(sub: Seq<u8>) -> Fl {
    Fl {
        frames: seq![Frame { text: sub, pos: 0, ext: false, pe: -1, lit: false, sep: true, base: Seq::empty() }],
        out: Seq::empty(),
        mode: Mode::Sep,
        pes: Seq::empty(),
        stop: false,
        incl: 0,
        ext_todo: true,
    }
}

/// The flattened DTD of the internal subset `sub`.
pub open spec fn flat(sub: Seq<u8>, cfg: Cfg, fuel: nat) -> FlatRes {
    run(init(sub), cfg, fuel)
}

// ---------------------------------------------------------------------------
// The document
// ---------------------------------------------------------------------------

/// What the document type declaration says, read as `doctype` reads it:
/// the internal subset's state (`DtdSt`), whether there is an external
/// identifier and what it is, and the span of the internal subset (the
/// text between `[` and `]`), if there is one.
pub struct DtInfo {
    pub st: DtdSt,
    pub ext: bool,
    pub sys: Seq<u8>,
    pub pubid: Seq<u8>,
    pub sub: Option<(int, int)>,
}

/// The system and public identifiers the tokens `t` hold from `k` on
/// (`external_id`'s: a `SysId`, or a `PubId` then a `SysId`).
pub open spec fn ext_ids(s: Seq<u8>, t: Seq<XTok>, k: int) -> (Seq<u8>, Seq<u8>) {
    if t.len() > k + 1 {
        match (t[k], t[k + 1]) {
            (XTok::PubId { start: pa, end: pb }, XTok::SysId { start: sa, end: sb }) => if 0 <= pa <= pb <= s.len()
                && 0 <= sa <= sb <= s.len() {
                (s.subrange(sa, sb), s.subrange(pa, pb))
            } else {
                (Seq::empty(), Seq::empty())
            },
            _ => (Seq::empty(), Seq::empty()),
        }
    } else if t.len() > k {
        match t[k] {
            XTok::SysId { start: sa, end: sb } => if 0 <= sa <= sb <= s.len() {
                (s.subrange(sa, sb), Seq::empty())
            } else {
                (Seq::empty(), Seq::empty())
            },
            _ => (Seq::empty(), Seq::empty()),
        }
    } else {
        (Seq::empty(), Seq::empty())
    }
}

/// `doctype` at `i`, with what it reads kept (`DtInfo`) instead of the
/// environment made of it.
pub open spec fn doctype_x(s: Seq<u8>, i: int, tape: Seq<XTok>, sa: bool) -> Option<(Seq<XTok>, int, DtInfo)> {
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
                let ids = ext_ids(s, t2, t1.len() as int);
                let m = ws_end(s, e);
                if byte_is(s, m, 0x5B) {
                    match int_subset(s, m + 1, t2, dtd_init(sa)) {
                        None => None,
                        Some((t3, st, q)) => {
                            let r = ws_end(s, q + 1);
                            if byte_is(s, r, 0x3E) {
                                Some(
                                    (
                                        t3.push(XTok::DoctypeEnd),
                                        r + 1,
                                        DtInfo { st, ext, sys: ids.0, pubid: ids.1, sub: Some((m + 1, q)) },
                                    ),
                                )
                            } else {
                                None
                            }
                        },
                    }
                } else if byte_is(s, m, 0x3E) {
                    Some(
                        (
                            t2.push(XTok::DoctypeEnd),
                            m + 1,
                            DtInfo { st: dtd_init(sa), ext, sys: ids.0, pubid: ids.1, sub: None },
                        ),
                    )
                } else {
                    None
                }
            },
        }
    }
}

/// `prolog`, with the document type declaration's `DtInfo` (if there is
/// one) in place of the environment, and the defaults not yet checked.
pub open spec fn prolog_x(s: Seq<u8>, enc: Enc) -> Option<(Seq<XTok>, int, Option<DtInfo>)> {
    match decl_head(s, enc) {
        None => None,
        Some((t0, p1, sd)) => match misc(s, p1, t0) {
            None => None,
            Some((t1, p2)) => {
                let dr = if has_lit(s, p2, lit_doctype()) {
                    match doctype_x(s, p2, t1, sd == 1) {
                        Some((t, e, d)) => Some((t, e, Some(d))),
                        None => None,
                    }
                } else {
                    Some((t1, p2, None))
                };
                match dr {
                    None => None,
                    Some((t2, p3, d)) => match misc(s, p3, t2) {
                        None => None,
                        Some((t3, p4)) => Some((t3, p4, d)),
                    },
                }
            },
        }
    }
}

/// The DTD is read whole (flattened): it has a parameter entity
/// reference, or an external subset to load.
pub open spec fn needs_flat(d: DtInfo, load: bool) -> bool {
    d.st.pe_seen || (load && d.ext)
}

pub open spec fn cfg_of(d: DtInfo, load: bool, ld: LoadFn) -> Cfg {
    Cfg { sa: d.st.sa, load, ld, has_ext: d.ext, ext_sys: d.sys, ext_pub: d.pubid }
}

pub open spec fn sub_text(s: Seq<u8>, d: DtInfo) -> Seq<u8> {
    match d.sub {
        Some((a, b)) => s.subrange(a, b),
        None => Seq::empty(),
    }
}

/// The declarations the content is checked against.
pub enum DtdRes {
    /// From the document's own text: the internal subset as written.
    Own(Env),
    /// From the flattened DTD `text` (`]` ends it), whose tape is `tape`.
    Flat { text: Seq<u8>, tape: Seq<XTok>, env: Env },
    Bad,
    Limit,
}

/// The flattened DTD `o` parsed as an internal subset: it must be one
/// whole, and its attribute defaults must be right. "Entity Declared" is
/// a WFC as for the document (§4.1): only if the document has neither an
/// external identifier nor a parameter entity reference, or is
/// standalone.
pub open spec fn flat_env(o: Seq<u8>, d: DtInfo) -> DtdRes {
    let text = o.push(0x5Du8);
    match int_subset(text, 0, Seq::empty(), dtd_init(d.st.sa)) {
        Some((tape, st, q)) => if q == o.len() {
            let env = env_of(text, st, d.ext || d.st.pe_seen);
            if defaults_ok(text, tape, env) {
                DtdRes::Flat { text, tape, env }
            } else {
                DtdRes::Bad
            }
        } else {
            DtdRes::Bad
        },
        None => DtdRes::Bad,
    }
}

/// The document's own declarations: its internal subset as written.
pub open spec fn own_env(s: Seq<u8>, t: Seq<XTok>, d: DtInfo) -> DtdRes {
    let env = env_of(s, d.st, d.ext);
    if defaults_ok(s, t, env) {
        DtdRes::Own(env)
    } else {
        DtdRes::Bad
    }
}

/// The declarations of the document `s`, whose prolog's tape is `t`. A
/// standalone document's DTD is read whole only to check it: what the
/// external subset and parameter entities declare does not count for its
/// content (WFC: Entity Declared, §4.1).
pub open spec fn dtd_x(s: Seq<u8>, t: Seq<XTok>, di: Option<DtInfo>, load: bool, ld: LoadFn, fuel: nat) -> DtdRes {
    match di {
        None => if defaults_ok(s, t, no_dtd()) {
            DtdRes::Own(no_dtd())
        } else {
            DtdRes::Bad
        },
        Some(d) => if !needs_flat(d, load) {
            own_env(s, t, d)
        } else {
            match flat(sub_text(s, d), cfg_of(d, load, ld), fuel) {
                FlatRes::Ok(o) => match flat_env(o, d) {
                    DtdRes::Flat { text, tape, env } => if d.st.sa {
                        own_env(s, t, d)
                    } else {
                        DtdRes::Flat { text, tape, env }
                    },
                    r => r,
                },
                FlatRes::Bad => DtdRes::Bad,
                FlatRes::Limit => DtdRes::Limit,
            }
        },
    }
}

pub enum DocRes {
    /// Well-formed: the document's tape, and the flattened DTD with its
    /// tape if it was flattened.
    Ok(Seq<XTok>, Option<(Seq<u8>, Seq<XTok>)>),
    Bad,
    Limit,
}

/// The content from `p` (the root element, then `Misc*` to the end),
/// against `env`.
pub open spec fn body_x(s: Seq<u8>, p: int, t: Seq<XTok>, env: Env, fl: Option<(Seq<u8>, Seq<XTok>)>) -> DocRes {
    match element(s, p, t, env) {
        None => DocRes::Bad,
        Some((t2, e)) => match misc(s, e, t2) {
            None => DocRes::Bad,
            Some((t3, f)) => if f == s.len() {
                DocRes::Ok(t3, fl)
            } else {
                DocRes::Bad
            },
        },
    }
}

/// `document`, with the DTD read whole where it has parameter entity
/// references or (with a loader) an external subset: the content is
/// checked against the flattened DTD's declarations.
pub open spec fn doc_x(s: Seq<u8>, enc: Enc, load: bool, ld: LoadFn, fuel: nat) -> DocRes {
    if !doc_chars(s) {
        DocRes::Bad
    } else {
        match prolog_x(s, enc) {
            None => DocRes::Bad,
            Some((t, p, di)) => match dtd_x(s, t, di, load, ld, fuel) {
                DtdRes::Own(env) => body_x(s, p, t, env, None),
                DtdRes::Flat { text, tape, env } => body_x(s, p, t, env, Some((text, tape))),
                DtdRes::Bad => DocRes::Bad,
                DtdRes::Limit => DocRes::Limit,
            },
        }
    }
}

/// An XML document in any encoding read here (`spec::parse`), with the
/// DTD read whole where it needs to be: the text in UTF-8, and `doc_x`.
pub open spec fn parse_x(b: Seq<u8>, load: bool, ld: LoadFn, fuel: nat) -> Option<(Seq<u8>, DocRes)> {
    match decode_input(b) {
        None => None,
        Some(u) => Some((u, doc_x(u, input_enc(b), load, ld, fuel))),
    }
}

} // verus!

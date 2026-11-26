//! The push parser: `Stream` takes the document a chunk at a time. Before
//! the root element it keeps all of the input (the prolog, which the
//! content refers to) and reads it an item at a time; from the root
//! element on, it keeps the prolog and a window (`stream::Win`).
//!
//! After each chunk, for every input `s` that begins with what was fed,
//! `parse(s)` is what the rest of `s` decides from where the parser
//! stands (`Stream::inv`); after the last chunk, the verdict is
//! `parse(input)`. A document that is not UTF-8 by its first bytes, or
//! whose XML declaration the parser cannot read before the declaration's
//! end, is handed back whole (`R_WHOLE`) for `enc::ex_parse`.
use crate::chars::*;
use crate::content::*;
use crate::doc::*;
use crate::items_spec::*;
use crate::dtd::*;
use crate::lex::*;
use crate::spec::*;
use crate::stable::*;
use crate::stable_pro::*;
use crate::stream::*;
use crate::stream_spec::*;
use crate::tape::*;
use verilith_core::prims::get;
use vstd::prelude::*;

verus! {

/// `Stream::phase`: at the start, before the end of the XML declaration (if any).
pub const PH_HEAD: u8 = 0;
/// In the `Misc*` after the XML declaration, before the document type declaration.
pub const PH_M1: u8 = 1;
/// In the `Misc*` after the document type declaration (or where it would be).
pub const PH_M2: u8 = 2;
/// In the root element, or after it.
pub const PH_BODY: u8 = 3;
/// The document is rejected; the rest of the input is not read.
pub const PH_FAILED: u8 = 4;
/// The document is to be parsed whole (`R_WHOLE`).
pub const PH_WHOLE: u8 = 5;
/// The verdict has been given.
pub const PH_DONE: u8 = 6;

/// `feed`'s results.
pub const R_MORE: u8 = 0;
/// The document is well-formed.
pub const R_OK: u8 = 1;
/// The document is rejected.
pub const R_ERR: u8 = 2;
/// The document is to be parsed whole, once all of it is fed.
pub const R_WHOLE: u8 = 3;
/// The window outgrew the token positions.
pub const R_LIMIT: u8 = 4;

/// The push parser's state (see the module docs).
pub struct Stream {
    /// The window over the input.
    pub w: Win,
    /// Where the parser is in the document (`PH_HEAD` to `PH_DONE`).
    pub phase: u8,
    /// Before the root element: the tape, and how much of it was emitted.
    pub ptape: Tape,
    /// How many of `ptape`'s tokens were emitted.
    pub pmark: usize,
    /// The XML declaration's standalone declaration: 0 absent, 1 `yes`, 2 `no`.
    pub sd: u8,
    /// The prolog's text and what its document type declaration declares.
    pub pro: Vec<u8>,
    /// What the document type declaration declares.
    pub dtd: DtdOut,
    /// The entities and attribute defaults declared, as the spec's environment.
    pub genv: Ghost<Env>,
    /// How far the document type declaration has been scanned for its end.
    pub dscan: DScan,
    /// The encoding the input was in: UTF-8, when the input is the text
    /// (`Stream::new`); another, when the text is the input decoded
    /// (`Stream::decoded`), whose declaration must name it.
    pub enc: Enc,
}

/// A scan of the document type declaration for where it may end, as the
/// input comes (as libxml2's `xmlParseLookupInternalSubset`): the prolog is
/// parsed once it can be complete, not again on every chunk. The scan only
/// times the parse; the parse decides.
pub struct DScan {
    /// How far the scan has read, from the declaration's start.
    pub at: usize,
    /// Where the scan is (`D_HEAD` to `D_END`).
    pub mode: u8,
    /// The quote that closes the literal the scan is in.
    pub q: u8,
}

/// The scan's modes: in the declaration before its internal subset, in a
/// literal there; in the subset, in a markup declaration, in a literal there,
/// in a comment, in a processing instruction; after the subset; at the end.
pub const D_HEAD: u8 = 0;
/// In a literal, before the internal subset.
pub const D_HEAD_LIT: u8 = 1;
/// In the internal subset.
pub const D_SUB: u8 = 2;
/// In a markup declaration.
pub const D_DECL: u8 = 3;
/// In a literal in a markup declaration.
pub const D_DECL_LIT: u8 = 4;
/// In a comment.
pub const D_COMMENT: u8 = 5;
/// In a processing instruction.
pub const D_PI: u8 = 6;
/// After the internal subset.
pub const D_AFTER: u8 = 7;
/// At the declaration's end.
pub const D_END: u8 = 8;

/// The scan of the declaration that starts at `p`, from where it was left
/// to the end of `buf`: whether its `>` has come.
fn dscan_step(d: &mut DScan, buf: &[u8], p: usize) -> bool
    requires
        p < buf@.len(),
{
    let n = buf.len();
    if d.at < p || d.at > n {
        d.at = p;
        d.mode = D_HEAD;
        d.q = 0;
    }
    while d.at < n
        invariant
            d.at <= n,
            n == buf@.len(),
        decreases n - d.at,
    {
        let k = d.at;
        let c = buf[k];
        let mut step: usize = 1;
        if d.mode == D_HEAD {
            if c == 0x22 || c == 0x27 {
                d.mode = D_HEAD_LIT;
                d.q = c;
            } else if c == 0x5B {
                d.mode = D_SUB;
            } else if c == 0x3E && k > p {
                d.at = k + 1;
                d.mode = D_END;
                return true;
            }
        } else if d.mode == D_HEAD_LIT || d.mode == D_DECL_LIT {
            if c == d.q {
                d.mode = if d.mode == D_HEAD_LIT {
                    D_HEAD
                } else {
                    D_DECL
                };
            }
        } else if d.mode == D_SUB {
            if c == 0x5D {
                d.mode = D_AFTER;
            } else if c == 0x3C {
                // A comment, a processing instruction or a declaration: the
                // next three bytes tell.
                if n - k < 4 {
                    return false;
                }
                if buf[k + 1] == 0x21 && buf[k + 2] == 0x2D && buf[k + 3] == 0x2D {
                    d.mode = D_COMMENT;
                    step = 4;
                } else if buf[k + 1] == 0x3F {
                    d.mode = D_PI;
                    step = 2;
                } else {
                    d.mode = D_DECL;
                }
            }
        } else if d.mode == D_DECL {
            if c == 0x22 || c == 0x27 {
                d.mode = D_DECL_LIT;
                d.q = c;
            } else if c == 0x3E {
                d.mode = D_SUB;
            }
        } else if d.mode == D_COMMENT {
            if c == 0x2D {
                if n - k < 3 {
                    return false;
                }
                if buf[k + 1] == 0x2D && buf[k + 2] == 0x3E {
                    d.mode = D_SUB;
                    step = 3;
                }
            }
        } else if d.mode == D_PI {
            if c == 0x3F {
                if n - k < 2 {
                    return false;
                }
                if buf[k + 1] == 0x3E {
                    d.mode = D_SUB;
                    step = 2;
                }
            }
        } else if d.mode == D_AFTER {
            if c == 0x3E {
                d.at = k + 1;
                d.mode = D_END;
                return true;
            }
        } else {
            return true;
        }
        d.at = k + step;
    }
    d.mode == D_END
}

impl Stream {
    pub open spec fn seen(&self) -> Seq<u8> {
        self.w.seen@
    }

    pub open spec fn utf8(&self) -> bool {
        enc_ok(self.seen(), self.enc)
    }

    pub open spec fn pro_ok(&self) -> bool {
        &&& self.pro@.len() <= MAX_POS
        &&& out_wf(self.pro@, &self.dtd)
        &&& out_view(self.pro@, &self.dtd) == self.genv@
        &&& ext(self.pro@, self.seen())
    }

    /// Before the root element: all of the input is kept.
    pub open spec fn pre(&self) -> bool {
        &&& self.w.base == 0
        &&& self.w.win_ok()
        &&& self.w.chars_inv()
        &&& self.ptape@.len() <= self.w.pos
        &&& self.pmark <= self.ptape@.len()
        &&& self.w.mode == M_ITEM
        &&& self.w.names_ok()
        &&& self.w.gst@.len() == 0
    }

    pub open spec fn m1_goal(&self) -> bool {
        forall|s: Seq<u8>|
            #[trigger] ext(self.seen(), s) ==> docx(s) == (if doc_chars(s) {
                after_m1(s, self.w.pos as int, self.ptape@, self.sd as int)
            } else {
                None
            })
    }

    pub open spec fn m2_goal(&self) -> bool {
        forall|s: Seq<u8>|
            #[trigger] ext(self.seen(), s) ==> docx(s) == (if doc_chars(s) {
                after_m2(s, self.w.pos as int, self.ptape@, self.genv@)
            } else {
                None
            })
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.phase <= PH_DONE
        &&& self.phase == PH_HEAD ==> self.pre() && self.w.pos == 0 && self.ptape@.len() == 0 && self.w.cpos == 0
        &&& self.phase == PH_M1 ==> self.pre() && self.utf8() && no_dflt(self.ptape@) && self.sd <= 2
            && self.m1_goal()
        &&& self.phase == PH_M2 ==> self.pre() && self.utf8() && self.pro_ok() && dflt_ok(
            self.pro@,
            self.ptape@,
            self.pro@.len() as int,
        ) && self.m2_goal()
        &&& self.phase == PH_BODY ==> self.utf8() && self.pro_ok() && self.w.inv(self.genv@)
        &&& self.phase == PH_FAILED ==> self.utf8() && fails(self.seen(), false)
        &&& self.phase == PH_WHOLE ==> self.w.base == 0 && self.w.win_ok()
    }

    /// Every token emitted so far, at positions in the input.
    pub open spec fn emitted(&self) -> Seq<XTok> {
        self.w.emitted()
    }

    /// What has been emitted: before the root element, the prolog's tokens
    /// up to `pmark`; from it on, the tokens read so far (`Win::emits`).
    pub open spec fn items_ok(&self) -> bool {
        &&& (self.phase == PH_HEAD || self.phase == PH_M1 || self.phase == PH_M2) ==> self.w.base == 0 && self.pmark
            <= self.ptape@.len() && self.emitted() == self.ptape@.subrange(0, self.pmark as int)
        &&& self.phase == PH_WHOLE ==> self.emitted().len() == 0
        &&& self.phase == PH_BODY ==> self.w.emits()
    }

    /// The same input, kept the same way.
    /// The verdict `r` (`R_OK`, `R_ERR`) on the input seen (`last`: all
    /// of it): on the text, on the input it is (when that is the text), and
    /// the text is read in the encoding it says it was in.
    pub open spec fn verdict(&self, r: u8, last: bool) -> bool {
        &&& r == R_OK ==> last && docx(self.seen()) is Some && enc_ok(self.seen(), self.enc) && (self.enc == Enc::Utf8
            ==> parse(self.seen()) is Some)
        &&& r == R_ERR ==> fails(self.seen(), last) && enc_ok(self.seen(), self.enc) && (self.enc == Enc::Utf8
            ==> fails_parse(self.seen(), last))
    }

    pub open spec fn same_input(&self, o: &Stream) -> bool {
        self.w.seen == o.w.seen && self.w.buf == o.w.buf && self.w.base == o.w.base && self.w.cpos == o.w.cpos
    }
}

/// A new parser, before any input, for input in UTF-8 (`Enc::Utf8`: the
/// input is the text), or for the text of input in `enc`, decoded.
pub fn stream_new(enc: Enc) -> (r: Stream)
    ensures
        r.inv(),
        r.phase == PH_HEAD,
        r.enc == enc,
        r.seen() == Seq::<u8>::empty(),
        r.items_ok(),
        r.emitted() == Seq::<XTok>::empty(),
{
    let pro: Vec<u8> = Vec::new();
    let dtd = DtdOut::none(pro.as_slice());
    let r = Stream {
        w: Win {
            buf: Vec::new(),
            base: 0,
            pos: 0,
            cpos: 0,
            mode: M_ITEM,
            tem: 0,
            tcr: false,
            tfirst: false,
            names: Vec::new(),
            ends: Vec::new(),
            out: Tape::new(),
            seen: Ghost(Seq::empty()),
            gst: Ghost(Seq::empty()),
            gt: Ghost(Seq::empty()),
            gts: Ghost(0),
            ge: Ghost(Emitted { prev: Seq::empty(), groups: Seq::empty(), open: Seq::empty() }),
        },
        phase: PH_HEAD,
        ptape: Tape::new(),
        pmark: 0,
        sd: 0,
        pro,
        dtd,
        genv: Ghost(no_dtd()),
        dscan: DScan { at: 0, mode: D_HEAD, q: 0 },
        enc,
    };
    proof {
        assert(r.emitted() =~= Seq::<XTok>::empty());
        assert(r.ptape@.subrange(0, 0) =~= Seq::<XTok>::empty());
        assert(r.w.buf@ =~= r.w.seen@.subrange(0, 0));
        assert forall|s: Seq<u8>| #[trigger] ext(r.seen(), s) implies doc_chars(s) == chars_from(s, 0) by {}
    }
    r
}

#[verifier::spinoff_prover]
proof fn lemma_head_goal(b: Seq<u8>, seen: Seq<u8>, n: int, p0: int, e: Enc)
    requires
        b == seen.subrange(0, seen.len() as int),
        n == b.len(),
        n >= 1,
        e == Enc::Utf8 ==> b[0] != 0xFE && b[0] != 0xFF,
        n >= 3 || b[0] != 0xEF,
        p0 == bom_end(b),
        decl_decided(b, p0, n),
        has_decl(b, p0) ==> (xmldecl(b, p0, e) matches Some((_, f, _)) && f <= n),
        decl_head(b, e) is Some,
    ensures
        enc_ok(seen, e),
        ({
            let (t0, p1, sd) = decl_head(b, e).unwrap();
            forall|s: Seq<u8>|
                #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                    after_m1(s, p1, t0, sd)
                } else {
                    None
                })
        }),
{
    hide(after_m1);
    hide(doc_chars);
    hide(xmldecl);
    hide(document);
    hide(input_enc);
    assert(b =~= seen);
    let (t0, p1, sd) = decl_head(b, e).unwrap();
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies (e == Enc::Utf8 ==> input_enc(s) == Enc::Utf8) && document(s, e)
        == docx(s) && docx(s) == (if doc_chars(s) {
        after_m1(s, p1, t0, sd)
    } else {
        None
    }) by {
        lemma_window(b, seen, 0, s);
        assert(seen.subrange(0, seen.len() as int) =~= seen);
        if e == Enc::Utf8 {
            lemma_head_utf8(b, s, n);
        }
        lemma_head_enc(b, s, n, e);
        reveal(document);
        lemma_document(s, e);
    }
}

/// Whether `?>` is in `b` from `q`.
fn has_pi_end(b: &[u8], q: usize) -> bool {
    let n = b.len();
    let mut i = q;
    while i < n && n - i > 1
        invariant
            n == b@.len(),
        decreases n - i,
    {
        if b[i] == 0x3F && b[i + 1] == 0x3E {
            return true;
        }
        i = i + 1;
    }
    false
}

/// Whether the window decides that no XML declaration starts at `p0`.
fn decl_mismatch(b: &[u8], p0: usize) -> (r: bool)
    requires
        p0 <= 3,
    ensures
        r ==> exists|q: int| 0 <= q < 5 && p0 + q < b@.len() && #[trigger] b@[p0 + q] != lit_xmldecl()[q],
{
    proof {
        lemma_lits();
    }
    let n = b.len();
    let mut k: usize = 0;
    while k < 5 && p0 + k < n
        invariant
            k <= 5,
            n == b@.len(),
            p0 <= 3,
            L_XMLDECL@ == lit_xmldecl(),
        decreases 5 - k,
    {
        if get(b, p0 + k) != L_XMLDECL[k] {
            proof {
                assert(b@[p0 + k as int] != lit_xmldecl()[k as int]);
            }
            return true;
        }
        k = k + 1;
    }
    false
}

/// The byte order mark and the XML declaration, once the window decides
/// them.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn head_step(st: &mut Stream) -> (r: u8)
    requires
        old(st).inv(),
        old(st).phase == PH_HEAD,
    ensures
        final(st).enc == old(st).enc,
        final(st).inv(),
        final(st).same_input(old(st)),
        r == S_ON ==> final(st).phase == PH_M1,
        r == S_WAIT ==> final(st).phase == PH_HEAD,
        r == S_FAIL ==> final(st).phase == PH_WHOLE,
        r == S_ON || r == S_WAIT || r == S_FAIL,
        final(st).w.out == old(st).w.out,
        final(st).w.ge == old(st).w.ge,
        final(st).pmark == old(st).pmark,
{
    hide(document);
    hide(xmldecl);
    hide(doc_chars);
    hide(after_m1);
    proof {
        lemma_lits();
    }
    slice_len_bound(st.w.buf.as_slice());
    let n = st.w.buf.len();
    if n == 0 {
        return S_WAIT;
    }
    let b0 = get(st.w.buf.as_slice(), 0);
    let raw = match st.enc {
        Enc::Utf8 => true,
        _ => false,
    };
    if raw && (b0 == 0xFE || b0 == 0xFF) {
        st.phase = PH_WHOLE;
        return S_FAIL;
    }
    if b0 == 0xEF && n < 3 {
        return S_WAIT;
    }
    proof {
        assert(st.enc == Enc::Utf8 ==> st.w.buf@[0] != 0xFE && st.w.buf@[0] != 0xFF);
    }
    let p0: usize = if n >= 3 && b0 == 0xEF && get(st.w.buf.as_slice(), 1) == 0xBB && get(st.w.buf.as_slice(), 2)
        == 0xBF {
        proof {
            assert(st.w.buf@.subrange(0, 3) =~= seq![0xEFu8, 0xBB, 0xBF]);
        }
        3
    } else {
        proof {
            if n >= 3 {
                assert(st.w.buf@.subrange(0, 3)[0] == st.w.buf@[0]);
                assert(st.w.buf@.subrange(0, 3)[1] == st.w.buf@[1]);
                assert(st.w.buf@.subrange(0, 3)[2] == st.w.buf@[2]);
            }
        }
        0
    };
    proof {
        assert(p0 == bom_end(st.w.buf@));
    }
    // Whether the window decides that a declaration starts at `p0`.
    let mism = decl_mismatch(st.w.buf.as_slice(), p0);
    if !mism && p0 + 6 > n {
        return S_WAIT;
    }
    proof {
        assert(decl_decided(st.w.buf@, p0 as int, n as int));
    }
    let hd = ex_has_lit(st.w.buf.as_slice(), p0, &L_XMLDECL) && p0 + 5 < n && ex_is_ws(get(st.w.buf.as_slice(), p0 + 5));
    proof {
        assert(hd == has_decl(st.w.buf@, p0 as int));
    }
    if hd {
        let mut t0 = Tape::new();
        match ex_xmldecl(st.w.buf.as_slice(), p0, &mut t0, st.enc) {
            Some((e, sd)) => {
                proof {
                    lemma_xmldecl_end(st.w.buf@, p0 as int, st.enc);
                    lemma_head_goal(st.w.buf@, st.w.seen@, n as int, p0 as int, st.enc);
                }
                st.ptape = t0;
                st.w.pos = e;
                st.sd = sd;
                st.phase = PH_M1;
                proof {
                    assert(decl_head(st.w.buf@, st.enc) == Some((st.ptape@, e as int, sd as int)));
                    assert(st.pre());
                    assert(st.utf8());
                    assert(st.m1_goal());
                }
                S_ON
            },
            None => {
                // The declaration is not one this parser reads before its
                // end, or it has not ended yet.
                if has_pi_end(st.w.buf.as_slice(), p0 + 5) {
                    st.phase = PH_WHOLE;
                    return S_FAIL;
                }
                S_WAIT
            },
        }
    } else {
        proof {
            lemma_head_goal(st.w.buf@, st.w.seen@, n as int, p0 as int, st.enc);
            assert(decl_head(st.w.buf@, st.enc) == Some((Seq::<XTok>::empty(), p0 as int, 0int)));
            assert(no_dflt(Seq::<XTok>::empty()));
        }
        st.w.pos = p0;
        st.sd = 0;
        st.phase = PH_M1;
        proof {
            assert(st.ptape@ == Seq::<XTok>::empty());
            assert(st.pre());
            assert(st.utf8());
            assert(st.m1_goal());
        }
        S_ON
    }
}


// ---------------------------------------------------------------------------
// Tapes
// ---------------------------------------------------------------------------

/// Appends `u`'s tokens to `t`.
pub fn tape_append(t: &mut Tape, u: &Tape)
    ensures
        final(t)@ == old(t)@ + u@,
{
    let n = u.toks.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == u@.len(),
            n == u.toks@.len(),
            t@ == old(t)@ + u@.subrange(0, i as int),
        decreases n - i,
    {
        let x = u.toks[i];
        proof {
            assert(x@ == u@[i as int]);
        }
        t.push(x);
        proof {
            assert(u@.subrange(0, i as int + 1) =~= u@.subrange(0, i as int).push(u@[i as int]));
        }
        i = i + 1;
    }
    proof {
        assert(u@.subrange(0, n as int) =~= u@);
    }
}

/// A copy of `u`.
pub fn tape_copy(u: &Tape) -> (r: Tape)
    ensures
        r@ == u@,
{
    let mut t = Tape::new();
    tape_append(&mut t, u);
    proof {
        assert(Seq::<XTok>::empty() + u@ =~= u@);
    }
    t
}

// ---------------------------------------------------------------------------
// Misc before the root element, on every input that begins with `seen`
// ---------------------------------------------------------------------------

proof fn lemma_lit_back(seen: Seq<u8>, s: Seq<u8>, k: int, lit: Seq<u8>)
    requires
        ext(seen, s),
        0 <= k,
        k + lit.len() <= seen.len(),
        has_lit(s, k, lit),
    ensures
        has_lit(seen, k, lit),
{
    assert(s.subrange(k, k + lit.len()) =~= seen.subrange(k, k + lit.len())) by {
        assert forall|i: int| 0 <= i < lit.len() implies #[trigger] s.subrange(k, k + lit.len())[i] == seen.subrange(
            k,
            k + lit.len(),
        )[i] by {
            lemma_ext_byte(seen, s, k + i);
        }
    }
}

/// `Misc` stops at `p`: the window decides that no part of it starts
/// there.
proof fn lemma_misc_stops(seen: Seq<u8>, p: int, t: Seq<XTok>)
    requires
        0 <= p < seen.len(),
        !is_ws(seen[p]),
        seen[p] != 0x3C || (p + 1 < seen.len() && seen[p + 1] != 0x3F && (seen[p + 1] != 0x21 || (p + 4
            <= seen.len() && !has_lit(seen, p, lit_comment())))),
    ensures
        forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> misc(s, p, t) == Some((t, p)),
{
    lemma_lits_stable();
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies misc(s, p, t) == Some((t, p)) by {
        lemma_ext_byte(seen, s, p);
        if seen[p] == 0x3C {
            lemma_ext_byte(seen, s, p + 1);
        }
        assert(!has_lit(s, p, lit_comment())) by {
            if has_lit(s, p, lit_comment()) {
                assert(s.subrange(p, p + 4)[0] == s[p]);
                assert(s.subrange(p, p + 4)[1] == s[p + 1]);
                if seen[p] == 0x3C && seen[p + 1] == 0x21 {
                    lemma_lit_back(seen, s, p, lit_comment());
                }
            }
        }
        assert(!has_lit(s, p, lit_pi())) by {
            if has_lit(s, p, lit_pi()) {
                assert(s.subrange(p, p + 2)[0] == s[p]);
                assert(s.subrange(p, p + 2)[1] == s[p + 1]);
            }
        }
        lemma_misc_stop(s, p, t);
    }
}

/// White space at `p`.
proof fn lemma_misc_ws_all(seen: Seq<u8>, p: int, t: Seq<XTok>)
    requires
        0 <= p < seen.len(),
        is_ws(seen[p]),
    ensures
        forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> misc(s, p, t) == misc(s, p + 1, t),
{
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies misc(s, p, t) == misc(s, p + 1, t) by {
        lemma_ext_byte(seen, s, p);
        lemma_misc_ws(s, p, t);
    }
}

/// The comment the window has at `p`.
proof fn lemma_misc_comment_all(seen: Seq<u8>, p: int, t: Seq<XTok>)
    requires
        0 <= p,
        has_lit(seen, p, lit_comment()),
        comment(seen, p, Seq::empty()) matches Some((_, e)) && e <= seen.len(),
    ensures
        ({
            let (u, e) = comment(seen, p, Seq::empty()).unwrap();
            &&& e >= p + 7
            &&& no_dflt(u)
            &&& u.len() == 1
            &&& forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> misc(s, p, t) == misc(s, e, t + u)
        }),
{
    let (u, e) = comment(seen, p, Seq::empty()).unwrap();
    lemma_ext_refl(seen);
    lemma_window(seen, seen, 0, seen);
    lemma_comment_pre(seen, seen, seen.len() as int, p, Seq::empty());
    assert(added(Seq::<XTok>::empty(), u) =~= u);
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies misc(s, p, t) == misc(s, e, t + u) by {
        lemma_window(seen, seen, 0, s);
        lemma_comment_pre(seen, s, seen.len() as int, p, Seq::empty());
        lemma_comment_tape(s, p, t);
        lemma_ext_lit(seen, s, p, lit_comment());
        lemma_misc_comment(s, p, t);
    }
}

/// The processing instruction the window has at `p`.
proof fn lemma_misc_pi_all(seen: Seq<u8>, p: int, t: Seq<XTok>)
    requires
        0 <= p,
        has_lit(seen, p, lit_pi()),
        pi(seen, p, Seq::empty()) matches Some((_, e)) && e <= seen.len(),
    ensures
        ({
            let (u, e) = pi(seen, p, Seq::empty()).unwrap();
            &&& e >= p + 4
            &&& no_dflt(u)
            &&& u.len() == 2
            &&& forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> misc(s, p, t) == misc(s, e, t + u)
        }),
{
    let (u, e) = pi(seen, p, Seq::empty()).unwrap();
    lemma_ext_refl(seen);
    lemma_window(seen, seen, 0, seen);
    lemma_pi_pre(seen, seen, seen.len() as int, p, Seq::empty());
    assert(added(Seq::<XTok>::empty(), u) =~= u);
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies misc(s, p, t) == misc(s, e, t + u) by {
        lemma_window(seen, seen, 0, s);
        lemma_pi_pre(seen, s, seen.len() as int, p, Seq::empty());
        lemma_pi_tape(s, p, t);
        lemma_ext_lit(seen, s, p, lit_pi());
        lemma_misc_pi(s, p, t);
    }
}

/// Moving over a part of `Misc` keeps both goals.
proof fn lemma_misc_move(seen: Seq<u8>, p: int, t: Seq<XTok>, p2: int, t2: Seq<XTok>, sd: int, env: Env)
    requires
        forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> misc(s, p, t) == misc(s, p2, t2),
    ensures
        (forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_m1(s, p, t, sd)
            } else {
                None
            })) ==> (forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_m1(s, p2, t2, sd)
            } else {
                None
            })),
        (forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_m2(s, p, t, env)
            } else {
                None
            })) ==> (forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_m2(s, p2, t2, env)
            } else {
                None
            })),
{
    hide(document);
    hide(doc_chars);
}

/// One part of `Misc` before the root element: white space, a comment or
/// a processing instruction (`S_ON`); or where `Misc` stops, which every
/// input that begins with what was fed agrees on (`S_DONE`).
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
fn misc_step(st: &mut Stream) -> (r: u8)
    requires
        old(st).inv(),
        old(st).phase == PH_M1 || old(st).phase == PH_M2,
    ensures
        final(st).enc == old(st).enc,
        final(st).inv(),
        final(st).same_input(old(st)),
        final(st).phase == old(st).phase,
        final(st).sd == old(st).sd,
        final(st).pro == old(st).pro,
        final(st).dtd == old(st).dtd,
        final(st).genv == old(st).genv,
        final(st).pmark == old(st).pmark,
        final(st).w.out == old(st).w.out,
        final(st).w.ge == old(st).w.ge,
        extends(old(st).ptape@, final(st).ptape@),
        r == S_ON || r == S_WAIT || r == S_DONE,
        r == S_ON ==> final(st).w.pos > old(st).w.pos,
        r != S_ON ==> final(st).w.pos == old(st).w.pos && final(st).ptape@ == old(st).ptape@,
        r == S_DONE ==> final(st).w.pos < final(st).w.buf@.len() && (forall|s: Seq<u8>|
            #[trigger] ext(final(st).seen(), s) ==> misc(s, final(st).w.pos as int, final(st).ptape@) == Some(
                (final(st).ptape@, final(st).w.pos as int),
            )),
{
    hide(after_m1);
    hide(after_m2);
    hide(misc);
    hide(document);
    hide(doc_chars);
    hide(comment);
    hide(pi);
    proof {
        lemma_lits();
    }
    slice_len_bound(st.w.buf.as_slice());
    let n = st.w.buf.len();
    let p = st.w.pos;
    let ghost seen = st.w.seen@;
    let ghost t = st.ptape@;
    proof {
        assert(seen.subrange(0, seen.len() as int) =~= seen);
        assert(st.w.buf@ == seen);
        assert(t.subrange(0, t.len() as int) =~= t);
    }
    if p == n {
        return S_WAIT;
    }
    let x = get(st.w.buf.as_slice(), p);
    if ex_is_ws(x) {
        proof {
            lemma_misc_ws_all(seen, p as int, t);
        }
        st.w.pos = p + 1;
        proof {
            assert(old(st).seen() == st.seen());
            lemma_misc_move(st.seen(), p as int, t, st.w.pos as int, st.ptape@, st.sd as int, st.genv@);
            if st.phase == PH_M1 {
                assert(old(st).m1_goal());
            } else {
                assert(old(st).m2_goal());
            }
            assert(st.pre());
            if st.phase == PH_M1 {
                assert(no_dflt(st.ptape@));
                assert(st.m1_goal());
            } else {
                assert(dflt_ok(st.pro@, st.ptape@, st.pro@.len() as int));
                assert(st.m2_goal());
            }
        }
        return S_ON;
    }
    if x != 0x3C {
        proof {
            lemma_misc_stops(seen, p as int, t);
        }
        return S_DONE;
    }
    if n - p < 2 {
        return S_WAIT;
    }
    let y = get(st.w.buf.as_slice(), p + 1);
    if y == 0x3F {
        let mut tp = Tape::new();
        match ex_pi(st.w.buf.as_slice(), p, &mut tp) {
            Some(e) => {
                proof {
                    assert(st.w.buf@.subrange(p as int, p + 2) =~= lit_pi());
                    lemma_misc_pi_all(seen, p as int, t);
                    if st.phase == PH_M1 {
                        lemma_no_dflt_add(t, tp@);
                    }
                    lemma_no_dflt_ok(st.pro@, tp@, st.pro@.len() as int);
                    if st.phase == PH_M2 {
                        lemma_dflt_ok_add(st.pro@, t, tp@, st.pro@.len() as int);
                    }
                }
                tape_append(&mut st.ptape, &tp);
                st.w.pos = e;
                proof {
                    assert(st.ptape@.subrange(0, t.len() as int) =~= t);
                    assert(old(st).seen() == st.seen());
                    lemma_misc_move(st.seen(), p as int, t, st.w.pos as int, st.ptape@, st.sd as int, st.genv@);
                    if st.phase == PH_M1 {
                        assert(old(st).m1_goal());
                    } else {
                        assert(old(st).m2_goal());
                    }
                    assert(st.pre());
                    if st.phase == PH_M1 {
                        assert(no_dflt(st.ptape@));
                        assert(st.m1_goal());
                    } else {
                        assert(dflt_ok(st.pro@, st.ptape@, st.pro@.len() as int));
                        assert(st.m2_goal());
                    }
                }
                S_ON
            },
            None => S_WAIT,
        }
    } else if y == 0x21 {
        if n - p < 4 {
            return S_WAIT;
        }
        if ex_has_lit(st.w.buf.as_slice(), p, &L_COMMENT) {
            let mut tp = Tape::new();
            match ex_comment(st.w.buf.as_slice(), p, &mut tp) {
                Some(e) => {
                    proof {
                        lemma_misc_comment_all(seen, p as int, t);
                        if st.phase == PH_M1 {
                            lemma_no_dflt_add(t, tp@);
                        }
                        lemma_no_dflt_ok(st.pro@, tp@, st.pro@.len() as int);
                        if st.phase == PH_M2 {
                            lemma_dflt_ok_add(st.pro@, t, tp@, st.pro@.len() as int);
                        }
                    }
                    tape_append(&mut st.ptape, &tp);
                    st.w.pos = e;
                    proof {
                        assert(st.ptape@.subrange(0, t.len() as int) =~= t);
                        assert(old(st).seen() == st.seen());
                        lemma_misc_move(st.seen(), p as int, t, st.w.pos as int, st.ptape@, st.sd as int, st.genv@);
                        if st.phase == PH_M1 {
                            assert(old(st).m1_goal());
                        } else {
                            assert(old(st).m2_goal());
                        }
                        assert(st.pre());
                        if st.phase == PH_M1 {
                            assert(no_dflt(st.ptape@));
                            assert(st.m1_goal());
                        } else {
                            assert(dflt_ok(st.pro@, st.ptape@, st.pro@.len() as int));
                            assert(st.m2_goal());
                            assert(old(st).utf8());
                            assert(old(st).seen() == st.seen());
                            assert(st.utf8());
                            assert(st.inv());
                        }
                    }
                    S_ON
                },
                None => S_WAIT,
            }
        } else {
            proof {
                lemma_misc_stops(seen, p as int, t);
            }
            S_DONE
        }
    } else {
        proof {
            lemma_misc_stops(seen, p as int, t);
        }
        S_DONE
    }
}


/// Whether the window decides that `lit` is not at `p`.
fn lit_mismatch(b: &[u8], p: usize, lit: &[u8]) -> (r: bool)
    ensures
        r ==> exists|q: int| 0 <= q < lit@.len() && p + q < b@.len() && #[trigger] b@[p + q] != lit@[q],
{
    let n = b.len();
    let l = lit.len();
    let mut k: usize = 0;
    while k < l && p < n && k < n - p
        invariant
            k <= l,
            n == b@.len(),
            l == lit@.len(),
        decreases l - k,
    {
        if b[p + k] != lit[k] {
            proof {
                assert(b@[p + k as int] != lit@[k as int]);
            }
            return true;
        }
        k = k + 1;
    }
    false
}

proof fn lemma_no_lit_ext(seen: Seq<u8>, p: int, lit: Seq<u8>, q: int)
    requires
        0 <= p,
        0 <= q < lit.len(),
        p + q < seen.len(),
        seen[p + q] != lit[q],
    ensures
        forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> !has_lit(s, p, lit),
{
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies !has_lit(s, p, lit) by {
        lemma_ext_byte(seen, s, p + q);
        if has_lit(s, p, lit) {
            assert(s.subrange(p, p + lit.len())[q] == s[p + q]);
        }
    }
}

/// No document type declaration, on every input: the goal after it.
proof fn lemma_m1_none(seen: Seq<u8>, p: int, t: Seq<XTok>, sd: int)
    requires
        forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> misc(s, p, t) == Some((t, p)),
        forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> !has_lit(s, p, lit_doctype()),
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_m1(s, p, t, sd)
            } else {
                None
            }),
    ensures
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_m2(s, p, t, no_dtd())
            } else {
                None
            }),
{
    hide(document);
    hide(doc_chars);
    hide(after_m2);
    hide(misc);
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies docx(s) == (if doc_chars(s) {
        after_m2(s, p, t, no_dtd())
    } else {
        None
    }) by {
        lemma_m1_stop(s, p, t, sd);
    }
}

/// The document type declaration the window has at `p`, on every input.
proof fn lemma_m1_doctype(seen: Seq<u8>, p: int, t: Seq<XTok>, sd: int)
    requires
        0 <= p,
        forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> misc(s, p, t) == Some((t, p)),
        has_lit(seen, p, lit_doctype()),
        doctype(seen, p, t, sd == 1) matches Some((_, e, _)) && e <= seen.len(),
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_m1(s, p, t, sd)
            } else {
                None
            }),
    ensures
        ({
            let (u, e, env) = doctype(seen, p, t, sd == 1).unwrap();
            forall|s: Seq<u8>|
                #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                    after_m2(s, e, u, env)
                } else {
                    None
                })
        }),
{
    hide(document);
    hide(doc_chars);
    hide(after_m2);
    hide(misc);
    hide(doctype);
    let (u, e, env) = doctype(seen, p, t, sd == 1).unwrap();
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies docx(s) == (if doc_chars(s) {
        after_m2(s, e, u, env)
    } else {
        None
    }) by {
        assert(seen.subrange(0, seen.len() as int) =~= seen);
        lemma_window(seen, seen, 0, s);
        lemma_doctype_eq(seen, s, seen.len() as int, p, t, sd == 1);
        lemma_ext_lit(seen, s, p, lit_doctype());
        lemma_m1_stop(s, p, t, sd);
    }
}

/// The declaration's tokens and the prolog's text, kept: defaults refer
/// to `x` before `e`.
proof fn lemma_m1_dflt(x: Seq<u8>, pro: Seq<u8>, p: int, t: Seq<XTok>, sd: int)
    requires
        0 <= p,
        no_dflt(t),
        doctype(x, p, t, sd == 1) matches Some((_, e, _)) && e <= x.len() && pro == x.subrange(0, e),
    ensures
        doctype(pro, p, t, sd == 1) == doctype(x, p, t, sd == 1),
        dflt_ok(pro, doctype(x, p, t, sd == 1).unwrap().0, pro.len() as int),
        doctype(x, p, t, sd == 1).unwrap().1 > p + 9,
        doctype(x, p, t, sd == 1).unwrap().0.len() >= t.len(),
{
    hide(doctype);
    let (u, e, env) = doctype(x, p, t, sd == 1).unwrap();
    assert(ag(x, x, x.len() as int));
    lemma_doctype_eq(x, x, x.len() as int, p, t, sd == 1);
    assert(ag(x, pro, e)) by {
        assert forall|k: int| 0 <= k < e implies #[trigger] x[k] == pro[k - 0] by {}
    }
    lemma_doctype_eq(x, pro, e, p, t, sd == 1);
    assert(ag(pro, pro, e));
    lemma_doctype_eq(pro, pro, e, p, t, sd == 1);
    lemma_no_dflt_ok(pro, t, e);
    lemma_dflt_ok_add(pro, t, added(t, u), e);
    assert(t + added(t, u) =~= u);
}

/// Where `Misc` stopped before the document type declaration: the
/// declaration, once the window has all of it, or none, once the window
/// decides there is none.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
fn m1_decide(st: &mut Stream) -> (r: u8)
    requires
        old(st).inv(),
        old(st).phase == PH_M1,
        old(st).w.pos < old(st).w.buf@.len(),
        forall|s: Seq<u8>|
            #[trigger] ext(old(st).seen(), s) ==> misc(s, old(st).w.pos as int, old(st).ptape@) == Some(
                (old(st).ptape@, old(st).w.pos as int),
            ),
    ensures
        final(st).enc == old(st).enc,
        final(st).inv(),
        final(st).same_input(old(st)),
        final(st).pmark == old(st).pmark,
        final(st).w.out == old(st).w.out,
        final(st).w.ge == old(st).w.ge,
        extends(old(st).ptape@, final(st).ptape@),
        r == S_ON || r == S_WAIT,
        r == S_ON ==> final(st).phase == PH_M2,
        r == S_WAIT ==> final(st).phase == PH_M1 && final(st).w.pos == old(st).w.pos && final(st).ptape@ == old(
            st,
        ).ptape@,
{
    hide(after_m1);
    hide(after_m2);
    hide(misc);
    hide(document);
    hide(doc_chars);
    hide(doctype);
    proof {
        lemma_lits();
    }
    slice_len_bound(st.w.buf.as_slice());
    let n = st.w.buf.len();
    let p = st.w.pos;
    let ghost seen = st.w.seen@;
    let ghost t = st.ptape@;
    let ghost sd = st.sd as int;
    proof {
        assert(t.subrange(0, t.len() as int) =~= t);
        assert(seen.subrange(0, seen.len() as int) =~= seen);
        assert(st.w.buf@ == seen);
        assert(old(st).m1_goal());
        assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies misc(s, p as int, t) == Some((t, p as int)) by {
            assert(ext(old(st).seen(), s));
        }
        assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies docx(s) == (if doc_chars(s) {
            after_m1(s, p as int, t, sd)
        } else {
            None
        }) by {
            assert(ext(old(st).seen(), s));
        }
    }
    if ex_has_lit(st.w.buf.as_slice(), p, &L_DOCTYPE) {
        let mut t1 = tape_copy(&st.ptape);
        match ex_doctype_opt(st.w.buf.as_slice(), p, &mut t1, st.sd) {
            Some((e, _d)) => {
                let mut pro: Vec<u8> = Vec::new();
                push_slice(&mut pro, st.w.buf.as_slice(), 0, e);
                let mut t2 = tape_copy(&st.ptape);
                proof {
                    assert(pro@ =~= seen.subrange(0, e as int));
                    lemma_m1_dflt(seen, pro@, p as int, t, sd);
                    lemma_m1_doctype(seen, p as int, t, sd);
                    assert(has_lit(pro@, p as int, lit_doctype())) by {
                        assert(pro@.subrange(p as int, p + 9) =~= seen.subrange(p as int, p + 9));
                    }
                }
                match ex_doctype_opt(pro.as_slice(), p, &mut t2, st.sd) {
                    Some((e2, d2)) => {
                        let ghost env = doctype(seen, p as int, t, sd == 1).unwrap().2;
                        st.ptape = t2;
                        st.w.pos = e2;
                        st.pro = pro;
                        st.dtd = d2;
                        st.genv = Ghost(env);
                        st.phase = PH_M2;
                        proof {
                            // The declaration's tokens follow the tape's.
                            assert(agree(pro@, pro@, 0, pro@.len() as int, 0));
                            lemma_doctype_eq(pro@, pro@, pro@.len() as int, p as int, t, sd == 1);
                            assert(e2 == e);
                            assert(ext(st.pro@, seen)) by {
                                assert(seen.subrange(0, st.pro@.len() as int) =~= st.pro@);
                            }
                            assert(st.pro_ok());
                            assert(st.pre());
                            assert(st.m2_goal());
                            assert(old(st).utf8());
                            assert(old(st).seen() == st.seen());
                            assert(st.utf8());
                            assert(st.inv());
                        }
                        S_ON
                    },
                    None => {
                        proof {
                            assert(false);
                        }
                        S_WAIT
                    },
                }
            },
            None => S_WAIT,
        }
    } else if n - p >= 9 || lit_mismatch(st.w.buf.as_slice(), p, &L_DOCTYPE) {
        proof {
            if n - p >= 9 {
                assert(!(seen.subrange(p as int, p + 9) =~= lit_doctype()));
                let q = choose|q: int| 0 <= q < 9 && #[trigger] seen.subrange(p as int, p + 9)[q] != lit_doctype()[q];
                assert(seen.subrange(p as int, p + 9)[q] == seen[p + q]);
                lemma_no_lit_ext(seen, p as int, lit_doctype(), q);
            } else {
                let q = choose|q: int| 0 <= q < 9 && p + q < seen.len() && #[trigger] seen[p + q] != lit_doctype()[q];
                lemma_no_lit_ext(seen, p as int, lit_doctype(), q);
            }
            lemma_m1_none(seen, p as int, t, sd);
            lemma_no_dflt_ok(Seq::<u8>::empty(), t, 0);
        }
        let pro: Vec<u8> = Vec::new();
        let d = DtdOut::none(pro.as_slice());
        proof {
            assert(ents_view(pro@, d.ents@) =~= Seq::<Ent>::empty());
            assert(d.oka@ =~= Seq::<bool>::empty());
            assert(d.okc@ =~= Seq::<bool>::empty());
            assert(out_view(pro@, &d) == no_dtd());
        }
        st.pro = pro;
        st.dtd = d;
        st.genv = Ghost(no_dtd());
        st.phase = PH_M2;
        proof {
            assert(ext(st.pro@, seen)) by {
                assert(seen.subrange(0, 0) =~= st.pro@);
            }
            assert(st.pro_ok());
            assert(st.pre());
            assert(st.m2_goal());
            assert(dflt_ok(st.pro@, st.ptape@, st.pro@.len() as int));
            assert(old(st).utf8());
            assert(old(st).seen() == st.seen());
            assert(st.utf8());
            assert(st.inv());
        }
        S_ON
    } else {
        S_WAIT
    }
}


// ---------------------------------------------------------------------------
// The root element's start tag
// ---------------------------------------------------------------------------

/// The root element's start tag, which the window has: the goal in its
/// content.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_root_goal(seen: Seq<u8>, pro: Seq<u8>, p: int, t: Seq<XTok>, env: Env)
    requires
        0 <= p,
        p + 1 < seen.len(),
        seen[p] == 0x3C,
        seen[p + 1] != 0x2F && seen[p + 1] != 0x21 && seen[p + 1] != 0x3F,
        ext(pro, seen),
        dflt_ok(pro, t, pro.len() as int),
        defaults_ok(pro, t, env),
        forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> misc(s, p, t) == Some((t, p)),
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_m2(s, p, t, env)
            } else {
                None
            }),
        item(seen, p, Seq::empty(), Seq::empty(), env) matches Some((_, _, e)) && e <= seen.len(),
    ensures
        ({
            let (sx, u, e) = item(seen, p, Seq::empty(), Seq::empty(), env).unwrap();
            &&& e > p
            &&& sx.len() == 0 || sx == Seq::<Open>::empty().push((p + 1, name_end(seen, p + 1), 0int))
            &&& forall|s: Seq<u8>|
                #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                    after_content(
                        s,
                        e,
                        stack_mv(Seq::empty(), sx, Seq::empty(), 0, t.len() as int),
                        t + mv(added(Seq::empty(), u), 0, t.len() as int),
                        env,
                    )
                } else {
                    None
                })
        }),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    hide(after_root);
    hide(item);
    hide(misc);
    hide(defaults_ok);
    let (sx, u, e) = item(seen, p, Seq::empty(), Seq::empty(), env).unwrap();
    assert(seen.subrange(0, seen.len() as int) =~= seen);
    lemma_ext_refl(seen);
    lemma_window(seen, seen, 0, seen);
    assert(!is_etag(seen, p));
    assert(item_reach(seen, p, e) == e);
    lemma_item_mv(seen, seen, 0, seen.len() as int, 0, p, Seq::empty(), Seq::empty(), Seq::empty(), Seq::empty(), env);
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies docx(s) == (if doc_chars(s) {
        after_content(
            s,
            e,
            stack_mv(Seq::empty(), sx, Seq::empty(), 0, t.len() as int),
            t + mv(added(Seq::empty(), u), 0, t.len() as int),
            env,
        )
    } else {
        None
    }) by {
        lemma_window(seen, seen, 0, s);
        lemma_item_mv(seen, s, 0, seen.len() as int, 0, p, Seq::empty(), Seq::empty(), Seq::empty(), t, env);
        lemma_ext_byte(seen, s, p);
        lemma_ext_byte(seen, s, p + 1);
        lemma_root_item(s, p, t, env);
        lemma_ext_trans(pro, seen, s);
        assert(pro.subrange(0, pro.len() as int) =~= pro);
        lemma_window(pro, pro, 0, s);
        lemma_defaults_ok_eq(pro, s, pro.len() as int, t, env);
        lemma_m2_stop(s, p, t, env);
    }
}

/// No root element at `p`, or defaults that fail: the document fails.
proof fn lemma_root_fails(seen: Seq<u8>, pro: Seq<u8>, p: int, t: Seq<XTok>, env: Env)
    requires
        0 <= p < seen.len(),
        seen[p] != 0x3C || (ext(pro, seen) && dflt_ok(pro, t, pro.len() as int) && !defaults_ok(pro, t, env)),
        forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> misc(s, p, t) == Some((t, p)),
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_m2(s, p, t, env)
            } else {
                None
            }),
    ensures
        fails(seen, false),
{
    hide(document);
    hide(doc_chars);
    hide(after_root);
    hide(misc);
    hide(defaults_ok);
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (false ==> s == seen) implies docx(s) is None by {
        lemma_m2_stop(s, p, t, env);
        if seen[p] != 0x3C {
            lemma_ext_byte(seen, s, p);
            lemma_after_root_not_lt(s, p, t, env);
        } else {
            lemma_ext_trans(pro, seen, s);
            assert(pro.subrange(0, pro.len() as int) =~= pro);
            lemma_window(pro, pro, 0, s);
            lemma_defaults_ok_eq(pro, s, pro.len() as int, t, env);
        }
    }
}

/// Emits the prolog's tokens not yet emitted.
fn flush_pro(st: &mut Stream)
    ensures
        final(st).enc == old(st).enc,
        final(st).w.buf == old(st).w.buf,
        final(st).w.seen == old(st).w.seen,
        final(st).w.base == old(st).w.base,
        final(st).w.pos == old(st).w.pos,
        final(st).w.cpos == old(st).w.cpos,
        final(st).w.mode == old(st).w.mode,
        final(st).w.tem == old(st).w.tem,
        final(st).w.tcr == old(st).w.tcr,
        final(st).w.tfirst == old(st).w.tfirst,
        final(st).w.names == old(st).w.names,
        final(st).w.ends == old(st).w.ends,
        final(st).w.gst == old(st).w.gst,
        final(st).w.gt == old(st).w.gt,
        final(st).w.gts == old(st).w.gts,
        final(st).phase == old(st).phase,
        final(st).ptape == old(st).ptape,
        final(st).pmark == (if old(st).pmark <= old(st).ptape@.len() {
            old(st).ptape@.len() as int
        } else {
            old(st).pmark as int
        }),
        final(st).sd == old(st).sd,
        final(st).pro == old(st).pro,
        final(st).dtd == old(st).dtd,
        final(st).genv == old(st).genv,
        final(st).w.ge == old(st).w.ge,
        old(st).pmark <= old(st).ptape@.len() ==> final(st).w.out@ == old(st).w.out@ + old(st).ptape@.subrange(
            old(st).pmark as int,
            old(st).ptape@.len() as int,
        ),
{
    let n = st.ptape.toks.len();
    let mut i = st.pmark;
    while i < n
        invariant
            n == st.ptape.toks@.len(),
            st.ptape == old(st).ptape,
            st.w.buf == old(st).w.buf,
            st.w.seen == old(st).w.seen,
            st.w.base == old(st).w.base,
            st.w.pos == old(st).w.pos,
            st.w.cpos == old(st).w.cpos,
            st.w.mode == old(st).w.mode,
            st.w.tem == old(st).w.tem,
            st.w.tcr == old(st).w.tcr,
            st.w.tfirst == old(st).w.tfirst,
            st.w.names == old(st).w.names,
            st.w.ends == old(st).w.ends,
            st.w.gst == old(st).w.gst,
            st.w.gt == old(st).w.gt,
            st.w.gts == old(st).w.gts,
            st.phase == old(st).phase,
            st.sd == old(st).sd,
            st.pro == old(st).pro,
            st.dtd == old(st).dtd,
            st.genv == old(st).genv,
            st.pmark == old(st).pmark,
            st.w.ge == old(st).w.ge,
            old(st).pmark <= i,
            old(st).pmark <= n ==> old(st).pmark <= i <= n && st.w.out@ == old(st).w.out@ + st.ptape@.subrange(
                old(st).pmark as int,
                i as int,
            ),
        decreases n - i,
    {
        let x = st.ptape.toks[i];
        st.w.out.push(x);
        proof {
            assert(x@ == st.ptape@[i as int]);
            assert(st.ptape@.subrange(old(st).pmark as int, i + 1) =~= st.ptape@.subrange(
                old(st).pmark as int,
                i as int,
            ).push(st.ptape@[i as int]));
        }
        i = i + 1;
    }
    if st.pmark <= n {
        st.pmark = n;
    }
}

/// The root element's start tag, once the window has it (`S_ON`); a
/// document that fails at the root (`S_FAIL`).
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
fn m2_root(st: &mut Stream) -> (r: u8)
    requires
        old(st).inv(),
        old(st).items_ok(),
        old(st).phase == PH_M2,
        old(st).w.pos < old(st).w.buf@.len(),
        forall|s: Seq<u8>|
            #[trigger] ext(old(st).seen(), s) ==> misc(s, old(st).w.pos as int, old(st).ptape@) == Some(
                (old(st).ptape@, old(st).w.pos as int),
            ),
    ensures
        final(st).enc == old(st).enc,
        final(st).inv(),
        final(st).items_ok(),
        final(st).same_input(old(st)),
        r == S_ON || r == S_WAIT || r == S_FAIL,
        r == S_ON ==> final(st).phase == PH_BODY,
        r == S_FAIL ==> final(st).phase == PH_FAILED,
        r == S_WAIT ==> final(st).phase == PH_M2 && final(st).w.pos == old(st).w.pos && final(st).ptape@ == old(
            st,
        ).ptape@ && final(st).pmark == old(st).pmark,
{
    hide(after_m2);
    hide(after_content);
    hide(misc);
    hide(document);
    hide(doc_chars);
    hide(item);
    hide(defaults_ok);
    slice_len_bound(st.w.buf.as_slice());
    slice_len_bound(st.pro.as_slice());
    let n = st.w.buf.len();
    let p = st.w.pos;
    let ghost seen = st.w.seen@;
    let ghost t = st.ptape@;
    let ghost envv = st.genv@;
    proof {
        assert(seen.subrange(0, seen.len() as int) =~= seen);
        assert(st.w.buf@ == seen);
        assert(old(st).m2_goal());
        assert(old(st).utf8());
        assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies misc(s, p as int, t) == Some((t, p as int)) by {
            assert(ext(old(st).seen(), s));
        }
        assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies docx(s) == (if doc_chars(s) {
            after_m2(s, p as int, t, envv)
        } else {
            None
        }) by {
            assert(ext(old(st).seen(), s));
        }
    }
    let x = get(st.w.buf.as_slice(), p);
    if x != 0x3C {
        proof {
            lemma_root_fails(seen, st.pro@, p as int, t, envv);
        }
        st.phase = PH_FAILED;
        proof {
            assert(st.seen() == seen);
            assert(st.utf8());
        }
        return S_FAIL;
    }
    if n - p < 2 {
        return S_WAIT;
    }
    let y = get(st.w.buf.as_slice(), p + 1);
    if y == 0x2F || y == 0x21 || y == 0x3F {
        return S_WAIT;
    }
    let ok = {
        let env = st.dtd.env(st.pro.as_slice());
        ex_defaults_ok(st.pro.as_slice(), &st.ptape, &env)
    };
    if !ok {
        proof {
            lemma_root_fails(seen, st.pro@, p as int, t, envv);
        }
        st.phase = PH_FAILED;
        proof {
            assert(st.seen() == seen);
            assert(st.utf8());
        }
        return S_FAIL;
    }
    let mut sc: Vec<(usize, usize, usize)> = Vec::new();
    let mut tp = Tape::new();
    proof {
        assert(stack_view(sc@) =~= Seq::<Open>::empty());
    }
    let res = {
        let env = st.dtd.env(st.pro.as_slice());
        ex_item(st.w.buf.as_slice(), p, &mut sc, &mut tp, &env)
    };
    match res {
        Some(e) => {
            let ghost (sx, u, _e) = item(seen, p as int, Seq::empty(), Seq::empty(), envv).unwrap();
            let ghost gst2 = stack_mv(Seq::empty(), sx, Seq::empty(), 0, t.len() as int);
            let ghost gt2 = t + mv(added(Seq::empty(), u), 0, t.len() as int);
            proof {
                lemma_root_goal(seen, st.pro@, p as int, t, envv);
                assert(sc@.len() == sx.len());
            }
            let ghost out0 = st.w.out@;
            let ghost pm = st.pmark as int;
            flush_pro(st);
            let ghost out1 = st.w.out@;
            if sc.len() == 1 {
                let top = sc[0];
                proof {
                    assert(stack_view(sc@)[0] == sx[0]);
                    assert(top.0 == p + 1 && top.1 == name_end(seen, p + 1));
                    assert(stack_ok(seen, sc@, tp@));
                    assert(sc@[0] == top);
                    assert(gst2 == Seq::<Open>::empty().push((top.0 as int, top.1 as int, t.len() as int)));
                }
                win_push_name(&mut st.w, top.0, top.1, Ghost((top.0 as int, top.1 as int, t.len() as int)));
            } else {
                proof {
                    assert(gst2 == Seq::<Open>::empty());
                }
            }
            st.w.out.toks.append(&mut tp.toks);
            st.w.pos = e;
            proof {
                st.w.gst@ = gst2;
                st.w.gt@ = gt2;
                // Emitted: the prolog's tokens, then the start tag's, each
                // its own group.
                let g0 = st.w.ge@;
                assert(st.w.out@ =~= out1 + u);
                assert(out1 == out0 + t.subrange(pm, t.len() as int));
                lemma_mv_zero(out0);
                lemma_mv_zero(st.w.out@);
                assert(g0.prev + out0 == t.subrange(0, pm));
                assert(st.w.emitted() =~= t + u) by {
                    assert(t.subrange(0, pm) + t.subrange(pm, t.len() as int) =~= t);
                }
                assert(t.subrange(0, t.len() as int) =~= t);
                lemma_pre_ext(t, t);
                lemma_pre_grps(t, t);
                lemma_sing(sing(t, 0), t, u, 0, t.len() as int);
                lemma_mv_zero(u);
                assert(added(Seq::<XTok>::empty(), u) =~= u);
                st.w.ge@ = Emitted { prev: g0.prev, groups: sing(t, 0) + sing(u, 0), open: Seq::empty() };
                assert(st.w.emitted() =~= flat(st.w.ge@.groups) + st.w.ge@.open);
                if sx.len() > 0 {
                    assert(sc@[0].2 < u.len());
                }
                assert(opens_in(st.w.gst@, st.w.gt@.len() as int));
                assert(st.w.emits());
            }
            st.phase = PH_BODY;
            proof {
                assert(st.seen() == seen);
                assert(st.utf8());
                assert(st.pro_ok());
                assert(st.w.goal(envv));
                assert(st.w.inv(envv));
            }
            S_ON
        },
        None => S_WAIT,
    }
}


// ---------------------------------------------------------------------------
// The last chunk before the root element: the rest of the document, whole
// ---------------------------------------------------------------------------

/// `after_m2` on `s` from `p`.
fn m2_finish(s: &[u8], p: usize, tape: &mut Tape, env: &XEnv) -> (r: bool)
    requires
        p <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= p,
        env_wf(env),
    ensures
        r == after_m2(s@, p as int, old(tape)@, env_view(env)) is Some,
        r ==> final(tape)@ == after_m2(s@, p as int, old(tape)@, env_view(env)).unwrap(),
{
    let n = s.len();
    match ex_misc(s, p, tape) {
        None => false,
        Some(p4) => {
            if !ex_defaults_ok(s, tape, env) {
                return false;
            }
            match ex_element(s, p4, tape, env) {
                None => false,
                Some(e) => match ex_misc(s, e, tape) {
                    None => false,
                    Some(f) => f == n,
                },
            }
        },
    }
}

/// `after_m1` on `s` from `p`.
fn m1_finish(s: &[u8], p: usize, tape: &mut Tape, sd: u8) -> (r: bool)
    requires
        p <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= p,
    ensures
        r == after_m1(s@, p as int, old(tape)@, sd as int) is Some,
        r ==> final(tape)@ == after_m1(s@, p as int, old(tape)@, sd as int).unwrap(),
{
    hide(after_m2);
    match ex_misc(s, p, tape) {
        None => false,
        Some(p2) => match ex_doctype_opt(s, p2, tape, sd) {
            None => false,
            Some((p3, d)) => {
                let env = d.env(s);
                m2_finish(s, p3, tape, &env)
            },
        },
    }
}

/// The document, at the last chunk, in `M1` or `M2`: all of it is in the
/// window.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn pro_finish(st: &mut Stream) -> (r: bool)
    requires
        old(st).inv(),
        old(st).phase == PH_M1 || old(st).phase == PH_M2,
        old(st).w.cpos == old(st).w.buf@.len(),
    ensures
        final(st).enc == old(st).enc,
        final(st).w == old(st).w,
        final(st).pmark == old(st).pmark,
        final(st).phase == old(st).phase,
        r == docx(old(st).seen()) is Some,
        r ==> final(st).ptape@ == docx(old(st).seen()).unwrap(),
        r ==> pre(old(st).ptape@, final(st).ptape@),
{
    hide(document);
    hide(doc_chars);
    hide(after_m2);
    hide(after_m1);
    slice_len_bound(st.w.buf.as_slice());
    slice_len_bound(st.pro.as_slice());
    let ghost seen = st.w.seen@;
    let ghost t = st.ptape@;
    proof {
        assert(seen.subrange(0, seen.len() as int) =~= seen);
        assert(st.w.buf@ == seen);
        lemma_ext_refl(seen);
        lemma_chars_end(seen);
        assert(doc_chars(seen));
        assert(t.len() <= st.w.pos);
    }
    if st.phase == PH_M1 {
        proof {
            assert(old(st).m1_goal());
            assert(docx(seen) == after_m1(seen, st.w.pos as int, t, st.sd as int));
        }
        let r = m1_finish(st.w.buf.as_slice(), st.w.pos, &mut st.ptape, st.sd);
        proof {
            if r {
                reveal(after_m1);
                lemma_after_m1_pre(seen, st.w.pos as int, t, st.sd as int);
            }
        }
        r
    } else {
        proof {
            assert(old(st).m2_goal());
            assert(docx(seen) == after_m2(seen, st.w.pos as int, t, st.genv@));
        }
        let env = st.dtd.env(st.pro.as_slice());
        let r = m2_finish(st.w.buf.as_slice(), st.w.pos, &mut st.ptape, &env);
        proof {
            if r {
                reveal(after_m2);
                lemma_after_m2_pre(seen, st.w.pos as int, t, st.genv@);
            }
        }
        r
    }
}


// ---------------------------------------------------------------------------
// Taking a chunk; dropping what has been read
// ---------------------------------------------------------------------------

/// `b` is `a` with `d` fed.
pub open spec fn fed(a: &Win, b: &Win, d: Seq<u8>) -> bool {
    &&& b.seen@ == a.seen@ + d
    &&& b.buf@ == a.buf@ + d
    &&& b.base == a.base
    &&& b.pos == a.pos
    &&& b.cpos == a.cpos
    &&& b.mode == a.mode
    &&& b.tem == a.tem
    &&& b.tcr == a.tcr
    &&& b.names == a.names
    &&& b.ends == a.ends
    &&& b.gst == a.gst
    &&& b.gt == a.gt
    &&& b.gts == a.gts
}

proof fn lemma_fed_ext(a: Seq<u8>, d: Seq<u8>, s: Seq<u8>)
    requires
        ext(a + d, s),
    ensures
        ext(a, s),
{
    assert(ext(a, a + d)) by {
        assert((a + d).subrange(0, a.len() as int) =~= a);
    }
    lemma_ext_trans(a, a + d, s);
}

#[verifier::spinoff_prover]
proof fn lemma_win_fed(a: &Win, b: &Win, d: Seq<u8>, env: Env)
    requires
        fed(a, b, d),
        a.win_ok(),
        b.buf@.len() <= MAX_POS,
    ensures
        b.win_ok(),
        a.names_ok() ==> b.names_ok(),
        a.mode_ok() ==> b.mode_ok(),
        a.chars_inv() ==> b.chars_inv(),
        a.goal(env) ==> b.goal(env),
        fails(a.seen@, false) ==> fails(b.seen@, false),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    let sa = a.seen@;
    let sb = b.seen@;
    assert(ext(sa, sb)) by {
        assert(sb.subrange(0, sa.len() as int) =~= sa);
    }
    assert(b.buf@ =~= sb.subrange(b.base as int, sb.len() as int));
    if a.names_ok() {
        assert forall|q: int| 0 <= q < b.ends@.len() implies b.nstart(q) <= #[trigger] b.ends@[q] <= b.names@.len()
            && 0 <= b.gst@[q].0 <= b.gst@[q].1 <= sb.len() && b.names@.subrange(b.nstart(q), b.ends@[q] as int)
            == sb.subrange(b.gst@[q].0, b.gst@[q].1) by {
            assert(a.ends@[q] == b.ends@[q]);
            assert(sb.subrange(b.gst@[q].0, b.gst@[q].1) =~= sa.subrange(a.gst@[q].0, a.gst@[q].1));
        }
    }
    if a.mode_ok() {
        let ts = a.gts@;
        let k = a.base + a.pos;
        if a.mode == M_TEXT {
            lemma_ext_byte(sa, sb, ts);
            lemma_has_cr_ext(sa, sb, ts, k);
            assert forall|s: Seq<u8>| #[trigger] ext(sb, s) implies text_end(s, ts) == text_end(s, k) by {
                lemma_ext_trans(sa, sb, s);
            }
        }
        if a.mode == M_CDATA {
            lemma_ext_lit(sa, sb, ts, lit_cdata());
            lemma_has_cr_ext(sa, sb, ts + 9, k);
            assert forall|s: Seq<u8>| #[trigger] ext(sb, s) implies cdata_end(s, ts + 9) == cdata_end(s, k) by {
                lemma_ext_trans(sa, sb, s);
            }
        }
    }
    if a.chars_inv() {
        assert forall|s: Seq<u8>| #[trigger] ext(sb, s) implies doc_chars(s) == chars_from(s, b.base + b.cpos) by {
            lemma_ext_trans(sa, sb, s);
        }
    }
    if a.goal(env) {
        assert forall|s: Seq<u8>| #[trigger] ext(sb, s) implies docx(s) == (if doc_chars(s) {
            after_content(s, b.at(), b.gst@, b.gt@, env)
        } else {
            None
        }) by {
            lemma_ext_trans(sa, sb, s);
        }
    }
    if fails(sa, false) {
        assert forall|s: Seq<u8>| #[trigger] ext(sb, s) && (false ==> s == sb) implies docx(s) is None by {
            lemma_ext_trans(sa, sb, s);
        }
    }
}

/// Appends the chunk.
fn win_append(w: &mut Win, data: &[u8])
    requires
        old(w).buf@.len() + data@.len() <= MAX_POS,
    ensures
        fed(old(w), final(w), data@),
        final(w).out == old(w).out,
        final(w).tfirst == old(w).tfirst,
        final(w).ge == old(w).ge,
{
    push_slice(&mut w.buf, data, 0, data.len());
    proof {
        assert(data@.subrange(0, data@.len() as int) =~= data@);
        w.seen@ = w.seen@ + data@;
    }
}


/// Drops what the window no longer needs: the bytes before where the
/// parser stands, the characters are checked, and the text being read is
/// emitted.
#[verifier::spinoff_prover]
fn win_compact(w: &mut Win, Ghost(env): Ghost<Env>)
    requires
        old(w).inv(env),
        old(w).base + old(w).buf@.len() <= usize::MAX,
        old(w).out@.len() == 0,
    ensures
        final(w).inv(env),
        final(w).ge == old(w).ge,
        final(w).emitted() == old(w).emitted(),
        old(w).emits() ==> final(w).emits(),
        final(w).seen == old(w).seen,
        final(w).at() == old(w).at(),
        final(w).base + final(w).pos == old(w).base + old(w).pos,
        final(w).base + final(w).cpos == old(w).base + old(w).cpos,
        final(w).buf@.len() <= old(w).buf@.len(),
        final(w).mode == old(w).mode,
        final(w).out == old(w).out,
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    let n = w.buf.len();
    let mut k = w.pos;
    if w.cpos < k {
        k = w.cpos;
    }
    if w.mode != M_ITEM && w.tem < k {
        k = w.tem;
    }
    if k == 0 {
        return;
    }
    let ghost b0 = w.buf@;
    let m = n - k;
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            m + k == n,
            n == b0.len(),
            w.buf@.len() == n,
            forall|j: int| 0 <= j < i ==> #[trigger] w.buf@[j] == b0[j + k],
            forall|j: int| i <= j < n ==> #[trigger] w.buf@[j] == b0[j],
        decreases m - i,
    {
        let x = w.buf[i + k];
        w.buf.set(i, x);
        i = i + 1;
    }
    w.buf.truncate(m);
    proof {
        assert(w.buf@ =~= b0.subrange(k as int, n as int));
        let seen = w.seen@;
        assert(w.buf@ =~= seen.subrange(w.base + k, seen.len() as int));
    }
    w.base = w.base + k;
    w.pos = w.pos - k;
    w.cpos = w.cpos - k;
    if w.tem >= k {
        w.tem = w.tem - k;
    } else {
        w.tem = 0;
    }
    proof {
        assert(w.win_ok());
        assert(w.mode_ok());
        assert(w.chars_inv());
        assert(w.goal(env));
        assert(w.emitted() =~= old(w).emitted());
    }
}

/// A stream with `d` fed keeps its invariant.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
proof fn lemma_stream_fed(a: &Stream, b: &Stream, d: Seq<u8>)
    requires
        a.inv(),
        a.phase != PH_FAILED && a.phase != PH_DONE,
        fed(&a.w, &b.w, d),
        b.w.buf@.len() <= MAX_POS,
        b.phase == a.phase,
        b.ptape == a.ptape,
        b.pmark == a.pmark,
        b.sd == a.sd,
        b.pro == a.pro,
        b.dtd == a.dtd,
        b.genv == a.genv,
        b.enc == a.enc,
    ensures
        b.inv(),
{
    hide(document);
    hide(doc_chars);
    hide(after_m1);
    hide(after_m2);
    hide(after_content);
    hide(input_enc);
    lemma_win_fed(&a.w, &b.w, d, a.genv@);
    let sa = a.seen();
    let sb = b.seen();
    assert(ext(sa, sb)) by {
        assert(sb.subrange(0, sa.len() as int) =~= sa);
    }
    if a.phase == PH_M1 || a.phase == PH_M2 || a.phase == PH_BODY {
        lemma_enc_ok_ext(sa, sb, a.enc);
    }
    if a.phase == PH_M1 {
        assert forall|s: Seq<u8>| #[trigger] ext(sb, s) implies docx(s) == (if doc_chars(s) {
            after_m1(s, b.w.pos as int, b.ptape@, b.sd as int)
        } else {
            None
        }) by {
            lemma_ext_trans(sa, sb, s);
        }
    }
    if a.phase == PH_M2 {
        assert forall|s: Seq<u8>| #[trigger] ext(sb, s) implies docx(s) == (if doc_chars(s) {
            after_m2(s, b.w.pos as int, b.ptape@, b.genv@)
        } else {
            None
        }) by {
            lemma_ext_trans(sa, sb, s);
        }
    }
    if a.phase == PH_M2 || a.phase == PH_BODY {
        lemma_ext_trans(a.pro@, sa, sb);
    }
}


// ---------------------------------------------------------------------------
// Feeding
// ---------------------------------------------------------------------------

/// The document fails on every input that begins with `seen` (at the end,
/// on `seen`).
pub open spec fn fails_parse(seen: Seq<u8>, last: bool) -> bool {
    forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) ==> parse(s) is None
}

proof fn lemma_fails_parse(st: &Stream, last: bool)
    requires
        st.utf8(),
        fails(st.seen(), last),
    ensures
        st.enc == Enc::Utf8 ==> fails_parse(st.seen(), last),
{
    hide(document);
    hide(input_enc);
    if st.enc == Enc::Utf8 {
        assert forall|s: Seq<u8>| #[trigger] ext(st.seen(), s) && (last ==> s == st.seen()) implies parse(s) is None by {
            lemma_parse_utf8(s);
        }
    }
}

proof fn lemma_fails_any(seen: Seq<u8>, last: bool)
    requires
        fails(seen, false),
    ensures
        fails(seen, last),
{
}

proof fn lemma_parse_ok(st: &Stream)
    requires
        st.utf8(),
        docx(st.seen()) is Some,
    ensures
        st.enc == Enc::Utf8 ==> parse(st.seen()) is Some,
{
    hide(document);
    hide(input_enc);
    lemma_ext_refl(st.seen());
    if st.enc == Enc::Utf8 {
        lemma_parse_utf8(st.seen());
    }
}

/// The characters fail: so does the document.
#[verifier::spinoff_prover]
proof fn lemma_chars_fail(st: &Stream, last: bool)
    requires
        st.inv(),
        st.phase == PH_M1 || st.phase == PH_M2 || st.phase == PH_BODY,
        forall|s: Seq<u8>|
            #[trigger] ext(st.seen(), s) && (last ==> s == st.seen()) ==> !chars_from(s, st.w.base + st.w.cpos),
    ensures
        fails(st.seen(), last),
{
    hide(document);
    hide(after_m1);
    hide(after_m2);
    hide(after_content);
    assert forall|s: Seq<u8>| #[trigger] ext(st.seen(), s) && (last ==> s == st.seen()) implies docx(s) is None by {
        if st.phase == PH_M1 {
            assert(st.m1_goal());
        } else if st.phase == PH_M2 {
            assert(st.m2_goal());
        } else {
            assert(st.w.goal(st.genv@));
        }
    }
}

impl Stream {
    /// A new parser.
    pub fn new() -> (r: Stream)
        ensures
            r.inv(),
            r.items_ok(),
            r.enc == Enc::Utf8,
            r.seen() == Seq::<u8>::empty(),
    {
        stream_new(Enc::Utf8)
    }

    /// A new parser for the text (in UTF-8) of a document in `enc`: its
    /// XML declaration, if any, must name `enc`.
    pub fn decoded(enc: Enc) -> (r: Stream)
        ensures
            r.inv(),
            r.items_ok(),
            r.phase == PH_HEAD,
            r.enc == enc,
            r.seen() == Seq::<u8>::empty(),
    {
        stream_new(enc)
    }

    /// Feeds the next chunk (`last`: the last one). Before the root
    /// element, the prolog's tokens are emitted as each is read, and from
    /// it on, the content's, to `w.out`, at positions in `w.buf`.
    /// `R_MORE`: more is needed; `R_OK`, `R_ERR`: the verdict; `R_WHOLE`:
    /// the document is to be parsed whole, from `w.buf`, once all of it is
    /// fed; `R_LIMIT`: the window outgrew the token positions.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(120)]
    pub fn feed(&mut self, data: &[u8], last: bool) -> (r: u8)
        requires
            old(self).inv(),
            old(self).items_ok(),
        ensures
            final(self).inv(),
            final(self).items_ok(),
            // Accepted: all that was emitted, chunk by chunk, is the
            // whole parse's tape.
            r == R_OK ==> items(final(self).emitted(), docx(final(self).seen()).unwrap()),
            r == R_WHOLE ==> final(self).emitted().len() == 0,
            r <= R_LIMIT,
            (old(self).phase == PH_FAILED || old(self).phase == PH_DONE) ==> r == R_ERR && final(self).seen()
                == old(self).seen(),
            r != R_LIMIT && !(old(self).phase == PH_FAILED || old(self).phase == PH_DONE) ==> final(self).seen()
                == old(self).seen() + data@,
            final(self).enc == old(self).enc,
            r == R_OK ==> final(self).verdict(r, last),
            r == R_ERR && !(old(self).phase == PH_FAILED || old(self).phase == PH_DONE) ==> final(self).verdict(r, last),
            r == R_MORE ==> !last,
            r == R_WHOLE ==> final(self).phase == PH_WHOLE && final(self).w.base == 0 && final(self).w.buf@
                == final(self).seen(),
            r == R_WHOLE ==> old(self).phase == PH_HEAD || old(self).phase == PH_WHOLE,
            old(self).phase != PH_HEAD && old(self).phase != PH_WHOLE ==> final(self).phase != PH_HEAD
                && final(self).phase != PH_WHOLE,
    {
        hide(document);
        hide(doc_chars);
        hide(after_m1);
        hide(after_m2);
        hide(after_content);
        hide(input_enc);
        hide(parse);
        // What the last chunk emitted is kept in the proof's account.
        proof {
            self.w.ge@ = Emitted { prev: self.emitted(), groups: self.w.ge@.groups, open: self.w.ge@.open };
        }
        self.w.out.clear();
        proof {
            assert(self.emitted() =~= old(self).emitted());
        }
        if self.phase == PH_FAILED || self.phase == PH_DONE {
            return R_ERR;
        }
        slice_len_bound(data);
        let n0 = self.w.buf.len();
        if data.len() as u64 > MAX_POS - n0 as u64 || self.w.base > usize::MAX - n0 || data.len() > usize::MAX - n0
            - self.w.base {
            self.phase = PH_DONE;
            return R_LIMIT;
        }
        let ghost s0 = self.seen();
        win_append(&mut self.w, data);
        proof {
            lemma_stream_fed(old(self), self, data@);
        }
        let ghost seen = self.seen();
        proof {
            assert(self.items_ok());
        }
        if self.phase == PH_BODY {
            win_compact(&mut self.w, Ghost(self.genv@));
            proof {
                assert(self.utf8());
                assert(self.pro_ok());
            }
        }
        if self.phase == PH_HEAD {
            proof {
                assert(self.emitted() =~= Seq::<XTok>::empty());
            }
            let h = head_step(self);
            proof {
                assert(self.emitted() =~= Seq::<XTok>::empty());
                assert(self.ptape@.subrange(0, self.pmark as int) =~= Seq::<XTok>::empty());
            }
            if h == S_WAIT {
                if last {
                    self.phase = PH_WHOLE;
                    proof {
                        assert(self.emitted() =~= self.ptape@.subrange(0, self.pmark as int));
                    }
                    return R_WHOLE;
                }
                return R_MORE;
            }
            if h == S_FAIL {
                proof {
                    assert(self.emitted() =~= old(self).ptape@.subrange(0, self.pmark as int));
                }
                return R_WHOLE;
            }
            proof {
                assert(self.ptape@.subrange(0, self.pmark as int) =~= Seq::<XTok>::empty());
            }
        }
        if self.phase == PH_WHOLE {
            proof {
                assert(self.w.buf@ =~= self.seen());
            }
            return R_WHOLE;
        }
        // The characters, as far as the window decides them.
        slice_len_bound(self.w.buf.as_slice());
        proof {
            assert(self.seen() == seen);
            assert(self.utf8());
        }
        match ex_chars_scan(self.w.buf.as_slice(), self.w.cpos, last, Ghost(seen), Ghost(self.w.base as int)) {
            Some(c2) => {
                self.w.cpos = c2;
                proof {
                    assert(self.seen() == seen);
                    assert(self.w.chars_inv());
                    assert(self.utf8());
                    if self.phase == PH_M1 {
                        assert(self.m1_goal());
                    }
                    if self.phase == PH_M2 {
                        assert(self.m2_goal());
                        assert(self.pro_ok());
                    }
                    if self.phase == PH_BODY {
                        assert(self.w.inv(self.genv@));
                        assert(self.pro_ok());
                    }
                    assert(self.inv());
                    assert(self.items_ok());
                }
            },
            None => {
                proof {
                    lemma_chars_fail(self, last);
                    lemma_fails_parse(self, last);
                }
                if last {
                    self.phase = PH_DONE;
                } else {
                    self.phase = PH_FAILED;
                    proof {
                        assert(self.seen() == seen);
                        assert(self.utf8());
                    }
                }
                return R_ERR;
            },
        }
        let ghost seen1 = self.seen();
        if self.phase == PH_M1 {
            let mut wait = false;
            loop
                invariant_except_break
                    self.phase == PH_M1,
                    !wait,
                invariant
                    self.inv(),
                    self.items_ok(),
                    self.seen() == seen1,
                    self.enc == old(self).enc,
                    last ==> self.w.cpos == self.w.buf@.len(),
                ensures
                    self.inv(),
                    self.items_ok(),
                    self.seen() == seen1,
                    self.enc == old(self).enc,
                    last ==> self.w.cpos == self.w.buf@.len(),
                    wait ==> self.phase == PH_M1,
                    !wait ==> self.phase == PH_M2,
                decreases self.w.buf@.len() - self.w.pos,
            {
                let ghost t0 = self.ptape@;
                let m = misc_step(self);
                proof {
                    assert(self.ptape@.subrange(0, self.pmark as int) =~= t0.subrange(0, self.pmark as int));
                }
                if m == S_WAIT {
                    wait = true;
                    break;
                }
                if m == S_DONE {
                    // A document type declaration is parsed once it may be
                    // complete (at the last chunk, in any case).
                    let n = self.w.buf.len();
                    let p = self.w.pos;
                    if !last && n - p >= 2 && self.w.buf[p + 1] == 0x21 {
                        let ghost b = *self;
                        let ready = dscan_step(&mut self.dscan, self.w.buf.as_slice(), p);
                        proof {
                            assert(self.seen() == b.seen());
                            assert(self.utf8() == b.utf8());
                            assert(self.m1_goal() == b.m1_goal());
                        }
                        if !ready {
                            wait = true;
                            break;
                        }
                    }
                    let ghost t1 = self.ptape@;
                    let d = m1_decide(self);
                    proof {
                        assert(self.ptape@.subrange(0, self.pmark as int) =~= t1.subrange(0, self.pmark as int));
                    }
                    if d == S_WAIT {
                        wait = true;
                        // It was not: on with the scan.
                        if self.dscan.mode == D_END {
                            let ghost b = *self;
                            self.dscan.mode = D_SUB;
                            proof {
                                assert(self.seen() == b.seen());
                                assert(self.utf8() == b.utf8());
                                assert(self.m1_goal() == b.m1_goal());
                            }
                        }
                    }
                    break;
                }
            }
            if wait {
                return self.prolog_wait(last);
            }
        }
        if self.phase == PH_M2 {
            let mut wait = false;
            let mut fail = false;
            loop
                invariant_except_break
                    self.phase == PH_M2,
                    !wait,
                    !fail,
                invariant
                    self.inv(),
                    self.items_ok(),
                    self.seen() == seen1,
                    self.enc == old(self).enc,
                    last ==> self.w.cpos == self.w.buf@.len(),
                ensures
                    self.inv(),
                    self.items_ok(),
                    self.seen() == seen1,
                    self.enc == old(self).enc,
                    last ==> self.w.cpos == self.w.buf@.len(),
                    wait ==> self.phase == PH_M2,
                    fail ==> self.phase == PH_FAILED,
                    !wait && !fail ==> self.phase == PH_BODY,
                decreases self.w.buf@.len() - self.w.pos,
            {
                let ghost t0 = self.ptape@;
                let m = misc_step(self);
                proof {
                    assert(self.ptape@.subrange(0, self.pmark as int) =~= t0.subrange(0, self.pmark as int));
                }
                if m == S_WAIT {
                    wait = true;
                    break;
                }
                if m == S_DONE {
                    let d = m2_root(self);
                    if d == S_WAIT {
                        wait = true;
                    }
                    if d == S_FAIL {
                        fail = true;
                    }
                    break;
                }
            }
            if wait {
                return self.prolog_wait(last);
            }
            if fail {
                proof {
                    lemma_fails_any(self.seen(), last);
                    lemma_fails_parse(self, last);
                }
                return R_ERR;
            }
        }
        // The content.
        proof {
            assert(self.phase == PH_BODY);
        }
        let ghost gv = self.genv@;
        let c = {
            let env = self.dtd.env(self.pro.as_slice());
            content_run(&mut self.w, &env, last)
        };
        if c == S_WAIT {
            proof {
                assert(self.utf8());
                assert(self.pro_ok());
            }
            return R_MORE;
        }
        if c == S_FAIL {
            proof {
                assert(self.utf8());
                lemma_fails_parse(self, last);
            }
            if last {
                self.phase = PH_DONE;
            } else {
                self.phase = PH_FAILED;
            }
            return R_ERR;
        }
        proof {
            assert(self.utf8());
            lemma_parse_ok(self);
            // The tokens read are the document's, each with its group.
            assert(self.w.emitted() =~= flat(self.w.ge@.groups));
            lemma_items(self.w.ge@.groups, self.w.gt@);
        }
        self.phase = PH_DONE;
        R_OK
    }

    /// The tokens the last chunk emitted, at positions in `window()`
    /// (`base()` in the input). They stay in the proof's account of what
    /// was emitted (`emitted`).
    pub fn take_out(&mut self) -> (r: Tape)
        ensures
            r@ == old(self).w.out@,
            final(self).w.out@.len() == 0,
            final(self).emitted() == old(self).emitted(),
            old(self).inv() ==> final(self).inv(),
            old(self).items_ok() ==> final(self).items_ok(),
    {
        proof {
            self.w.ge@ = Emitted { prev: self.emitted(), groups: self.w.ge@.groups, open: self.w.ge@.open };
        }
        let mut r = Tape::new();
        std::mem::swap(&mut r, &mut self.w.out);
        proof {
            assert(self.emitted() =~= old(self).emitted());
        }
        r
    }

    /// Before the root element, the window decides nothing more: at the
    /// last chunk, the rest of the document whole.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
    fn prolog_wait(&mut self, last: bool) -> (r: u8)
        requires
            old(self).inv(),
            old(self).items_ok(),
            old(self).phase == PH_M1 || old(self).phase == PH_M2,
            last ==> old(self).w.cpos == old(self).w.buf@.len(),
        ensures
            final(self).inv(),
            final(self).items_ok(),
            r == R_OK ==> items(final(self).emitted(), docx(final(self).seen()).unwrap()),
            final(self).seen() == old(self).seen(),
            final(self).enc == old(self).enc,
            final(self).phase != PH_HEAD && final(self).phase != PH_WHOLE,
            r == R_MORE || r == R_OK || r == R_ERR,
            final(self).verdict(r, last),
            r == R_MORE ==> !last,
    {
        hide(document);
        hide(parse);
        hide(input_enc);
        hide(doc_chars);
        hide(after_m1);
        hide(after_m2);
        let ghost seen = self.seen();
        proof {
            assert(self.utf8());
        }
        let ghost t0 = self.ptape@;
        let ghost out0 = self.w.out@;
        let ghost pm = self.pmark as int;
        proof {
            lemma_mv_zero(out0);
            assert(self.w.ge@.prev + out0 == t0.subrange(0, pm));
        }
        if !last {
            flush_pro(self);
            proof {
                assert(self.inv());
                lemma_mv_zero(self.w.out@);
                assert(self.emitted() =~= self.ptape@.subrange(0, self.pmark as int));
            }
            return R_MORE;
        }
        let ok = pro_finish(self);
        proof {
            assert(self.seen() == seen);
            assert(self.utf8());
        }
        if ok {
            flush_pro(self);
            self.phase = PH_DONE;
            proof {
                lemma_parse_ok(self);
                // Emitted: the prolog's tokens as they were, then the rest
                // of the tape.
                let t1 = self.ptape@;
                let a = t0.subrange(0, pm);
                let b = t1.subrange(pm, t1.len() as int);
                lemma_mv_zero(self.w.out@);
                assert(self.emitted() =~= a + b);
                assert(pre(a, t1)) by {
                    assert forall|i: int| 0 <= i < a.len() implies #[trigger] same_item(a[i], t1[i]) by {
                        assert(a[i] == t0[i]);
                        assert(same_item(t0[i], t1[i]));
                    }
                }
                lemma_pre_grps(a, t1);
                lemma_sing(sing(a, 0), t1.subrange(0, pm), b, 0, 0);
                lemma_mv_zero(b);
                assert(t1.subrange(0, pm) + b =~= t1);
                lemma_items(sing(a, 0) + sing(b, 0), t1);
            }
            R_OK
        } else {
            self.phase = PH_DONE;
            proof {
                lemma_ext_refl(self.seen());
                assert(fails(self.seen(), true));
                lemma_fails_parse(self, true);
            }
            R_ERR
        }
    }
}

} // verus!

// ---------------------------------------------------------------------------
// For the readers of the stream (the C ABIs): plain Rust, which decides
// nothing about the document.
// ---------------------------------------------------------------------------

impl Stream {
    /// Where in the input the parser has read to: the start of the item it
    /// has not finished.
    pub fn progress(&self) -> usize {
        self.w.base + self.w.pos
    }

    /// Where, in the window, the next chunk keeps it from: no event of
    /// the stream starts before it.
    pub fn keep(&self) -> usize {
        if self.phase != PH_BODY {
            return 0;
        }
        let mut k = self.w.pos.min(self.w.cpos);
        if self.w.mode != M_ITEM {
            k = k.min(self.w.tem);
        }
        k
    }

    /// The input from `base()`.
    pub fn window(&self) -> &[u8] {
        &self.w.buf
    }

    /// Where `window()` starts, in the input.
    pub fn base(&self) -> usize {
        self.w.base
    }

    /// Where the parser is in the document (`PH_HEAD` to `PH_DONE`).
    pub fn phase(&self) -> u8 {
        self.phase
    }

    /// In character data, which has not ended yet.
    pub fn in_text(&self) -> bool {
        self.phase == PH_BODY && self.w.mode == M_TEXT
    }

    /// In a CDATA section, which has not ended yet.
    pub fn in_cdata(&self) -> bool {
        self.phase == PH_BODY && self.w.mode == M_CDATA
    }

    /// Before the root element, in the document type declaration.
    pub fn in_doctype(&self) -> bool {
        self.phase == PH_M1 && self.w.buf.len() - self.w.pos >= 2 && self.w.buf[self.w.pos + 1] == b'!'
    }

    /// No element is open: past the root element.
    pub fn after_root(&self) -> bool {
        (self.phase == PH_BODY || self.phase == PH_DONE) && self.w.ends.is_empty()
    }

    /// Past the document type declaration: `dtd` and `prolog` are final.
    pub fn dtd_read(&self) -> bool {
        self.phase == PH_M2 || self.phase == PH_BODY || (self.phase >= PH_FAILED && self.phase != PH_WHOLE)
    }

    /// The declarations, and the text their positions are in.
    pub fn dtd(&self) -> &DtdOut {
        &self.dtd
    }

    /// The prolog's text: all the input before the root element.
    pub fn prolog(&self) -> &[u8] {
        &self.pro
    }

    /// The prolog's tokens (at positions in the input, which is all kept
    /// before the root element).
    pub fn prolog_toks(&self) -> &[Tok] {
        &self.ptape.toks
    }

    /// The XML declaration says `standalone="yes"`.
    pub fn standalone(&self) -> bool {
        self.sd == 1
    }

    /// For telling why the document failed (the verdict is `feed`'s): a
    /// document that reads as this one does from where the parser stands,
    /// with the prolog and the open elements' start tags before it; how
    /// long that prefix is; and where in the window the rest begins.
    pub fn diagnosis(&self) -> (Vec<u8>, usize, usize) {
        // Nothing dropped yet: the window is the input, whole.
        if self.w.base == 0 {
            return (self.w.buf.clone(), 0, 0);
        }
        let mut t = self.pro.clone();
        let mut from = self.w.pos;
        if self.w.ends.is_empty() {
            t.extend_from_slice(b"<_/>");
        } else {
            let mut a = 0;
            for &e in &self.w.ends {
                t.push(b'<');
                t.extend_from_slice(&self.w.names[a..e]);
                t.push(b'>');
                a = e;
            }
            if self.w.mode != M_ITEM {
                from = self.w.tem.min(self.w.pos);
                if self.w.mode == M_CDATA {
                    t.extend_from_slice(b"<![CDATA[");
                }
            }
        }
        let n = t.len();
        t.extend_from_slice(&self.w.buf[from.min(self.w.buf.len())..]);
        (t, n, from)
    }
}

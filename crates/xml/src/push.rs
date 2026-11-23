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

pub const PH_HEAD: u8 = 0;
pub const PH_M1: u8 = 1;
pub const PH_M2: u8 = 2;
pub const PH_BODY: u8 = 3;
pub const PH_FAILED: u8 = 4;
pub const PH_WHOLE: u8 = 5;
pub const PH_DONE: u8 = 6;

/// `feed`'s results.
pub const R_MORE: u8 = 0;
pub const R_OK: u8 = 1;
pub const R_ERR: u8 = 2;
pub const R_WHOLE: u8 = 3;
pub const R_LIMIT: u8 = 4;

pub struct Stream {
    pub w: Win,
    pub phase: u8,
    /// Before the root element: the tape, and how much of it was emitted.
    pub ptape: Tape,
    pub pmark: usize,
    pub sd: u8,
    /// The prolog's text and what its document type declaration declares.
    pub pro: Vec<u8>,
    pub dtd: DtdOut,
    pub genv: Ghost<Env>,
}

impl Stream {
    pub open spec fn seen(&self) -> Seq<u8> {
        self.w.seen@
    }

    pub open spec fn utf8(&self) -> bool {
        forall|s: Seq<u8>| #[trigger] ext(self.seen(), s) ==> input_enc(s) == Enc::Utf8
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
            #[trigger] ext(self.seen(), s) ==> document(s, Enc::Utf8) == (if doc_chars(s) {
                after_m1(s, self.w.pos as int, self.ptape@, self.sd as int)
            } else {
                None
            })
    }

    pub open spec fn m2_goal(&self) -> bool {
        forall|s: Seq<u8>|
            #[trigger] ext(self.seen(), s) ==> document(s, Enc::Utf8) == (if doc_chars(s) {
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

    /// The same input, kept the same way.
    pub open spec fn same_input(&self, o: &Stream) -> bool {
        self.w.seen == o.w.seen && self.w.buf == o.w.buf && self.w.base == o.w.base && self.w.cpos == o.w.cpos
    }
}

/// A new parser, before any input.
pub fn stream_new() -> (r: Stream)
    ensures
        r.inv(),
        r.phase == PH_HEAD,
        r.seen() == Seq::<u8>::empty(),
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
        },
        phase: PH_HEAD,
        ptape: Tape::new(),
        pmark: 0,
        sd: 0,
        pro,
        dtd,
        genv: Ghost(no_dtd()),
    };
    proof {
        assert(r.w.buf@ =~= r.w.seen@.subrange(0, 0));
        assert forall|s: Seq<u8>| #[trigger] ext(r.seen(), s) implies doc_chars(s) == chars_from(s, 0) by {}
    }
    r
}

#[verifier::spinoff_prover]
proof fn lemma_head_goal(b: Seq<u8>, seen: Seq<u8>, n: int, p0: int)
    requires
        b == seen.subrange(0, seen.len() as int),
        n == b.len(),
        n >= 1,
        b[0] != 0xFE && b[0] != 0xFF,
        n >= 3 || b[0] != 0xEF,
        p0 == bom_end(b),
        decl_decided(b, p0, n),
        has_decl(b, p0) ==> (xmldecl(b, p0, Enc::Utf8) matches Some((_, e, _)) && e <= n),
        decl_head(b, Enc::Utf8) is Some,
    ensures
        ({
            let (t0, p1, sd) = decl_head(b, Enc::Utf8).unwrap();
            forall|s: Seq<u8>|
                #[trigger] ext(seen, s) ==> input_enc(s) == Enc::Utf8 && document(s, Enc::Utf8) == (if doc_chars(s) {
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
    let (t0, p1, sd) = decl_head(b, Enc::Utf8).unwrap();
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies input_enc(s) == Enc::Utf8 && document(s, Enc::Utf8) == (
    if doc_chars(s) {
        after_m1(s, p1, t0, sd)
    } else {
        None
    }) by {
        lemma_window(b, seen, 0, s);
        assert(seen.subrange(0, seen.len() as int) =~= seen);
        lemma_head_utf8(b, s, n);
        reveal(document);
        lemma_document(s, Enc::Utf8);
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
        final(st).inv(),
        final(st).same_input(old(st)),
        r == S_ON ==> final(st).phase == PH_M1,
        r == S_WAIT ==> final(st).phase == PH_HEAD,
        r == S_FAIL ==> final(st).phase == PH_WHOLE,
        r == S_ON || r == S_WAIT || r == S_FAIL,
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
    if b0 == 0xFE || b0 == 0xFF {
        st.phase = PH_WHOLE;
        return S_FAIL;
    }
    if b0 == 0xEF && n < 3 {
        return S_WAIT;
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
        match ex_xmldecl(st.w.buf.as_slice(), p0, &mut t0, Enc::Utf8) {
            Some((e, sd)) => {
                proof {
                    lemma_xmldecl_end(st.w.buf@, p0 as int, Enc::Utf8);
                    lemma_head_goal(st.w.buf@, st.w.seen@, n as int, p0 as int);
                }
                st.ptape = t0;
                st.w.pos = e;
                st.sd = sd;
                st.phase = PH_M1;
                proof {
                    assert(decl_head(st.w.buf@, Enc::Utf8) == Some((st.ptape@, e as int, sd as int)));
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
            lemma_head_goal(st.w.buf@, st.w.seen@, n as int, p0 as int);
            assert(decl_head(st.w.buf@, Enc::Utf8) == Some((Seq::<XTok>::empty(), p0 as int, 0int)));
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

} // verus!

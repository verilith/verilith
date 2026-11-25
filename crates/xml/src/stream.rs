//! The incremental parser: a document fed in chunks, read as far as each
//! chunk decides, with what has been read dropped. After every chunk, for
//! every document `s` that begins with the bytes fed so far, `parse(s)`
//! is what the rest of `s` decides from where the parser stands
//! (`Stream::inv`); after the last, the verdict is `parse` of the whole
//! input. What the parser keeps is the prolog (whose declarations the
//! content refers to), the names of the open elements, and a window of
//! the input from the item being read.
use crate::chars::*;
use crate::content::*;
use crate::doc::*;
use crate::dtd::*;
use crate::lex::*;
use crate::spec::*;
use crate::stable::*;
use crate::stable_pro::*;
use crate::stream_spec::*;
use crate::tape::*;
use verilith_core::prims::get;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Characters
// ---------------------------------------------------------------------------

/// `chars_from` over the window from `c`, as far as the window decides it:
/// the new position, or `None` where the window decides that a byte is no
/// part of a `Char` (at the end, `last`: wherever a code point is cut
/// short).
pub fn ex_chars_scan(b: &[u8], c: usize, last: bool, Ghost(seen): Ghost<Seq<u8>>, Ghost(base): Ghost<int>) -> (r:
    Option<usize>)
    requires
        c <= b@.len(),
        0 <= base,
        base + b@.len() == seen.len(),
        b@ == seen.subrange(base, seen.len() as int),
    ensures
        match r {
            Some(c2) => c <= c2 <= b@.len() && (last ==> c2 == b@.len()) && (forall|s: Seq<u8>|
                #[trigger] ext(seen, s) ==> chars_from(s, base + c) == chars_from(s, base + c2)),
            None => (forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) ==> !chars_from(s, base + c)),
        },
{
    let n = b.len();
    let mut i = c;
    while i < n
        invariant
            c <= i <= n,
            n == b@.len(),
            0 <= base,
            base + b@.len() == seen.len(),
            b@ == seen.subrange(base, seen.len() as int),
            forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> chars_from(s, base + c) == chars_from(s, base + i),
        decreases n - i,
    {
        let x = get(b, i);
        if x < 0x80 {
            if x < 0x20 && x != 0x09 && x != 0x0A && x != 0x0D {
                proof {
                    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies !chars_from(
                        s,
                        base + c,
                    ) by {
                        lemma_window(b@, seen, base, s);
                        lemma_chars_step(b@, s, 0, n as int, -base, i as int, 1);
                    }
                }
                return None;
            }
            proof {
                assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies chars_from(s, base + c) == chars_from(
                    s,
                    base + i + 1,
                ) by {
                    lemma_window(b@, seen, base, s);
                    lemma_chars_step(b@, s, 0, n as int, -base, i as int, 1);
                }
            }
            i = i + 1;
        } else {
            match ex_cp_at_hi(b, i) {
                None => {
                    if n - i >= 4 || last {
                        proof {
                            assert(utf8_len(b@, i as int) is None);
                            assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies !chars_from(
                                s,
                                base + c,
                            ) by {
                                lemma_window(b@, seen, base, s);
                                if n - i >= 4 {
                                    lemma_chars_bad(b@, s, 0, n as int, -base, i as int);
                                } else {
                                    lemma_window_exact(b@, seen, base);
                                    lemma_chars_tail(b@, seen, 0, -base, i as int);
                                }
                            }
                        }
                        return None;
                    }
                    return Some(i);
                },
                Some((cp, l)) => {
                    proof {
                        lemma_cp_in_bounds(b@, i as int);
                        assert(utf8_len(b@, i as int) == Some(l as int));
                    }
                    if l == 3 && cp >= 0xFFFE {
                        proof {
                            assert(b@[i as int] == 0xEF && b@[i as int + 1] == 0xBF && b@[i as int + 2] >= 0xBE);
                            assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies !chars_from(
                                s,
                                base + c,
                            ) by {
                                lemma_window(b@, seen, base, s);
                                lemma_chars_step(b@, s, 0, n as int, -base, i as int, 3);
                            }
                        }
                        return None;
                    }
                    proof {
                        if l == 3 {
                            assert(!(b@[i as int] == 0xEF && b@[i as int + 1] == 0xBF && b@[i as int + 2] >= 0xBE));
                        }
                        assert(char_seq_ok(b@, i as int, l as int));
                        assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies chars_from(s, base + c) == chars_from(
                            s,
                            base + i + l,
                        ) by {
                            lemma_window(b@, seen, base, s);
                            lemma_chars_step(b@, s, 0, n as int, -base, i as int, l as int);
                        }
                    }
                    i = i + l;
                },
            }
        }
    }
    Some(i)
}

// ---------------------------------------------------------------------------
// The window, in the root element and after it
// ---------------------------------------------------------------------------

/// `Win::mode`: reading an item.
pub const M_ITEM: u8 = 0;
/// Reading text.
pub const M_TEXT: u8 = 1;
/// Reading a CDATA section.
pub const M_CDATA: u8 = 2;

/// Steps' results.
pub const S_ON: u8 = 0;
/// The step needs more input.
pub const S_WAIT: u8 = 1;
/// The step found the document not well-formed.
pub const S_FAIL: u8 = 2;
/// The step reached the end of the document.
pub const S_DONE: u8 = 3;

/// Emitted pieces of text and CDATA sections: bit 0, a carriage return in
/// the piece; bit 1, the first piece of a CDATA section; bit 2, its last.
pub const P_CR: u8 = 1;
/// The first piece of a CDATA section.
pub const P_FIRST: u8 = 2;
/// The last piece of a CDATA section.
pub const P_LAST: u8 = 4;

/// The window the parser reads the root element through: the input it has not finished with, and the open elements.
pub struct Win {
    /// The input from `base`.
    pub buf: Vec<u8>,
    /// Where `buf` starts, in the input.
    pub base: usize,
    /// Where the parser stands in `buf`.
    pub pos: usize,
    /// How far the characters are checked.
    pub cpos: usize,
    /// Reading an item, text, or a CDATA section.
    pub mode: u8,
    /// Text or a CDATA section: emitted up to `tem`; a carriage return so
    /// far; nothing emitted yet.
    pub tem: usize,
    /// A carriage return in the text so far.
    pub tcr: bool,
    /// Nothing of the text emitted yet.
    pub tfirst: bool,
    /// The names of the open elements, end to end, and where each ends.
    pub names: Vec<u8>,
    /// Where each open element's name ends in `names`.
    pub ends: Vec<usize>,
    /// What this chunk emitted, at positions in `buf`.
    pub out: Tape,
    /// The input fed so far.
    pub seen: Ghost<Seq<u8>>,
    /// The open elements, in the spec's terms.
    pub gst: Ghost<Seq<Open>>,
    /// The tokens emitted so far, in the spec's terms.
    pub gt: Ghost<Seq<XTok>>,
    /// Where the text or CDATA section being read starts, in the input.
    pub gts: Ghost<int>,
}

impl Win {
    pub open spec fn n(&self) -> int {
        self.buf@.len() as int
    }

    pub open spec fn nstart(&self, q: int) -> int {
        if q == 0 {
            0
        } else {
            self.ends@[q - 1] as int
        }
    }

    pub open spec fn names_ok(&self) -> bool {
        &&& self.ends@.len() == self.gst@.len()
        &&& self.ends@.len() == 0 ==> self.names@.len() == 0
        &&& self.ends@.len() > 0 ==> self.ends@.last() == self.names@.len()
        &&& forall|q1: int, q2: int|
            0 <= q1 <= q2 < self.ends@.len() ==> #[trigger] self.ends@[q1] <= #[trigger] self.ends@[q2]
        &&& forall|q: int|
            0 <= q < self.ends@.len() ==> self.nstart(q) <= #[trigger] self.ends@[q] <= self.names@.len() && 0
                <= self.gst@[q].0 <= self.gst@[q].1 <= self.seen@.len() && self.names@.subrange(
                self.nstart(q),
                self.ends@[q] as int,
            ) == self.seen@.subrange(self.gst@[q].0, self.gst@[q].1)
    }

    pub open spec fn win_ok(&self) -> bool {
        &&& self.base + self.buf@.len() == self.seen@.len()
        &&& self.buf@ == self.seen@.subrange(self.base as int, self.seen@.len() as int)
        &&& self.pos <= self.buf@.len()
        &&& self.cpos <= self.buf@.len()
        &&& self.buf@.len() <= MAX_POS
    }

    /// Where the document continues from, in the input.
    pub open spec fn at(&self) -> int {
        if self.mode == M_ITEM {
            self.base + self.pos
        } else {
            self.gts@
        }
    }

    pub open spec fn mode_ok(&self) -> bool {
        let seen = self.seen@;
        let ts = self.gts@;
        let k = self.base + self.pos;
        &&& self.mode <= 2
        &&& self.mode != M_ITEM ==> self.gst@.len() > 0 && self.tem <= self.pos
        &&& self.mode == M_TEXT ==> 0 <= ts <= k && ts < seen.len() && seen[ts] != 0x3C && seen[ts] != 0x26
            && self.tcr == has_cr(seen, ts, k) && ts <= self.base + self.tem && (forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> text_end(s, ts) == text_end(s, k))
        &&& self.mode == M_CDATA ==> 0 <= ts && ts + 9 <= k && has_lit(seen, ts, lit_cdata()) && self.tcr == has_cr(
            seen,
            ts + 9,
            k,
        ) && ts + 9 <= self.base + self.tem && (forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> cdata_end(s, ts + 9) == cdata_end(s, k))
    }

    pub open spec fn goal(&self, env: Env) -> bool {
        forall|s: Seq<u8>|
            #[trigger] ext(self.seen@, s) ==> docx(s) == (if doc_chars(s) {
                after_content(s, self.at(), self.gst@, self.gt@, env)
            } else {
                None
            })
    }

    pub open spec fn chars_inv(&self) -> bool {
        forall|s: Seq<u8>| #[trigger] ext(self.seen@, s) ==> doc_chars(s) == chars_from(s, self.base + self.cpos)
    }

    pub open spec fn inv(&self, env: Env) -> bool {
        &&& self.win_ok()
        &&& self.names_ok()
        &&& self.mode_ok()
        &&& self.goal(env)
        &&& self.chars_inv()
    }

    /// How much is left to do, for termination.
    pub open spec fn left(&self) -> int {
        3 * (self.n() - self.pos) + if self.mode != M_ITEM {
            1int
        } else if self.pos < self.n() && self.buf@[self.pos as int] != 0x3C && self.buf@[self.pos as int] != 0x26
            && self.gst@.len() > 0 {
            2int
        } else {
            0int
        }
    }

    /// The same window and input.
    pub open spec fn same_win(&self, o: &Win) -> bool {
        self.seen == o.seen && self.buf == o.buf && self.base == o.base && self.cpos == o.cpos
    }
}

/// The document fails, on every input that begins with `seen` (at the
/// end, on `seen`).
pub open spec fn fails(seen: Seq<u8>, last: bool) -> bool {
    forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) ==> docx(s) is None
}

pub proof fn lemma_ext_refl(s: Seq<u8>)
    ensures
        ext(s, s),
{
    assert(s.subrange(0, s.len() as int) =~= s);
}

pub proof fn lemma_ext_byte(seen: Seq<u8>, s: Seq<u8>, k: int)
    requires
        ext(seen, s),
        0 <= k < seen.len(),
    ensures
        s[k] == seen[k],
        k < s.len(),
{
    assert(s.subrange(0, seen.len() as int)[k] == s[k]);
}

pub proof fn lemma_ext_lit(seen: Seq<u8>, s: Seq<u8>, k: int, lit: Seq<u8>)
    requires
        ext(seen, s),
        has_lit(seen, k, lit),
    ensures
        has_lit(s, k, lit),
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

/// An item that ends past the end, or before it starts: the content
/// fails.
pub proof fn lemma_content_past(s: Seq<u8>, j: int, st: Seq<Open>, t: Seq<XTok>, env: Env)
    requires
        st.len() > 0,
        0 <= j < s.len(),
        item(s, j, st, t, env) matches Some((_, _, e)) && (e > s.len() || e <= j),
    ensures
        after_content(s, j, st, t, env) is None,
{
}

/// Appends `b[a..e]` to `v`.
pub fn push_slice(v: &mut Vec<u8>, b: &[u8], a: usize, e: usize)
    requires
        a <= e <= b@.len(),
    ensures
        final(v)@ == old(v)@ + b@.subrange(a as int, e as int),
{
    let mut i = a;
    while i < e
        invariant
            a <= i <= e <= b@.len(),
            v@ == old(v)@ + b@.subrange(a as int, i as int),
        decreases e - i,
    {
        v.push(b[i]);
        proof {
            assert(b@.subrange(a as int, i as int + 1) =~= b@.subrange(a as int, i as int).push(b@[i as int]));
        }
        i = i + 1;
    }
}


#[verifier::spinoff_prover]
proof fn lemma_step_item_goal(b: Seq<u8>, seen: Seq<u8>, base: int, j: int, gst: Seq<Open>, gt: Seq<XTok>, envv: Env)
    requires
        0 <= base <= seen.len(),
        b == seen.subrange(base, seen.len() as int),
        0 <= j < b.len(),
        gst.len() > 0,
        !is_etag(b, j),
        item(b, j, Seq::empty(), Seq::empty(), envv) matches Some((_, _, e)) && item_reach(b, j, e) <= b.len(),
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_content(s, base + j, gst, gt, envv)
            } else {
                None
            }),
    ensures
        ({
            let (sx, u, e) = item(b, j, Seq::empty(), Seq::empty(), envv).unwrap();
            let gst2 = stack_mv(Seq::empty(), sx, gst, -base, gt.len() as int);
            let gt2 = gt + mv(added(Seq::empty(), u), -base, gt.len() as int);
            forall|s: Seq<u8>|
                #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                    after_content(s, base + e, gst2, gt2, envv)
                } else {
                    None
                })
        }),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    hide(item);
    let (sx, u, e) = item(b, j, Seq::empty(), Seq::empty(), envv).unwrap();
    let gst2 = stack_mv(Seq::empty(), sx, gst, -base, gt.len() as int);
    let gt2 = gt + mv(added(Seq::empty(), u), -base, gt.len() as int);
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies docx(s) == (if doc_chars(s) {
        after_content(s, base + e, gst2, gt2, envv)
    } else {
        None
    }) by {
        lemma_window(b, seen, base, s);
        lemma_item_mv(b, s, 0, b.len() as int, -base, j, Seq::empty(), Seq::empty(), gst, gt, envv);
        lemma_content_step(s, base + j, gst, gt, envv);
    }
}

/// Opens an element whose name is `buf[a..e]`, `p` in the input.
#[verifier::spinoff_prover]
pub fn win_push_name(w: &mut Win, a: usize, e: usize, Ghost(p): Ghost<Open>)
    requires
        old(w).names_ok(),
        a <= e <= old(w).buf@.len(),
        0 <= p.0 <= p.1 <= old(w).seen@.len(),
        old(w).buf@.subrange(a as int, e as int) == old(w).seen@.subrange(p.0, p.1),
    ensures
        final(w).names_ok(),
        final(w).gst@ == old(w).gst@.push(p),
        final(w).buf == old(w).buf,
        final(w).seen == old(w).seen,
        final(w).base == old(w).base,
        final(w).pos == old(w).pos,
        final(w).cpos == old(w).cpos,
        final(w).mode == old(w).mode,
        final(w).tem == old(w).tem,
        final(w).tcr == old(w).tcr,
        final(w).gt == old(w).gt,
        final(w).gts == old(w).gts,
        final(w).out == old(w).out,
{
    let ghost names0 = w.names@;
    let ghost ends0 = w.ends@;
    let ghost gst = w.gst@;
    push_slice(&mut w.names, w.buf.as_slice(), a, e);
    w.ends.push(w.names.len());
    proof {
        w.gst@ = gst.push(p);
        let gst2 = w.gst@;
        let seen = w.seen@;
        assert forall|q1: int, q2: int| 0 <= q1 <= q2 < w.ends@.len() implies #[trigger] w.ends@[q1]
            <= #[trigger] w.ends@[q2] by {
            if q2 < ends0.len() {
                assert(w.ends@[q1] == ends0[q1]);
                assert(w.ends@[q2] == ends0[q2]);
            } else if q1 < ends0.len() {
                assert(w.ends@[q1] == ends0[q1]);
                assert(ends0[q1] <= names0.len());
            }
        }
        assert forall|q: int| 0 <= q < w.ends@.len() implies w.nstart(q) <= #[trigger] w.ends@[q] <= w.names@.len()
            && 0 <= gst2[q].0 <= gst2[q].1 <= seen.len() && w.names@.subrange(w.nstart(q), w.ends@[q] as int)
            == seen.subrange(gst2[q].0, gst2[q].1) by {
            if q < ends0.len() {
                assert(w.ends@[q] == ends0[q]);
                if q > 0 {
                    assert(w.ends@[q - 1] == ends0[q - 1]);
                }
                assert(gst2[q] == gst[q]);
                assert(w.names@.subrange(w.nstart(q), w.ends@[q] as int) =~= names0.subrange(
                    w.nstart(q),
                    w.ends@[q] as int,
                ));
            } else {
                assert(q == ends0.len());
                if q > 0 {
                    assert(w.ends@[q - 1] == ends0[q - 1]);
                }
                assert(w.nstart(q) == names0.len());
                assert(w.names@.subrange(w.nstart(q), w.ends@[q] as int) =~= w.buf@.subrange(a as int, e as int));
            }
        }
    }
}

pub proof fn lemma_ext_span(seen: Seq<u8>, s: Seq<u8>, a: int, b: int)
    requires
        ext(seen, s),
        0 <= a <= b <= seen.len(),
    ensures
        s.subrange(a, b) == seen.subrange(a, b),
{
    assert forall|k: int| 0 <= k < b - a implies #[trigger] s.subrange(a, b)[k] == seen.subrange(a, b)[k] by {
        lemma_ext_byte(seen, s, a + k);
    }
    assert(s.subrange(a, b) =~= seen.subrange(a, b));
}

/// Closes the innermost element.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
fn win_pop_name(w: &mut Win)
    requires
        old(w).names_ok(),
        old(w).ends@.len() > 0,
    ensures
        final(w).names_ok(),
        final(w).gst@ == old(w).gst@.drop_last(),
        final(w).buf == old(w).buf,
        final(w).seen == old(w).seen,
        final(w).base == old(w).base,
        final(w).pos == old(w).pos,
        final(w).cpos == old(w).cpos,
        final(w).mode == old(w).mode,
        final(w).tem == old(w).tem,
        final(w).tcr == old(w).tcr,
        final(w).gt == old(w).gt,
        final(w).gts == old(w).gts,
        final(w).out == old(w).out,
{
    let ghost names0 = w.names@;
    let ghost ends0 = w.ends@;
    let ghost gst = w.gst@;
    let k = w.ends.len() - 1;
    let a = if k == 0 {
        0
    } else {
        w.ends[k - 1]
    };
    proof {
        assert(w.nstart(k as int) == a);
        assert(a <= w.ends@[k as int]);
    }
    w.names.truncate(a);
    w.ends.pop();
    proof {
        w.gst@ = gst.drop_last();
        let gst2 = w.gst@;
        let seen = w.seen@;
        assert forall|q1: int, q2: int| 0 <= q1 <= q2 < w.ends@.len() implies #[trigger] w.ends@[q1]
            <= #[trigger] w.ends@[q2] by {
            assert(w.ends@[q1] == ends0[q1]);
            assert(w.ends@[q2] == ends0[q2]);
        }
        assert forall|q: int| 0 <= q < w.ends@.len() implies w.nstart(q) <= #[trigger] w.ends@[q] <= w.names@.len()
            && 0 <= gst2[q].0 <= gst2[q].1 <= seen.len() && w.names@.subrange(w.nstart(q), w.ends@[q] as int)
            == seen.subrange(gst2[q].0, gst2[q].1) by {
            assert(w.ends@[q] == ends0[q]);
            if q > 0 {
                assert(w.ends@[q - 1] == ends0[q - 1]);
            }
            assert(ends0[q] <= ends0[k as int - 1]);
            assert(gst2[q] == gst[q]);
            assert(w.names@.subrange(w.nstart(q), w.ends@[q] as int) =~= names0.subrange(
                w.nstart(q),
                w.ends@[q] as int,
            ));
        }
        if w.ends@.len() > 0 {
            assert(w.ends@.last() == ends0[k as int - 1]);
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_step_etag_goal(
    b: Seq<u8>,
    seen: Seq<u8>,
    base: int,
    j: int,
    gst: Seq<Open>,
    gt: Seq<XTok>,
    envv: Env,
    e: int,
)
    requires
        0 <= base <= seen.len(),
        b == seen.subrange(base, seen.len() as int),
        0 <= j,
        j + 1 < b.len(),
        b[j] == 0x3C,
        b[j + 1] == 0x2F,
        name_end(b, j + 2) < b.len(),
        b[name_end(b, j + 2)] < 0x80,
        e == ws_end(b, name_end(b, j + 2)),
        e < b.len(),
        b[e] == 0x3E,
        gst.len() > 0,
        0 <= gst.last().0 <= gst.last().1 <= seen.len(),
        b.subrange(j + 2, name_end(b, j + 2)) == seen.subrange(gst.last().0, gst.last().1),
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_content(s, base + j, gst, gt, envv)
            } else {
                None
            }),
    ensures
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_content(s, base + e + 1, gst.drop_last(), close_at(gt.push(XTok::ETag), gst.last().2), envv)
            } else {
                None
            }),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    hide(item);
    lemma_name_end(b, j + 2);
    lemma_ws_end_ge(b, name_end(b, j + 2));
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies docx(s) == (if doc_chars(s) {
        after_content(s, base + e + 1, gst.drop_last(), close_at(gt.push(XTok::ETag), gst.last().2), envv)
    } else {
        None
    }) by {
        lemma_window(b, seen, base, s);
        lemma_ext_span(seen, s, gst.last().0, gst.last().1);
        lemma_etag_mv(b, s, 0, b.len() as int, -base, j, gst, gt, envv);
        lemma_content_step(s, base + j, gst, gt, envv);
    }
}

/// The window decides that the end tag at `j` fails.
#[verifier::spinoff_prover]
proof fn lemma_etag_fail(
    b: Seq<u8>,
    seen: Seq<u8>,
    base: int,
    j: int,
    gst: Seq<Open>,
    gt: Seq<XTok>,
    envv: Env,
    last: bool,
)
    requires
        0 <= base <= seen.len(),
        b == seen.subrange(base, seen.len() as int),
        0 <= j,
        j + 1 < b.len(),
        b[j] == 0x3C,
        b[j + 1] == 0x2F,
        gst.len() > 0,
        0 <= gst.last().0 <= gst.last().1 <= seen.len(),
        ({
            let n = name_end(b, j + 2);
            let e = ws_end(b, n);
            (n < b.len() && b[n] < 0x80 && (b.subrange(j + 2, n) != seen.subrange(gst.last().0, gst.last().1) || (e
                < b.len() && b[e] != 0x3E))) || (last && (n == b.len() || b[n] >= 0x80 || e == b.len()))
        }),
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_content(s, base + j, gst, gt, envv)
            } else {
                None
            }),
    ensures
        fails(seen, last),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    hide(item);
    let n = name_end(b, j + 2);
    lemma_name_end(b, j + 2);
    let e = ws_end(b, n);
    lemma_ws_end_ge(b, n);
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies docx(s) is None by {
        lemma_window(b, seen, base, s);
        lemma_ext_span(seen, s, gst.last().0, gst.last().1);
        if n < b.len() && b[n] < 0x80 && (b.subrange(j + 2, n) != seen.subrange(gst.last().0, gst.last().1) || (e
            < b.len() && b[e] != 0x3E)) {
            lemma_etag_mv(b, s, 0, b.len() as int, -base, j, gst, gt, envv);
        } else {
            lemma_window_exact(b, seen, base);
            assert(tail(b, seen, 0, -base));
            if n == b.len() || e == b.len() {
                lemma_etag_tail(b, seen, 0, -base, j, gst, gt, envv);
            } else {
                // The name stops at a byte of 0x80 or more, which is no
                // white space and no `>`.
                lemma_name_end_tail(b, seen, 0, -base, j + 2);
                lemma_ws_end_tail(b, seen, 0, -base, n);
                assert(!is_ws(b[n]));
                assert(e == n);
                assert(b[n] == seen[n + base]);
                reveal(item);
                assert(item(seen, base + j, gst, gt, envv) is None);
            }
        }
        lemma_content_fail(s, base + j, gst, gt, envv);
    }
}

/// An end tag, checked against the innermost open element's name.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
// `env` is only for the proof.
#[allow(unused_variables)]
fn step_etag(w: &mut Win, env: &XEnv, last: bool) -> (r: u8)
    requires
        old(w).inv(env_view(env)),
        old(w).mode == M_ITEM,
        old(w).gst@.len() > 0,
        old(w).pos + 1 < old(w).buf@.len(),
        old(w).buf@[old(w).pos as int] == 0x3C,
        old(w).buf@[old(w).pos as int + 1] == 0x2F,
    ensures
        final(w).same_win(old(w)),
        r == S_ON ==> final(w).inv(env_view(env)) && final(w).left() < old(w).left(),
        r == S_WAIT ==> !last && final(w).inv(env_view(env)),
        r == S_ON || r == S_WAIT || r == S_FAIL,
        r == S_FAIL ==> fails(final(w).seen@, last),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    let ghost envv = env_view(env);
    let ghost seen = w.seen@;
    let ghost base = w.base as int;
    let ghost gst = w.gst@;
    let ghost gt = w.gt@;
    let j = w.pos;
    let n = w.buf.len();
    let n2 = ex_name_end(w.buf.as_slice(), j + 2);
    let k = w.ends.len() - 1;
    let a = if k == 0 {
        0
    } else {
        w.ends[k - 1]
    };
    let z = w.ends[k];
    proof {
        assert(w.nstart(k as int) == a);
        assert(gst.last() == gst[k as int]);
        assert(w.names@.subrange(a as int, z as int) == seen.subrange(gst.last().0, gst.last().1));
    }
    if n2 == n || get(w.buf.as_slice(), n2) >= 0x80 {
        if last {
            proof {
                lemma_etag_fail(w.buf@, seen, base, j as int, gst, gt, envv, last);
            }
            return S_FAIL;
        }
        return S_WAIT;
    }
    let e = ex_ws_end(w.buf.as_slice(), n2);
    let same = ex_bytes_eq(w.buf.as_slice(), j + 2, n2, w.names.as_slice(), a, z);
    if !same || (e < n && get(w.buf.as_slice(), e) != 0x3E) {
        proof {
            lemma_etag_fail(w.buf@, seen, base, j as int, gst, gt, envv, last);
        }
        return S_FAIL;
    }
    if e == n {
        if last {
            proof {
                lemma_etag_fail(w.buf@, seen, base, j as int, gst, gt, envv, last);
            }
            return S_FAIL;
        }
        return S_WAIT;
    }
    proof {
        lemma_step_etag_goal(w.buf@, seen, base, j as int, gst, gt, envv, e as int);
        w.gt@ = close_at(gt.push(XTok::ETag), gst.last().2);
    }
    win_pop_name(w);
    // The end tag's span, `<` to after `>` (an empty-element tag's has
    // none).
    w.out.push(tok(Kind::ETag, j, e + 1, 0));
    w.pos = e + 1;
    S_ON
}

/// One item that is not an end tag, text, or a CDATA section, in the root
/// element, read with `item` in the window.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
fn step_item(w: &mut Win, env: &XEnv, last: bool) -> (r: u8)
    requires
        old(w).inv(env_view(env)),
        env_wf(env),
        old(w).mode == M_ITEM,
        old(w).gst@.len() > 0,
        old(w).pos < old(w).buf@.len(),
        !is_etag(old(w).buf@, old(w).pos as int),
        old(w).buf@[old(w).pos as int] == 0x3C || old(w).buf@[old(w).pos as int] == 0x26,
    ensures
        final(w).same_win(old(w)),
        r == S_ON ==> final(w).inv(env_view(env)) && final(w).left() < old(w).left(),
        r == S_WAIT ==> !last && final(w).inv(env_view(env)),
        r == S_ON || r == S_WAIT || r == S_FAIL,
        r == S_FAIL ==> fails(final(w).seen@, last),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    hide(item);
    let ghost envv = env_view(env);
    let ghost seen = w.seen@;
    let ghost base = w.base as int;
    let ghost n = w.buf@.len() as int;
    let ghost gst = w.gst@;
    let ghost gt = w.gt@;
    slice_len_bound(w.buf.as_slice());
    let j = w.pos;
    let mut sc: Vec<(usize, usize, usize)> = Vec::new();
    let mut tp = Tape::new();
    proof {
        assert(stack_view(sc@) =~= Seq::<Open>::empty());
    }
    match ex_item(w.buf.as_slice(), j, &mut sc, &mut tp, env) {
        Some(e) => {
            let ghost (sx, u, _e) = item(w.buf@, j as int, Seq::empty(), Seq::empty(), envv).unwrap();
            let ghost gst2 = stack_mv(Seq::empty(), sx, gst, -base, gt.len() as int);
            let ghost gt2 = gt + mv(added(Seq::empty(), u), -base, gt.len() as int);
            proof {
                assert(item_reach(w.buf@, j as int, e as int) <= n);
                assert(agree(w.buf@, w.buf@, 0, n, 0));
                lemma_item_mv(w.buf@, w.buf@, 0, n, 0, j as int, Seq::empty(), Seq::empty(), Seq::empty(), Seq::empty(), envv);
                assert(sc@.len() == sx.len());
                lemma_step_item_goal(w.buf@, seen, base, j as int, gst, gt, envv);
            }
            if sc.len() == 1 {
                let top = sc[0];
                proof {
                    assert(sx == Seq::<Open>::empty().push((j + 1, name_end(w.buf@, j + 1), 0int)));
                    assert(stack_view(sc@)[0] == sx[0]);
                    assert(top.0 == j + 1 && top.1 == name_end(w.buf@, j + 1));
                    assert(stack_ok(w.buf@, sc@, tp@));
                    assert(sc@[0] == top);
                    assert(gst2 == gst.push((top.0 + base, top.1 + base, gt.len() as int)));
                    assert(w.buf@.subrange(top.0 as int, top.1 as int) =~= seen.subrange(
                        top.0 + base,
                        top.1 + base,
                    ));
                }
                win_push_name(w, top.0, top.1, Ghost((top.0 + base, top.1 + base, gt.len() as int)));
            } else {
                proof {
                    assert(sx.len() == 0);
                    assert(gst2 == gst);
                }
            }
            w.out.toks.append(&mut tp.toks);
            w.pos = e;
            proof {
                w.gst@ = gst2;
                w.gt@ = gt2;
                assert(w.gst@.len() == w.ends@.len());
            }
            S_ON
        },
        None => {
            if last {
                proof {
                    lemma_window_exact(w.buf@, seen, base);
                    lemma_ext_refl(seen);
                    assert(tail(w.buf@, seen, 0, -base));
                    lemma_item_flip(w.buf@, seen, 0, -base, j as int, gst, gt, Seq::empty(), Seq::empty(), envv);
                    if item(seen, base + j, gst, gt, envv) is None {
                        lemma_content_fail(seen, base + j, gst, gt, envv);
                    } else {
                        lemma_content_past(seen, base + j, gst, gt, envv);
                    }
                    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies docx(s) is None by {}
                }
                return S_FAIL;
            }
            S_WAIT
        },
    }
}

/// Whether `b[a..e]` has a carriage return (for the emitted pieces).
fn ex_any_cr(b: &[u8], a: usize, e: usize) -> (r: bool)
    requires
        a <= e <= b@.len(),
{
    let mut i = a;
    while i < e
        invariant
            a <= i <= e <= b@.len(),
        decreases e - i,
    {
        if b[i] == 0x0D {
            return true;
        }
        i = i + 1;
    }
    false
}

/// Emits the text or CDATA section read so far, up to `e`.
fn win_emit(w: &mut Win, kind: Kind, e: usize, flags: u8)
    requires
        old(w).tem <= e <= old(w).buf@.len(),
        old(w).buf@.len() <= MAX_POS,
    ensures
        final(w).buf == old(w).buf,
        final(w).seen == old(w).seen,
        final(w).base == old(w).base,
        final(w).pos == old(w).pos,
        final(w).cpos == old(w).cpos,
        final(w).mode == old(w).mode,
        final(w).tem == e,
        final(w).tcr == old(w).tcr,
        final(w).gt == old(w).gt,
        final(w).gst == old(w).gst,
        final(w).gts == old(w).gts,
        final(w).names == old(w).names,
        final(w).ends == old(w).ends,
{
    let cr = ex_any_cr(w.buf.as_slice(), w.tem, e);
    let f = if cr {
        flags | P_CR
    } else {
        flags
    };
    w.out.push(tok(kind, w.tem, e, f));
    w.tem = e;
    w.tfirst = false;
}

/// Where a piece emitted while the text goes on may end: before the
/// characters still being checked, and not between a carriage return and
/// what follows it.
fn piece_end(w: &Win, m: usize) -> (e: usize)
    requires
        w.tem <= m <= w.buf@.len(),
    ensures
        w.tem <= e <= m,
{
    let mut e = if m < w.cpos {
        m
    } else {
        w.cpos
    };
    if e < w.tem {
        e = w.tem;
    }
    if e > w.tem && w.buf[e - 1] == 0x0D {
        e = e - 1;
    }
    e
}


#[verifier::spinoff_prover]
proof fn lemma_text_commit(
    b: Seq<u8>,
    seen: Seq<u8>,
    base: int,
    m: int,
    ts: int,
    gst: Seq<Open>,
    gt: Seq<XTok>,
    envv: Env,
    cr: bool,
)
    requires
        0 <= base <= seen.len(),
        b == seen.subrange(base, seen.len() as int),
        0 <= m < b.len(),
        b[m] == 0x3C || b[m] == 0x26,
        0 <= ts <= base + m,
        ts < seen.len(),
        seen[ts] != 0x3C && seen[ts] != 0x26,
        gst.len() > 0,
        cr == has_cr(seen, ts, base + m),
        forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> text_end(s, ts) == text_end(s, base + m),
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_content(s, ts, gst, gt, envv)
            } else {
                None
            }),
    ensures
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_content(s, base + m, gst, gt.push(XTok::Text { start: ts, end: base + m, cr: cr }), envv)
            } else {
                None
            }),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    let k = base + m;
    assert(b[m] == seen[k]);
    assert(ts < k);
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies docx(s) == (if doc_chars(s) {
        after_content(s, k, gst, gt.push(XTok::Text { start: ts, end: k, cr: cr }), envv)
    } else {
        None
    }) by {
        lemma_window(b, seen, base, s);
        lemma_text_stop(b, s, 0, b.len() as int, -base, m);
        lemma_ext_byte(seen, s, ts);
        lemma_text_item(s, ts, k, gst, gt, envv);
        lemma_has_cr_ext(seen, s, ts, k);
        lemma_content_step(s, ts, gst, gt, envv);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_text_cdend_fail(
    b: Seq<u8>,
    seen: Seq<u8>,
    base: int,
    m: int,
    ts: int,
    gst: Seq<Open>,
    gt: Seq<XTok>,
    envv: Env,
    last: bool,
)
    requires
        0 <= base <= seen.len(),
        b == seen.subrange(base, seen.len() as int),
        0 <= m,
        m + 3 <= b.len(),
        b[m] == 0x5D && b[m + 1] == 0x5D && b[m + 2] == 0x3E,
        0 <= ts < seen.len(),
        seen[ts] != 0x3C && seen[ts] != 0x26,
        gst.len() > 0,
        forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> text_end(s, ts) == text_end(s, base + m),
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_content(s, ts, gst, gt, envv)
            } else {
                None
            }),
    ensures
        fails(seen, last),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies docx(s) is None by {
        lemma_window(b, seen, base, s);
        lemma_text_cdend(b, s, 0, b.len() as int, -base, m);
        lemma_ext_byte(seen, s, ts);
        assert(item(s, ts, gst, gt, envv) is None);
        lemma_content_fail(s, ts, gst, gt, envv);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_text_last_fail(
    b: Seq<u8>,
    seen: Seq<u8>,
    base: int,
    m: int,
    ts: int,
    gst: Seq<Open>,
    gt: Seq<XTok>,
    envv: Env,
)
    requires
        0 <= base <= seen.len(),
        b == seen.subrange(base, seen.len() as int),
        0 <= m <= b.len(),
        forall|k: int| m <= k < b.len() ==> #[trigger] b[k] != 0x3C && b[k] != 0x26,
        0 <= ts < seen.len(),
        seen[ts] != 0x3C && seen[ts] != 0x26,
        gst.len() > 0,
        forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> text_end(s, ts) == text_end(s, base + m),
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_content(s, ts, gst, gt, envv)
            } else {
                None
            }),
    ensures
        fails(seen, true),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    lemma_window_exact(b, seen, base);
    assert(tail(b, seen, 0, -base));
    lemma_text_tail(b, seen, 0, -base, m);
    lemma_ext_refl(seen);
    assert(text_end(seen, ts) == text_end(seen, base + m));
    if text_end(seen, ts) is None {
        assert(item(seen, ts, gst, gt, envv) is None);
        lemma_content_fail(seen, ts, gst, gt, envv);
    } else {
        lemma_text_to_end(seen, ts, gst, gt, envv);
    }
}

/// Text, from where it was left, as far as the window decides it.
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
// `env` is only for the proof.
#[allow(unused_variables)]
fn step_text(w: &mut Win, env: &XEnv, last: bool) -> (r: u8)
    requires
        old(w).inv(env_view(env)),
        old(w).mode == M_TEXT,
    ensures
        final(w).same_win(old(w)),
        r == S_ON ==> final(w).inv(env_view(env)) && final(w).left() < old(w).left(),
        r == S_WAIT ==> !last && final(w).inv(env_view(env)),
        r == S_ON || r == S_WAIT || r == S_FAIL,
        r == S_FAIL ==> fails(final(w).seen@, last),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    hide(item);
    let ghost envv = env_view(env);
    let ghost seen = w.seen@;
    let ghost base = w.base as int;
    let ghost gst = w.gst@;
    let ghost gt = w.gt@;
    let ghost ts = w.gts@;
    let n = w.buf.len();
    let mut m = w.pos;
    let mut cr = w.tcr;
    loop
        invariant
            w.inv(envv),
            w.mode == M_TEXT,
            old(w).mode == M_TEXT,
            seen == w.seen@,
            base == w.base,
            gst == w.gst@,
            gt == w.gt@,
            ts == w.gts@,
            envv == env_view(env),
            n == w.buf@.len(),
            w.same_win(old(w)),
            w.tem == old(w).tem,
            w.pos == old(w).pos,
            w.pos <= m <= n,
            cr == has_cr(seen, ts, base + m),
            forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> text_end(s, ts) == text_end(s, base + m),
        ensures
            m == n || (w.buf@[m as int] == 0x5D && (n - m == 1 || (n - m == 2 && w.buf@[m + 1] == 0x5D))),
        decreases n - m,
    {
        if m == n {
            break ;
        }
        let x = get(w.buf.as_slice(), m);
        if x == 0x3C || x == 0x26 {
            // The text ends at `m`.
            let ghost k = base + m;
            let ghost t2 = gt.push(XTok::Text { start: ts, end: k, cr: cr });
            proof {
                lemma_text_commit(w.buf@, seen, base, m as int, ts, gst, gt, envv, cr);
            }
            if m > w.tem {
                win_emit(w, Kind::Text, m, 0);
            }
            w.mode = M_ITEM;
            w.pos = m;
            proof {
                w.gt@ = t2;
            }
            return S_ON;
        }
        if x == 0x5D && n - m > 2 && get(w.buf.as_slice(), m + 1) == 0x5D && get(w.buf.as_slice(), m + 2) == 0x3E {
            proof {
                lemma_text_cdend_fail(w.buf@, seen, base, m as int, ts, gst, gt, envv, last);
            }
            // The text before `]]>` is reported, then the error.
            if m > w.tem {
                win_emit(w, Kind::Text, m, 0);
            }
            return S_FAIL;
        }
        let safe = x != 0x5D || (n - m > 1 && get(w.buf.as_slice(), m + 1) != 0x5D) || (n - m > 2 && get(
            w.buf.as_slice(),
            m + 2,
        ) != 0x3E);
        if !safe {
            break ;
        }
        proof {
            assert(text_safe(w.buf@, m as int, n as int));
            assert(w.buf@[m as int] == seen[base + m]);
            lemma_has_cr_step(seen, ts, base + m);
            assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies text_end(s, ts) == text_end(s, base + m + 1) by {
                lemma_window(w.buf@, seen, base, s);
                lemma_text_step(w.buf@, s, 0, n as int, -base, m as int);
            }
        }
        cr = cr || x == 0x0D;
        m = m + 1;
    }
    // The window ends before the text does.
    if last {
        proof {
            assert forall|k: int| m <= k < n implies #[trigger] w.buf@[k] != 0x3C && w.buf@[k] != 0x26 by {
                if k > m {
                    assert(w.buf@[m as int] == 0x5D);
                }
            }
            lemma_text_last_fail(w.buf@, seen, base, m as int, ts, gst, gt, envv);
        }
        // The text up to the end is reported, then the error.
        if n > w.tem {
            win_emit(w, Kind::Text, n, 0);
        }
        return S_FAIL;
    }
    w.pos = m;
    w.tcr = cr;
    let e = piece_end(w, m);
    if e > w.tem {
        win_emit(w, Kind::Text, e, 0);
    }
    S_WAIT
}

/// A CDATA section, from where it was left, as far as the window decides
/// it.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
// `env` is only for the proof.
#[allow(unused_variables)]
fn step_cdata(w: &mut Win, env: &XEnv, last: bool) -> (r: u8)
    requires
        old(w).inv(env_view(env)),
        old(w).mode == M_CDATA,
    ensures
        final(w).same_win(old(w)),
        r == S_ON ==> final(w).inv(env_view(env)) && final(w).left() < old(w).left(),
        r == S_WAIT ==> !last && final(w).inv(env_view(env)),
        r == S_ON || r == S_WAIT || r == S_FAIL,
        r == S_FAIL ==> fails(final(w).seen@, last),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    hide(item);
    let ghost envv = env_view(env);
    let ghost seen = w.seen@;
    let ghost base = w.base as int;
    let ghost gst = w.gst@;
    let ghost gt = w.gt@;
    let ghost ts = w.gts@;
    let n = w.buf.len();
    let mut m = w.pos;
    let mut cr = w.tcr;
    loop
        invariant
            w.inv(envv),
            w.mode == M_CDATA,
            old(w).mode == M_CDATA,
            seen == w.seen@,
            base == w.base,
            gst == w.gst@,
            gt == w.gt@,
            ts == w.gts@,
            envv == env_view(env),
            n == w.buf@.len(),
            w.same_win(old(w)),
            w.tem == old(w).tem,
            w.pos == old(w).pos,
            w.pos <= m <= n,
            cr == has_cr(seen, ts + 9, base + m),
            forall|s: Seq<u8>| #[trigger] ext(seen, s) ==> cdata_end(s, ts + 9) == cdata_end(s, base + m),
        ensures
            n - m <= 2,
        decreases n - m,
    {
        if m == n {
            break ;
        }
        let x = get(w.buf.as_slice(), m);
        if x == 0x5D && n - m > 2 && get(w.buf.as_slice(), m + 1) == 0x5D && get(w.buf.as_slice(), m + 2) == 0x3E {
            let ghost k = base + m;
            let ghost t2 = gt.push(XTok::CData { start: ts + 9, end: k, cr: cr });
            proof {
                assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies docx(s) == (if doc_chars(s) {
                    after_content(s, k + 3, gst, t2, envv)
                } else {
                    None
                }) by {
                    lemma_window(w.buf@, seen, base, s);
                    lemma_cdata_stop(w.buf@, s, 0, n as int, -base, m as int);
                    lemma_ext_lit(seen, s, ts, lit_cdata());
                    lemma_cdata_item(s, ts, k, gst, gt, envv);
                    lemma_has_cr_ext(seen, s, ts + 9, k);
                    lemma_content_step(s, ts, gst, gt, envv);
                }
            }
            let f = if w.tfirst {
                P_FIRST | P_LAST
            } else {
                P_LAST
            };
            win_emit(w, Kind::CData, m, f);
            w.mode = M_ITEM;
            w.pos = m + 3;
            proof {
                w.gt@ = t2;
            }
            return S_ON;
        }
        let safe = x != 0x5D || (n - m > 1 && get(w.buf.as_slice(), m + 1) != 0x5D) || (n - m > 2 && get(
            w.buf.as_slice(),
            m + 2,
        ) != 0x3E);
        if !safe {
            break ;
        }
        proof {
            assert(no_cdend(w.buf@, m as int, n as int));
            assert(w.buf@[m as int] == seen[base + m]);
            lemma_has_cr_step(seen, ts + 9, base + m);
            assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies cdata_end(s, ts + 9) == cdata_end(
                s,
                base + m + 1,
            ) by {
                lemma_window(w.buf@, seen, base, s);
                lemma_cdata_step(w.buf@, s, 0, n as int, -base, m as int);
            }
        }
        cr = cr || x == 0x0D;
        m = m + 1;
    }
    if last {
        proof {
            lemma_window_exact(w.buf@, seen, base);
            assert(tail(w.buf@, seen, 0, -base));
            lemma_cdata_tail(w.buf@, seen, 0, -base, m as int);
            lemma_ext_refl(seen);
            lemma_cdata_fail(seen, ts, gst, gt, envv);
            lemma_content_fail(seen, ts, gst, gt, envv);
            assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies docx(s) is None by {}
        }
        // The section's text up to the end is reported, then the error.
        if n > w.tem || w.tfirst {
            let f = if w.tfirst {
                P_FIRST
            } else {
                0
            };
            win_emit(w, Kind::CData, n, f);
        }
        return S_FAIL;
    }
    w.pos = m;
    w.tcr = cr;
    let e = piece_end(w, m);
    if e > w.tem || w.tfirst {
        let f = if w.tfirst {
            P_FIRST
        } else {
            0
        };
        win_emit(w, Kind::CData, e, f);
    }
    S_WAIT
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_epilog_item_goal(b: Seq<u8>, seen: Seq<u8>, base: int, j: int, gt: Seq<XTok>, envv: Env)
    requires
        0 <= base <= seen.len(),
        b == seen.subrange(base, seen.len() as int),
        0 <= j < b.len(),
        has_lit(b, j, lit_comment()) || has_lit(b, j, lit_pi()),
        item(b, j, Seq::empty(), Seq::empty(), envv) matches Some((_, _, e)) && j < e <= b.len(),
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_content(s, base + j, Seq::empty(), gt, envv)
            } else {
                None
            }),
    ensures
        ({
            let (sx, u, e) = item(b, j, Seq::empty(), Seq::empty(), envv).unwrap();
            let gt2 = gt + mv(added(Seq::empty(), u), -base, gt.len() as int);
            sx.len() == 0 && forall|s: Seq<u8>|
                #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                    after_content(s, base + e, Seq::empty(), gt2, envv)
                } else {
                    None
                })
        }),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    hide(fin);
    hide(item);
    let (sx, u, e) = item(b, j, Seq::empty(), Seq::empty(), envv).unwrap();
    let gt2 = gt + mv(added(Seq::empty(), u), -base, gt.len() as int);
    lemma_lits_stable();
    assert(b.subrange(j, j + 2)[0] == b[j] && b.subrange(j, j + 2)[1] == b[j + 1]);
    assert(!is_etag(b, j));
    lemma_fin_item(b, j, Seq::empty(), envv);
    assert(item_reach(b, j, e) <= b.len());
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies docx(s) == (if doc_chars(s) {
        after_content(s, base + e, Seq::empty(), gt2, envv)
    } else {
        None
    }) by {
        lemma_window(b, seen, base, s);
        lemma_item_mv(b, s, 0, b.len() as int, -base, j, Seq::empty(), Seq::empty(), Seq::empty(), gt, envv);
        if has_lit(b, j, lit_pi()) {
            lemma_has_lit(b, s, 0, b.len() as int, -base, j, lit_pi());
        } else {
            lemma_has_lit(b, s, 0, b.len() as int, -base, j, lit_comment());
        }
        lemma_fin_item(s, base + j, gt, envv);
        lemma_content_done(s, base + j, gt, envv);
        lemma_content_done(s, base + e, gt2, envv);
    }
}


#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_epilog_stop(b: Seq<u8>, seen: Seq<u8>, base: int, j: int, gt: Seq<XTok>, envv: Env, last: bool)
    requires
        0 <= base <= seen.len(),
        b == seen.subrange(base, seen.len() as int),
        0 <= j < b.len(),
        !is_ws(b[j]),
        ({
            let n = b.len() as int;
            let stop = b[j] != 0x3C || (n - j >= 2 && b[j + 1] != 0x3F && b[j + 1] != 0x21) || (n - j >= 4 && b[j
                + 1] == 0x21 && (b[j + 2] != 0x2D || b[j + 3] != 0x2D));
            let short = n - j < 2 || (b[j + 1] == 0x21 && n - j < 4);
            stop || (last && short)
        }),
        forall|s: Seq<u8>|
            #[trigger] ext(seen, s) ==> docx(s) == (if doc_chars(s) {
                after_content(s, base + j, Seq::empty(), gt, envv)
            } else {
                None
            }),
    ensures
        fails(seen, last),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    hide(fin);
    lemma_lits_stable();
    let n = b.len() as int;
    let x = b[j];
    let stop = b[j] != 0x3C || (n - j >= 2 && b[j + 1] != 0x3F && b[j + 1] != 0x21) || (n - j >= 4 && b[j + 1]
        == 0x21 && (b[j + 2] != 0x2D || b[j + 3] != 0x2D));
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies docx(s) is None by {
        lemma_window(b, seen, base, s);
        let k = base + j;
        assert(b[j] == s[k]);
        if x != 0x3C {
            lemma_has_lit_no(b, s, 0, n, -base, j, lit_comment(), 0);
            lemma_has_lit_no(b, s, 0, n, -base, j, lit_pi(), 0);
        } else if stop && n - j >= 2 && b[j + 1] != 0x3F && b[j + 1] != 0x21 {
            lemma_has_lit_no(b, s, 0, n, -base, j, lit_comment(), 1);
            lemma_has_lit_no(b, s, 0, n, -base, j, lit_pi(), 1);
        } else if stop {
            if b[j + 2] != 0x2D {
                lemma_has_lit_no(b, s, 0, n, -base, j, lit_comment(), 2);
            } else {
                lemma_has_lit_no(b, s, 0, n, -base, j, lit_comment(), 3);
            }
            lemma_has_lit_no(b, s, 0, n, -base, j, lit_pi(), 1);
        } else {
            // `s` is `seen`, which ends within four bytes.
            lemma_window_exact(b, seen, base);
            if n - j >= 2 {
                lemma_has_lit_no(b, s, 0, n, -base, j, lit_pi(), 1);
                assert(b[j + 1] == s[k + 1]);
            }
        }
        lemma_fin_stop(s, k, gt);
        lemma_content_done(s, k, gt, envv);
    }
}

/// After the root element: white space, comments and processing
/// instructions to the end.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
fn step_epilog(w: &mut Win, env: &XEnv, last: bool) -> (r: u8)
    requires
        old(w).inv(env_view(env)),
        env_wf(env),
        old(w).mode == M_ITEM,
        old(w).gst@.len() == 0,
        last ==> old(w).cpos == old(w).buf@.len(),
    ensures
        final(w).same_win(old(w)),
        r == S_ON ==> final(w).inv(env_view(env)) && final(w).left() < old(w).left(),
        r == S_WAIT ==> !last && final(w).inv(env_view(env)),
        r == S_ON || r == S_WAIT || r == S_FAIL || r == S_DONE,
        r == S_FAIL ==> fails(final(w).seen@, last),
        r == S_DONE ==> last && docx(final(w).seen@) == Some(final(w).gt@),
{
    hide(document);
    hide(doc_chars);
    hide(item);
    hide(after_content);
    hide(fin);
    let ghost envv = env_view(env);
    let ghost seen = w.seen@;
    let ghost base = w.base as int;
    let ghost gt = w.gt@;
    slice_len_bound(w.buf.as_slice());
    proof {
        lemma_lits_stable();
        assert(w.gst@ =~= Seq::<Open>::empty());
    }
    let j = w.pos;
    let n = w.buf.len();
    if j == n {
        if last {
            proof {
                lemma_ext_refl(seen);
                lemma_window_exact(w.buf@, seen, base);
                lemma_fin_end(seen, gt);
                lemma_content_done(seen, base + j, gt, envv);
                lemma_chars_end(seen);
                reveal(doc_chars);
            }
            return S_DONE;
        }
        return S_WAIT;
    }
    let x = get(w.buf.as_slice(), j);
    if x == 0x20 || x == 0x09 || x == 0x0A || x == 0x0D {
        proof {
            assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies docx(s) == (if doc_chars(s) {
                after_content(s, base + j + 1, Seq::empty(), gt, envv)
            } else {
                None
            }) by {
                lemma_window(w.buf@, seen, base, s);
                assert(w.buf@[j as int] == s[base + j]);
                lemma_fin_ws(s, base + j, gt);
                lemma_content_done(s, base + j, gt, envv);
                lemma_content_done(s, base + j + 1, gt, envv);
            }
        }
        w.pos = j + 1;
        return S_ON;
    }
    // Decided: `Misc` stops here, before the end.
    let stop = x != 0x3C || (n - j >= 2 && get(w.buf.as_slice(), j + 1) != 0x3F && get(w.buf.as_slice(), j + 1)
        != 0x21) || (n - j >= 4 && get(w.buf.as_slice(), j + 1) == 0x21 && (get(w.buf.as_slice(), j + 2) != 0x2D
        || get(w.buf.as_slice(), j + 3) != 0x2D));
    // At the end, too short for a comment or a processing instruction.
    let short = n - j < 2 || (get(w.buf.as_slice(), j + 1) == 0x21 && n - j < 4);
    if stop || (last && short) {
        proof {
            lemma_epilog_stop(w.buf@, seen, base, j as int, gt, envv, last);
        }
        return S_FAIL;
    }
    if short {
        return S_WAIT;
    }
    // A comment or a processing instruction.
    proof {
        if w.buf@[j + 1] == 0x3F {
            assert(w.buf@.subrange(j as int, j + 2) =~= lit_pi());
        } else {
            assert(w.buf@.subrange(j as int, j + 4) =~= lit_comment());
        }
    }
    let mut sc: Vec<(usize, usize, usize)> = Vec::new();
    let mut tp = Tape::new();
    proof {
        assert(stack_view(sc@) =~= Seq::<Open>::empty());
    }
    match ex_item(w.buf.as_slice(), j, &mut sc, &mut tp, env) {
        Some(e) => {
            let ghost (sx, u, _e) = item(w.buf@, j as int, Seq::empty(), Seq::empty(), envv).unwrap();
            proof {
                lemma_epilog_item_goal(w.buf@, seen, base, j as int, gt, envv);
                w.gt@ = gt + mv(added(Seq::empty(), u), -base, gt.len() as int);
            }
            w.out.toks.append(&mut tp.toks);
            w.pos = e;
            S_ON
        },
        None => {
            if last {
                proof {
                    lemma_window_exact(w.buf@, seen, base);
                    lemma_ext_refl(seen);
                    assert(tail(w.buf@, seen, 0, -base));
                    lemma_lits_stable();
                    assert(w.buf@.subrange(j as int, j + 2)[0] == w.buf@[j as int]);
                    assert(!is_etag(w.buf@, j as int));
                    lemma_item_flip(
                        w.buf@,
                        seen,
                        0,
                        -base,
                        j as int,
                        Seq::empty(),
                        gt,
                        Seq::empty(),
                        Seq::empty(),
                        envv,
                    );
                    if w.buf@[j + 1] == 0x3F {
                        lemma_has_lit(w.buf@, seen, 0, n as int, -base, j as int, lit_pi());
                    } else {
                        lemma_has_lit(w.buf@, seen, 0, n as int, -base, j as int, lit_comment());
                    }
                    lemma_fin_item_fail(seen, base + j, gt, envv);
                    lemma_content_done(seen, base + j, gt, envv);
                    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies docx(s) is None by {}
                }
                return S_FAIL;
            }
            S_WAIT
        },
    }
}

/// Starts a CDATA section at `pos`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn start_cdata(w: &mut Win, Ghost(envv): Ghost<Env>)
    requires
        old(w).inv(envv),
        old(w).mode == M_ITEM,
        old(w).gst@.len() > 0,
        old(w).pos + 9 <= old(w).buf@.len(),
        has_lit(old(w).buf@, old(w).pos as int, lit_cdata()),
    ensures
        final(w).same_win(old(w)),
        final(w).inv(envv),
        final(w).left() < old(w).left(),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    hide(text_end);
    let ghost seen = w.seen@;
    let ghost base = w.base as int;
    proof {
        lemma_ext_refl(seen);
        lemma_window(w.buf@, seen, base, seen);
        lemma_has_lit(w.buf@, seen, 0, w.buf@.len() as int, -base, w.pos as int, lit_cdata());
        w.gts@ = base + w.pos;
        lemma_has_cr_empty(seen, base + w.pos + 9);
    }
    let p = w.pos;
    let _n = w.buf.len();
    assert(p + 9 <= _n);
    w.mode = M_CDATA;
    w.pos = p + 9;
    w.tem = w.pos;
    w.tcr = false;
    w.tfirst = true;
}

/// Starts text at `pos`.
#[verifier::spinoff_prover]
fn start_text(w: &mut Win, Ghost(envv): Ghost<Env>)
    requires
        old(w).inv(envv),
        old(w).mode == M_ITEM,
        old(w).gst@.len() > 0,
        old(w).pos < old(w).buf@.len(),
        old(w).buf@[old(w).pos as int] != 0x3C,
        old(w).buf@[old(w).pos as int] != 0x26,
    ensures
        final(w).same_win(old(w)),
        final(w).inv(envv),
        final(w).left() < old(w).left(),
{
    let ghost seen = w.seen@;
    let ghost base = w.base as int;
    proof {
        w.gts@ = base + w.pos;
        assert(w.buf@[w.pos as int] == seen[base + w.pos]);
        lemma_has_cr_empty(seen, base + w.pos);
    }
    w.mode = M_TEXT;
    w.tem = w.pos;
    w.tcr = false;
}

/// Reads the window as far as it decides the document. At the end
/// (`last`), the verdict.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub fn content_run(w: &mut Win, env: &XEnv, last: bool) -> (r: u8)
    requires
        old(w).inv(env_view(env)),
        env_wf(env),
        last ==> old(w).cpos == old(w).buf@.len(),
    ensures
        final(w).same_win(old(w)),
        r == S_WAIT || r == S_FAIL || r == S_DONE,
        r == S_WAIT ==> !last && final(w).inv(env_view(env)),
        r == S_FAIL ==> fails(final(w).seen@, last),
        r == S_DONE ==> last && docx(final(w).seen@) == Some(final(w).gt@),
{
    hide(document);
    hide(doc_chars);
    hide(after_content);
    hide(item);
    hide(text_end);
    hide(cdata_end);
    let ghost envv = env_view(env);
    loop
        invariant
            w.inv(envv),
            w.same_win(old(w)),
            envv == env_view(env),
            env_wf(env),
            last ==> w.cpos == w.buf@.len(),
        decreases w.left(),
    {
        let n = w.buf.len();
        let r = if w.mode == M_TEXT {
            step_text(w, env, last)
        } else if w.mode == M_CDATA {
            step_cdata(w, env, last)
        } else if w.ends.len() == 0 {
            step_epilog(w, env, last)
        } else {
            let j = w.pos;
            if j == n {
                if last {
                    proof {
                        let seen = w.seen@;
                        lemma_ext_refl(seen);
                        lemma_window_exact(w.buf@, seen, w.base as int);
                        lemma_content_fail(seen, w.base + j, w.gst@, w.gt@, envv);
                        assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies docx(s) is None by {}
                    }
                    S_FAIL
                } else {
                    S_WAIT
                }
            } else {
                let x = get(w.buf.as_slice(), j);
                if x == 0x3C {
                    if n - j >= 2 && get(w.buf.as_slice(), j + 1) == 0x2F {
                        step_etag(w, env, last)
                    } else if n - j >= 3 && get(w.buf.as_slice(), j + 1) == 0x21 && get(w.buf.as_slice(), j + 2)
                        == 0x5B {
                        if n - j >= 9 && ex_has_lit(w.buf.as_slice(), j, &L_CDATA) {
                            proof {
                                lemma_lits();
                            }
                            start_cdata(w, Ghost(envv));
                            S_ON
                        } else if n - j >= 9 || last {
                            step_item(w, env, last)
                        } else {
                            S_WAIT
                        }
                    } else {
                        step_item(w, env, last)
                    }
                } else if x == 0x26 {
                    step_item(w, env, last)
                } else {
                    start_text(w, Ghost(envv));
                    S_ON
                }
            }
        };
        if r != S_ON {
            return r;
        }
    }
}

} // verus!

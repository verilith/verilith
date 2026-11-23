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
use verilith_core::utf8::utf8_len;
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

pub const M_ITEM: u8 = 0;
pub const M_TEXT: u8 = 1;
pub const M_CDATA: u8 = 2;

/// Steps' results.
pub const S_ON: u8 = 0;
pub const S_WAIT: u8 = 1;
pub const S_FAIL: u8 = 2;
pub const S_DONE: u8 = 3;

/// Emitted pieces of text and CDATA sections: bit 0, a carriage return in
/// the piece; bit 1, the first piece of a CDATA section; bit 2, its last.
pub const P_CR: u8 = 1;
pub const P_FIRST: u8 = 2;
pub const P_LAST: u8 = 4;

pub struct Win {
    /// The input from `base`.
    pub buf: Vec<u8>,
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
    pub tcr: bool,
    pub tfirst: bool,
    /// The names of the open elements, end to end, and where each ends.
    pub names: Vec<u8>,
    pub ends: Vec<usize>,
    /// What this chunk emitted, at positions in `buf`.
    pub out: Tape,
    pub seen: Ghost<Seq<u8>>,
    pub gst: Ghost<Seq<Open>>,
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
            #[trigger] ext(self.seen@, s) ==> document(s, Enc::Utf8) == (if doc_chars(s) {
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
    forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) ==> document(s, Enc::Utf8) is None
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

fn push_slice(v: &mut Vec<u8>, b: &[u8], a: usize, e: usize)
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
            #[trigger] ext(seen, s) ==> document(s, Enc::Utf8) == (if doc_chars(s) {
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
                #[trigger] ext(seen, s) ==> document(s, Enc::Utf8) == (if doc_chars(s) {
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
    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) implies document(s, Enc::Utf8) == (if doc_chars(s) {
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
fn win_push_name(w: &mut Win, a: usize, e: usize, Ghost(p): Ghost<Open>)
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
                    assert forall|s: Seq<u8>| #[trigger] ext(seen, s) && (last ==> s == seen) implies document(
                        s,
                        Enc::Utf8,
                    ) is None by {}
                }
                return S_FAIL;
            }
            S_WAIT
        },
    }
}

} // verus!

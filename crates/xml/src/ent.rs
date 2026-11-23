//! Verified code for internal entities: their replacement text, and which
//! may be referred to in attribute values and in content (`oka_seq`,
//! `okc_seq`).
//!
//! Each of the two is a system of Horn clauses (`fix.rs`): an entity may be
//! referred to if its replacement text is right by itself, with every
//! entity allowed (`a_local`, `c_local`), and every internal entity it
//! refers to may be (`a_deps`, `c_deps`). `lemma_oka_hlev` and
//! `lemma_okc_hlev` prove the spec's levels are the levels of those
//! clauses, so `fix::ex_hfix` computes them: one pass over the replacement
//! texts to find each entity's own verdict and references, then a worklist
//! linear in their number. The levels settle by the number of entities
//! (`lemma_oka_settled`, `lemma_okc_settled`): a chain of references
//! longer than that repeats an entity, which is recursion.
use crate::chars::*;
use crate::content::*;
use crate::fix::*;
use crate::lex::*;
use crate::spec::*;
use crate::tape::*;
#[cfg(verus_keep_ghost)]
use verilith_core::utf8::utf8_encode;
use vstd::prelude::*;

verus! {

/// Appends the UTF-8 encoding of `c`.
#[inline(always)]
pub fn push_utf8(out: &mut Vec<u8>, c: u32)
    requires
        c <= 0x10FFFF,
    ensures
        final(out)@ == old(out)@ + utf8_encode(c),
{
    let ghost e = utf8_encode(c);
    if c < 0x80 {
        out.push(c as u8);
    } else if c < 0x800 {
        out.push((0xC0 + c / 64) as u8);
        out.push((0x80 + c % 64) as u8);
    } else if c < 0x10000 {
        out.push((0xE0 + c / 4096) as u8);
        out.push((0x80 + (c / 64) % 64) as u8);
        out.push((0x80 + c % 64) as u8);
    } else {
        out.push((0xF0 + c / 262144) as u8);
        out.push((0x80 + (c / 4096) % 64) as u8);
        out.push((0x80 + (c / 64) % 64) as u8);
        out.push((0x80 + c % 64) as u8);
    }
    assert(out@ =~= old(out)@ + e);
}

/// A character reference is at least four bytes (`&#N;`), and no
/// character takes more than four in UTF-8: the replacement text is never
/// longer than the literal.
pub proof fn lemma_charref_len(s: Seq<u8>, a: int)
    ensures
        charref(s, a) matches Some((c, e)) ==> e >= a + 4 && utf8_encode(c as u32).len() <= 4,
{
}

/// `repl(s, a, b)`.
pub fn ex_repl(s: &[u8], a: usize, b: usize) -> (r: Vec<u8>)
    requires
        a <= b <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
    ensures
        r@ == repl(s@, a as int, b as int),
        r@.len() <= b - a,
{
    let mut out: Vec<u8> = Vec::new();
    let mut i = a;
    proof {
        assert(out@ + repl(s@, a as int, b as int) =~= repl(s@, a as int, b as int));
    }
    while i < b
        invariant
            a <= i <= b <= s@.len() <= isize::MAX,
            s@.len() <= MAX_POS,
            out@ + repl(s@, i as int, b as int) == repl(s@, a as int, b as int),
            out@.len() <= i - a,
        decreases b - i,
    {
        let c = get(s, i);
        if c == 0x26 && ex_byte_is(s, i + 1, 0x23) {
            match ex_charref(s, i) {
                Some((v, e)) => {
                    if e > b {
                        proof {
                            assert(out@ + Seq::<u8>::empty() =~= out@);
                        }
                        return out;
                    }
                    proof {
                        lemma_charref_len(s@, i as int);
                        assert(repl(s@, i as int, b as int) == utf8_encode(v) + repl(s@, e as int, b as int));
                        assert(out@ + (utf8_encode(v) + repl(s@, e as int, b as int)) =~= (out@ + utf8_encode(v))
                            + repl(s@, e as int, b as int));
                    }
                    push_utf8(&mut out, v);
                    i = e;
                },
                None => {
                    proof {
                        assert(out@ + Seq::<u8>::empty() =~= out@);
                    }
                    return out;
                },
            }
        } else if c == 0x0D {
            let k = if i + 1 < b && get(s, i + 1) == 0x0A { i + 2 } else { i + 1 };
            proof {
                assert(repl(s@, i as int, b as int) == seq![0x0Au8] + repl(s@, k as int, b as int));
                assert(out@ + (seq![0x0Au8] + repl(s@, k as int, b as int)) =~= out@.push(0x0Au8) + repl(
                    s@,
                    k as int,
                    b as int,
                ));
            }
            out.push(0x0A);
            i = k;
        } else {
            proof {
                assert(repl(s@, i as int, b as int) == seq![c] + repl(s@, i + 1, b as int));
                assert(out@ + (seq![c] + repl(s@, i + 1, b as int)) =~= out@.push(c) + repl(s@, i + 1, b as int));
            }
            out.push(c);
            i = i + 1;
        }
    }
    proof {
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
    out
}

/// `att_text(r, 0, env)`.
pub fn ex_att_text(r: &[u8], env: &XEnv) -> (ok: bool)
    requires
        r@.len() <= isize::MAX,
        r@.len() <= MAX_POS,
        env_wf(env),
    ensures
        ok == att_text(r@, 0, env_view(env)),
{
    proof {
        lemma_lim_all(env);
    }
    let n = r.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == r@.len() <= isize::MAX,
            r@.len() <= MAX_POS,
            env_wf(env),
            lim_view(env, env.ents@.len() as int) == env_view(env),
            att_text(r@, i as int, env_view(env)) == att_text(r@, 0, env_view(env)),
        decreases n - i,
    {
        let c = get(r, i);
        if c == 0x3C {
            return false;
        }
        if c == 0x26 {
            match ex_att_ref(r, i, Some(env), env.ents.len()) {
                None => {
                    return false;
                },
                Some(e) => {
                    i = e;
                },
            }
        } else {
            i = i + 1;
        }
    }
    true
}

/// The replacement texts of the internal entities are in `rts`.
pub open spec fn rts_ok(doc: Seq<u8>, ents: Seq<XEnt>, rts: Seq<Vec<u8>>) -> bool {
    &&& rts.len() == ents.len()
    &&& forall|k: int|
        #![trigger rts[k]]
        0 <= k < ents.len() ==> rts[k]@.len() <= doc.len() && (ents[k].kind == 0 ==> rts[k]@ == repl(
            doc,
            ents[k].va as int,
            ents[k].vb as int,
        ))
}

/// The replacement text of each internal entity (and an empty one for
/// the others).
pub fn ex_rts(doc: &[u8], ents: &[XEnt]) -> (r: Vec<Vec<u8>>)
    requires
        doc@.len() <= isize::MAX,
        doc@.len() <= MAX_POS,
        ents_wf(doc@, ents@),
    ensures
        rts_ok(doc@, ents@, r@),
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    while k < ents.len()
        invariant
            k <= ents@.len(),
            doc@.len() <= isize::MAX,
            doc@.len() <= MAX_POS,
            ents_wf(doc@, ents@),
            out@.len() == k,
            forall|q: int|
                #![trigger out@[q]]
                0 <= q < k ==> out@[q]@.len() <= doc@.len() && (ents@[q].kind == 0 ==> out@[q]@ == repl(
                    doc@,
                    ents@[q].va as int,
                    ents@[q].vb as int,
                )),
        decreases ents@.len() - k,
    {
        let e = ents[k];
        proof {
            assert(e.va <= e.vb <= doc@.len());
        }
        if e.kind == 0 {
            out.push(ex_repl(doc, e.va as usize, e.vb as usize));
        } else {
            out.push(Vec::new());
        }
        k = k + 1;
    }
    out
}


// ---------------------------------------------------------------------------
// The clauses: each entity's own verdict and the entities it refers to
// ---------------------------------------------------------------------------

/// Every one of `n` entities allowed.
pub open spec fn all_ok(n: int) -> Seq<bool> {
    Seq::new(n as nat, |k: int| true)
}

/// The internal entity that the reference at `i` names, if it names one
/// (`r[i]` is `&`): not a character reference, not a predefined entity.
pub open spec fn ref_int(r: Seq<u8>, i: int, ents: Seq<Ent>) -> Option<int> {
    if byte_is(r, i + 1, 0x23) {
        None
    } else {
        let n = name_end(r, i + 1);
        if n > i + 1 && byte_is(r, n, 0x3B) && predef(r, i + 1, n) is None {
            match find_ent(ents, r.subrange(i + 1, n)) {
                Some(j) => if ents[j].kind is Internal {
                    Some(j)
                } else {
                    None
                },
                None => None,
            }
        } else {
            None
        }
    }
}

pub open spec fn opt_seq(o: Option<int>) -> Seq<int> {
    match o {
        Some(j) => seq![j],
        None => Seq::empty(),
    }
}

/// The environment of `ent_oka`, with the entities allowed in attribute
/// values `p`.
pub open spec fn aenv(ents: Seq<Ent>, wfc: bool, p: Seq<bool>) -> Env {
    Env { ents, wfc, oka: p, okc: Seq::empty() }
}

/// The environment of `ent_okc`, with the entities allowed in content `p`.
pub open spec fn cenv(ents: Seq<Ent>, wfc: bool, oka: Seq<bool>, p: Seq<bool>) -> Env {
    Env { ents, wfc, oka, okc: p }
}

/// The internal entities named by the references `att_text` meets in `r`
/// from `i`, with every entity allowed.
pub open spec fn att_deps(r: Seq<u8>, i: int, ents: Seq<Ent>, wfc: bool) -> Seq<int>
    decreases r.len() - i,
{
    if !(0 <= i < r.len()) || r[i] == 0x3C {
        Seq::empty()
    } else if r[i] == 0x26 {
        match att_ref(r, i, Some(aenv(ents, wfc, all_ok(ents.len() as int)))) {
            None => Seq::empty(),
            Some(e) => if i < e <= r.len() {
                opt_seq(ref_int(r, i, ents)) + att_deps(r, e, ents, wfc)
            } else {
                Seq::empty()
            },
        }
    } else {
        att_deps(r, i + 1, ents, wfc)
    }
}

/// The internal entities named by the references in content that
/// `ent_content` meets in `r` from `i`, with every entity allowed in
/// content.
pub open spec fn cdeps(r: Seq<u8>, i: int, st: Seq<Open>, t: Seq<XTok>, ents: Seq<Ent>, wfc: bool, oka: Seq<bool>) -> Seq<
    int,
>
    decreases r.len() - i,
{
    if !(0 <= i < r.len()) {
        Seq::empty()
    } else {
        match item(r, i, st, t, cenv(ents, wfc, oka, all_ok(ents.len() as int))) {
            None => Seq::empty(),
            Some((st2, t2, e)) => if i < e <= r.len() {
                (if r[i] == 0x26 {
                    opt_seq(ref_int(r, i, ents))
                } else {
                    Seq::empty()
                }) + cdeps(r, e, st2, t2, ents, wfc, oka)
            } else {
                Seq::empty()
            },
        }
    }
}

/// Each entity's own verdict in attribute values.
pub open spec fn a_local(s: Seq<u8>, ents: Seq<Ent>, wfc: bool) -> Seq<bool> {
    Seq::new(
        ents.len(),
        |k: int|
            match ents[k].kind {
                EKind::Internal { start, end } => att_text(repl(s, start, end), 0, aenv(ents, wfc, all_ok(ents.len() as int))),
                _ => false,
            },
    )
}

pub open spec fn a_deps(s: Seq<u8>, ents: Seq<Ent>, wfc: bool) -> Seq<Seq<int>> {
    Seq::new(
        ents.len(),
        |k: int|
            match ents[k].kind {
                EKind::Internal { start, end } => att_deps(repl(s, start, end), 0, ents, wfc),
                _ => Seq::empty(),
            },
    )
}

/// Each entity's own verdict in content.
pub open spec fn c_local(s: Seq<u8>, ents: Seq<Ent>, wfc: bool, oka: Seq<bool>) -> Seq<bool> {
    Seq::new(
        ents.len(),
        |k: int|
            match ents[k].kind {
                EKind::Internal { start, end } => ent_content(
                    repl(s, start, end),
                    0,
                    Seq::empty(),
                    Seq::empty(),
                    cenv(ents, wfc, oka, all_ok(ents.len() as int)),
                ) is Some,
                _ => false,
            },
    )
}

pub open spec fn c_deps(s: Seq<u8>, ents: Seq<Ent>, wfc: bool, oka: Seq<bool>) -> Seq<Seq<int>> {
    Seq::new(
        ents.len(),
        |k: int|
            match ents[k].kind {
                EKind::Internal { start, end } => cdeps(repl(s, start, end), 0, Seq::empty(), Seq::empty(), ents, wfc, oka),
                _ => Seq::empty(),
            },
    )
}

// ---------------------------------------------------------------------------
// The spec's levels are the clauses' levels
// ---------------------------------------------------------------------------

/// A reference in an attribute value is allowed with `p` when it is with
/// every entity allowed and the internal entity it names, if any, is in `p`.
proof fn lemma_att_ref_split(r: Seq<u8>, i: int, ents: Seq<Ent>, wfc: bool, p: Seq<bool>)
    requires
        p.len() == ents.len(),
    ensures
        att_ref(r, i, Some(aenv(ents, wfc, p))) == match ref_int(r, i, ents) {
            Some(j) => if p[j] {
                att_ref(r, i, Some(aenv(ents, wfc, all_ok(ents.len() as int))))
            } else {
                None
            },
            None => att_ref(r, i, Some(aenv(ents, wfc, all_ok(ents.len() as int)))),
        },
{
    if !byte_is(r, i + 1, 0x23) {
        let n = name_end(r, i + 1);
        lemma_find_range(ents, r.subrange(i + 1, n));
    }
}

/// `att_text` with `p` is `att_text` with every entity allowed, and the
/// entities its references name in `p`.
proof fn lemma_att_text_split(r: Seq<u8>, i: int, ents: Seq<Ent>, wfc: bool, p: Seq<bool>)
    requires
        p.len() == ents.len(),
    ensures
        att_text(r, i, aenv(ents, wfc, p)) == (att_text(r, i, aenv(ents, wfc, all_ok(ents.len() as int))) && all_in(
            att_deps(r, i, ents, wfc),
            p,
        )),
    decreases r.len() - i,
{
    let t = aenv(ents, wfc, all_ok(ents.len() as int));
    if !(0 <= i < r.len()) || r[i] == 0x3C {
    } else if r[i] == 0x26 {
        lemma_att_ref_split(r, i, ents, wfc, p);
        match att_ref(r, i, Some(t)) {
            None => {},
            Some(e) => if i < e <= r.len() {
                lemma_att_text_split(r, e, ents, wfc, p);
                lemma_all_in_add(opt_seq(ref_int(r, i, ents)), att_deps(r, e, ents, wfc), p);
                if !byte_is(r, i + 1, 0x23) {
                    lemma_find_range(ents, r.subrange(i + 1, name_end(r, i + 1)));
                }
                match ref_int(r, i, ents) {
                    Some(j) => {
                        assert(opt_seq(Some(j))[0] == j);
                        assert(all_in(seq![j], p) == p[j]);
                    },
                    None => {
                        assert(all_in(Seq::<int>::empty(), p));
                    },
                }
            } else {
            },
        }
    } else {
        lemma_att_text_split(r, i + 1, ents, wfc, p);
    }
}

/// `oka_seq` is the clauses' `hlev`.
pub proof fn lemma_oka_hlev(s: Seq<u8>, ents: Seq<Ent>, wfc: bool, d: nat)
    ensures
        oka_seq(s, ents, wfc, d) == hlev(a_local(s, ents, wfc), a_deps(s, ents, wfc), d),
    decreases d,
{
    let (lo, ds) = (a_local(s, ents, wfc), a_deps(s, ents, wfc));
    if d == 0 {
        assert(oka_seq(s, ents, wfc, d) =~= hlev(lo, ds, d));
    } else {
        lemma_oka_hlev(s, ents, wfc, (d - 1) as nat);
        let prev = oka_seq(s, ents, wfc, (d - 1) as nat);
        lemma_hlev_len(lo, ds, (d - 1) as nat);
        assert forall|k: int| 0 <= k < ents.len() implies #[trigger] ent_oka(s, ents, wfc, prev, k) == (lo[k] && all_in(
            ds[k],
            prev,
        )) by {
            match ents[k].kind {
                EKind::Internal { start, end } => {
                    lemma_att_text_split(repl(s, start, end), 0, ents, wfc, prev);
                },
                _ => {},
            }
        }
        assert(oka_seq(s, ents, wfc, d) =~= hstep(lo, ds, prev));
    }
}

/// The levels of `oka_seq` settle by the number of entities.
pub proof fn lemma_oka_settled(s: Seq<u8>, ents: Seq<Ent>, wfc: bool, m: nat)
    ensures
        oka_seq(s, ents, wfc, ents.len() + m) == oka_seq(s, ents, wfc, ents.len()),
{
    lemma_oka_hlev(s, ents, wfc, ents.len() + m);
    lemma_oka_hlev(s, ents, wfc, ents.len());
    lemma_hlev_settled(a_local(s, ents, wfc), a_deps(s, ents, wfc), m);
}

/// A reference in an attribute value does not depend on which entities
/// may be referred to in content.
proof fn lemma_att_chars_okc(s: Seq<u8>, i: int, q: u8, e1: Env, e2: Env)
    requires
        e1.ents == e2.ents && e1.wfc == e2.wfc && e1.oka == e2.oka,
    ensures
        att_chars(s, i, q, Some(e1)) == att_chars(s, i, q, Some(e2)),
    decreases s.len() - i,
{
    if 0 <= i < s.len() && s[i] != q && s[i] != 0x3C {
        assert(att_ref(s, i, Some(e1)) == att_ref(s, i, Some(e2)));
        if s[i] == 0x26 {
            match att_ref(s, i, Some(e1)) {
                Some(e) => if i < e <= s.len() {
                    lemma_att_chars_okc(s, e, q, e1, e2);
                },
                None => {},
            }
        } else {
            lemma_att_chars_okc(s, i + 1, q, e1, e2);
        }
    }
}

proof fn lemma_attrs_okc(s: Seq<u8>, i: int, t: Seq<XTok>, e1: Env, e2: Env)
    requires
        e1.ents == e2.ents && e1.wfc == e2.wfc && e1.oka == e2.oka,
    ensures
        attrs(s, i, t, e1) == attrs(s, i, t, e2),
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if !byte_is(s, j, 0x3E) && !has_lit(s, j, lit_empty_end()) && j != i {
        let n = name_end(s, j);
        if n != j {
            match eq_end(s, n) {
                Some(v) => if 0 <= v < s.len() && quote(s[v]) {
                    lemma_att_chars_okc(s, v + 1, s[v], e1, e2);
                    match att_chars(s, v + 1, s[v], Some(e1)) {
                        Some(q) => if i < q + 1 <= s.len() {
                            lemma_attrs_okc(
                                s,
                                q + 1,
                                t.push(XTok::Attr { start: j, end: n }).push(
                                    XTok::AttVal { start: v + 1, end: q, plain: att_plain(s, v + 1, q) },
                                ),
                                e1,
                                e2,
                            );
                        },
                        None => {},
                    }
                },
                None => {},
            }
        }
    }
}

/// An item with `p` is the item with every entity allowed in content,
/// unless it is a reference to an internal entity not in `p`.
proof fn lemma_item_split(r: Seq<u8>, i: int, st: Seq<Open>, t: Seq<XTok>, ents: Seq<Ent>, wfc: bool, oka: Seq<bool>, p: Seq<bool>)
    requires
        0 <= i < r.len(),
        p.len() == ents.len(),
    ensures
        item(r, i, st, t, cenv(ents, wfc, oka, p)) == if r[i] == 0x26 && (ref_int(r, i, ents) matches Some(j) && !p[j]) {
            None
        } else {
            item(r, i, st, t, cenv(ents, wfc, oka, all_ok(ents.len() as int)))
        },
{
    let (ep, et) = (cenv(ents, wfc, oka, p), cenv(ents, wfc, oka, all_ok(ents.len() as int)));
    if r[i] == 0x3C {
        let n = name_end(r, i + 1);
        lemma_attrs_okc(r, n, t.push(XTok::STag { start: i + 1, end: n, close: 0 }), ep, et);
        assert(stag(r, i, t, ep) == stag(r, i, t, et));
    } else if r[i] == 0x26 {
        if !byte_is(r, i + 1, 0x23) {
            let n = name_end(r, i + 1);
            lemma_find_range(ents, r.subrange(i + 1, n));
        }
        assert(content_ref(r, i, ep) == if (ref_int(r, i, ents) matches Some(j) && !p[j]) {
            None
        } else {
            content_ref(r, i, et)
        });
    }
}

/// `ent_content` with `p` succeeds when it does with every entity allowed
/// in content and the entities its references name are in `p`.
proof fn lemma_ent_content_split(r: Seq<u8>, i: int, st: Seq<Open>, t: Seq<XTok>, ents: Seq<Ent>, wfc: bool, oka: Seq<bool>, p: Seq<bool>)
    requires
        p.len() == ents.len(),
    ensures
        (ent_content(r, i, st, t, cenv(ents, wfc, oka, p)) is Some) == (ent_content(
            r,
            i,
            st,
            t,
            cenv(ents, wfc, oka, all_ok(ents.len() as int)),
        ) is Some && all_in(cdeps(r, i, st, t, ents, wfc, oka), p)),
    decreases r.len() - i,
{
    let et = cenv(ents, wfc, oka, all_ok(ents.len() as int));
    if 0 <= i < r.len() {
        lemma_item_split(r, i, st, t, ents, wfc, oka, p);
        match item(r, i, st, t, et) {
            None => {},
            Some((st2, t2, e)) => if i < e <= r.len() {
                lemma_ent_content_split(r, e, st2, t2, ents, wfc, oka, p);
                let a = if r[i] == 0x26 {
                    opt_seq(ref_int(r, i, ents))
                } else {
                    Seq::empty()
                };
                lemma_all_in_add(a, cdeps(r, e, st2, t2, ents, wfc, oka), p);
                if !byte_is(r, i + 1, 0x23) {
                    lemma_find_range(ents, r.subrange(i + 1, name_end(r, i + 1)));
                }
                if r[i] == 0x26 {
                    match ref_int(r, i, ents) {
                        Some(j) => {
                            assert(opt_seq(Some(j))[0] == j);
                            assert(all_in(seq![j], p) == p[j]);
                        },
                        None => {
                            assert(all_in(Seq::<int>::empty(), p));
                        },
                    }
                } else {
                    assert(all_in(Seq::<int>::empty(), p));
                }
            },
        }
    } else {
        assert(all_in(Seq::<int>::empty(), p));
    }
}

/// `okc_seq` is the clauses' `hlev`.
pub proof fn lemma_okc_hlev(s: Seq<u8>, ents: Seq<Ent>, wfc: bool, oka: Seq<bool>, d: nat)
    ensures
        okc_seq(s, ents, wfc, oka, d) == hlev(c_local(s, ents, wfc, oka), c_deps(s, ents, wfc, oka), d),
    decreases d,
{
    let (lo, ds) = (c_local(s, ents, wfc, oka), c_deps(s, ents, wfc, oka));
    if d == 0 {
        assert(okc_seq(s, ents, wfc, oka, d) =~= hlev(lo, ds, d));
    } else {
        lemma_okc_hlev(s, ents, wfc, oka, (d - 1) as nat);
        let prev = okc_seq(s, ents, wfc, oka, (d - 1) as nat);
        lemma_hlev_len(lo, ds, (d - 1) as nat);
        assert forall|k: int| 0 <= k < ents.len() implies #[trigger] ent_okc(s, ents, wfc, oka, prev, k) == (lo[k] && all_in(
            ds[k],
            prev,
        )) by {
            match ents[k].kind {
                EKind::Internal { start, end } => {
                    lemma_ent_content_split(repl(s, start, end), 0, Seq::empty(), Seq::empty(), ents, wfc, oka, prev);
                },
                _ => {},
            }
        }
        assert(okc_seq(s, ents, wfc, oka, d) =~= hstep(lo, ds, prev));
    }
}

/// The levels of `okc_seq` settle by the number of entities.
pub proof fn lemma_okc_settled(s: Seq<u8>, ents: Seq<Ent>, wfc: bool, oka: Seq<bool>, m: nat)
    ensures
        okc_seq(s, ents, wfc, oka, ents.len() + m) == okc_seq(s, ents, wfc, oka, ents.len()),
{
    lemma_okc_hlev(s, ents, wfc, oka, ents.len() + m);
    lemma_okc_hlev(s, ents, wfc, oka, ents.len());
    lemma_hlev_settled(c_local(s, ents, wfc, oka), c_deps(s, ents, wfc, oka), m);
}

// ---------------------------------------------------------------------------
// Code: each entity's verdict and references, then the worklist
// ---------------------------------------------------------------------------

/// `ref_int` at `i`, as an index.
fn ex_ref_int(r: &[u8], i: usize, env: &XEnv) -> (o: Option<usize>)
    requires
        i < r@.len() <= isize::MAX,
        r@.len() <= MAX_POS,
        env_wf(env),
    ensures
        match ref_int(r@, i as int, env_view(env).ents) {
            Some(j) => o == Some(j as usize) && j < env.ents@.len(),
            None => o is None,
        },
{
    if ex_byte_is(r, i + 1, 0x23) {
        return None;
    }
    let n = ex_name_end(r, i + 1);
    if !(n > i + 1 && ex_byte_is(r, n, 0x3B)) || ex_predef(r, i + 1, n).is_some() {
        return None;
    }
    proof {
        lemma_lim_all(env);
    }
    match ex_find_ent(env, env.ents.len(), r, i + 1, n) {
        Some(j) => {
            proof {
                assert(env_view(env).ents[j as int] == ent_view(env.doc@, env.ents@[j as int]));
            }
            if env.ents[j].kind == 0 {
                Some(j)
            } else {
                None
            }
        },
        None => None,
    }
}

pub open spec fn ix_view(v: Seq<usize>) -> Seq<int> {
    v.map_values(|x: usize| x as int)
}

proof fn lemma_ix_push(v: Seq<usize>, x: usize)
    ensures
        ix_view(v.push(x)) == ix_view(v) + seq![x as int],
{
    assert(ix_view(v.push(x)) =~= ix_view(v) + seq![x as int]);
}

/// `att_text(r, 0, env)` with every entity allowed, and when it holds,
/// `att_deps(r, 0, ..)`.
fn ex_att_scan(r: &[u8], env: &XEnv) -> (res: (bool, Vec<usize>))
    requires
        r@.len() <= isize::MAX,
        r@.len() <= MAX_POS,
        env_wf(env),
        env.oka@ == all_ok(env.ents@.len() as int),
        env.okc@ == Seq::<bool>::empty(),
    ensures
        res.0 == att_text(r@, 0, env_view(env)),
        res.0 ==> ix_view(res.1@) == att_deps(r@, 0, env_view(env).ents, env.wfc),
        forall|q: int| 0 <= q < res.1@.len() ==> #[trigger] res.1@[q] < env.ents@.len(),
{
    let ghost es = env_view(env).ents;
    proof {
        lemma_lim_all(env);
        assert(env_view(env) == aenv(es, env.wfc, all_ok(es.len() as int)));
    }
    let n = r.len();
    let mut deps: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(ix_view(deps@) + att_deps(r@, 0, es, env.wfc) =~= att_deps(r@, 0, es, env.wfc));
    }
    while i < n
        invariant
            i <= n,
            n == r@.len() <= isize::MAX,
            r@.len() <= MAX_POS,
            env_wf(env),
            es == env_view(env).ents,
            env_view(env) == aenv(es, env.wfc, all_ok(es.len() as int)),
            lim_view(env, env.ents@.len() as int) == env_view(env),
            att_text(r@, i as int, env_view(env)) == att_text(r@, 0, env_view(env)),
            ix_view(deps@) + att_deps(r@, i as int, es, env.wfc) == att_deps(r@, 0, es, env.wfc),
            forall|q: int| 0 <= q < deps@.len() ==> #[trigger] deps@[q] < env.ents@.len(),
        decreases n - i,
    {
        let c = get(r, i);
        if c == 0x3C {
            return (false, deps);
        }
        if c == 0x26 {
            match ex_att_ref(r, i, Some(env), env.ents.len()) {
                None => {
                    return (false, deps);
                },
                Some(e) => {
                    let ghost before = deps@;
                    match ex_ref_int(r, i, env) {
                        Some(j) => {
                            deps.push(j);
                            proof {
                                lemma_ix_push(before, j);
                                assert(opt_seq(ref_int(r@, i as int, es)) == seq![j as int]);
                            }
                        },
                        None => {
                            proof {
                                assert(opt_seq(ref_int(r@, i as int, es)) == Seq::<int>::empty());
                            }
                        },
                    }
                    proof {
                        let a = opt_seq(ref_int(r@, i as int, es));
                        let b = att_deps(r@, e as int, es, env.wfc);
                        assert(att_deps(r@, i as int, es, env.wfc) == a + b);
                        assert(ix_view(before) + (a + b) =~= (ix_view(before) + a) + b);
                        assert(ix_view(deps@) == ix_view(before) + a) by {
                            if a.len() == 0 {
                                assert(ix_view(before) + a =~= ix_view(before));
                            }
                        }
                    }
                    i = e;
                },
            }
        } else {
            i = i + 1;
        }
    }
    proof {
        assert(ix_view(deps@) + Seq::<int>::empty() =~= ix_view(deps@));
    }
    (true, deps)
}

/// `ent_content(r, 0, [], [], env)` with every entity allowed in content,
/// and when it holds, `cdeps(r, 0, ..)`.
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
fn ex_content_scan(r: &[u8], tape: &mut Tape, env: &XEnv) -> (res: (bool, Vec<usize>))
    requires
        r@.len() <= isize::MAX,
        r@.len() <= MAX_POS,
        env_wf(env),
        env.okc@ == all_ok(env.ents@.len() as int),
    ensures
        res.0 == ent_content(r@, 0, Seq::empty(), Seq::empty(), env_view(env)) is Some,
        res.0 ==> ix_view(res.1@) == cdeps(r@, 0, Seq::empty(), Seq::empty(), env_view(env).ents, env.wfc, env.oka@),
        forall|q: int| 0 <= q < res.1@.len() ==> #[trigger] res.1@[q] < env.ents@.len(),
{
    let ghost es = env_view(env).ents;
    let ghost ev = env_view(env);
    proof {
        assert(ev == cenv(es, env.wfc, env.oka@, all_ok(es.len() as int)));
    }
    let n = r.len();
    let mut j: usize = 0;
    let mut deps: Vec<usize> = Vec::new();
    let mut stack: Vec<(usize, usize, usize)> = Vec::new();
    tape.clear();
    proof {
        assert(stack_view(stack@) =~= Seq::<Open>::empty());
        let whole = cdeps(r@, 0, Seq::empty(), Seq::empty(), es, env.wfc, env.oka@);
        assert(ix_view(deps@) + whole =~= whole);
    }
    loop
        invariant
            j <= n,
            n == r@.len() <= isize::MAX,
            r@.len() <= MAX_POS,
            tape@.len() <= j,
            env_wf(env),
            es == env_view(env).ents,
            ev == env_view(env),
            ev == cenv(es, env.wfc, env.oka@, all_ok(es.len() as int)),
            stack_ok(r@, stack@, tape@),
            ent_content(r@, j as int, stack_view(stack@), tape@, ev) == ent_content(r@, 0, Seq::empty(), Seq::empty(), ev),
            ix_view(deps@) + cdeps(r@, j as int, stack_view(stack@), tape@, es, env.wfc, env.oka@) == cdeps(
                r@,
                0,
                Seq::empty(),
                Seq::empty(),
                es,
                env.wfc,
                env.oka@,
            ),
            forall|q: int| 0 <= q < deps@.len() ==> #[trigger] deps@[q] < env.ents@.len(),
        decreases n - j,
    {
        if j >= n {
            proof {
                assert(ix_view(deps@) + Seq::<int>::empty() =~= ix_view(deps@));
            }
            return (stack.len() == 0, deps);
        }
        let dep = if get(r, j) == 0x26 {
            ex_ref_int(r, j, env)
        } else {
            None
        };
        let ghost st0 = stack_view(stack@);
        let ghost t0 = tape@;
        match ex_item(r, j, &mut stack, tape, env) {
            None => {
                return (false, deps);
            },
            Some(e) => {
                let ghost before = deps@;
                proof {
                    let a = if r@[j as int] == 0x26 {
                        opt_seq(ref_int(r@, j as int, es))
                    } else {
                        Seq::empty()
                    };
                    let b = cdeps(r@, e as int, stack_view(stack@), tape@, es, env.wfc, env.oka@);
                    assert(cdeps(r@, j as int, st0, t0, es, env.wfc, env.oka@) == a + b);
                    assert(ix_view(before) + (a + b) =~= (ix_view(before) + a) + b);
                }
                match dep {
                    Some(q) => {
                        deps.push(q);
                        proof {
                            lemma_ix_push(before, q);
                        }
                    },
                    None => {
                        proof {
                            assert(ix_view(before) + Seq::<int>::empty() =~= ix_view(before));
                        }
                    },
                }
                j = e;
            },
        }
    }
}

/// `oka_seq` and `okc_seq` at the depth of the number of entities.
pub fn ex_ent_flags(doc: &[u8], ents: &[XEnt], wfc: bool, rts: &Vec<Vec<u8>>, idx: &crate::index::NameIndex) -> (r: (
    Vec<bool>,
    Vec<bool>,
))
    requires
        doc@.len() <= isize::MAX,
        doc@.len() <= MAX_POS,
        ents_wf(doc@, ents@),
        rts_ok(doc@, ents@, rts@),
        crate::index::indexes(idx, doc@, ents@),
    ensures
        r.0@ == oka_seq(doc@, ents_view(doc@, ents@), wfc, ents@.len() as nat),
        r.1@ == okc_seq(doc@, ents_view(doc@, ents@), wfc, r.0@, ents@.len() as nat),
{
    let ghost es = ents_view(doc@, ents@);
    let n = ents.len();
    let mut all: Vec<bool> = Vec::new();
    while all.len() < n
        invariant
            all@.len() <= n,
            forall|q: int| 0 <= q < all@.len() ==> all@[q],
        decreases n - all@.len(),
    {
        all.push(true);
    }
    proof {
        assert(all@ =~= all_ok(n as int));
    }
    let none: Vec<bool> = Vec::new();
    // Attribute values.
    let mut local: Vec<bool> = Vec::new();
    let mut deps: Vec<Vec<usize>> = Vec::new();
    {
        let env = XEnv { doc, ents, wfc, oka: all.as_slice(), okc: none.as_slice(), idx };
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                n == ents@.len() == es.len(),
                es == ents_view(doc@, ents@),
                doc@.len() <= isize::MAX,
                doc@.len() <= MAX_POS,
                env_wf(&env),
                env.doc@ == doc@ && env.ents@ == ents@ && env.wfc == wfc,
                env.oka@ == all_ok(n as int) && env.okc@ == Seq::<bool>::empty(),
                env_view(&env) == aenv(es, wfc, all_ok(n as int)),
                rts_ok(doc@, ents@, rts@),
                local@.len() == k && deps@.len() == k,
                forall|q: int| 0 <= q < k ==> #[trigger] local@[q] == a_local(doc@, es, wfc)[q],
                forall|q: int| 0 <= q < k && local@[q] ==> #[trigger] deps_view(deps@)[q] == a_deps(doc@, es, wfc)[q],
                forall|q: int, i: int| 0 <= q < k && 0 <= i < deps@[q]@.len() ==> #[trigger] deps@[q]@[i] < n,
            decreases n - k,
        {
            let e = ents[k];
            proof {
                assert(es[k as int] == ent_view(doc@, e));
                assert(rts@[k as int]@.len() <= doc@.len());
            }
            let (v, dv) = if e.kind == 0 {
                ex_att_scan(rts[k].as_slice(), &env)
            } else {
                (false, Vec::new())
            };
            let ghost dvv = dv@;
            let ghost d0 = deps@;
            local.push(v);
            deps.push(dv);
            proof {
                assert(deps_view(deps@)[k as int] == ix_view(dvv));
                assert forall|q: int| 0 <= q < k implies #[trigger] deps_view(deps@)[q] == deps_view(d0)[q] by {
                    assert(deps@[q] == d0[q]);
                }
                if e.kind == 0 {
                    assert(rts@[k as int]@ == repl(doc@, e.va as int, e.vb as int));
                }
                assert forall|q: int, i: int| 0 <= q < k + 1 && 0 <= i < deps@[q]@.len() implies #[trigger] deps@[q]@[i] < n by {
                    if q == k {
                        assert(deps@[q]@ == dvv);
                    }
                }
            }
            k = k + 1;
        }
    }
    let oka = ex_hfix(&local, &deps);
    proof {
        let (lo, ds) = (a_local(doc@, es, wfc), a_deps(doc@, es, wfc));
        assert(local@ =~= lo);
        lemma_hlev_deps(lo, deps_view(deps@), ds, n as nat);
        lemma_oka_hlev(doc@, es, wfc, n as nat);
    }
    // Content.
    let mut local: Vec<bool> = Vec::new();
    let mut deps: Vec<Vec<usize>> = Vec::new();
    let mut scratch = Tape::new();
    {
        let env = XEnv { doc, ents, wfc, oka: oka.as_slice(), okc: all.as_slice(), idx };
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                n == ents@.len() == es.len(),
                es == ents_view(doc@, ents@),
                doc@.len() <= isize::MAX,
                doc@.len() <= MAX_POS,
                env_wf(&env),
                env.doc@ == doc@ && env.ents@ == ents@ && env.wfc == wfc,
                env.okc@ == all_ok(n as int),
                env_view(&env) == cenv(es, wfc, oka@, all_ok(n as int)),
                rts_ok(doc@, ents@, rts@),
                local@.len() == k && deps@.len() == k,
                forall|q: int| 0 <= q < k ==> #[trigger] local@[q] == c_local(doc@, es, wfc, oka@)[q],
                forall|q: int| 0 <= q < k && local@[q] ==> #[trigger] deps_view(deps@)[q] == c_deps(doc@, es, wfc, oka@)[q],
                forall|q: int, i: int| 0 <= q < k && 0 <= i < deps@[q]@.len() ==> #[trigger] deps@[q]@[i] < n,
            decreases n - k,
        {
            let e = ents[k];
            proof {
                assert(es[k as int] == ent_view(doc@, e));
                assert(rts@[k as int]@.len() <= doc@.len());
            }
            let (v, dv) = if e.kind == 0 {
                ex_content_scan(rts[k].as_slice(), &mut scratch, &env)
            } else {
                (false, Vec::new())
            };
            let ghost dvv = dv@;
            let ghost d0 = deps@;
            local.push(v);
            deps.push(dv);
            proof {
                assert(deps_view(deps@)[k as int] == ix_view(dvv));
                assert forall|q: int| 0 <= q < k implies #[trigger] deps_view(deps@)[q] == deps_view(d0)[q] by {
                    assert(deps@[q] == d0[q]);
                }
                if e.kind == 0 {
                    assert(rts@[k as int]@ == repl(doc@, e.va as int, e.vb as int));
                }
                assert forall|q: int, i: int| 0 <= q < k + 1 && 0 <= i < deps@[q]@.len() implies #[trigger] deps@[q]@[i] < n by {
                    if q == k {
                        assert(deps@[q]@ == dvv);
                    }
                }
            }
            k = k + 1;
        }
    }
    let okc = ex_hfix(&local, &deps);
    proof {
        let (lo, ds) = (c_local(doc@, es, wfc, oka@), c_deps(doc@, es, wfc, oka@));
        assert(local@ =~= lo);
        lemma_hlev_deps(lo, deps_view(deps@), ds, n as nat);
        lemma_okc_hlev(doc@, es, wfc, oka@, n as nat);
    }
    (oka, okc)
}
} // verus!

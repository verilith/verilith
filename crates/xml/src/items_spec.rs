//! What the push parser emits, against the whole parse's tape: every token
//! of the tape is emitted once, in order, as it is, except that a start
//! tag's link to its end tag is left out (the push parser emits the start
//! tag before the end tag has come), and that character data and a CDATA
//! section may come in pieces that cover the token's span end to end.
//!
//! `items(e, t)`: the tokens `e`, at positions in the input, are the tape
//! `t` in that sense. `Stream::feed` ensures `items` of all it emitted and
//! the whole parse's tape when it accepts the document.
//!
//! Proof only: nothing here runs.
use crate::chars::*;
use crate::spec::*;
use crate::stable::*;
use crate::stable_pro::*;
use crate::stream_spec::*;
use vstd::prelude::*;

verus! {

/// The emitted token `a` is the tape's token `b`: the same token, but for
/// a start tag's link to its end tag.
pub open spec fn same_item(a: XTok, b: XTok) -> bool {
    match b {
        XTok::STag { start, end, .. } => a matches XTok::STag { start: s2, end: e2, .. } && s2 == start && e2
            == end,
        _ => a == b,
    }
}

/// A piece of character data (`cd` false) or of a CDATA section (`cd`).
pub open spec fn piece(x: XTok, cd: bool) -> bool {
    if cd {
        x is CData
    } else {
        x is Text
    }
}

/// Where a piece starts.
pub open spec fn pa(x: XTok) -> int {
    match x {
        XTok::Text { start, .. } => start,
        XTok::CData { start, .. } => start,
        _ => 0,
    }
}

/// Where a piece ends.
pub open spec fn pb(x: XTok) -> int {
    match x {
        XTok::Text { end, .. } => end,
        XTok::CData { end, .. } => end,
        _ => 0,
    }
}

/// The pieces `g` cover `a..e`, each starting where the one before ended.
pub open spec fn run(g: Seq<XTok>, cd: bool, a: int, e: int) -> bool
    decreases g.len(),
{
    if g.len() == 0 {
        a == e
    } else {
        piece(g.last(), cd) && pb(g.last()) == e && run(g.drop_last(), cd, a, pa(g.last()))
    }
}

/// The tokens `g` are what is emitted for the tape's token `x`.
pub open spec fn grp(g: Seq<XTok>, x: XTok) -> bool {
    match x {
        XTok::Text { start, end, .. } => g.len() > 0 && run(g, false, start, end),
        XTok::CData { start, end, .. } => g.len() > 0 && run(g, true, start, end),
        _ => g.len() == 1 && same_item(g[0], x),
    }
}

/// The groups, end to end.
pub open spec fn flat(g: Seq<Seq<XTok>>) -> Seq<XTok>
    decreases g.len(),
{
    if g.len() == 0 {
        Seq::empty()
    } else {
        flat(g.drop_last()) + g.last()
    }
}

/// One group for each token of `t`.
pub open spec fn grps(g: Seq<Seq<XTok>>, t: Seq<XTok>) -> bool {
    &&& g.len() == t.len()
    &&& forall|i: int| 0 <= i < t.len() ==> #[trigger] grp(g[i], t[i])
}

/// The emitted tokens `e` are the tape `t`.
pub open spec fn items(e: Seq<XTok>, t: Seq<XTok>) -> bool {
    exists|g: Seq<Seq<XTok>>| #[trigger] grps(g, t) && flat(g) == e
}

/// A group of one token, `u[i]` moved by `d`, for each token of `u`.
pub open spec fn sing(u: Seq<XTok>, d: int) -> Seq<Seq<XTok>> {
    Seq::new(u.len(), |i: int| seq![mv_tok(u[i], d, 0)])
}

// ---------------------------------------------------------------------------
// Groups
// ---------------------------------------------------------------------------

pub proof fn lemma_flat_push(g: Seq<Seq<XTok>>, x: Seq<XTok>)
    ensures
        flat(g.push(x)) == flat(g) + x,
{
    assert(g.push(x).drop_last() =~= g);
}

pub proof fn lemma_grps_empty()
    ensures
        grps(Seq::empty(), Seq::empty()),
        flat(Seq::<Seq<XTok>>::empty()) == Seq::<XTok>::empty(),
{
}

pub proof fn lemma_grps_push(g: Seq<Seq<XTok>>, t: Seq<XTok>, x: Seq<XTok>, y: XTok)
    requires
        grps(g, t),
        grp(x, y),
    ensures
        grps(g.push(x), t.push(y)),
        flat(g.push(x)) == flat(g) + x,
{
    lemma_flat_push(g, x);
    assert forall|i: int| 0 <= i < t.len() + 1 implies #[trigger] grp(g.push(x)[i], t.push(y)[i]) by {
        if i < t.len() {
            assert(g.push(x)[i] == g[i]);
            assert(t.push(y)[i] == t[i]);
        }
    }
}

/// A run with one more piece.
pub proof fn lemma_run_push(g: Seq<XTok>, cd: bool, a: int, x: XTok)
    requires
        run(g, cd, a, pa(x)),
        piece(x, cd),
    ensures
        run(g.push(x), cd, a, pb(x)),
        g.push(x).len() > 0,
{
    assert(g.push(x).drop_last() =~= g);
    assert(g.push(x).last() == x);
}

/// A run over a span that is not empty has a piece.
pub proof fn lemma_run_nonempty(g: Seq<XTok>, cd: bool, a: int, e: int)
    requires
        run(g, cd, a, e),
        a != e,
    ensures
        g.len() > 0,
{
}

/// The run of nothing.
pub proof fn lemma_run_empty(cd: bool, a: int)
    ensures
        run(Seq::empty(), cd, a, a),
{
}

/// A token moved is its own group.
pub proof fn lemma_grp_mv(x: XTok, d: int, k: int)
    ensures
        grp(seq![mv_tok(x, d, 0)], mv_tok(x, d, k)),
{
    reveal_with_fuel(run, 2);
    let g = seq![mv_tok(x, d, 0)];
    assert(g.drop_last() =~= Seq::<XTok>::empty());
    assert(g.last() == mv_tok(x, d, 0));
    assert(g[0] == mv_tok(x, d, 0));
}

/// The tokens `u`, emitted at `d` one by one, are the tape's tokens `u`
/// moved by `d` (and their links by `k`).
pub proof fn lemma_sing(g: Seq<Seq<XTok>>, t: Seq<XTok>, u: Seq<XTok>, d: int, k: int)
    requires
        grps(g, t),
    ensures
        grps(g + sing(u, d), t + mv(u, d, k)),
        flat(g + sing(u, d)) == flat(g) + mv(u, d, 0),
    decreases u.len(),
{
    if u.len() == 0 {
        assert(g + sing(u, d) =~= g);
        assert(t + mv(u, d, k) =~= t);
        assert(flat(g) + mv(u, d, 0) =~= flat(g));
    } else {
        let u1 = u.drop_last();
        let x = u.last();
        lemma_sing(g, t, u1, d, k);
        assert(g + sing(u, d) =~= (g + sing(u1, d)).push(seq![mv_tok(x, d, 0)]));
        assert(t + mv(u, d, k) =~= (t + mv(u1, d, k)).push(mv_tok(x, d, k)));
        assert(mv(u, d, 0) =~= mv(u1, d, 0).push(mv_tok(x, d, 0)));
        lemma_grp_mv(x, d, k);
        lemma_grps_push(g + sing(u1, d), t + mv(u1, d, k), seq![mv_tok(x, d, 0)], mv_tok(x, d, k));
        assert(flat(g) + mv(u, d, 0) =~= flat(g) + mv(u1, d, 0) + seq![mv_tok(x, d, 0)]);
    }
}

/// Linking a start tag to its end tag changes no group.
pub proof fn lemma_grps_close(g: Seq<Seq<XTok>>, t: Seq<XTok>, k: int)
    requires
        grps(g, t),
        0 <= k < t.len(),
    ensures
        grps(g, close_at(t, k)),
{
    let t2 = close_at(t, k);
    assert forall|i: int| 0 <= i < t2.len() implies #[trigger] grp(g[i], t2[i]) by {
        assert(grp(g[i], t[i]));
    }
}

/// `items` from groups.
pub proof fn lemma_items(g: Seq<Seq<XTok>>, t: Seq<XTok>)
    requires
        grps(g, t),
    ensures
        items(flat(g), t),
{
}

// ---------------------------------------------------------------------------
// A tape that grows: the tokens before stay, but for start tags' links
// ---------------------------------------------------------------------------

/// `u` begins with `t`'s tokens, but for start tags' links.
pub open spec fn pre(t: Seq<XTok>, u: Seq<XTok>) -> bool {
    &&& t.len() <= u.len()
    &&& forall|i: int| 0 <= i < t.len() ==> #[trigger] same_item(t[i], u[i])
}

pub proof fn lemma_pre_ext(t: Seq<XTok>, u: Seq<XTok>)
    requires
        extends(t, u),
    ensures
        pre(t, u),
{
    assert forall|i: int| 0 <= i < t.len() implies #[trigger] same_item(t[i], u[i]) by {
        assert(u.subrange(0, t.len() as int)[i] == u[i]);
    }
}

pub proof fn lemma_pre_trans(t: Seq<XTok>, t1: Seq<XTok>, u: Seq<XTok>)
    requires
        pre(t, t1),
        pre(t1, u),
    ensures
        pre(t, u),
{
    assert forall|i: int| 0 <= i < t.len() implies #[trigger] same_item(t[i], u[i]) by {
        assert(same_item(t[i], t1[i]));
        assert(same_item(t1[i], u[i]));
    }
}

pub proof fn lemma_pre_close(t: Seq<XTok>, u: Seq<XTok>, k: int)
    requires
        pre(t, u),
        0 <= k < u.len(),
    ensures
        pre(t, close_at(u, k)),
{
    let u2 = close_at(u, k);
    assert forall|i: int| 0 <= i < t.len() implies #[trigger] same_item(t[i], u2[i]) by {
        assert(same_item(t[i], u[i]));
    }
}

/// The tokens emitted from `t` are, one by one, `u`'s first.
pub proof fn lemma_pre_grps(t: Seq<XTok>, u: Seq<XTok>)
    requires
        pre(t, u),
    ensures
        grps(sing(t, 0), u.subrange(0, t.len() as int)),
        flat(sing(t, 0)) == t,
{
    let g = sing(t, 0);
    let u1 = u.subrange(0, t.len() as int);
    assert forall|i: int| 0 <= i < u1.len() implies #[trigger] grp(g[i], u1[i]) by {
        reveal_with_fuel(run, 2);
        lemma_mv_tok_zero(t[i]);
        assert(g[i] == seq![t[i]]);
        assert(same_item(t[i], u[i]));
        assert(seq![t[i]].drop_last() =~= Seq::<XTok>::empty());
    }
    lemma_sing(Seq::empty(), Seq::empty(), t, 0, 0);
    assert(Seq::<Seq<XTok>>::empty() + sing(t, 0) =~= sing(t, 0));
    lemma_mv_zero(t);
    assert(Seq::<XTok>::empty() + t =~= t);
}

/// The open elements' start tags are in the tape.
pub open spec fn opens_in(st: Seq<Open>, n: int) -> bool {
    forall|q: int| 0 <= q < st.len() ==> 0 <= #[trigger] st[q].2 < n
}

pub proof fn lemma_misc_ge(s: Seq<u8>, i: int, t: Seq<XTok>)
    requires
        misc(s, i, t) is Some,
    ensures
        misc(s, i, t).unwrap().1 >= i,
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    lemma_ws_end_ge(s, i);
    if has_lit(s, j, lit_comment()) {
        let (t1, e) = comment(s, j, t).unwrap();
        lemma_misc_ge(s, e, t1);
    } else if has_lit(s, j, lit_pi()) {
        let (t1, e) = pi(s, j, t).unwrap();
        lemma_misc_ge(s, e, t1);
    }
}

/// One item of content keeps the tape's tokens.
pub proof fn lemma_item_pre(s: Seq<u8>, i: int, st: Seq<Open>, t: Seq<XTok>, env: Env)
    requires
        0 <= i < s.len(),
        st.len() > 0,
        opens_in(st, t.len() as int),
        item(s, i, st, t, env) matches Some((_, _, e)) && e <= s.len() && (is_etag(s, i) || item_reach(s, i, e)
            <= s.len()),
    ensures
        item(s, i, st, t, env) matches Some((st2, t2, _)) && pre(t, t2) && opens_in(st2, t2.len() as int),
{
    let (st2, t2, e) = item(s, i, st, t, env).unwrap();
    if is_etag(s, i) {
        let top = st.last();
        assert(st[st.len() - 1] == top);
        let t1 = t.push(XTok::ETag);
        assert(extends(t, t1)) by {
            assert(t1.subrange(0, t.len() as int) =~= t);
        }
        lemma_pre_ext(t, t1);
        lemma_pre_close(t, t1, top.2);
        assert(t2 == close_at(t1, top.2));
        assert forall|q: int| 0 <= q < st2.len() implies 0 <= #[trigger] st2[q].2 < t2.len() by {
            assert(st2[q] == st[q]);
        }
    } else {
        assert(agree(s, s, 0, s.len() as int, 0));
        lemma_item_mv(s, s, 0, s.len() as int, 0, i, st, t, st, t, env);
        lemma_pre_ext(t, t2);
        if st2 != st {
            // A start tag opened an element: its token is in the tape.
            lemma_lits_stable();
            assert(s[i] == 0x3C);
            assert(!has_lit(s, i, lit_comment()));
            assert(!has_lit(s, i, lit_cdata()));
            assert(!byte_is(s, i + 1, 0x3F));
            lemma_stag_mv(s, s, 0, s.len() as int, 0, i, t, t, env, 0);
            assert(t2.len() > t.len());
        }
        assert forall|q: int| 0 <= q < st2.len() implies 0 <= #[trigger] st2[q].2 < t2.len() by {
            if q < st.len() {
                assert(st2[q] == st[q]);
            }
        }
    }
}

/// Content keeps the tape's tokens.
pub proof fn lemma_content_pre(s: Seq<u8>, i: int, st: Seq<Open>, t: Seq<XTok>, env: Env)
    requires
        opens_in(st, t.len() as int),
        content(s, i, st, t, env) is Some,
    ensures
        pre(t, content(s, i, st, t, env).unwrap().0),
    decreases s.len() - i,
{
    if st.len() == 0 {
        assert(pre(t, t));
    } else {
        let (st2, t2, e) = item(s, i, st, t, env).unwrap();
        if !is_etag(s, i) && s[i] != 0x3C && s[i] != 0x26 {
            // Character data keeps the elements open: the content goes on
            // after it, so it does not end the input.
            assert(st2 == st);
            assert(e < s.len());
        }
        lemma_item_pre(s, i, st, t, env);
        lemma_content_pre(s, e, st2, t2, env);
        lemma_pre_trans(t, t2, content(s, e, st2, t2, env).unwrap().0);
    }
}

/// An element keeps the tape's tokens.
pub proof fn lemma_element_pre(s: Seq<u8>, i: int, t: Seq<XTok>, env: Env)
    requires
        element(s, i, t, env) matches Some((_, e)) && e <= s.len(),
    ensures
        pre(t, element(s, i, t, env).unwrap().0),
{
    let (t1, e1, empty) = stag(s, i, t, env).unwrap();
    let u = element(s, i, t, env).unwrap().0;
    if !empty {
        assert(0 <= e1 < s.len());
    }
    assert(agree(s, s, 0, s.len() as int, 0));
    lemma_stag_mv(s, s, 0, s.len() as int, 0, i, t, t, env, 0);
    lemma_pre_ext(t, t1);
    if empty {
        let t2 = t1.push(XTok::ETag);
        assert(extends(t1, t2)) by {
            assert(t2.subrange(0, t1.len() as int) =~= t1);
        }
        lemma_pre_ext(t1, t2);
        lemma_pre_trans(t, t1, t2);
        lemma_pre_close(t, t2, t.len() as int);
    } else {
        let st = seq![(i + 1, name_end(s, i + 1), t.len() as int)];
        assert(st[0].2 == t.len());
        lemma_content_pre(s, e1, st, t1, env);
        lemma_pre_trans(t, t1, u);
    }
}

/// From the root element on: the tape keeps its tokens.
pub proof fn lemma_after_m2_pre(s: Seq<u8>, p: int, t: Seq<XTok>, env: Env)
    requires
        after_m2(s, p, t, env) is Some,
    ensures
        pre(t, after_m2(s, p, t, env).unwrap()),
{
    let (t3, p4) = misc(s, p, t).unwrap();
    lemma_misc_toks(s, p, t);
    lemma_pre_ext(t, t3);
    let (t2, e) = element(s, p4, t3, env).unwrap();
    let (t4, f) = misc(s, e, t2).unwrap();
    lemma_misc_ge(s, e, t2);
    lemma_element_pre(s, p4, t3, env);
    lemma_misc_toks(s, e, t2);
    lemma_pre_ext(t2, t4);
    lemma_pre_trans(t, t3, t2);
    lemma_pre_trans(t, t2, t4);
}

/// After the root element is reached: where `after_m2` starts is before
/// the end.
pub proof fn lemma_after_m2_in(s: Seq<u8>, p: int, t: Seq<XTok>, env: Env)
    requires
        after_m2(s, p, t, env) is Some,
    ensures
        p < s.len(),
{
    let (t3, p4) = misc(s, p, t).unwrap();
    lemma_misc_ge(s, p, t);
    assert(byte_is(s, p4, 0x3C));
}

/// From after the XML declaration on: the tape keeps its tokens.
pub proof fn lemma_after_m1_pre(s: Seq<u8>, p: int, t: Seq<XTok>, sd: int)
    requires
        0 <= p,
        after_m1(s, p, t, sd) is Some,
    ensures
        pre(t, after_m1(s, p, t, sd).unwrap()),
{
    let (t1, p2) = misc(s, p, t).unwrap();
    lemma_misc_toks(s, p, t);
    lemma_misc_ge(s, p, t);
    lemma_pre_ext(t, t1);
    let (t2, p3, env) = doctype_opt(s, p2, t1, sd).unwrap();
    lemma_after_m2_in(s, p3, t2, env);
    if has_lit(s, p2, lit_doctype()) {
        assert(agree(s, s, 0, s.len() as int, 0));
        lemma_doctype_eq(s, s, s.len() as int, p2, t1, sd == 1);
        lemma_pre_ext(t1, t2);
    } else {
        assert(pre(t1, t2));
    }
    lemma_after_m2_pre(s, p3, t2, env);
    lemma_pre_trans(t, t1, t2);
    lemma_pre_trans(t, t2, after_m1(s, p, t, sd).unwrap());
}

} // verus!

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


// ---------------------------------------------------------------------------
// The flags on pieces
// ---------------------------------------------------------------------------

/// A token's flag byte has `P_CR` (bit 0).
pub open spec fn crb(f: u8) -> bool {
    f % 2 == 1
}

/// ... `P_FIRST` (bit 1).
pub open spec fn firstb(f: u8) -> bool {
    (f / 2) % 2 == 1
}

/// ... `P_LAST` (bit 2).
pub open spec fn lastb(f: u8) -> bool {
    (f / 4) % 2 == 1
}

/// The flags `f` of the piece `x` of character data (`cd` false) or of a
/// CDATA section (`cd`) in the input `s`: `P_CR` exactly if the piece has
/// a carriage return; `P_FIRST` exactly if it is a section's first piece,
/// `P_LAST` exactly if it is its last; no other bit.
pub open spec fn piece_fl(s: Seq<u8>, x: XTok, f: u8, cd: bool, first: bool, last: bool) -> bool {
    &&& 0 <= pa(x) <= pb(x) <= s.len()
    &&& f < 8
    &&& crb(f) == has_cr(s, pa(x), pb(x))
    &&& firstb(f) == (cd && first)
    &&& lastb(f) == (cd && last)
}

/// Piece `j` of the group `g` has the right flags.
pub open spec fn gat(s: Seq<u8>, g: Seq<XTok>, fl: Seq<u8>, j: int) -> bool {
    piece_fl(s, g[j], fl[j], g[0] is CData, j == 0, j == g.len() - 1)
}

/// The flags `fl` of the group `g`: one for each token, and for the pieces
/// of character data or of a CDATA section, the right ones.
pub open spec fn grp_fl(s: Seq<u8>, g: Seq<XTok>, fl: Seq<u8>) -> bool {
    &&& fl.len() == g.len()
    &&& g.len() > 0 && (g[0] is Text || g[0] is CData) ==> forall|j: int|
        0 <= j < g.len() ==> #[trigger] gat(s, g, fl, j)
}

/// Piece `j` of the pieces `o` read so far has the right flags.
pub open spec fn oat(s: Seq<u8>, o: Seq<XTok>, fl: Seq<u8>, cd: bool, j: int) -> bool {
    piece_fl(s, o[j], fl[j], cd, j == 0, false)
}

/// The pieces `o` of the text or CDATA section (`cd`) still being read,
/// with their flags `fl`: none is the last yet.
pub open spec fn open_fl(s: Seq<u8>, o: Seq<XTok>, fl: Seq<u8>, cd: bool) -> bool {
    &&& fl.len() == o.len()
    &&& forall|j: int| 0 <= j < o.len() ==> #[trigger] oat(s, o, fl, cd, j)
}

/// Groups of flags, end to end.
pub open spec fn flat8(g: Seq<Seq<u8>>) -> Seq<u8>
    decreases g.len(),
{
    if g.len() == 0 {
        Seq::empty()
    } else {
        flat8(g.drop_last()) + g.last()
    }
}

/// The flags `gf` of the groups `g`: one for each token, and the right
/// ones from group `k0` on.
pub open spec fn fls(s: Seq<u8>, g: Seq<Seq<XTok>>, gf: Seq<Seq<u8>>, k0: int) -> bool {
    &&& gf.len() == g.len()
    &&& 0 <= k0 <= g.len()
    &&& forall|i: int| 0 <= i < g.len() ==> (#[trigger] gf[i]).len() == g[i].len()
    &&& forall|i: int| k0 <= i < g.len() ==> #[trigger] grp_fl(s, g[i], gf[i])
}

/// **The flags of what the push parser emits.** `fl` are the flag bytes of
/// the emitted tokens `e`, one each; `e` is the tape `t` in pieces
/// (`items`), and from the tape's token `k0` on, every piece of character
/// data or of a CDATA section carries the right flags (`grp_fl`).
pub open spec fn items_fl(s: Seq<u8>, e: Seq<XTok>, fl: Seq<u8>, t: Seq<XTok>, k0: int) -> bool {
    exists|g: Seq<Seq<XTok>>, gf: Seq<Seq<u8>>|
        #[trigger] grps(g, t) && flat(g) == e && #[trigger] fls(s, g, gf, k0) && flat8(gf) == fl
}

pub proof fn lemma_flat8_push(g: Seq<Seq<u8>>, x: Seq<u8>)
    ensures
        flat8(g.push(x)) == flat8(g) + x,
{
    assert(g.push(x).drop_last() =~= g);
}

pub proof fn lemma_fls_push(s: Seq<u8>, g: Seq<Seq<XTok>>, gf: Seq<Seq<u8>>, k0: int, x: Seq<XTok>, fx: Seq<u8>)
    requires
        fls(s, g, gf, k0),
        grp_fl(s, x, fx),
    ensures
        fls(s, g.push(x), gf.push(fx), k0),
        flat8(gf.push(fx)) == flat8(gf) + fx,
{
    lemma_flat8_push(gf, fx);
    let g2 = g.push(x);
    let f2 = gf.push(fx);
    assert forall|i: int| 0 <= i < g2.len() implies (#[trigger] f2[i]).len() == g2[i].len() by {
        if i < g.len() {
            assert(f2[i] == gf[i] && g2[i] == g[i]);
        }
    }
    assert forall|i: int| k0 <= i < g2.len() implies #[trigger] grp_fl(s, g2[i], f2[i]) by {
        if i < g.len() {
            assert(f2[i] == gf[i] && g2[i] == g[i]);
        }
    }
}

/// One flag group of one flag for each flag of `f`.
pub open spec fn sing8(f: Seq<u8>) -> Seq<Seq<u8>> {
    Seq::new(f.len(), |i: int| seq![f[i]])
}

/// Groups of one token that is not a piece take any flags.
pub proof fn lemma_fls_sing(s: Seq<u8>, g: Seq<Seq<XTok>>, gf: Seq<Seq<u8>>, k0: int, u: Seq<XTok>, d: int, f: Seq<u8>)
    requires
        fls(s, g, gf, k0),
        f.len() == u.len(),
        forall|i: int| 0 <= i < u.len() ==> !(#[trigger] u[i] is Text) && !(u[i] is CData),
    ensures
        fls(s, g + sing(u, d), gf + sing8(f), k0),
        flat8(gf + sing8(f)) == flat8(gf) + f,
    decreases u.len(),
{
    if u.len() == 0 {
        assert(g + sing(u, d) =~= g);
        assert(gf + sing8(f) =~= gf);
        assert(flat8(gf) + f =~= flat8(gf));
    } else {
        let u1 = u.drop_last();
        let f1 = f.drop_last();
        assert forall|i: int| 0 <= i < u1.len() implies !(#[trigger] u1[i] is Text) && !(u1[i] is CData) by {
            assert(u1[i] == u[i]);
        }
        lemma_fls_sing(s, g, gf, k0, u1, d, f1);
        assert(g + sing(u, d) =~= (g + sing(u1, d)).push(seq![mv_tok(u.last(), d, 0)]));
        assert(gf + sing8(f) =~= (gf + sing8(f1)).push(seq![f.last()]));
        let x = seq![mv_tok(u.last(), d, 0)];
        assert(x[0] == mv_tok(u.last(), d, 0));
        assert(!(u[u.len() - 1] is Text) && !(u[u.len() - 1] is CData));
        assert(grp_fl(s, x, seq![f.last()]));
        lemma_fls_push(s, g + sing(u1, d), gf + sing8(f1), k0, x, seq![f.last()]);
        assert(flat8(gf) + f =~= flat8(gf) + f1 + seq![f.last()]);
    }
}

/// One flag group for each flag of `f`.
pub proof fn lemma_flat8_sing(f: Seq<u8>)
    ensures
        flat8(sing8(f)) == f,
    decreases f.len(),
{
    if f.len() > 0 {
        let f1 = f.drop_last();
        lemma_flat8_sing(f1);
        assert(sing8(f).drop_last() =~= sing8(f1));
        assert(f =~= f1 + seq![f.last()]);
    } else {
        assert(f =~= Seq::<u8>::empty());
    }
}

/// The flags stay right as more input comes.
pub proof fn lemma_piece_fl_ext(s: Seq<u8>, s2: Seq<u8>, x: XTok, f: u8, cd: bool, first: bool, last: bool)
    requires
        piece_fl(s, x, f, cd, first, last),
        s.len() <= s2.len(),
        s2.subrange(0, s.len() as int) == s,
    ensures
        piece_fl(s2, x, f, cd, first, last),
{
    if has_cr(s, pa(x), pb(x)) {
        let k = choose|k: int| pa(x) <= k < pb(x) && s[k] == 0x0D;
        assert(s2.subrange(0, s.len() as int)[k] == s2[k]);
    }
    if has_cr(s2, pa(x), pb(x)) {
        let k = choose|k: int| pa(x) <= k < pb(x) && s2[k] == 0x0D;
        assert(s2.subrange(0, s.len() as int)[k] == s2[k]);
    }
}

pub proof fn lemma_fls_ext(s: Seq<u8>, s2: Seq<u8>, g: Seq<Seq<XTok>>, gf: Seq<Seq<u8>>, k0: int)
    requires
        fls(s, g, gf, k0),
        s.len() <= s2.len(),
        s2.subrange(0, s.len() as int) == s,
    ensures
        fls(s2, g, gf, k0),
{
    assert forall|i: int| k0 <= i < g.len() implies #[trigger] grp_fl(s2, g[i], gf[i]) by {
        assert(grp_fl(s, g[i], gf[i]));
        let x = g[i];
        if x.len() > 0 && (x[0] is Text || x[0] is CData) {
            assert forall|j: int| 0 <= j < x.len() implies #[trigger] gat(s2, x, gf[i], j) by {
                assert(gat(s, x, gf[i], j));
                lemma_piece_fl_ext(s, s2, x[j], gf[i][j], x[0] is CData, j == 0, j == x.len() - 1);
            }
        }
    }
}

pub proof fn lemma_open_fl_ext(s: Seq<u8>, s2: Seq<u8>, o: Seq<XTok>, fl: Seq<u8>, cd: bool)
    requires
        open_fl(s, o, fl, cd),
        s.len() <= s2.len(),
        s2.subrange(0, s.len() as int) == s,
    ensures
        open_fl(s2, o, fl, cd),
{
    assert forall|j: int| 0 <= j < o.len() implies #[trigger] oat(s2, o, fl, cd, j) by {
        assert(oat(s, o, fl, cd, j));
        lemma_piece_fl_ext(s, s2, o[j], fl[j], cd, j == 0, false);
    }
}

/// The pieces read so far, with one more, are the section's group.
pub proof fn lemma_close_fl(s: Seq<u8>, o: Seq<XTok>, fl: Seq<u8>, cd: bool, x: XTok, f: u8)
    requires
        open_fl(s, o, fl, cd),
        piece_fl(s, x, f, cd, o.len() == 0, true),
        piece(x, cd),
        o.len() > 0 ==> piece(o[0], cd),
    ensures
        grp_fl(s, o.push(x), fl.push(f)),
{
    let g = o.push(x);
    let gl = fl.push(f);
    assert(g[0] is CData == cd) by {
        if o.len() > 0 {
            assert(g[0] == o[0]);
        }
    }
    assert forall|j: int| 0 <= j < g.len() implies #[trigger] gat(s, g, gl, j) by {
        if j < o.len() {
            assert(g[j] == o[j] && gl[j] == fl[j]);
            assert(oat(s, o, fl, cd, j));
        }
    }
}


// ---------------------------------------------------------------------------
// Items that are not text: no piece among their tokens
// ---------------------------------------------------------------------------

/// No token of `t` from `k` on is character data or a CDATA section.
pub open spec fn np_from(t: Seq<XTok>, k: int) -> bool {
    forall|j: int| k <= j < t.len() ==> !(#[trigger] t[j] is Text) && !(t[j] is CData)
}

pub proof fn lemma_np_push(t: Seq<XTok>, k: int, x: XTok)
    requires
        np_from(t, k),
        !(x is Text) && !(x is CData),
    ensures
        np_from(t.push(x), k),
{
    assert forall|j: int| k <= j < t.push(x).len() implies !(#[trigger] t.push(x)[j] is Text) && !(t.push(x)[j] is CData) by {
        if j < t.len() {
            assert(t.push(x)[j] == t[j]);
        }
    }
}

pub proof fn lemma_np_close(t: Seq<XTok>, k: int, c: int)
    requires
        np_from(t, k),
        0 <= c < t.len(),
    ensures
        np_from(close_at(t, c), k),
        close_at(t, c).len() == t.len(),
{
    let t2 = close_at(t, c);
    assert forall|j: int| k <= j < t2.len() implies !(#[trigger] t2[j] is Text) && !(t2[j] is CData) by {
        if j != c {
            assert(t2[j] == t[j]);
        }
    }
}

pub proof fn lemma_np_attrs(s: Seq<u8>, i: int, tape: Seq<XTok>, env: Env, k: int)
    requires
        np_from(tape, k),
    ensures
        attrs(s, i, tape, env) matches Some((t2, _, _)) ==> np_from(t2, k) && t2.len() >= tape.len(),
    decreases s.len() - i,
{
    let j = ws_end(s, i);
    if byte_is(s, j, 0x3E) {
    } else if has_lit(s, j, lit_empty_end()) {
    } else if j == i {
    } else {
        let n = name_end(s, j);
        if n != j {
            match eq_end(s, n) {
                None => {},
                Some(v) => if 0 <= v < s.len() && quote(s[v]) {
                    match att_chars(s, v + 1, s[v], Some(env)) {
                        None => {},
                        Some(q) => if i < q + 1 <= s.len() {
                            let t1 = tape.push(XTok::Attr { start: j, end: n });
                            let t2 = t1.push(XTok::AttVal { start: v + 1, end: q, plain: att_plain(s, v + 1, q) });
                            lemma_np_push(tape, k, XTok::Attr { start: j, end: n });
                            lemma_np_push(t1, k, XTok::AttVal { start: v + 1, end: q, plain: att_plain(s, v + 1, q) });
                            lemma_np_attrs(s, q + 1, t2, env, k);
                        },
                    }
                },
            }
        }
    }
}

/// An item that starts with `<` (but not a CDATA section's `<![CDATA[`)
/// or `&`, outside any element, adds no character data and no CDATA
/// section to the tape.
pub proof fn lemma_np_item(s: Seq<u8>, i: int, tape: Seq<XTok>, env: Env, k: int)
    requires
        0 <= i < s.len(),
        (s[i] == 0x3C && !has_lit(s, i, lit_cdata())) || s[i] == 0x26,
        np_from(tape, k),
    ensures
        item(s, i, Seq::empty(), tape, env) matches Some((_, t2, _)) ==> np_from(t2, k),
{
    let stack = Seq::<Open>::empty();
    if s[i] == 0x3C {
        if byte_is(s, i + 1, 0x2F) {
        } else if has_lit(s, i, lit_comment()) {
            if let Some(e) = comment_end(s, i + 4) {
                lemma_np_push(tape, k, XTok::Comment { start: i + 4, end: e - 3 });
            }
        } else if byte_is(s, i + 1, 0x3F) {
            if let Some((t, e)) = pi(s, i, tape) {
                let n = name_end(s, i + 2);
                lemma_np_push(tape, k, XTok::PI { start: i + 2, end: n });
                let t1 = tape.push(XTok::PI { start: i + 2, end: n });
                assert(t.len() == t1.len() + 1 && t.drop_last() == t1 && !(t.last() is Text) && !(t.last() is CData));
                lemma_np_push(t1, k, t.last());
                assert(t =~= t1.push(t.last()));
            }
        } else {
            let n = name_end(s, i + 1);
            if n != i + 1 {
                let t = tape.push(XTok::STag { start: i + 1, end: n, close: 0 });
                lemma_np_push(tape, k, XTok::STag { start: i + 1, end: n, close: 0 });
                lemma_np_attrs(s, n, t, env, k);
                if let Some((t2, e, empty)) = stag(s, i, tape, env) {
                    if empty {
                        lemma_np_push(t2, k, XTok::ETag);
                        lemma_np_close(t2.push(XTok::ETag), k, tape.len() as int);
                    }
                }
            }
        }
    } else {
        if let Some((x, e)) = content_ref(s, i, env) {
            lemma_np_push(tape, k, x);
        }
    }
}


/// Every piece of a run is a piece.
pub proof fn lemma_run_pieces(g: Seq<XTok>, cd: bool, a: int, e: int)
    requires
        run(g, cd, a, e),
    ensures
        forall|j: int| 0 <= j < g.len() ==> #[trigger] piece(g[j], cd),
    decreases g.len(),
{
    if g.len() > 0 {
        lemma_run_pieces(g.drop_last(), cd, a, pa(g.last()));
        assert forall|j: int| 0 <= j < g.len() implies #[trigger] piece(g[j], cd) by {
            if j < g.len() - 1 {
                assert(g[j] == g.drop_last()[j]);
            }
        }
    }
}

/// Character data's pieces, read to its end, are its group.
pub proof fn lemma_text_close_fl(s: Seq<u8>, o: Seq<XTok>, fl: Seq<u8>)
    requires
        open_fl(s, o, fl, false),
        o.len() > 0,
        piece(o[0], false),
    ensures
        grp_fl(s, o, fl),
{
    assert forall|j: int| 0 <= j < o.len() implies #[trigger] gat(s, o, fl, j) by {
        assert(oat(s, o, fl, false, j));
    }
}


/// What does not start `<![` is not a CDATA section.
pub proof fn lemma_not_cdata(s: Seq<u8>, i: int)
    requires
        0 <= i,
        i + 9 <= s.len() ==> s[i + 1] != 0x21 || s[i + 2] != 0x5B,
    ensures
        !has_lit(s, i, lit_cdata()),
{
    if has_lit(s, i, lit_cdata()) {
        assert(s.subrange(i, i + 9)[1] == s[i + 1]);
        assert(s.subrange(i, i + 9)[2] == s[i + 2]);
    }
}

} // verus!

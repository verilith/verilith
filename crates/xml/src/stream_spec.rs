//! What the incremental parser (`stream`) keeps true between chunks: for
//! every input `s` that begins with the bytes seen so far, `document(s)`
//! is what the rest of the document decides from where the parser stands.
//! These are the spec's functions from each such point, how one step
//! moves from one to the next, and how a step read in the window the
//! parser keeps carries over to `s`.
//!
//! Proof only: nothing here runs.
use crate::chars::*;
use crate::spec::*;
use crate::stable::*;
use crate::stable_pro::*;
use vstd::prelude::*;

verus! {

/// `s` begins with `seen`.
pub open spec fn ext(seen: Seq<u8>, s: Seq<u8>) -> bool {
    seen.len() <= s.len() && s.subrange(0, seen.len() as int) == seen
}

pub proof fn lemma_ext_trans(a: Seq<u8>, b: Seq<u8>, s: Seq<u8>)
    requires
        ext(a, b),
        ext(b, s),
    ensures
        ext(a, s),
{
    assert(s.subrange(0, a.len() as int) =~= b.subrange(0, a.len() as int));
}

/// The window `b` is `seen` from `base`: on any `s` that begins with
/// `seen`, `b` agrees with `s` moved by `base`.
pub proof fn lemma_window(b: Seq<u8>, seen: Seq<u8>, base: int, s: Seq<u8>)
    requires
        0 <= base <= seen.len(),
        b == seen.subrange(base, seen.len() as int),
        ext(seen, s),
    ensures
        agree(b, s, 0, b.len() as int, -base),
{
    assert forall|k: int| 0 <= k < b.len() implies #[trigger] b[k] == s[k - (-base)] by {
        assert(b[k] == seen[base + k]);
        assert(s.subrange(0, seen.len() as int)[base + k] == s[base + k]);
    }
}

/// At the end: the window is all that remains of `seen`, and `s` is
/// `seen`.
pub proof fn lemma_window_exact(b: Seq<u8>, seen: Seq<u8>, base: int)
    requires
        0 <= base <= seen.len(),
        b == seen.subrange(base, seen.len() as int),
    ensures
        agree(b, seen, 0, b.len() as int, -base),
        seen.len() == b.len() + base,
        agree(seen, b, base, seen.len() as int, base),
{
    assert(seen.subrange(0, seen.len() as int) =~= seen);
    lemma_window(b, seen, base, seen);
    lemma_agree_flip(b, seen, 0, b.len() as int, -base);
}

// ---------------------------------------------------------------------------
// The document from each point
// ---------------------------------------------------------------------------

/// After the root element: `Misc*` to the end.
pub open spec fn fin(s: Seq<u8>, e: int, t: Seq<XTok>) -> Option<Seq<XTok>> {
    match misc(s, e, t) {
        None => None,
        Some((t3, f)) => if f == s.len() {
            Some(t3)
        } else {
            None
        },
    }
}

/// In the root element's content.
pub open spec fn after_content(s: Seq<u8>, j: int, st: Seq<Open>, t: Seq<XTok>, env: Env) -> Option<Seq<XTok>> {
    match content(s, j, st, t, env) {
        None => None,
        Some((t2, e)) => fin(s, e, t2),
    }
}

/// At the root element.
pub open spec fn after_root(s: Seq<u8>, p: int, t: Seq<XTok>, env: Env) -> Option<Seq<XTok>> {
    match element(s, p, t, env) {
        None => None,
        Some((t2, e)) => fin(s, e, t2),
    }
}

/// In the `Misc*` after the document type declaration (or where it would
/// be).
pub open spec fn after_m2(s: Seq<u8>, p: int, t: Seq<XTok>, env: Env) -> Option<Seq<XTok>> {
    match misc(s, p, t) {
        None => None,
        Some((t3, p4)) => if defaults_ok(s, t3, env) {
            after_root(s, p4, t3, env)
        } else {
            None
        },
    }
}

/// In the `Misc*` after the XML declaration.
pub open spec fn after_m1(s: Seq<u8>, p: int, t: Seq<XTok>, sd: int) -> Option<Seq<XTok>> {
    match misc(s, p, t) {
        None => None,
        Some((t1, p2)) => match doctype_opt(s, p2, t1, sd) {
            None => None,
            Some((t2, p3, env)) => after_m2(s, p3, t2, env),
        },
    }
}

pub open spec fn after_head(s: Seq<u8>, enc: Enc) -> Option<Seq<XTok>> {
    match decl_head(s, enc) {
        None => None,
        Some((t0, p1, sd)) => after_m1(s, p1, t0, sd),
    }
}

pub proof fn lemma_document(s: Seq<u8>, enc: Enc)
    ensures
        document(s, enc) == (if doc_chars(s) {
            after_head(s, enc)
        } else {
            None
        }),
{
}

pub proof fn lemma_parse_utf8(s: Seq<u8>)
    requires
        input_enc(s) == Enc::Utf8,
    ensures
        parse(s) == (match document(s, Enc::Utf8) {
            Some(t) => Some((s, t)),
            None => None,
        }),
{
}

// ---------------------------------------------------------------------------
// One step of Misc, and where it stops
// ---------------------------------------------------------------------------

pub proof fn lemma_ws_end_step(s: Seq<u8>, p: int)
    requires
        0 <= p < s.len(),
        is_ws(s[p]),
    ensures
        ws_end(s, p) == ws_end(s, p + 1),
{
}

pub proof fn lemma_misc_ws(s: Seq<u8>, p: int, t: Seq<XTok>)
    requires
        0 <= p < s.len(),
        is_ws(s[p]),
    ensures
        misc(s, p, t) == misc(s, p + 1, t),
{
    lemma_ws_end_step(s, p);
    let j = ws_end(s, p);
    lemma_ws_end_ge(s, p + 1);
    lemma_lits_stable();
    if has_lit(s, j, lit_comment()) {
        if let Some((t1, e)) = comment(s, j, t) {
            lemma_comment_end_ge(s, j + 4);
        }
    } else if has_lit(s, j, lit_pi()) {
        if let Some((t1, e)) = pi(s, j, t) {
            lemma_pi_min(s, j, t);
        }
    }
}

/// A comment or a processing instruction at `p`, read as an item.
pub proof fn lemma_misc_item(s: Seq<u8>, p: int, st: Seq<Open>, t: Seq<XTok>, env: Env)
    requires
        0 <= p < s.len(),
        has_lit(s, p, lit_comment()) || has_lit(s, p, lit_pi()),
        item(s, p, st, t, env) matches Some((_, _, e)) && p < e <= s.len(),
    ensures
        item(s, p, st, t, env) matches Some((st2, t2, e)) && st2 == st && misc(s, p, t) == misc(s, e, t2),
{
    lemma_lits_stable();
    assert(s.subrange(p, p + 2)[0] == s[p] && s.subrange(p, p + 2)[1] == s[p + 1]);
    assert(s[p] == 0x3C);
    assert(!is_ws(s[p]));
    assert(ws_end(s, p) == p);
    if has_lit(s, p, lit_comment()) {
        assert(s.subrange(p, p + 4)[1] == s[p + 1]);
        assert(!byte_is(s, p + 1, 0x2F));
    } else {
        assert(!byte_is(s, p + 1, 0x2F));
        assert(!has_lit(s, p, lit_comment()));
        assert(!has_lit(s, p, lit_cdata())) by {
            if has_lit(s, p, lit_cdata()) {
                assert(s.subrange(p, p + 9)[1] == s[p + 1]);
            }
        }
        assert(byte_is(s, p + 1, 0x3F));
    }
}

/// Where `Misc` stops: at the end, or at a byte that starts none of its
/// parts.
pub proof fn lemma_misc_stop(s: Seq<u8>, p: int, t: Seq<XTok>)
    requires
        0 <= p <= s.len(),
        p == s.len() || (!is_ws(s[p]) && !has_lit(s, p, lit_comment()) && !has_lit(s, p, lit_pi())),
    ensures
        misc(s, p, t) == Some((t, p)),
{
    if p < s.len() {
        assert(ws_end(s, p) == p);
    } else {
        assert(ws_end(s, p) == p);
        assert(!has_lit(s, p, lit_comment()));
        assert(!has_lit(s, p, lit_pi()));
    }
}

/// Before the document type declaration: `Misc` stopped at `p`.
pub proof fn lemma_m1_stop(s: Seq<u8>, p: int, t: Seq<XTok>, sd: int)
    requires
        misc(s, p, t) == Some((t, p)),
    ensures
        after_m1(s, p, t, sd) == (match doctype_opt(s, p, t, sd) {
            None => None,
            Some((t2, p3, env)) => after_m2(s, p3, t2, env),
        }),
{
}

/// At the root element: `Misc` stopped at `p`.
pub proof fn lemma_m2_stop(s: Seq<u8>, p: int, t: Seq<XTok>, env: Env)
    requires
        misc(s, p, t) == Some((t, p)),
    ensures
        after_m2(s, p, t, env) == (if defaults_ok(s, t, env) {
            after_root(s, p, t, env)
        } else {
            None
        }),
{
}

/// The root element's start tag, read as an item.
pub proof fn lemma_root_item(s: Seq<u8>, p: int, t: Seq<XTok>, env: Env)
    requires
        0 <= p,
        p + 1 < s.len(),
        s[p] == 0x3C,
        s[p + 1] != 0x2F && s[p + 1] != 0x21 && s[p + 1] != 0x3F,
    ensures
        match item(s, p, Seq::empty(), t, env) {
            None => after_root(s, p, t, env) is None,
            Some((st2, t2, e)) => (p < e <= s.len() ==> after_root(s, p, t, env) == after_content(
                s,
                e,
                st2,
                t2,
                env,
            )) && (st2.len() == 0 || st2.len() == 1),
        },
{
    lemma_lits_stable();
    assert(!has_lit(s, p, lit_comment())) by {
        if has_lit(s, p, lit_comment()) {
            assert(s.subrange(p, p + 4)[1] == s[p + 1]);
        }
    }
    assert(!has_lit(s, p, lit_cdata())) by {
        if has_lit(s, p, lit_cdata()) {
            assert(s.subrange(p, p + 9)[1] == s[p + 1]);
        }
    }
    assert(byte_is(s, p, 0x3C));
    match stag(s, p, t, env) {
        None => {},
        Some((t1, e, empty)) => {
            if !empty {
                let st1 = Seq::<Open>::empty().push((p + 1, name_end(s, p + 1), t.len() as int));
                assert(st1 =~= seq![(p + 1, name_end(s, p + 1), t.len() as int)]);
            }
        },
    }
}

/// One item in the content.
pub proof fn lemma_content_step(s: Seq<u8>, j: int, st: Seq<Open>, t: Seq<XTok>, env: Env)
    requires
        st.len() > 0,
        0 <= j < s.len(),
        item(s, j, st, t, env) matches Some((_, _, e)) && j < e <= s.len(),
    ensures
        item(s, j, st, t, env) matches Some((st2, t2, e)) && after_content(s, j, st, t, env) == after_content(
            s,
            e,
            st2,
            t2,
            env,
        ),
{
}

/// An item that fails, or that ends past the end: the content fails.
pub proof fn lemma_content_fail(s: Seq<u8>, j: int, st: Seq<Open>, t: Seq<XTok>, env: Env)
    requires
        st.len() > 0,
        0 <= j <= s.len(),
        j == s.len() || item(s, j, st, t, env) is None,
    ensures
        after_content(s, j, st, t, env) is None,
{
}

/// The root element has ended.
pub proof fn lemma_content_done(s: Seq<u8>, j: int, t: Seq<XTok>, env: Env)
    ensures
        after_content(s, j, Seq::empty(), t, env) == fin(s, j, t),
{
}

/// Text that runs to the end, with an element open: the content fails.
pub proof fn lemma_text_to_end(s: Seq<u8>, j: int, st: Seq<Open>, t: Seq<XTok>, env: Env)
    requires
        st.len() > 0,
        0 <= j < s.len(),
        s[j] != 0x3C && s[j] != 0x26,
        text_end(s, j) == Some(s.len() as int),
    ensures
        after_content(s, j, st, t, env) is None,
{
    let e = s.len() as int;
    let t2 = t.push(XTok::Text { start: j, end: e, cr: has_cr(s, j, e) });
    assert(item(s, j, st, t, env) == Some((st, t2, e)));
    lemma_content_step(s, j, st, t, env);
}

// ---------------------------------------------------------------------------
// End tags, checked against the names the parser keeps
// ---------------------------------------------------------------------------

/// An end tag read in the window `x`, whose name is the name of the
/// innermost open element in `y`.
pub proof fn lemma_etag_mv(
    x: Seq<u8>,
    y: Seq<u8>,
    lo: int,
    hi: int,
    d: int,
    j: int,
    st: Seq<Open>,
    t: Seq<XTok>,
    env: Env,
)
    requires
        agree(x, y, lo, hi, d),
        lo <= j,
        j + 1 < hi,
        x[j] == 0x3C,
        x[j + 1] == 0x2F,
        name_end(x, j + 2) < hi,
        x[name_end(x, j + 2)] < 0x80,
        st.len() > 0,
        0 <= st.last().0 <= st.last().1 <= y.len(),
    ensures
        ({
            let n = name_end(x, j + 2);
            let e = ws_end(x, n);
            let top = st.last();
            let same = x.subrange(j + 2, n) == y.subrange(top.0, top.1);
            (same && e < hi && x[e] == 0x3E) ==> item(y, j - d, st, t, env) == Some(
                (st.drop_last(), close_at(t.push(XTok::ETag), top.2), e + 1 - d),
            )
        }),
        ({
            let n = name_end(x, j + 2);
            let top = st.last();
            x.subrange(j + 2, n) != y.subrange(top.0, top.1) ==> item(y, j - d, st, t, env) is None
        }),
        ({
            let n = name_end(x, j + 2);
            let e = ws_end(x, n);
            (e < hi && x[e] != 0x3E) ==> item(y, j - d, st, t, env) is None
        }),
{
    lemma_name_end(x, j + 2);
    let n = name_end(x, j + 2);
    lemma_name_end_mv(x, y, lo, hi, d, j + 2);
    lemma_agree_span(x, y, lo, hi, d, j + 2, n);
    lemma_byte_is(x, y, lo, hi, d, j + 1, 0x2F);
    assert(x[j] == y[j - d]);
    let e = ws_end(x, n);
    if e < hi {
        lemma_ws_end_mv(x, y, lo, hi, d, n);
        lemma_ws_end_ge(x, n);
        lemma_byte_is(x, y, lo, hi, d, e, 0x3E);
    }
}

// ---------------------------------------------------------------------------
// Text and CDATA sections, a piece at a time
// ---------------------------------------------------------------------------

/// The window decides that no `]]>` starts at `m`, and `m` is no `<` or
/// `&`.
pub open spec fn no_cdend(x: Seq<u8>, m: int, hi: int) -> bool {
    x[m] != 0x5D || (m + 1 < hi && x[m + 1] != 0x5D) || (m + 2 < hi && x[m + 2] != 0x3E)
}

pub open spec fn text_safe(x: Seq<u8>, m: int, hi: int) -> bool {
    x[m] != 0x3C && x[m] != 0x26 && no_cdend(x, m, hi)
}

pub proof fn lemma_no_cdend_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, m: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= m < hi,
        no_cdend(x, m, hi),
    ensures
        !has_lit(y, m - d, lit_cdata_end()),
        y[m - d] == x[m],
{
    lemma_lits_stable();
    if x[m] != 0x5D {
        lemma_has_lit_no(x, y, lo, hi, d, m, lit_cdata_end(), 0);
    } else if m + 1 < hi && x[m + 1] != 0x5D {
        lemma_has_lit_no(x, y, lo, hi, d, m, lit_cdata_end(), 1);
    } else {
        lemma_has_lit_no(x, y, lo, hi, d, m, lit_cdata_end(), 2);
    }
}

/// One byte of text that the window decides is text.
pub proof fn lemma_text_step(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, m: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= m < hi,
        text_safe(x, m, hi),
    ensures
        text_end(y, m - d) == text_end(y, m + 1 - d),
        0 <= m - d < y.len(),
{
    lemma_no_cdend_mv(x, y, lo, hi, d, m);
}

/// The window has `]]>` at `m` in text: the text fails.
pub proof fn lemma_text_cdend(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, m: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= m,
        m + 3 <= hi,
        x[m] == 0x5D && x[m + 1] == 0x5D && x[m + 2] == 0x3E,
    ensures
        text_end(y, m - d) is None,
{
    lemma_lits_stable();
    assert(x.subrange(m, m + 3) =~= lit_cdata_end());
    lemma_has_lit(x, y, lo, hi, d, m, lit_cdata_end());
    assert(y[m - d] == x[m]);
}

/// The window has the end of the text at `m`.
pub proof fn lemma_text_stop(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, m: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= m < hi,
        x[m] == 0x3C || x[m] == 0x26,
    ensures
        text_end(y, m - d) == Some(m - d),
{
    assert(y[m - d] == x[m]);
}

/// One byte of a CDATA section that the window decides is not its end.
pub proof fn lemma_cdata_step(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, m: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= m < hi,
        no_cdend(x, m, hi),
    ensures
        cdata_end(y, m - d) == cdata_end(y, m + 1 - d),
        0 <= m - d < y.len(),
{
    lemma_no_cdend_mv(x, y, lo, hi, d, m);
}

pub proof fn lemma_cdata_stop(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, m: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= m,
        m + 3 <= hi,
        x[m] == 0x5D && x[m + 1] == 0x5D && x[m + 2] == 0x3E,
    ensures
        cdata_end(y, m - d) == Some(m + 3 - d),
{
    lemma_lits_stable();
    assert(x.subrange(m, m + 3) =~= lit_cdata_end());
    lemma_has_lit(x, y, lo, hi, d, m, lit_cdata_end());
}

/// Text from `ts` that has reached `k`, where it ends: the item.
pub proof fn lemma_text_item(s: Seq<u8>, ts: int, k: int, st: Seq<Open>, t: Seq<XTok>, env: Env)
    requires
        0 <= ts < k <= s.len(),
        s[ts] != 0x3C && s[ts] != 0x26,
        text_end(s, ts) == Some(k),
    ensures
        item(s, ts, st, t, env) == Some((st, t.push(XTok::Text { start: ts, end: k, cr: has_cr(s, ts, k) }), k)),
{
}

/// A CDATA section from `j` whose text has reached `k`, where `]]>` is.
pub proof fn lemma_cdata_item(s: Seq<u8>, j: int, k: int, st: Seq<Open>, t: Seq<XTok>, env: Env)
    requires
        0 <= j,
        has_lit(s, j, lit_cdata()),
        cdata_end(s, j + 9) == Some(k + 3),
    ensures
        item(s, j, st, t, env) == Some(
            (st, t.push(XTok::CData { start: j + 9, end: k, cr: has_cr(s, j + 9, k) }), k + 3),
        ),
{
    lemma_lits_stable();
    assert(s.subrange(j, j + 9)[0] == s[j]);
    assert(s.subrange(j, j + 9)[1] == s[j + 1]);
    assert(s.subrange(j, j + 9)[2] == s[j + 2]);
    assert(!has_lit(s, j, lit_comment())) by {
        if has_lit(s, j, lit_comment()) {
            assert(s.subrange(j, j + 4)[2] == s[j + 2]);
        }
    }
}

/// A CDATA section from `j` that runs to the end: the item fails.
pub proof fn lemma_cdata_fail(s: Seq<u8>, j: int, st: Seq<Open>, t: Seq<XTok>, env: Env)
    requires
        0 <= j,
        has_lit(s, j, lit_cdata()),
        cdata_end(s, j + 9) is None,
    ensures
        item(s, j, st, t, env) is None,
{
    lemma_lits_stable();
    assert(s.subrange(j, j + 9)[0] == s[j]);
    assert(s.subrange(j, j + 9)[1] == s[j + 1]);
    assert(s.subrange(j, j + 9)[2] == s[j + 2]);
    assert(!has_lit(s, j, lit_comment())) by {
        if has_lit(s, j, lit_comment()) {
            assert(s.subrange(j, j + 4)[2] == s[j + 2]);
        }
    }
}

/// `cdata_end` that reaches the end of `s` without `]]>`.
pub proof fn lemma_cdata_end_none(s: Seq<u8>, m: int)
    requires
        0 <= m,
        m + 2 >= s.len(),
    ensures
        cdata_end(s, m) is None,
    decreases s.len() - m,
{
    if 0 <= m < s.len() {
        assert(!has_lit(s, m, lit_cdata_end()));
        lemma_cdata_end_none(s, m + 1);
    }
}

pub proof fn lemma_has_cr_step(s: Seq<u8>, a: int, b: int)
    requires
        a <= b < s.len(),
    ensures
        has_cr(s, a, b + 1) == (has_cr(s, a, b) || s[b] == 0x0D),
{
    if has_cr(s, a, b + 1) {
        let k = choose|k: int| a <= k < b + 1 && s[k] == 0x0D;
        if k < b {
            assert(has_cr(s, a, b));
        }
    }
    if s[b] == 0x0D {
        assert(a <= b < b + 1 && s[b] == 0x0D);
    }
    if has_cr(s, a, b) {
        let k = choose|k: int| a <= k < b && s[k] == 0x0D;
        assert(a <= k < b + 1 && s[k] == 0x0D);
    }
}

pub proof fn lemma_has_cr_empty(s: Seq<u8>, a: int)
    ensures
        !has_cr(s, a, a),
{
}

/// `has_cr` over bytes `seen` has, on any `s` that begins with it.
pub proof fn lemma_has_cr_ext(seen: Seq<u8>, s: Seq<u8>, a: int, b: int)
    requires
        ext(seen, s),
        0 <= a,
        b <= seen.len(),
    ensures
        has_cr(s, a, b) == has_cr(seen, a, b),
{
    if has_cr(s, a, b) {
        let k = choose|k: int| a <= k < b && s[k] == 0x0D;
        assert(s.subrange(0, seen.len() as int)[k] == s[k]);
    }
    if has_cr(seen, a, b) {
        let k = choose|k: int| a <= k < b && seen[k] == 0x0D;
        assert(s.subrange(0, seen.len() as int)[k] == s[k]);
    }
}

// ---------------------------------------------------------------------------
// Characters, one code point at a time
// ---------------------------------------------------------------------------

/// One code point that the window has whole: `chars_from` past it is the
/// same, and so it is if it is a `Char`.
pub proof fn lemma_chars_step(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, m: int, l: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= m,
        m + l <= hi,
        utf8_len(x, m) == Some(l),
    ensures
        chars_from(y, m - d) == (char_seq_ok(x, m, l) && chars_from(y, m + l - d)),
{
    assert(x[m] == y[m - d]);
    if l >= 2 {
        assert(x[m + 1] == y[m + 1 - d]);
    }
    if l >= 3 {
        assert(x[m + 2] == y[m + 2 - d]);
    }
    if l >= 4 {
        assert(x[m + 3] == y[m + 3 - d]);
    }
    assert(utf8_len(y, m - d) == Some(l));
    assert(char_seq_ok(y, m - d, l) == char_seq_ok(x, m, l));
}

/// Four bytes decide whether a code point starts at `m`.
pub proof fn lemma_chars_bad(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, m: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= m,
        m + 4 <= hi,
        utf8_len(x, m) is None,
    ensures
        !chars_from(y, m - d),
{
    assert(x[m] == y[m - d]);
    assert(x[m + 1] == y[m + 1 - d]);
    assert(x[m + 2] == y[m + 2 - d]);
    assert(x[m + 3] == y[m + 3 - d]);
    assert(utf8_len(y, m - d) is None);
}

/// At the end, where the window is all that remains: the same, for a code
/// point the window has cut short.
pub proof fn lemma_chars_tail(x: Seq<u8>, y: Seq<u8>, lo: int, d: int, m: int)
    requires
        agree(x, y, lo, x.len() as int, d),
        y.len() == x.len() - d,
        lo <= m < x.len(),
        utf8_len(x, m) is None || utf8_len(x, m).unwrap() + m > x.len(),
    ensures
        !chars_from(y, m - d),
{
    assert(x[m] == y[m - d]);
    if m + 1 < x.len() {
        assert(x[m + 1] == y[m + 1 - d]);
    }
    if m + 2 < x.len() {
        assert(x[m + 2] == y[m + 2 - d]);
    }
    if m + 3 < x.len() {
        assert(x[m + 3] == y[m + 3 - d]);
    }
    assert(utf8_len(y, m - d) == utf8_len(x, m));
}

pub proof fn lemma_chars_end(y: Seq<u8>)
    ensures
        chars_from(y, y.len() as int),
{
}

// ---------------------------------------------------------------------------
// The head: byte order mark, XML declaration, encoding
// ---------------------------------------------------------------------------

/// The window decides whether an XML declaration starts at `p0`.
pub open spec fn decl_decided(x: Seq<u8>, p0: int, hi: int) -> bool {
    p0 + 6 <= hi || exists|k: int| 0 <= k < 5 && p0 + k < hi && #[trigger] x[p0 + k] != lit_xmldecl()[k]
}

pub open spec fn has_decl(x: Seq<u8>, p0: int) -> bool {
    has_lit(x, p0, lit_xmldecl()) && 0 <= p0 + 5 < x.len() && is_ws(x[p0 + 5])
}

/// The window has decided the head, in UTF-8: `parse` reads the document
/// as UTF-8, and the head is what it is in the window.
#[verifier::spinoff_prover]
pub proof fn lemma_head_utf8(x: Seq<u8>, y: Seq<u8>, hi: int)
    requires
        ag(x, y, hi),
        hi >= 3 || (hi >= 1 && x[0] != 0xEF),
        hi >= 1 && x[0] != 0xFE && x[0] != 0xFF,
        decl_decided(x, bom_end(x), hi),
        has_decl(x, bom_end(x)) ==> (xmldecl(x, bom_end(x), Enc::Utf8) matches Some((_, e, _)) && e <= hi),
    ensures
        input_enc(y) == Enc::Utf8,
        input_enc(x) == Enc::Utf8,
        decl_head(y, Enc::Utf8) == decl_head(x, Enc::Utf8),
        bom_end(y) == bom_end(x),
        has_decl(y, bom_end(x)) == has_decl(x, bom_end(x)),
{
    hide(xmldecl);
    lemma_bom_end_eq(x, y, hi);
    let p0 = bom_end(x);
    assert(lit_xmldecl() =~= seq![0x3Cu8, 0x3F, 0x78, 0x6D, 0x6C]);
    // No UTF-16 byte order mark.
    lemma_not_lit(x, y, hi, 0, seq![0xFEu8, 0xFF]);
    lemma_not_lit(x, y, hi, 0, seq![0xFFu8, 0xFE]);
    // The declaration.
    if p0 + 6 <= hi {
        lemma_lit_eq(x, y, hi, p0, lit_xmldecl());
        lemma_byte_eq(x, y, hi, p0 + 5);
    } else {
        let k = choose|k: int| 0 <= k < 5 && p0 + k < hi && #[trigger] x[p0 + k] != lit_xmldecl()[k];
        lemma_not_lit_at(x, y, hi, p0, lit_xmldecl(), k);
    }
    assert(has_decl(y, p0) == has_decl(x, p0));
    if has_decl(x, p0) {
        reveal(xmldecl);
        lemma_xmldecl_eq(x, y, hi, p0, Enc::Utf8);
        // The declared encoding: the one `xmldecl` checked is UTF-8.
        let (v, _, _) = version_info(x, p0 + 5).unwrap();
        lemma_version_info_eq(x, y, hi, p0 + 5);
        let j = ws_end(x, v);
        if j > v && has_lit(x, j, lit_encoding()) {
            assert(lit_encoding() =~= seq![0x65u8, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67]);
            lemma_enc_span_eq(x, y, hi, j);
            lemma_ws_eq(x, y, hi, v);
            lemma_lit_eq(x, y, hi, j, lit_encoding());
            let (_, a, b) = enc_span(x, j).unwrap();
            assert(ci_eq(x, a, b, lit_utf8()));
            assert(lit_utf8().len() == 5);
            assert(lit_latin1().len() == 10);
            assert(lit_ascii().len() == 8);
            assert(declared_enc(x) == Some((a, b)));
            assert(declared_enc(y) == Some((a, b)));
        } else {
            if j > v {
                assert(j < hi);
                if has_lit(y, j, lit_encoding()) {
                    lemma_lit_eq(x, y, hi, j, lit_encoding());
                    if j + 8 > hi {
                        // `j` is before the declaration's end; so is the
                        // literal, which would be the encoding.
                        lemma_not_lit(x, y, hi, j, lit_encoding());
                    }
                }
            }
            lemma_ws_eq(x, y, hi, v);
            assert(declared_enc(x) is None);
            assert(declared_enc(y) is None);
        }
    } else {
        assert(declared_enc(x) is None);
        assert(declared_enc(y) is None);
    }
}

// ---------------------------------------------------------------------------
// At the end: the window is all of what remains
// ---------------------------------------------------------------------------

/// `x` from `lo` is `y` from `lo - d`, to the end of both.
pub open spec fn tail(x: Seq<u8>, y: Seq<u8>, lo: int, d: int) -> bool {
    agree(x, y, lo, x.len() as int, d) && y.len() == x.len() - d
}

pub proof fn lemma_cp_at_tail(x: Seq<u8>, y: Seq<u8>, lo: int, d: int, i: int)
    requires
        tail(x, y, lo, d),
        lo <= i,
    ensures
        cp_at(y, i - d) == cp_at(x, i),
{
    if i < x.len() {
        assert(x[i] == y[i - d]);
        if i + 1 < x.len() {
            assert(x[i + 1] == y[i + 1 - d]);
        }
        if i + 2 < x.len() {
            assert(x[i + 2] == y[i + 2 - d]);
        }
        if i + 3 < x.len() {
            assert(x[i + 3] == y[i + 3 - d]);
        }
        assert(utf8_len(y, i - d) == utf8_len(x, i));
        if let Some(l) = utf8_len(x, i) {
            assert(cp_val(y, i - d, l) == cp_val(x, i, l));
        }
    }
}

pub proof fn lemma_name_rest_tail(x: Seq<u8>, y: Seq<u8>, lo: int, d: int, i: int)
    requires
        tail(x, y, lo, d),
        lo <= i,
    ensures
        name_rest(y, i - d) == name_rest(x, i) - d,
    decreases x.len() - i,
{
    lemma_cp_at_tail(x, y, lo, d, i);
    lemma_cp_in_bounds(x, i);
    if 0 <= i && i + cp_len(x, i) <= x.len() && name_char_at(x, i) {
        lemma_name_rest_tail(x, y, lo, d, i + cp_len(x, i));
    }
}

pub proof fn lemma_name_end_tail(x: Seq<u8>, y: Seq<u8>, lo: int, d: int, i: int)
    requires
        tail(x, y, lo, d),
        lo <= i,
    ensures
        name_end(y, i - d) == name_end(x, i) - d,
{
    lemma_cp_at_tail(x, y, lo, d, i);
    lemma_cp_in_bounds(x, i);
    if name_start_at(x, i) {
        lemma_name_rest_tail(x, y, lo, d, i + cp_len(x, i));
    }
}

pub proof fn lemma_ws_end_tail(x: Seq<u8>, y: Seq<u8>, lo: int, d: int, i: int)
    requires
        tail(x, y, lo, d),
        lo <= i,
    ensures
        ws_end(y, i - d) == ws_end(x, i) - d,
    decreases x.len() - i,
{
    if 0 <= i < x.len() {
        assert(x[i] == y[i - d]);
        if is_ws(x[i]) {
            lemma_ws_end_tail(x, y, lo, d, i + 1);
        }
    }
}

/// An end tag at the end that the window does not finish: it fails.
pub proof fn lemma_etag_tail(x: Seq<u8>, y: Seq<u8>, lo: int, d: int, j: int, st: Seq<Open>, t: Seq<XTok>, env: Env)
    requires
        tail(x, y, lo, d),
        lo <= j,
        j + 1 < x.len(),
        x[j] == 0x3C,
        x[j + 1] == 0x2F,
        st.len() > 0,
        ({
            let n = name_end(x, j + 2);
            n == x.len() || ws_end(x, n) == x.len()
        }),
    ensures
        item(y, j - d, st, t, env) is None,
{
    lemma_name_end(x, j + 2);
    lemma_name_end_tail(x, y, lo, d, j + 2);
    let n = name_end(x, j + 2);
    lemma_ws_end_tail(x, y, lo, d, n);
    lemma_ws_end_ge(x, n);
    assert(x[j] == y[j - d]);
    assert(x[j + 1] == y[j + 1 - d]);
}

/// Text at the end that the window does not end: it fails or runs to the
/// end.
pub proof fn lemma_text_tail(x: Seq<u8>, y: Seq<u8>, lo: int, d: int, m: int)
    requires
        tail(x, y, lo, d),
        lo <= m <= x.len(),
        forall|k: int| m <= k < x.len() ==> #[trigger] x[k] != 0x3C && x[k] != 0x26,
    ensures
        text_end(y, m - d) is None || text_end(y, m - d) == Some(y.len() as int),
    decreases x.len() - m,
{
    if m < x.len() {
        assert(x[m] == y[m - d]);
        assert(x[m] != 0x3C && x[m] != 0x26);
        lemma_text_tail(x, y, lo, d, m + 1);
    }
}

/// A CDATA section at the end with no `]]>` in the window: it fails.
pub proof fn lemma_cdata_tail(x: Seq<u8>, y: Seq<u8>, lo: int, d: int, m: int)
    requires
        tail(x, y, lo, d),
        lo <= m,
        forall|k: int| m <= k && k + 3 <= x.len() ==> !(#[trigger] x[k] == 0x5D && x[k + 1] == 0x5D && x[k + 2] == 0x3E),
    ensures
        cdata_end(y, m - d) is None,
    decreases x.len() - m,
{
    lemma_lits_stable();
    if m < x.len() {
        if has_lit(y, m - d, lit_cdata_end()) {
            assert(y.subrange(m - d, m - d + 3)[0] == y[m - d]);
            assert(y.subrange(m - d, m - d + 3)[1] == y[m - d + 1]);
            assert(y.subrange(m - d, m - d + 3)[2] == y[m - d + 2]);
            assert(x[m] == y[m - d]);
            assert(x[m + 1] == y[m + 1 - d]);
            assert(x[m + 2] == y[m + 2 - d]);
        }
        lemma_cdata_tail(x, y, lo, d, m + 1);
    }
}

/// An item that the window, which is all that remains, does not read: it
/// fails on `y`, or it is text that runs to the end.
pub proof fn lemma_item_flip(
    x: Seq<u8>,
    y: Seq<u8>,
    lo: int,
    d: int,
    j: int,
    st: Seq<Open>,
    t: Seq<XTok>,
    st2: Seq<Open>,
    t2: Seq<XTok>,
    env: Env,
)
    requires
        tail(x, y, lo, d),
        lo <= j < x.len(),
        !is_etag(x, j),
        item(x, j, st2, t2, env) is None,
    ensures
        item(y, j - d, st, t, env) matches Some((_, _, e)) ==> (e > y.len() || (e == y.len() && x[j] != 0x3C
            && x[j] != 0x26)),
{
    assert(x[j] == y[j - d]);
    if j + 1 < x.len() {
        assert(x[j + 1] == y[j + 1 - d]);
    }
    assert(is_etag(y, j - d) == is_etag(x, j));
    lemma_agree_flip(x, y, lo, x.len() as int, d);
    if let Some((_, _, e)) = item(y, j - d, st, t, env) {
        if item_reach(y, j - d, e) <= y.len() {
            lemma_item_mv(y, x, lo - d, y.len() as int, -d, j - d, st, t, st2, t2, env);
        }
    }
}

/// `Misc` stops before the end: the document fails.
pub proof fn lemma_fin_stop(s: Seq<u8>, p: int, t: Seq<XTok>)
    requires
        0 <= p < s.len(),
        !is_ws(s[p]) && !has_lit(s, p, lit_comment()) && !has_lit(s, p, lit_pi()),
    ensures
        fin(s, p, t) is None,
{
    lemma_misc_stop(s, p, t);
}

pub proof fn lemma_fin_end(s: Seq<u8>, t: Seq<XTok>)
    ensures
        fin(s, s.len() as int, t) == Some(t),
{
    lemma_misc_stop(s, s.len() as int, t);
}

pub proof fn lemma_fin_ws(s: Seq<u8>, p: int, t: Seq<XTok>)
    requires
        0 <= p < s.len(),
        is_ws(s[p]),
    ensures
        fin(s, p, t) == fin(s, p + 1, t),
{
    lemma_misc_ws(s, p, t);
}

/// A comment or processing instruction after the root element that fails
/// or ends past the end: the document fails.
pub proof fn lemma_fin_item_fail(s: Seq<u8>, p: int, t: Seq<XTok>, env: Env)
    requires
        0 <= p < s.len(),
        has_lit(s, p, lit_comment()) || has_lit(s, p, lit_pi()),
        item(s, p, Seq::empty(), t, env) matches Some((_, _, e)) ==> e > s.len(),
    ensures
        fin(s, p, t) is None,
{
    lemma_lits_stable();
    assert(s.subrange(p, p + 2)[0] == s[p] && s.subrange(p, p + 2)[1] == s[p + 1]);
    assert(!is_ws(s[p]));
    assert(ws_end(s, p) == p);
    if has_lit(s, p, lit_comment()) {
        assert(s.subrange(p, p + 4)[1] == s[p + 1]);
        assert(!byte_is(s, p + 1, 0x2F));
    } else {
        assert(!byte_is(s, p + 1, 0x2F));
        assert(!has_lit(s, p, lit_comment()));
        assert(!has_lit(s, p, lit_cdata())) by {
            if has_lit(s, p, lit_cdata()) {
                assert(s.subrange(p, p + 9)[1] == s[p + 1]);
            }
        }
        assert(byte_is(s, p + 1, 0x3F));
    }
}

pub proof fn lemma_fin_item(s: Seq<u8>, p: int, t: Seq<XTok>, env: Env)
    requires
        0 <= p < s.len(),
        has_lit(s, p, lit_comment()) || has_lit(s, p, lit_pi()),
        item(s, p, Seq::empty(), t, env) matches Some((_, _, e)) && p < e <= s.len(),
    ensures
        item(s, p, Seq::empty(), t, env) matches Some((st2, t2, e)) && st2.len() == 0 && fin(s, p, t) == fin(s, e, t2),
{
    lemma_misc_item(s, p, Seq::empty(), t, env);
}

// ---------------------------------------------------------------------------
// The prolog, a step at a time
// ---------------------------------------------------------------------------

pub proof fn lemma_comment_tape(s: Seq<u8>, p: int, t: Seq<XTok>)
    ensures
        comment(s, p, t) == (match comment(s, p, Seq::empty()) {
            Some((u, e)) => Some((t + u, e)),
            None => None,
        }),
{
    if let Some((u, e)) = comment(s, p, Seq::empty()) {
        assert(t + u =~= t.push(u[0]));
    }
}

pub proof fn lemma_pi_tape(s: Seq<u8>, p: int, t: Seq<XTok>)
    ensures
        pi(s, p, t) == (match pi(s, p, Seq::empty()) {
            Some((u, e)) => Some((t + u, e)),
            None => None,
        }),
{
    if let Some((u, e)) = pi(s, p, Seq::empty()) {
        assert(t + u =~= t.push(u[0]).push(u[1]));
    }
}

/// A comment at `p` in `Misc`.
pub proof fn lemma_misc_comment(s: Seq<u8>, p: int, t: Seq<XTok>)
    requires
        0 <= p,
        has_lit(s, p, lit_comment()),
        comment(s, p, t) matches Some((_, e)) && p < e <= s.len(),
    ensures
        comment(s, p, t) matches Some((t2, e)) && misc(s, p, t) == misc(s, e, t2),
{
    lemma_lits_stable();
    assert(s.subrange(p, p + 4)[0] == s[p]);
    assert(ws_end(s, p) == p);
}

/// A processing instruction at `p` in `Misc`.
pub proof fn lemma_misc_pi(s: Seq<u8>, p: int, t: Seq<XTok>)
    requires
        0 <= p,
        has_lit(s, p, lit_pi()),
        pi(s, p, t) matches Some((_, e)) && p < e <= s.len(),
    ensures
        pi(s, p, t) matches Some((t2, e)) && misc(s, p, t) == misc(s, e, t2),
{
    lemma_lits_stable();
    assert(s.subrange(p, p + 2)[0] == s[p]);
    assert(s.subrange(p, p + 2)[1] == s[p + 1]);
    assert(ws_end(s, p) == p);
    assert(!has_lit(s, p, lit_comment())) by {
        if has_lit(s, p, lit_comment()) {
            assert(s.subrange(p, p + 4)[1] == s[p + 1]);
        }
    }
}

/// No element starts at `p`.
pub proof fn lemma_after_root_not_lt(s: Seq<u8>, p: int, t: Seq<XTok>, env: Env)
    requires
        0 <= p < s.len(),
        s[p] != 0x3C,
    ensures
        after_root(s, p, t, env) is None,
{
}

/// The comment or processing instruction the window has at `p`, on `y`.
pub proof fn lemma_comment_pre(x: Seq<u8>, y: Seq<u8>, hi: int, p: int, t: Seq<XTok>)
    requires
        ag(x, y, hi),
        0 <= p,
        comment(x, p, t) matches Some((_, e)) && e <= hi,
    ensures
        comment(y, p, t) == comment(x, p, t),
        comment(x, p, t) matches Some((u, e)) && e >= p + 7 && no_dflt(added(t, u)) && extends(t, u) && u.len()
            == t.len() + 1,
{
    lemma_comment_mv(x, y, 0, hi, 0, p, t, t, 0);
    let (u, e) = comment(x, p, t).unwrap();
    lemma_mv_zero(added(t, u));
    assert(t + added(t, u) =~= u);
    lemma_comment_tokens(x, p, t);
}

pub proof fn lemma_pi_pre(x: Seq<u8>, y: Seq<u8>, hi: int, p: int, t: Seq<XTok>)
    requires
        ag(x, y, hi),
        0 <= p,
        pi(x, p, t) matches Some((_, e)) && e <= hi,
    ensures
        pi(y, p, t) == pi(x, p, t),
        pi(x, p, t) matches Some((u, e)) && e >= p + 4 && no_dflt(added(t, u)) && extends(t, u) && u.len() == t.len()
            + 2,
{
    lemma_pi_mv(x, y, 0, hi, 0, p, t, t, 0);
    let (u, e) = pi(x, p, t).unwrap();
    lemma_mv_zero(added(t, u));
    assert(t + added(t, u) =~= u);
    lemma_pi_tokens(x, p, t);
}

} // verus!

//! What the spec reads: a spec function that succeeds at `i` and ends at
//! `e` reads only the bytes from `i` to `e` (character data also reads the
//! byte that ends it), so it gives the same result on any input that has
//! those bytes, wherever they sit there. Two uses:
//!
//! * a prefix of a document: an item parsed on what has arrived so far,
//!   ending before what has arrived ends, is the same item on every
//!   extension of it (`agree(x, y, 0, x.len(), 0)` for any `y` that
//!   starts with `x`), so it can be reported before the rest arrives;
//! * a window: the same bytes moved to the front of a smaller buffer
//!   (`d` > 0) give the same item with its positions moved by `d`, so the
//!   incremental parser can drop what it has reported.
//!
//! Proof only: nothing here runs.
use crate::chars::*;
use crate::spec::*;
#[cfg(verus_keep_ghost)]
use verilith_core::num::{digits_end, is_digit};
#[cfg(verus_keep_ghost)]
use verilith_core::utf8::{byte_in, utf8_len};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Agreement
// ---------------------------------------------------------------------------

/// `y` holds `x[lo..hi]` moved down by `d`: `y[k - d] == x[k]`.
pub open spec fn agree(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int) -> bool {
    0 <= lo <= hi <= x.len() && 0 <= lo - d && hi - d <= y.len() && forall|k: int|
        lo <= k < hi ==> #[trigger] x[k] == y[k - d]
}

/// Agreement on a smaller range.
pub proof fn lemma_agree_sub(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, lo2: int, hi2: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= lo2 <= hi2 <= hi,
    ensures
        agree(x, y, lo2, hi2, d),
{
    assert forall|k: int| lo2 <= k < hi2 implies #[trigger] x[k] == y[k - d] by {
        assert(x[k] == y[k - d]);
    }
}

/// The same agreement, read from `y`'s side.
pub proof fn lemma_agree_flip(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int)
    requires
        agree(x, y, lo, hi, d),
    ensures
        agree(y, x, lo - d, hi - d, -d),
{
    assert forall|k: int| lo - d <= k < hi - d implies #[trigger] y[k] == x[k - (-d)] by {
        assert(x[k + d] == y[k + d - d]);
    }
}

/// Agreement through a third input.
pub proof fn lemma_agree_trans(x: Seq<u8>, y: Seq<u8>, z: Seq<u8>, lo: int, hi: int, d: int, d2: int)
    requires
        agree(x, y, lo, hi, d),
        agree(y, z, lo - d, hi - d, d2),
    ensures
        agree(x, z, lo, hi, d + d2),
{
    assert forall|k: int| lo <= k < hi implies #[trigger] x[k] == z[k - (d + d2)] by {
        assert(x[k] == y[k - d]);
        assert(y[k - d] == z[k - d - d2]);
    }
}

/// `x` is a prefix of `y`: they agree on all of `x`, in place.
pub proof fn lemma_agree_prefix(x: Seq<u8>, y: Seq<u8>)
    requires
        x.len() <= y.len(),
        y.subrange(0, x.len() as int) == x,
    ensures
        agree(x, y, 0, x.len() as int, 0),
{
    assert forall|k: int| 0 <= k < x.len() implies #[trigger] x[k] == y[k - 0] by {
        assert(y.subrange(0, x.len() as int)[k] == y[k]);
    }
}

/// The spans `x[a..b]` and `y[a - d..b - d]` are the same bytes.
pub proof fn lemma_agree_span(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, a: int, b: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= a <= b <= hi,
    ensures
        x.subrange(a, b) == y.subrange(a - d, b - d),
{
    assert forall|k: int| 0 <= k < b - a implies #[trigger] x.subrange(a, b)[k] == y.subrange(a - d, b - d)[k] by {
        assert(x[a + k] == y[a + k - d]);
    }
    assert(x.subrange(a, b) =~= y.subrange(a - d, b - d));
}

// ---------------------------------------------------------------------------
// Tokens moved with their input
// ---------------------------------------------------------------------------

/// A token whose spans are moved down by `d`; a start tag's link to its end
/// (once it is linked) moves by `k` places in the tape.
pub open spec fn mv_tok(t: XTok, d: int, k: int) -> XTok {
    match t {
        XTok::XmlDecl { start, end, sd } => XTok::XmlDecl { start: start - d, end: end - d, sd },
        XTok::Encoding { start, end } => XTok::Encoding { start: start - d, end: end - d },
        XTok::Doctype { start, end } => XTok::Doctype { start: start - d, end: end - d },
        XTok::DoctypeEnd => XTok::DoctypeEnd,
        XTok::PubId { start, end } => XTok::PubId { start: start - d, end: end - d },
        XTok::SysId { start, end } => XTok::SysId { start: start - d, end: end - d },
        XTok::ElementDecl { start, end } => XTok::ElementDecl { start: start - d, end: end - d },
        XTok::AttlistDecl { start, end } => XTok::AttlistDecl { start: start - d, end: end - d },
        XTok::AttDef { start, end, ty } => XTok::AttDef { start: start - d, end: end - d, ty },
        XTok::AttDefault { start, end, kind, nents } => XTok::AttDefault {
            start: start - d,
            end: end - d,
            kind,
            nents,
        },
        XTok::EntityDecl { start, end, pe } => XTok::EntityDecl { start: start - d, end: end - d, pe },
        XTok::EntityValue { start, end } => XTok::EntityValue { start: start - d, end: end - d },
        XTok::NData { start, end } => XTok::NData { start: start - d, end: end - d },
        XTok::NotationDecl { start, end } => XTok::NotationDecl { start: start - d, end: end - d },
        XTok::PERef { start, end } => XTok::PERef { start: start - d, end: end - d },
        XTok::Comment { start, end } => XTok::Comment { start: start - d, end: end - d },
        XTok::PI { start, end } => XTok::PI { start: start - d, end: end - d },
        XTok::PIData { start, end } => XTok::PIData { start: start - d, end: end - d },
        XTok::STag { start, end, close } => XTok::STag {
            start: start - d,
            end: end - d,
            close: if close == 0 {
                0
            } else {
                close + k
            },
        },
        XTok::Attr { start, end } => XTok::Attr { start: start - d, end: end - d },
        XTok::AttVal { start, end, plain } => XTok::AttVal { start: start - d, end: end - d, plain },
        XTok::ETag => XTok::ETag,
        XTok::Text { start, end, cr } => XTok::Text { start: start - d, end: end - d, cr },
        XTok::CData { start, end, cr } => XTok::CData { start: start - d, end: end - d, cr },
        XTok::CharRef { pos, cp } => XTok::CharRef { pos: pos - d, cp },
        XTok::EntRef { start, end } => XTok::EntRef { start: start - d, end: end - d },
    }
}

pub open spec fn mv(t: Seq<XTok>, d: int, k: int) -> Seq<XTok> {
    t.map_values(|x: XTok| mv_tok(x, d, k))
}

pub proof fn lemma_mv_tok_zero(t: XTok)
    ensures
        mv_tok(t, 0, 0) == t,
{
}

pub proof fn lemma_mv_zero(t: Seq<XTok>)
    ensures
        mv(t, 0, 0) == t,
{
    assert forall|q: int| 0 <= q < t.len() implies #[trigger] mv(t, 0, 0)[q] == t[q] by {
        lemma_mv_tok_zero(t[q]);
    }
    assert(mv(t, 0, 0) =~= t);
}

pub proof fn lemma_mv_push(t: Seq<XTok>, x: XTok, d: int, k: int)
    ensures
        mv(t.push(x), d, k) == mv(t, d, k).push(mv_tok(x, d, k)),
{
    assert(mv(t.push(x), d, k) =~= mv(t, d, k).push(mv_tok(x, d, k)));
}

pub proof fn lemma_mv_add(t: Seq<XTok>, u: Seq<XTok>, d: int, k: int)
    ensures
        mv(t + u, d, k) == mv(t, d, k) + mv(u, d, k),
{
    assert(mv(t + u, d, k) =~= mv(t, d, k) + mv(u, d, k));
}

pub proof fn lemma_mv_empty(d: int, k: int)
    ensures
        mv(Seq::<XTok>::empty(), d, k) == Seq::<XTok>::empty(),
{
    assert(mv(Seq::<XTok>::empty(), d, k) =~= Seq::<XTok>::empty());
}

/// The tokens a step added to the tape `t` to give `t2`.
pub open spec fn added(t: Seq<XTok>, t2: Seq<XTok>) -> Seq<XTok> {
    t2.subrange(t.len() as int, t2.len() as int)
}

/// `t2` is `t` with tokens added.
pub open spec fn extends(t: Seq<XTok>, t2: Seq<XTok>) -> bool {
    t.len() <= t2.len() && t2.subrange(0, t.len() as int) == t
}

pub proof fn lemma_extends_push2(t: Seq<XTok>, a: XTok, b: XTok, t2: Seq<XTok>)
    requires
        extends(t.push(a).push(b), t2),
    ensures
        extends(t, t2),
        added(t, t2) == seq![a, b] + added(t.push(a).push(b), t2),
{
    let t1 = t.push(a).push(b);
    assert(t2.subrange(0, t.len() as int) =~= t1.subrange(0, t.len() as int));
    assert(t1.subrange(0, t.len() as int) =~= t);
    assert(added(t, t2) =~= seq![a, b] + added(t1, t2)) by {
        assert forall|q: int| 0 <= q < added(t, t2).len() implies #[trigger] added(t, t2)[q] == (seq![a, b] + added(
            t1,
            t2,
        ))[q] by {
            if q == 0 {
                assert(t2[t.len() as int] == t1[t.len() as int]);
            } else if q == 1 {
                assert(t2[t.len() as int + 1] == t1[t.len() as int + 1]);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Bytes, white space, literals
// ---------------------------------------------------------------------------

pub proof fn lemma_byte_is(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int, c: u8)
    requires
        agree(x, y, lo, hi, d),
        lo <= i < hi,
    ensures
        byte_is(y, i - d, c) == byte_is(x, i, c),
{
    assert(x[i] == y[i - d]);
}

pub proof fn lemma_has_lit(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int, lit: Seq<u8>)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        i + lit.len() <= hi,
    ensures
        has_lit(y, i - d, lit) == has_lit(x, i, lit),
{
    lemma_agree_span(x, y, lo, hi, d, i, i + lit.len());
}

/// A literal that would run past `hi` is not there in `y` either, if the
/// part of it before `hi` already differs.
pub proof fn lemma_has_lit_no(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int, lit: Seq<u8>, k: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        0 <= k < lit.len(),
        i + k < hi,
        x[i + k] != lit[k],
    ensures
        !has_lit(y, i - d, lit),
        !has_lit(x, i, lit),
{
    assert(x[i + k] == y[i + k - d]);
    if has_lit(y, i - d, lit) {
        assert(y.subrange(i - d, i - d + lit.len())[k] == y[i - d + k]);
    }
    if has_lit(x, i, lit) {
        assert(x.subrange(i, i + lit.len())[k] == x[i + k]);
    }
}

pub proof fn lemma_ws_end_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        ws_end(x, i) < hi,
    ensures
        ws_end(y, i - d) == ws_end(x, i) - d,
    decreases x.len() - i,
{
    lemma_ws_end_ge(x, i);
    assert(x[i] == y[i - d]);
    if 0 <= i < x.len() && is_ws(x[i]) {
        lemma_ws_end_mv(x, y, lo, hi, d, i + 1);
    }
}

pub proof fn lemma_ws_end_ge(s: Seq<u8>, i: int)
    ensures
        ws_end(s, i) >= i,
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_ws(s[i]) {
        lemma_ws_end_ge(s, i + 1);
    }
}

/// White space ends where it ends, and only white space was passed.
pub proof fn lemma_ws_end_ws(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= ws_end(s, i) <= s.len(),
        forall|k: int| i <= k < ws_end(s, i) ==> is_ws(#[trigger] s[k]),
        ws_end(s, i) < s.len() ==> !is_ws(s[ws_end(s, i)]),
    decreases s.len() - i,
{
    if i < s.len() && is_ws(s[i]) {
        lemma_ws_end_ws(s, i + 1);
    }
}

/// The byte where something ended after white space at `i` is ASCII.
pub open spec fn ascii_at(s: Seq<u8>, i: int) -> bool {
    0 <= i < s.len() && s[i] < 0x80
}

pub proof fn lemma_eq_end_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i <= x.len(),
        eq_end(x, i) matches Some(v) && v < hi,
    ensures
        eq_end(y, i - d) == Some(eq_end(x, i).unwrap() - d),
        ascii_at(x, i),
{
    let j = ws_end(x, i);
    lemma_ws_end_ws(x, i);
    lemma_ws_end_ws(x, j + 1);
    lemma_ws_end_mv(x, y, lo, hi, d, i);
    lemma_byte_is(x, y, lo, hi, d, j, 0x3D);
    lemma_ws_end_mv(x, y, lo, hi, d, j + 1);
    if j > i {
        assert(is_ws(x[i]));
    }
}

// ---------------------------------------------------------------------------
// Characters and names
// ---------------------------------------------------------------------------

/// The code point at `i`, where it is ASCII or lies before `hi`.
pub proof fn lemma_cp_at_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i < hi,
        x[i] < 0x80 || (cp_at(x, i) matches Some((_, l)) && i + l <= hi),
    ensures
        cp_at(y, i - d) == cp_at(x, i),
{
    assert(x[i] == y[i - d]);
    if x[i] >= 0x80 {
        let l = cp_at(x, i).unwrap().1;
        if l >= 2 {
            assert(x[i + 1] == y[i + 1 - d]);
        }
        if l >= 3 {
            assert(x[i + 2] == y[i + 2 - d]);
        }
        if l >= 4 {
            assert(x[i + 3] == y[i + 3 - d]);
        }
        assert(utf8_len(y, i - d) == utf8_len(x, i));
    }
}

pub proof fn lemma_name_rest_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i <= x.len(),
        name_rest(x, i) < hi,
        x[name_rest(x, i)] < 0x80,
    ensures
        name_rest(y, i - d) == name_rest(x, i) - d,
    decreases x.len() - i,
{
    lemma_cp_in_bounds(x, i);
    lemma_cp_in_bounds(y, i - d);
    if 0 <= i && i + cp_len(x, i) <= x.len() && name_char_at(x, i) {
        lemma_name_rest(x, i + cp_len(x, i));
        lemma_cp_at_mv(x, y, lo, hi, d, i);
        lemma_name_rest_mv(x, y, lo, hi, d, i + cp_len(x, i));
    } else {
        lemma_cp_at_mv(x, y, lo, hi, d, i);
    }
}

pub proof fn lemma_name_end_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i <= x.len(),
        name_end(x, i) < hi,
        x[name_end(x, i)] < 0x80,
    ensures
        name_end(y, i - d) == name_end(x, i) - d,
{
    lemma_cp_in_bounds(x, i);
    lemma_name_end(x, i);
    if name_start_at(x, i) {
        lemma_cp_at_mv(x, y, lo, hi, d, i);
        lemma_name_rest(x, i + cp_len(x, i));
        lemma_name_rest_mv(x, y, lo, hi, d, i + cp_len(x, i));
    } else {
        lemma_cp_at_mv(x, y, lo, hi, d, i);
    }
}

// ---------------------------------------------------------------------------
// References
// ---------------------------------------------------------------------------

pub proof fn lemma_hex_end_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        hex_end(x, i) < hi,
    ensures
        hex_end(y, i - d) == hex_end(x, i) - d,
    decreases x.len() - i,
{
    lemma_hex_end_ge(x, i);
    assert(x[i] == y[i - d]);
    if 0 <= i < x.len() && is_hex(x[i]) {
        lemma_hex_end_mv(x, y, lo, hi, d, i + 1);
    }
}

pub proof fn lemma_digits_end_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        digits_end(x, i) < hi,
    ensures
        digits_end(y, i - d) == digits_end(x, i) - d,
    decreases x.len() - i,
{
    lemma_digits_end_ge(x, i);
    assert(x[i] == y[i - d]);
    if 0 <= i < x.len() && is_digit(x[i]) {
        lemma_digits_end_mv(x, y, lo, hi, d, i + 1);
    }
}

pub proof fn lemma_hexv_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, a: int, b: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= a,
        b <= hi,
    ensures
        hexv(y, a - d, b - d) == hexv(x, a, b),
    decreases b - a,
{
    if a < b {
        assert(x[b - 1] == y[b - 1 - d]);
        lemma_hexv_mv(x, y, lo, hi, d, a, b - 1);
    }
}

pub proof fn lemma_decv_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, a: int, b: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= a,
        b <= hi,
    ensures
        decv(y, a - d, b - d) == decv(x, a, b),
    decreases b - a,
{
    if a < b {
        assert(x[b - 1] == y[b - 1 - d]);
        lemma_decv_mv(x, y, lo, hi, d, a, b - 1);
    }
}

pub proof fn lemma_hex_end_ge(s: Seq<u8>, i: int)
    ensures
        hex_end(s, i) >= i,
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_hex(s[i]) {
        lemma_hex_end_ge(s, i + 1);
    }
}

pub proof fn lemma_digits_end_ge(s: Seq<u8>, i: int)
    ensures
        digits_end(s, i) >= i,
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_digit(s[i]) {
        lemma_digits_end_ge(s, i + 1);
    }
}

pub proof fn lemma_charref_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        charref(x, i) matches Some((_, e)) && e <= hi,
    ensures
        charref(y, i - d) == (match charref(x, i) {
            Some((c, e)) => Some((c, e - d)),
            None => None,
        }),
{
    lemma_hex_end_ge(x, i + 3);
    lemma_digits_end_ge(x, i + 2);
    lemma_byte_is(x, y, lo, hi, d, i + 2, 0x78);
    if byte_is(x, i + 2, 0x78) {
        let e = hex_end(x, i + 3);
        lemma_hex_end_mv(x, y, lo, hi, d, i + 3);
        lemma_byte_is(x, y, lo, hi, d, e, 0x3B);
        lemma_hexv_mv(x, y, lo, hi, d, i + 3, e);
    } else {
        let e = digits_end(x, i + 2);
        lemma_digits_end_mv(x, y, lo, hi, d, i + 2);
        lemma_byte_is(x, y, lo, hi, d, e, 0x3B);
        lemma_decv_mv(x, y, lo, hi, d, i + 2, e);
    }
}

pub proof fn lemma_predef_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, a: int, b: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= a <= b <= hi,
    ensures
        predef(y, a - d, b - d) == predef(x, a, b),
{
    lemma_agree_span(x, y, lo, hi, d, a, b);
}

pub proof fn lemma_ref_syntax_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i < hi,
        ref_syntax(x, i) matches Some(e) && e <= hi,
    ensures
        ref_syntax(y, i - d) == Some(ref_syntax(x, i).unwrap() - d),
{
    lemma_name_end(x, i + 1);
    if byte_is(x, i + 1, 0x23) {
        lemma_byte_is(x, y, lo, hi, d, i + 1, 0x23);
        lemma_charref_mv(x, y, lo, hi, d, i);
    } else {
        let n = name_end(x, i + 1);
        lemma_byte_is(x, y, lo, hi, d, i + 1, 0x23);
        lemma_name_end_mv(x, y, lo, hi, d, i + 1);
        lemma_byte_is(x, y, lo, hi, d, n, 0x3B);
    }
}

pub proof fn lemma_att_ref_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int, env: Option<Env>)
    requires
        agree(x, y, lo, hi, d),
        lo <= i < hi,
        att_ref(x, i, env) matches Some(e) && e <= hi,
    ensures
        att_ref(y, i - d, env) == Some(att_ref(x, i, env).unwrap() - d),
{
    lemma_name_end(x, i + 1);
    if byte_is(x, i + 1, 0x23) {
        lemma_byte_is(x, y, lo, hi, d, i + 1, 0x23);
        lemma_charref_mv(x, y, lo, hi, d, i);
    } else {
        let n = name_end(x, i + 1);
        lemma_byte_is(x, y, lo, hi, d, i + 1, 0x23);
        lemma_name_end_mv(x, y, lo, hi, d, i + 1);
        lemma_byte_is(x, y, lo, hi, d, n, 0x3B);
        lemma_predef_mv(x, y, lo, hi, d, i + 1, n);
        lemma_agree_span(x, y, lo, hi, d, i + 1, n);
    }
}

pub proof fn lemma_content_ref_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int, env: Env)
    requires
        agree(x, y, lo, hi, d),
        lo <= i < hi,
        content_ref(x, i, env) matches Some((_, e)) && e <= hi,
    ensures
        content_ref(y, i - d, env) == (match content_ref(x, i, env) {
            Some((t, e)) => Some((mv_tok(t, d, 0), e - d)),
            None => None,
        }),
{
    lemma_name_end(x, i + 1);
    if byte_is(x, i + 1, 0x23) {
        lemma_byte_is(x, y, lo, hi, d, i + 1, 0x23);
        lemma_charref_mv(x, y, lo, hi, d, i);
    } else {
        let n = name_end(x, i + 1);
        lemma_byte_is(x, y, lo, hi, d, i + 1, 0x23);
        lemma_name_end_mv(x, y, lo, hi, d, i + 1);
        lemma_byte_is(x, y, lo, hi, d, n, 0x3B);
        lemma_predef_mv(x, y, lo, hi, d, i + 1, n);
        lemma_agree_span(x, y, lo, hi, d, i + 1, n);
    }
}

// ---------------------------------------------------------------------------
// Attribute values
// ---------------------------------------------------------------------------

pub proof fn lemma_att_ref_end(s: Seq<u8>, i: int, env: Option<Env>)
    requires
        0 <= i < s.len(),
        att_ref(s, i, env) is Some,
    ensures
        att_ref(s, i, env).unwrap() > i,
{
    lemma_hex_end_ge(s, i + 3);
    lemma_digits_end_ge(s, i + 2);
    lemma_name_end(s, i + 1);
}

pub proof fn lemma_att_chars_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int, q: u8, env: Option<Env>)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        att_chars(x, i, q, env) matches Some(r) && r < hi,
    ensures
        att_chars(y, i - d, q, env) == Some(att_chars(x, i, q, env).unwrap() - d),
        att_chars(x, i, q, env).unwrap() >= i,
    decreases x.len() - i,
{
    if x[i] == q {
        assert(x[i] == y[i - d]);
    } else if x[i] == 0x3C {
    } else if x[i] == 0x26 {
        let e = att_ref(x, i, env).unwrap();
        lemma_att_ref_end(x, i, env);
        lemma_att_chars_mv(x, y, lo, hi, d, e, q, env);
        assert(x[i] == y[i - d]);
        lemma_att_ref_mv(x, y, lo, hi, d, i, env);
    } else {
        lemma_att_chars_mv(x, y, lo, hi, d, i + 1, q, env);
        assert(x[i] == y[i - d]);
    }
}

pub proof fn lemma_att_plain_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, a: int, b: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= a <= b <= hi,
    ensures
        att_plain(y, a - d, b - d) == att_plain(x, a, b),
{
    if att_plain(x, a, b) {
        assert forall|k: int| a - d <= k < b - d implies y[k] != 0x26 && y[k] != 0x09 && y[k] != 0x0A && y[k]
            != 0x0D by {
            assert(x[k + d] == y[k + d - d]);
        }
    }
    if att_plain(y, a - d, b - d) {
        assert forall|k: int| a <= k < b implies x[k] != 0x26 && x[k] != 0x09 && x[k] != 0x0A && x[k] != 0x0D by {
            assert(x[k] == y[k - d]);
        }
    }
}

pub proof fn lemma_has_cr_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, a: int, b: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= a <= b <= hi,
    ensures
        has_cr(y, a - d, b - d) == has_cr(x, a, b),
{
    if has_cr(x, a, b) {
        let k = choose|k: int| a <= k < b && x[k] == 0x0D;
        assert(x[k] == y[k - d]);
        assert(a - d <= k - d < b - d && y[k - d] == 0x0D);
    }
    if has_cr(y, a - d, b - d) {
        let k = choose|k: int| a - d <= k < b - d && y[k] == 0x0D;
        assert(x[k + d] == y[k + d - d]);
        assert(a <= k + d < b && x[k + d] == 0x0D);
    }
}

// ---------------------------------------------------------------------------
// Comments, processing instructions, CDATA sections, character data
// ---------------------------------------------------------------------------

/// A step that adds tokens to a tape, moved: on `y` from `i - d` with the
/// tape `t2`, it adds the moved tokens of the step on `x` from `i` with the
/// tape `t`.
pub open spec fn tape_mv(r: Option<(Seq<XTok>, int)>, t: Seq<XTok>, t2: Seq<XTok>, d: int, k: int) -> Option<
    (Seq<XTok>, int),
> {
    match r {
        Some((u, e)) => Some((t2 + mv(added(t, u), d, k), e - d)),
        None => None,
    }
}

pub proof fn lemma_comment_end_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        comment_end(x, i) matches Some(e) && e <= hi,
    ensures
        comment_end(y, i - d) == Some(comment_end(x, i).unwrap() - d),
        comment_end(x, i).unwrap() >= i + 3,
    decreases x.len() - i,
{
    if x[i] == 0x2D && byte_is(x, i + 1, 0x2D) {
        assert(x[i] == y[i - d]);
        lemma_byte_is(x, y, lo, hi, d, i + 1, 0x2D);
        lemma_byte_is(x, y, lo, hi, d, i + 2, 0x3E);
    } else {
        lemma_comment_end_mv(x, y, lo, hi, d, i + 1);
        assert(x[i] == y[i - d]);
        if x[i] == 0x2D {
            lemma_byte_is(x, y, lo, hi, d, i + 1, 0x2D);
        }
    }
}

pub proof fn lemma_comment_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int, t: Seq<XTok>, t2: Seq<XTok>, k: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        comment(x, i, t) matches Some((_, e)) && e <= hi,
    ensures
        comment(y, i - d, t2) == tape_mv(comment(x, i, t), t, t2, d, k),
        comment(x, i, t) matches Some((u, e)) && extends(t, u) && e >= i + 7,
{
    lemma_comment_end_mv(x, y, lo, hi, d, i + 4);
    let (u, e) = comment(x, i, t).unwrap();
    assert(added(t, u) =~= seq![XTok::Comment { start: i + 4, end: e - 3 }]);
    assert(u.subrange(0, t.len() as int) =~= t);
    assert(mv(added(t, u), d, k) =~= seq![XTok::Comment { start: i + 4 - d, end: e - 3 - d }]);
    assert(t2.push(XTok::Comment { start: i + 4 - d, end: e - 3 - d }) =~= t2 + mv(added(t, u), d, k));
}

pub proof fn lemma_pi_end_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        pi_end(x, i) matches Some(e) && e <= hi,
    ensures
        pi_end(y, i - d) == Some(pi_end(x, i).unwrap() - d),
        pi_end(x, i).unwrap() >= i + 2,
    decreases x.len() - i,
{
    if x[i] == 0x3F && byte_is(x, i + 1, 0x3E) {
        assert(x[i] == y[i - d]);
        lemma_byte_is(x, y, lo, hi, d, i + 1, 0x3E);
    } else {
        lemma_pi_end_mv(x, y, lo, hi, d, i + 1);
        assert(x[i] == y[i - d]);
        if x[i] == 0x3F {
            lemma_byte_is(x, y, lo, hi, d, i + 1, 0x3E);
        }
    }
}

pub proof fn lemma_pi_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int, t: Seq<XTok>, t2: Seq<XTok>, k: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        pi(x, i, t) matches Some((_, e)) && e <= hi,
    ensures
        pi(y, i - d, t2) == tape_mv(pi(x, i, t), t, t2, d, k),
        pi(x, i, t) matches Some((u, e)) && extends(t, u) && e >= i + 4,
{
    let n = name_end(x, i + 2);
    lemma_name_end(x, i + 2);
    let (u, e) = pi(x, i, t).unwrap();
    if has_lit(x, n, lit_pi_end()) {
        assert(x.subrange(n, n + 2)[0] == x[n]);
        lemma_name_end_mv(x, y, lo, hi, d, i + 2);
        lemma_has_lit(x, y, lo, hi, d, n, lit_pi_end());
        if n == i + 5 {
            assert(x[i + 2] == y[i + 2 - d]);
            assert(x[i + 3] == y[i + 3 - d]);
            assert(x[i + 4] == y[i + 4 - d]);
        }
        assert(added(t, u) =~= seq![XTok::PI { start: i + 2, end: n }, XTok::PIData { start: n, end: n }]);
        assert(u.subrange(0, t.len() as int) =~= t);
        assert(t2.push(XTok::PI { start: i + 2 - d, end: n - d }).push(XTok::PIData { start: n - d, end: n - d })
            =~= t2 + mv(added(t, u), d, k));
    } else {
        let dd = ws_end(x, n);
        lemma_ws_end_ge(x, n);
        lemma_pi_end_mv(x, y, lo, hi, d, dd);
        lemma_ws_end_mv(x, y, lo, hi, d, n);
        lemma_name_end_mv(x, y, lo, hi, d, i + 2);
        lemma_has_lit(x, y, lo, hi, d, n, lit_pi_end());
        assert(x[n] == y[n - d]);
        if n == i + 5 {
            assert(x[i + 2] == y[i + 2 - d]);
            assert(x[i + 3] == y[i + 3 - d]);
            assert(x[i + 4] == y[i + 4 - d]);
        }
        assert(added(t, u) =~= seq![XTok::PI { start: i + 2, end: n }, XTok::PIData { start: dd, end: e - 2 }]);
        assert(u.subrange(0, t.len() as int) =~= t);
        assert(t2.push(XTok::PI { start: i + 2 - d, end: n - d }).push(
            XTok::PIData { start: dd - d, end: e - 2 - d },
        ) =~= t2 + mv(added(t, u), d, k));
    }
}

pub proof fn lemma_cdata_end_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        cdata_end(x, i) matches Some(e) && e <= hi,
    ensures
        cdata_end(y, i - d) == Some(cdata_end(x, i).unwrap() - d),
        cdata_end(x, i).unwrap() >= i + 3,
    decreases x.len() - i,
{
    if has_lit(x, i, lit_cdata_end()) {
        lemma_has_lit(x, y, lo, hi, d, i, lit_cdata_end());
    } else {
        lemma_cdata_end_mv(x, y, lo, hi, d, i + 1);
        lemma_has_lit(x, y, lo, hi, d, i, lit_cdata_end());
    }
}

/// Character data: it also reads the byte that ends it, which must come
/// before `hi`.
pub proof fn lemma_text_end_mv(x: Seq<u8>, y: Seq<u8>, lo: int, hi: int, d: int, i: int)
    requires
        agree(x, y, lo, hi, d),
        lo <= i,
        text_end(x, i) matches Some(e) && e < hi,
    ensures
        text_end(y, i - d) == Some(text_end(x, i).unwrap() - d),
        text_end(x, i).unwrap() >= i,
        x[text_end(x, i).unwrap()] == 0x3C || x[text_end(x, i).unwrap()] == 0x26,
    decreases x.len() - i,
{
    if !(0 <= i < x.len()) || x[i] == 0x3C || x[i] == 0x26 {
        assert(x[i] == y[i - d]);
    } else {
        lemma_text_end_mv(x, y, lo, hi, d, i + 1);
        assert(x[i] == y[i - d]);
        let e = text_end(x, i).unwrap();
        // The literal `]]>` at `i` is decided by what lies before `hi`:
        // either it fits, or the byte that ends the text is inside it.
        if i + 3 <= hi {
            lemma_has_lit(x, y, lo, hi, d, i, lit_cdata_end());
        } else {
            assert(lit_cdata_end() =~= seq![0x5Du8, 0x5D, 0x3E]);
            lemma_has_lit_no(x, y, lo, hi, d, i, lit_cdata_end(), e - i);
        }
    }
}

pub proof fn lemma_text_end_ge(s: Seq<u8>, i: int)
    requires
        text_end(s, i) is Some,
    ensures
        text_end(s, i).unwrap() >= i,
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) || s[i] == 0x3C || s[i] == 0x26 {
    } else if has_lit(s, i, lit_cdata_end()) {
    } else {
        lemma_text_end_ge(s, i + 1);
    }
}

// ---------------------------------------------------------------------------
// Tags and items
// ---------------------------------------------------------------------------

/// Every attribute name in `t` lies in `a..b`.
pub open spec fn names_in(t: Seq<XTok>, a: int, b: int) -> bool {
    forall|q: int|
        #![trigger t[q]]
        0 <= q < t.len() && t[q] is Attr ==> a <= t[q]->Attr_start <= t[q]->Attr_end <= b
}

pub proof fn lemma_mv_index(t: Seq<XTok>, d: int, k: int, q: int)
    requires
        0 <= q < t.len(),
    ensures
        mv(t, d, k)[q] == mv_tok(t[q], d, k),
        mv(t, d, k).len() == t.len(),
{
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_attrs_mv(
    x: Seq<u8>,
    y: Seq<u8>,
    lo: int,
    hi: int,
    d: int,
    i: int,
    t: Seq<XTok>,
    t2: Seq<XTok>,
    env: Env,
    k: int,
)
    requires
        agree(x, y, lo, hi, d),
        lo <= i <= x.len(),
        attrs(x, i, t, env) matches Some((_, e, _)) && e <= hi,
    ensures
        attrs(x, i, t, env) matches Some((u, e, em)) && extends(t, u) && e > i && ascii_at(x, i) && names_in(
            added(t, u),
            i,
            e,
        ) && attrs(y, i - d, t2, env) == Some((t2 + mv(added(t, u), d, k), e - d, em)),
    decreases x.len() - i,
{
    let j = ws_end(x, i);
    lemma_ws_end_ws(x, i);
    let (u, e, em) = attrs(x, i, t, env).unwrap();
    if byte_is(x, j, 0x3E) {
        lemma_ws_end_mv(x, y, lo, hi, d, i);
        lemma_byte_is(x, y, lo, hi, d, j, 0x3E);
        assert(added(t, u) =~= Seq::<XTok>::empty());
        assert(u.subrange(0, t.len() as int) =~= t);
        lemma_mv_empty(d, k);
        assert(t2 + Seq::<XTok>::empty() =~= t2);
        if j > i {
            assert(is_ws(x[i]));
        }
    } else if has_lit(x, j, lit_empty_end()) {
        assert(x.subrange(j, j + 2)[0] == x[j]);
        lemma_ws_end_mv(x, y, lo, hi, d, i);
        lemma_byte_is(x, y, lo, hi, d, j, 0x3E);
        lemma_has_lit(x, y, lo, hi, d, j, lit_empty_end());
        assert(added(t, u) =~= Seq::<XTok>::empty());
        assert(u.subrange(0, t.len() as int) =~= t);
        lemma_mv_empty(d, k);
        assert(t2 + Seq::<XTok>::empty() =~= t2);
        if j > i {
            assert(is_ws(x[i]));
        }
    } else {
        assert(j != i);
        assert(is_ws(x[i]));
        let n = name_end(x, j);
        lemma_name_end(x, j);
        let v = eq_end(x, n).unwrap();
        lemma_ws_end_ge(x, n);
        lemma_ws_end_ge(x, ws_end(x, n) + 1);
        let q = att_chars(x, v + 1, x[v], Some(env)).unwrap();
        let ta = XTok::Attr { start: j, end: n };
        let tv = XTok::AttVal { start: v + 1, end: q, plain: att_plain(x, v + 1, q) };
        let t1 = t.push(ta).push(tv);
        lemma_attrs_mv(x, y, lo, hi, d, q + 1, t1, t2.push(mv_tok(ta, d, k)).push(mv_tok(tv, d, k)), env, k);
        lemma_att_chars_mv(x, y, lo, hi, d, v + 1, x[v], Some(env));
        lemma_eq_end_mv(x, y, lo, hi, d, n);
        lemma_name_end_mv(x, y, lo, hi, d, j);
        lemma_ws_end_mv(x, y, lo, hi, d, i);
        lemma_byte_is(x, y, lo, hi, d, j, 0x3E);
        lemma_has_lit(x, y, lo, hi, d, j, lit_empty_end());
        assert(x[v] == y[v - d]);
        lemma_att_plain_mv(x, y, lo, hi, d, v + 1, q);
        lemma_attrs_tapes(t, ta, tv, u, t2, d, k, i, e, q);
    }
}

/// The tapes of one more attribute, moved.
proof fn lemma_attrs_tapes(t: Seq<XTok>, ta: XTok, tv: XTok, u: Seq<XTok>, t2: Seq<XTok>, d: int, k: int, i: int, e: int, q: int)
    requires
        extends(t.push(ta).push(tv), u),
        names_in(added(t.push(ta).push(tv), u), q + 1, e),
        ta matches XTok::Attr { start, end } && i <= start <= end <= e,
        tv is AttVal,
        i <= q,
    ensures
        extends(t, u),
        t2.push(mv_tok(ta, d, k)).push(mv_tok(tv, d, k)) + mv(added(t.push(ta).push(tv), u), d, k) == t2 + mv(
            added(t, u),
            d,
            k,
        ),
        names_in(added(t, u), i, e),
{
    let t1 = t.push(ta).push(tv);
    lemma_extends_push2(t, ta, tv, u);
    let r1 = added(t1, u);
    lemma_mv_add(seq![ta, tv], r1, d, k);
    assert(mv(seq![ta, tv], d, k) =~= seq![mv_tok(ta, d, k), mv_tok(tv, d, k)]);
    assert(t2.push(mv_tok(ta, d, k)).push(mv_tok(tv, d, k)) + mv(r1, d, k) =~= t2 + mv(added(t, u), d, k));
    assert forall|p: int|
        #![trigger added(t, u)[p]]
        0 <= p < added(t, u).len() && added(t, u)[p] is Attr implies i <= added(t, u)[p]->Attr_start
        <= added(t, u)[p]->Attr_end <= e by {
        if p >= 2 {
            assert(added(t, u)[p] == r1[p - 2]);
        }
    }
}

/// `attrs_distinct` over moved tokens.
pub proof fn lemma_distinct_mv(
    x: Seq<u8>,
    y: Seq<u8>,
    lo: int,
    hi: int,
    d: int,
    t: Seq<XTok>,
    a: Seq<XTok>,
    t2: Seq<XTok>,
    k: int,
)
    requires
        agree(x, y, lo, hi, d),
        names_in(a, lo, hi),
    ensures
        attrs_distinct(y, t2 + mv(a, d, k), t2.len() as int) == attrs_distinct(x, t + a, t.len() as int),
{
    let u = t + a;
    let w = t2 + mv(a, d, k);
    assert forall|p: int| 0 <= p < a.len() implies #[trigger] w[t2.len() + p] == mv_tok(a[p], d, k) && u[t.len()
        + p] == a[p] by {
        lemma_mv_index(a, d, k, p);
    }
    assert forall|p: int| 0 <= p < a.len() && #[trigger] a[p] is Attr implies x.subrange(
        a[p]->Attr_start,
        a[p]->Attr_end,
    ) == y.subrange(a[p]->Attr_start - d, a[p]->Attr_end - d) by {
        lemma_agree_span(x, y, lo, hi, d, a[p]->Attr_start, a[p]->Attr_end);
    }
    if attrs_distinct(x, u, t.len() as int) {
        assert forall|j: int, q: int|
            t2.len() <= j < q < w.len() && #[trigger] w[j] is Attr && #[trigger] w[q] is Attr implies y.subrange(
            w[j]->Attr_start,
            w[j]->Attr_end,
        ) != y.subrange(w[q]->Attr_start, w[q]->Attr_end) by {
            let j0 = j - t2.len();
            let q0 = q - t2.len();
            assert(w[j] == mv_tok(a[j0], d, k));
            assert(w[q] == mv_tok(a[q0], d, k));
            assert(u[t.len() + j0] == a[j0]);
            assert(u[t.len() + q0] == a[q0]);
            assert(u[t.len() + j0] is Attr && u[t.len() + q0] is Attr);
        }
    }
    if attrs_distinct(y, w, t2.len() as int) {
        assert forall|j: int, q: int|
            t.len() <= j < q < u.len() && #[trigger] u[j] is Attr && #[trigger] u[q] is Attr implies x.subrange(
            u[j]->Attr_start,
            u[j]->Attr_end,
        ) != x.subrange(u[q]->Attr_start, u[q]->Attr_end) by {
            let j0 = j - t.len();
            let q0 = q - t.len();
            assert(u[j] == a[j0]);
            assert(u[q] == a[q0]);
            assert(w[t2.len() + j0] == mv_tok(a[j0], d, k));
            assert(w[t2.len() + q0] == mv_tok(a[q0], d, k));
            assert(w[t2.len() + j0] is Attr && w[t2.len() + q0] is Attr);
        }
    }
}

pub proof fn lemma_stag_mv(
    x: Seq<u8>,
    y: Seq<u8>,
    lo: int,
    hi: int,
    d: int,
    i: int,
    t: Seq<XTok>,
    t2: Seq<XTok>,
    env: Env,
    k: int,
)
    requires
        agree(x, y, lo, hi, d),
        lo <= i < x.len(),
        stag(x, i, t, env) matches Some((_, e, _)) && e <= hi,
    ensures
        stag(x, i, t, env) matches Some((u, e, em)) && extends(t, u) && e > i + 1 && name_end(x, i + 1) > i + 1
            && u.len() > t.len() && u[t.len() as int] == (XTok::STag { start: i + 1, end: name_end(x, i + 1), close: 0 })
            && stag(y, i - d, t2, env) == Some((t2 + mv(added(t, u), d, k), e - d, em)),
        name_end(y, i + 1 - d) == name_end(x, i + 1) - d,
{
    let n = name_end(x, i + 1);
    lemma_name_end(x, i + 1);
    let st = XTok::STag { start: i + 1, end: n, close: 0 };
    let t1 = t.push(st);
    let t1y = t2.push(mv_tok(st, d, k));
    let (u, e, em) = stag(x, i, t, env).unwrap();
    lemma_attrs_mv(x, y, lo, hi, d, n, t1, t1y, env, k);
    lemma_name_end_mv(x, y, lo, hi, d, i + 1);
    let r1 = added(t1, u);
    assert(u.subrange(0, t1.len() as int) =~= t1);
    assert(u =~= t1 + r1);
    lemma_agree_sub(x, y, lo, hi, d, lo, hi);
    assert(names_in(r1, lo, hi));
    lemma_distinct_mv(x, y, lo, hi, d, t1, r1, t1y, k);
    assert(u.subrange(0, t.len() as int) =~= t);
    assert(u[t.len() as int] == t1[t.len() as int]);
    assert(added(t, u) =~= seq![st] + r1);
    lemma_mv_add(seq![st], r1, d, k);
    assert(mv(seq![st], d, k) =~= seq![mv_tok(st, d, k)]);
    assert(t1y + mv(r1, d, k) =~= t2 + mv(added(t, u), d, k));
}

/// What a step that is not an end tag does to the open elements, moved.
pub open spec fn stack_mv(st: Seq<Open>, sx: Seq<Open>, st2: Seq<Open>, d: int, tl: int) -> Seq<Open> {
    if sx.len() == st.len() {
        st2
    } else {
        st2.push((sx.last().0 - d, sx.last().1 - d, tl))
    }
}

/// `item` reads `s[i..e]`, and character data also the byte after it.
pub open spec fn item_reach(s: Seq<u8>, i: int, e: int) -> int {
    if s[i] == 0x3C || s[i] == 0x26 {
        e
    } else {
        e + 1
    }
}

/// The item at `i` is an end tag.
pub open spec fn is_etag(s: Seq<u8>, i: int) -> bool {
    s[i] == 0x3C && byte_is(s, i + 1, 0x2F)
}

/// A name may not start with `!`, `?` or `/`.
pub proof fn lemma_name_start_byte(s: Seq<u8>, i: int)
    requires
        name_start_at(s, i),
    ensures
        0 <= i < s.len() && s[i] != 0x21 && s[i] != 0x3F && s[i] != 0x2F,
{
}

/// An item other than an end tag, moved: on `y` from `i - d`, with any
/// open elements `st2` and tape `t2`, it is the same item. (End tags read
/// the open elements' names: the incremental parser checks them itself.)
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_item_mv(
    x: Seq<u8>,
    y: Seq<u8>,
    lo: int,
    hi: int,
    d: int,
    i: int,
    st: Seq<Open>,
    t: Seq<XTok>,
    st2: Seq<Open>,
    t2: Seq<XTok>,
    env: Env,
)
    requires
        agree(x, y, lo, hi, d),
        lo <= i < hi,
        !is_etag(x, i),
        item(x, i, st, t, env) matches Some((_, _, e)) && item_reach(x, i, e) <= hi,
    ensures
        item(x, i, st, t, env) matches Some((sx, u, e)) && extends(t, u) && e > i && (sx == st || (sx == st.push(
            (i + 1, name_end(x, i + 1), t.len() as int),
        ))) && item(y, i - d, st2, t2, env) == Some(
            (stack_mv(st, sx, st2, d, t2.len() as int), t2 + mv(added(t, u), d, t2.len() - t.len()), e - d),
        ),
{
    let kk = t2.len() - t.len();
    let (sx, u, e) = item(x, i, st, t, env).unwrap();
    assert(x[i] == y[i - d]);
    lemma_lits_stable();
    if x[i] == 0x3C {
        if has_lit(x, i, lit_comment()) {
            lemma_comment_mv(x, y, lo, hi, d, i, t, t2, kk);
            lemma_byte_is(x, y, lo, hi, d, i + 1, 0x2F);
            lemma_has_lit(x, y, lo, hi, d, i, lit_comment());
        } else if has_lit(x, i, lit_cdata()) {
            let c = cdata_end(x, i + 9).unwrap();
            lemma_cdata_end_mv(x, y, lo, hi, d, i + 9);
            lemma_byte_is(x, y, lo, hi, d, i + 1, 0x2F);
            lemma_has_lit(x, y, lo, hi, d, i, lit_cdata());
            assert(x.subrange(i, i + 9)[2] == x[i + 2]);
            lemma_has_lit_no(x, y, lo, hi, d, i, lit_comment(), 2);
            lemma_has_cr_mv(x, y, lo, hi, d, i + 9, c - 3);
            let tk = XTok::CData { start: i + 9, end: c - 3, cr: has_cr(x, i + 9, c - 3) };
            assert(added(t, u) =~= seq![tk]);
            assert(u.subrange(0, t.len() as int) =~= t);
            assert(mv(seq![tk], d, kk) =~= seq![mv_tok(tk, d, kk)]);
            assert(t2.push(mv_tok(tk, d, kk)) =~= t2 + mv(added(t, u), d, kk));
        } else if byte_is(x, i + 1, 0x3F) {
            lemma_pi_mv(x, y, lo, hi, d, i, t, t2, kk);
            lemma_byte_is(x, y, lo, hi, d, i + 1, 0x2F);
            lemma_has_lit_no(x, y, lo, hi, d, i, lit_comment(), 1);
            lemma_has_lit_no(x, y, lo, hi, d, i, lit_cdata(), 1);
            lemma_byte_is(x, y, lo, hi, d, i + 1, 0x3F);
        } else {
            lemma_stag_mv(x, y, lo, hi, d, i, t, t2, env, kk);
            lemma_byte_is(x, y, lo, hi, d, i + 1, 0x2F);
            lemma_name_end(x, i + 1);
            lemma_name_start_byte(x, i + 1);
            lemma_has_lit_no(x, y, lo, hi, d, i, lit_comment(), 1);
            lemma_has_lit_no(x, y, lo, hi, d, i, lit_cdata(), 1);
            lemma_byte_is(x, y, lo, hi, d, i + 1, 0x3F);
            let (u0, e0, em) = stag(x, i, t, env).unwrap();
            let n = name_end(x, i + 1);
            let a0 = added(t, u0);
            let uy0 = t2 + mv(a0, d, kk);
            if em {
                // The start tag is linked to the end the empty tag adds.
                let u1 = u0.push(XTok::ETag);
                assert(u == close_at(u1, t.len() as int));
                let uy1 = uy0.push(XTok::ETag);
                let uy = close_at(uy1, t2.len() as int);
                assert(u0[t.len() as int] == (XTok::STag { start: i + 1, end: n, close: 0 }));
                assert(u.subrange(0, t.len() as int) =~= t) by {
                    assert(u0.subrange(0, t.len() as int) =~= t);
                }
                assert(uy =~= t2 + mv(added(t, u), d, kk)) by {
                    lemma_mv_index(a0, d, kk, 0);
                    assert(a0[0] == u0[t.len() as int]);
                    assert forall|p: int| 0 <= p < uy.len() implies #[trigger] uy[p] == (t2 + mv(added(t, u), d, kk))[p] by {
                        if p >= t2.len() {
                            let p0 = p - t2.len();
                            lemma_mv_index(added(t, u), d, kk, p0);
                            if p0 == 0 {
                            } else if p0 < a0.len() {
                                lemma_mv_index(a0, d, kk, p0);
                                assert(added(t, u)[p0] == u0[t.len() + p0]);
                                assert(a0[p0] == u0[t.len() + p0]);
                            } else {
                                assert(added(t, u)[p0] == XTok::ETag);
                            }
                        }
                    }
                }
            } else {
                assert(u == u0);
                assert(sx == st.push((i + 1, n, t.len() as int)));
            }
        }
    } else if x[i] == 0x26 {
        lemma_content_ref_mv(x, y, lo, hi, d, i, env);
        let (tk, c) = content_ref(x, i, env).unwrap();
        lemma_hex_end_ge(x, i + 3);
        lemma_digits_end_ge(x, i + 2);
        lemma_name_end(x, i + 1);
        assert(added(t, u) =~= seq![tk]);
        assert(u.subrange(0, t.len() as int) =~= t);
        assert(mv(seq![tk], d, kk) =~= seq![mv_tok(tk, d, kk)]);
        assert(t2.push(mv_tok(tk, d, kk)) =~= t2 + mv(added(t, u), d, kk));
    } else {
        lemma_text_end_mv(x, y, lo, hi, d, i);
        let c = text_end(x, i).unwrap();
        lemma_has_cr_mv(x, y, lo, hi, d, i, c);
        let tk = XTok::Text { start: i, end: c, cr: has_cr(x, i, c) };
        assert(added(t, u) =~= seq![tk]);
        assert(u.subrange(0, t.len() as int) =~= t);
        assert(mv(seq![tk], d, kk) =~= seq![mv_tok(tk, d, kk)]);
        assert(t2.push(mv_tok(tk, d, kk)) =~= t2 + mv(added(t, u), d, kk));
        assert(x[c] == 0x3C || x[c] == 0x26);
        assert(c > i);
    }
}

pub proof fn lemma_lits_stable()
    ensures
        lit_comment() == seq![0x3Cu8, 0x21, 0x2D, 0x2D],
        lit_cdata() == seq![0x3Cu8, 0x21, 0x5B, 0x43, 0x44, 0x41, 0x54, 0x41, 0x5B],
        lit_pi_end() == seq![0x3Fu8, 0x3E],
        lit_empty_end() == seq![0x2Fu8, 0x3E],
        lit_cdata_end() == seq![0x5Du8, 0x5D, 0x3E],
{
}

} // verus!

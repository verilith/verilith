//! What the spec reads, for the prolog: the XML declaration, `Misc`, and
//! the document type declaration with its internal subset and what it
//! leaves for the content. The prolog is read in place (it stays at the
//! start of the text the incremental parser keeps), so these are stated
//! for an input `y` that has the bytes of `x` before `hi` where `x` has
//! them: each function that succeeds on `x` and reads only bytes before
//! `hi` gives the same result on `y`.
//!
//! Proof only: nothing here runs.
use crate::chars::*;
use crate::spec::*;
use crate::stable::*;
#[cfg(verus_keep_ghost)]
use verilith_core::num::{digits_end, is_digit};
use vstd::prelude::*;

verus! {

/// `y` has `x`'s bytes before `hi`, in place.
pub open spec fn ag(x: Seq<u8>, y: Seq<u8>, hi: int) -> bool {
    agree(x, y, 0, hi, 0)
}

/// The literal is not at `i` in either input: its first byte differs.
pub proof fn lemma_not_lit(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, lit: Seq<u8>)
    requires
        ag(x, y, hi),
        0 <= i < hi,
        lit.len() > 0,
        x[i] != lit[0],
    ensures
        !has_lit(x, i, lit),
        !has_lit(y, i, lit),
{
    lemma_has_lit_no(x, y, 0, hi, 0, i, lit, 0);
}

pub proof fn lemma_ws_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int)
    requires
        ag(x, y, hi),
        0 <= i,
        ws_end(x, i) < hi,
    ensures
        ws_end(y, i) == ws_end(x, i),
        ws_end(x, i) >= i,
{
    lemma_ws_end_mv(x, y, 0, hi, 0, i);
    lemma_ws_end_ge(x, i);
}

pub proof fn lemma_lit_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, lit: Seq<u8>)
    requires
        ag(x, y, hi),
        0 <= i,
        i + lit.len() <= hi,
    ensures
        has_lit(y, i, lit) == has_lit(x, i, lit),
{
    lemma_has_lit(x, y, 0, hi, 0, i, lit);
}

pub proof fn lemma_byte_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int)
    requires
        ag(x, y, hi),
        0 <= i < hi,
    ensures
        y[i] == x[i],
        i < y.len(),
{
    assert(x[i] == y[i - 0]);
}

pub proof fn lemma_name_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int)
    requires
        ag(x, y, hi),
        0 <= i <= x.len(),
        name_end(x, i) < hi,
        x[name_end(x, i)] < 0x80,
    ensures
        name_end(y, i) == name_end(x, i),
        i <= name_end(x, i),
{
    lemma_name_end_mv(x, y, 0, hi, 0, i);
    lemma_name_end(x, i);
}

pub proof fn lemma_eq_end_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int)
    requires
        ag(x, y, hi),
        0 <= i <= x.len(),
        eq_end(x, i) matches Some(v) && v < hi,
    ensures
        eq_end(y, i) == eq_end(x, i),
        ascii_at(x, i),
        eq_end(x, i).unwrap() > i,
{
    lemma_eq_end_mv(x, y, 0, hi, 0, i);
    lemma_ws_end_ge(x, i);
    lemma_ws_end_ge(x, ws_end(x, i) + 1);
}

pub proof fn lemma_span_eq(x: Seq<u8>, y: Seq<u8>, hi: int, a: int, b: int)
    requires
        ag(x, y, hi),
        0 <= a <= b <= hi,
    ensures
        y.subrange(a, b) == x.subrange(a, b),
{
    lemma_agree_span(x, y, 0, hi, 0, a, b);
}

// ---------------------------------------------------------------------------
// The XML declaration
// ---------------------------------------------------------------------------

pub proof fn lemma_version_info_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int)
    requires
        ag(x, y, hi),
        0 <= i,
        version_info(x, i) matches Some((e, _, _)) && e <= hi,
    ensures
        version_info(y, i) == version_info(x, i),
        version_info(x, i).unwrap().0 > i,
{
    let j = ws_end(x, i);
    lemma_ws_end_ge(x, i);
    let k = eq_end(x, j + 7).unwrap();
    lemma_ws_end_ge(x, j + 7);
    lemma_ws_end_ge(x, ws_end(x, j + 7) + 1);
    let dd = digits_end(x, k + 3);
    lemma_digits_end_ge(x, k + 3);
    lemma_ws_eq(x, y, hi, i);
    lemma_lit_eq(x, y, hi, j, lit_version());
    lemma_eq_end_eq(x, y, hi, j + 7);
    lemma_byte_eq(x, y, hi, k);
    lemma_byte_eq(x, y, hi, k + 1);
    lemma_byte_eq(x, y, hi, k + 2);
    lemma_digits_end_mv(x, y, 0, hi, 0, k + 3);
    lemma_byte_eq(x, y, hi, dd);
}

pub proof fn lemma_enc_rest_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int)
    requires
        ag(x, y, hi),
        0 <= i,
        enc_rest(x, i) < hi,
    ensures
        enc_rest(y, i) == enc_rest(x, i),
        enc_rest(x, i) >= i,
    decreases x.len() - i,
{
    if 0 <= i < x.len() && enc_char(x[i]) {
        lemma_enc_rest_eq(x, y, hi, i + 1);
        lemma_byte_eq(x, y, hi, i);
    } else {
        lemma_byte_eq(x, y, hi, i);
    }
}

pub proof fn lemma_enc_span_eq(x: Seq<u8>, y: Seq<u8>, hi: int, j: int)
    requires
        ag(x, y, hi),
        0 <= j,
        j + 8 <= x.len(),
        enc_span(x, j) matches Some((e, _, _)) && e <= hi,
    ensures
        enc_span(y, j) == enc_span(x, j),
        enc_span(x, j) matches Some((e, a, b)) && j < a <= b < e && e > j + 8,
{
    let k = eq_end(x, j + 8).unwrap();
    lemma_ws_end_ge(x, j + 8);
    lemma_ws_end_ge(x, ws_end(x, j + 8) + 1);
    let n = enc_rest(x, k + 2);
    lemma_enc_rest_eq(x, y, hi, k + 2);
    lemma_eq_end_eq(x, y, hi, j + 8);
    lemma_byte_eq(x, y, hi, k);
    lemma_byte_eq(x, y, hi, k + 1);
    lemma_byte_eq(x, y, hi, n);
}

pub proof fn lemma_ci_eq_eq(x: Seq<u8>, y: Seq<u8>, hi: int, a: int, b: int, lit: Seq<u8>)
    requires
        ag(x, y, hi),
        0 <= a <= b <= hi,
    ensures
        ci_eq(y, a, b, lit) == ci_eq(x, a, b, lit),
{
    if b - a == lit.len() {
        assert forall|k: int| 0 <= k < lit.len() implies #[trigger] x[a + k] == y[a + k] by {
            lemma_byte_eq(x, y, hi, a + k);
        }
        if ci_eq(x, a, b, lit) {
            assert forall|k: int| 0 <= k < lit.len() implies lower(#[trigger] y[a + k]) == lower(lit[k]) by {
                assert(x[a + k] == y[a + k]);
            }
        }
        if ci_eq(y, a, b, lit) {
            assert forall|k: int| 0 <= k < lit.len() implies lower(#[trigger] x[a + k]) == lower(lit[k]) by {
                assert(x[a + k] == y[a + k]);
            }
        }
    }
}

pub proof fn lemma_encoding_decl_eq(x: Seq<u8>, y: Seq<u8>, hi: int, j: int, enc: Enc)
    requires
        ag(x, y, hi),
        0 <= j,
        j + 8 <= x.len(),
        encoding_decl(x, j, enc) matches Some((e, _, _)) && e <= hi,
    ensures
        encoding_decl(y, j, enc) == encoding_decl(x, j, enc),
        encoding_decl(x, j, enc).unwrap().0 > j + 8,
{
    lemma_enc_span_eq(x, y, hi, j);
    let (e, a, b) = enc_span(x, j).unwrap();
    lemma_ci_eq_eq(x, y, hi, a, b, lit_utf8());
    lemma_ci_eq_eq(x, y, hi, a, b, lit_utf16());
    lemma_ci_eq_eq(x, y, hi, a, b, lit_latin1());
    lemma_ci_eq_eq(x, y, hi, a, b, lit_ascii());
}

pub proof fn lemma_sd_decl_eq(x: Seq<u8>, y: Seq<u8>, hi: int, j: int)
    requires
        ag(x, y, hi),
        0 <= j,
        j + 10 <= x.len(),
        sd_decl(x, j) matches Some((e, _)) && e <= hi,
    ensures
        sd_decl(y, j) == sd_decl(x, j),
        sd_decl(x, j).unwrap().0 > j + 10,
{
    let k = eq_end(x, j + 10).unwrap();
    lemma_ws_end_ge(x, j + 10);
    lemma_ws_end_ge(x, ws_end(x, j + 10) + 1);
    lemma_eq_end_eq(x, y, hi, j + 10);
    lemma_byte_eq(x, y, hi, k);
    assert(lit_yes() =~= seq![0x79u8, 0x65, 0x73]);
    assert(lit_no() =~= seq![0x6Eu8, 0x6F]);
    if has_lit(x, k + 1, lit_yes()) && byte_is(x, k + 4, x[k]) {
        lemma_lit_eq(x, y, hi, k + 1, lit_yes());
        lemma_byte_eq(x, y, hi, k + 4);
    } else {
        // `no`: its first byte rules out `yes`.
        lemma_lit_eq(x, y, hi, k + 1, lit_no());
        lemma_byte_eq(x, y, hi, k + 3);
        assert(x.subrange(k + 1, k + 3)[0] == x[k + 1]);
        lemma_not_lit(x, y, hi, k + 1, lit_yes());
    }
}

/// After the version (and encoding, and standalone declaration), the
/// declaration ends with `?>`: where an optional part is absent, the byte
/// there is `?`, which decides that it is absent.
pub proof fn lemma_xmldecl_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, enc: Enc)
    requires
        ag(x, y, hi),
        0 <= i,
        i + 5 <= x.len(),
        xmldecl(x, i, enc) matches Some((_, e, _)) && e <= hi,
    ensures
        xmldecl(y, i, enc) == xmldecl(x, i, enc),
        xmldecl(x, i, enc).unwrap().1 > i + 5,
        version_info(x, i + 5) matches Some((v, _, _)) && v <= xmldecl(x, i, enc).unwrap().1 && ws_end(x, v)
            < xmldecl(x, i, enc).unwrap().1 && ws_end(x, v) >= v && ((ws_end(x, v) > v && has_lit(
            x,
            ws_end(x, v),
            lit_encoding(),
        )) ==> (enc_span(x, ws_end(x, v)) matches Some((e2, _, _)) && e2 <= xmldecl(x, i, enc).unwrap().1
            && ws_end(x, v) + 8 <= x.len())),
{
    lemma_lits_stable();
    assert(lit_encoding() =~= seq![0x65u8, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67]);
    assert(lit_standalone() =~= seq![0x73u8, 0x74, 0x61, 0x6E, 0x64, 0x61, 0x6C, 0x6F, 0x6E, 0x65]);
    let (v, va, vb) = version_info(x, i + 5).unwrap();
    let j = ws_end(x, v);
    lemma_ws_end_ge(x, v);
    let er = if j > v && has_lit(x, j, lit_encoding()) {
        encoding_decl(x, j, enc)
    } else {
        Some((v, -1, -1))
    };
    let (e, ea, eb) = er.unwrap();
    let k = ws_end(x, e);
    lemma_ws_end_ge(x, e);
    let sr = if k > e && has_lit(x, k, lit_standalone()) {
        sd_decl(x, k)
    } else {
        Some((e, 0))
    };
    let (dd, sd) = sr.unwrap();
    let m = ws_end(x, dd);
    lemma_ws_end_ge(x, dd);
    assert(has_lit(x, m, lit_pi_end()));
    assert(x.subrange(m, m + 2)[0] == x[m]);
    lemma_ws_eq(x, y, hi, dd);
    lemma_lit_eq(x, y, hi, m, lit_pi_end());
    if k > e && has_lit(x, k, lit_standalone()) {
        assert(x.subrange(k, k + 10).len() == 10);
        lemma_sd_decl_eq(x, y, hi, k);
        lemma_lit_eq(x, y, hi, k, lit_standalone());
    } else if k > e {
        // No standalone declaration: `m == k` and `x[k]` is `?`.
        lemma_not_lit(x, y, hi, k, lit_standalone());
    }
    lemma_ws_eq(x, y, hi, e);
    if j > v && has_lit(x, j, lit_encoding()) {
        assert(x.subrange(j, j + 8).len() == 8);
        lemma_encoding_decl_eq(x, y, hi, j, enc);
        lemma_lit_eq(x, y, hi, j, lit_encoding());
    } else if j > v {
        lemma_not_lit(x, y, hi, j, lit_encoding());
    }
    lemma_ws_eq(x, y, hi, v);
    lemma_version_info_eq(x, y, hi, i + 5);
}

pub proof fn lemma_bom_end_eq(x: Seq<u8>, y: Seq<u8>, hi: int)
    requires
        ag(x, y, hi),
        hi >= 3 || (hi >= 1 && x[0] != 0xEF),
    ensures
        bom_end(y) == bom_end(x),
{
    if hi >= 3 {
        lemma_lit_eq(x, y, hi, 0, seq![0xEFu8, 0xBB, 0xBF]);
    } else {
        lemma_not_lit(x, y, hi, 0, seq![0xEFu8, 0xBB, 0xBF]);
    }
}

// ---------------------------------------------------------------------------
// Misc
// ---------------------------------------------------------------------------

/// One `Misc` step at `i` (after white space): a comment or a processing
/// instruction, or none.
pub open spec fn misc_tail_ok(x: Seq<u8>, j: int, hi: int) -> bool {
    j + 4 <= hi || (j < hi && x[j] != 0x3C) || (j + 1 < hi && x[j] == 0x3C && x[j + 1] != 0x21 && x[j + 1] != 0x3F)
}

/// `Misc*` that ends at `j`, where what follows is decided before `hi`
/// (four bytes are enough; fewer, where they already rule out a comment
/// and a processing instruction).
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn lemma_misc_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, t: Seq<XTok>)
    requires
        ag(x, y, hi),
        0 <= i,
        misc(x, i, t) matches Some((_, j)) && misc_tail_ok(x, j, hi),
    ensures
        misc(y, i, t) == misc(x, i, t),
        misc(x, i, t) matches Some((u, j)) && j >= i && extends(t, u),
    decreases x.len() - i,
{
    lemma_lits_stable();
    let j = ws_end(x, i);
    lemma_ws_end_ge(x, i);
    if has_lit(x, j, lit_comment()) {
        let (t1, e) = comment(x, j, t).unwrap();
        lemma_misc_eq(x, y, hi, e, t1);
        let (u, f) = misc(x, e, t1).unwrap();
        lemma_misc_end_ge(x, e, t1);
        lemma_comment_mv(x, y, 0, hi, 0, j, t, t, 0);
        lemma_mv_zero(added(t, t1));
        assert(t + added(t, t1) =~= t1);
        lemma_lit_eq(x, y, hi, j, lit_comment());
        lemma_ws_eq(x, y, hi, i);
        assert(u.subrange(0, t.len() as int) =~= t1.subrange(0, t.len() as int));
    } else if has_lit(x, j, lit_pi()) {
        let (t1, e) = pi(x, j, t).unwrap();
        lemma_misc_eq(x, y, hi, e, t1);
        lemma_misc_end_ge(x, e, t1);
        let (u, f) = misc(x, e, t1).unwrap();
        lemma_pi_mv(x, y, 0, hi, 0, j, t, t, 0);
        lemma_mv_zero(added(t, t1));
        assert(t + added(t, t1) =~= t1);
        assert(x.subrange(j, j + 2)[1] == x[j + 1]);
        lemma_lit_eq(x, y, hi, j, lit_pi());
        lemma_not_lit_at(x, y, hi, j, lit_comment(), 2);
        lemma_ws_eq(x, y, hi, i);
        assert(u.subrange(0, t.len() as int) =~= t1.subrange(0, t.len() as int));
    } else {
        assert(t.subrange(0, t.len() as int) =~= t);
        lemma_ws_eq(x, y, hi, i);
        if j + 4 <= hi {
            lemma_lit_eq(x, y, hi, j, lit_comment());
            lemma_lit_eq(x, y, hi, j, lit_pi());
        } else if x[j] != 0x3C {
            lemma_not_lit(x, y, hi, j, lit_comment());
            lemma_not_lit(x, y, hi, j, lit_pi());
        } else {
            lemma_not_lit_at(x, y, hi, j, lit_comment(), 1);
            lemma_not_lit_at(x, y, hi, j, lit_pi(), 1);
        }
    }
}

pub proof fn lemma_not_lit_at(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, lit: Seq<u8>, k: int)
    requires
        ag(x, y, hi),
        0 <= i,
        0 <= k < lit.len(),
        i + k < hi,
        x[i + k] != lit[k],
    ensures
        !has_lit(x, i, lit),
        !has_lit(y, i, lit),
{
    lemma_has_lit_no(x, y, 0, hi, 0, i, lit, k);
}

pub proof fn lemma_misc_end_ge(s: Seq<u8>, i: int, t: Seq<XTok>)
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
        lemma_misc_end_ge(s, e, t1);
    } else if has_lit(s, j, lit_pi()) {
        let (t1, e) = pi(s, j, t).unwrap();
        lemma_misc_end_ge(s, e, t1);
    }
}

// ---------------------------------------------------------------------------
// Literals and external identifiers
// ---------------------------------------------------------------------------

pub proof fn lemma_lit_end_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, q: u8)
    requires
        ag(x, y, hi),
        0 <= i,
        lit_end(x, i, q) matches Some(e) && e <= hi,
    ensures
        lit_end(y, i, q) == lit_end(x, i, q),
        lit_end(x, i, q).unwrap() > i,
    decreases x.len() - i,
{
    if x[i] == q {
        lemma_byte_eq(x, y, hi, i);
    } else {
        lemma_lit_end_eq(x, y, hi, i + 1, q);
        lemma_byte_eq(x, y, hi, i);
    }
}

pub proof fn lemma_pubid_end_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, q: u8)
    requires
        ag(x, y, hi),
        0 <= i,
        pubid_end(x, i, q) matches Some(e) && e <= hi,
    ensures
        pubid_end(y, i, q) == pubid_end(x, i, q),
        pubid_end(x, i, q).unwrap() > i,
    decreases x.len() - i,
{
    if x[i] == q {
        lemma_byte_eq(x, y, hi, i);
    } else {
        lemma_pubid_end_eq(x, y, hi, i + 1, q);
        lemma_byte_eq(x, y, hi, i);
    }
}

pub proof fn lemma_sys_lit_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int)
    requires
        ag(x, y, hi),
        0 <= i,
        sys_lit(x, i) matches Some(e) && e <= hi,
    ensures
        sys_lit(y, i) == sys_lit(x, i),
        sys_lit(x, i).unwrap() > i + 1,
{
    lemma_lit_end_eq(x, y, hi, i + 1, x[i]);
    lemma_byte_eq(x, y, hi, i);
}

pub proof fn lemma_pubid_lit_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int)
    requires
        ag(x, y, hi),
        0 <= i,
        pubid_lit(x, i) matches Some(e) && e <= hi,
    ensures
        pubid_lit(y, i) == pubid_lit(x, i),
        pubid_lit(x, i).unwrap() > i + 1,
{
    lemma_pubid_end_eq(x, y, hi, i + 1, x[i]);
    lemma_byte_eq(x, y, hi, i);
}

/// The tokens added have no attribute defaults.
pub open spec fn no_dflt(t: Seq<XTok>) -> bool {
    forall|k: int| 0 <= k < t.len() ==> !(#[trigger] t[k] is AttDefault)
}

pub proof fn lemma_external_id_eq(x: Seq<u8>, y: Seq<u8>, hi: int, k: int, t: Seq<XTok>)
    requires
        ag(x, y, hi),
        0 <= k,
        external_id(x, k, t) matches Some((_, e)) && e <= hi,
    ensures
        external_id(y, k, t) == external_id(x, k, t),
        external_id(x, k, t) matches Some((u, e)) && e > k + 6 && extends(t, u) && no_dflt(added(t, u)),
{
    assert(lit_system() =~= seq![0x53u8, 0x59, 0x53, 0x54, 0x45, 0x4D]);
    assert(lit_public() =~= seq![0x50u8, 0x55, 0x42, 0x4C, 0x49, 0x43]);
    let (u, e) = external_id(x, k, t).unwrap();
    if has_lit(x, k, lit_system()) {
        let j = ws_end(x, k + 6);
        lemma_ws_end_ge(x, k + 6);
        lemma_sys_lit_eq(x, y, hi, j);
        lemma_ws_eq(x, y, hi, k + 6);
        lemma_lit_eq(x, y, hi, k, lit_system());
        assert(u.subrange(0, t.len() as int) =~= t);
        assert(added(t, u) =~= seq![XTok::SysId { start: j + 1, end: e - 1 }]);
    } else {
        let j = ws_end(x, k + 6);
        lemma_ws_end_ge(x, k + 6);
        let e1 = pubid_lit(x, j).unwrap();
        let m = ws_end(x, e1);
        lemma_ws_end_ge(x, e1);
        lemma_sys_lit_eq(x, y, hi, m);
        lemma_pubid_lit_eq(x, y, hi, j);
        lemma_ws_eq(x, y, hi, e1);
        lemma_ws_eq(x, y, hi, k + 6);
        assert(x.subrange(k, k + 6)[0] == x[k]);
        lemma_not_lit(x, y, hi, k, lit_system());
        lemma_lit_eq(x, y, hi, k, lit_public());
        assert(u.subrange(0, t.len() as int) =~= t);
        assert(added(t, u) =~= seq![XTok::PubId { start: j + 1, end: e1 - 1 }, XTok::SysId { start: m + 1, end: e - 1 }]);
    }
}

// ---------------------------------------------------------------------------
// Element type declarations
// ---------------------------------------------------------------------------

pub proof fn lemma_quant_end_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int)
    requires
        ag(x, y, hi),
        0 <= i < hi,
    ensures
        quant_end(y, i) == quant_end(x, i),
        i <= quant_end(x, i) <= i + 1,
{
    lemma_byte_eq(x, y, hi, i);
}

/// A content model ends with `)` and perhaps a quantifier: whether one
/// follows is the byte after the `)`, so the model must end before `hi`
/// (the declaration's `>` is after it).
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn lemma_cmodel_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, st: Seq<u8>, after: bool)
    requires
        ag(x, y, hi),
        0 <= i,
        cmodel(x, i, st, after) matches Some(e) && e < hi,
    ensures
        cmodel(y, i, st, after) == cmodel(x, i, st, after),
        cmodel(x, i, st, after).unwrap() > i,
    decreases x.len() - i,
{
    let j = ws_end(x, i);
    lemma_ws_end_ge(x, i);
    if !after {
        if x[j] == 0x28 {
            lemma_cmodel_eq(x, y, hi, j + 1, st.push(0), false);
            lemma_ws_eq(x, y, hi, i);
            lemma_byte_eq(x, y, hi, j);
        } else {
            let k = name_end(x, j);
            lemma_name_end(x, j);
            let q = quant_end(x, k);
            lemma_cmodel_eq(x, y, hi, q, st, true);
            lemma_cmodel_after_ascii(x, q, st);
            lemma_quant_end_eq(x, y, hi, k);
            lemma_name_eq(x, y, hi, j);
            lemma_ws_eq(x, y, hi, i);
            lemma_byte_eq(x, y, hi, j);
        }
    } else if x[j] == 0x29 {
        let k = quant_end(x, j + 1);
        if st.len() != 1 {
            lemma_cmodel_eq(x, y, hi, k, st.drop_last(), true);
        }
        lemma_quant_end_eq(x, y, hi, j + 1);
        lemma_ws_eq(x, y, hi, i);
        lemma_byte_eq(x, y, hi, j);
    } else {
        lemma_cmodel_eq(x, y, hi, j + 1, st.drop_last().push(x[j]), false);
        lemma_ws_eq(x, y, hi, i);
        lemma_byte_eq(x, y, hi, j);
    }
}

/// Where a content particle has ended, the model goes on with white space,
/// `)`, `|` or `,`.
proof fn lemma_cmodel_after_ascii(x: Seq<u8>, i: int, st: Seq<u8>)
    requires
        cmodel(x, i, st, true) is Some,
    ensures
        0 <= i < x.len() && x[i] < 0x80,
{
    let j = ws_end(x, i);
    lemma_ws_end_ws(x, i);
    if j > i {
        assert(is_ws(x[i]));
    }
}

pub proof fn lemma_mixed_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, names: bool)
    requires
        ag(x, y, hi),
        0 <= i,
        mixed(x, i, names) matches Some(e) && e < hi,
    ensures
        mixed(y, i, names) == mixed(x, i, names),
        mixed(x, i, names).unwrap() > i,
    decreases x.len() - i,
{
    let j = ws_end(x, i);
    lemma_ws_end_ge(x, i);
    if byte_is(x, j, 0x29) {
        lemma_byte_is(x, y, 0, hi, 0, j + 1, 0x2A);
        lemma_byte_is(x, y, 0, hi, 0, j, 0x29);
        lemma_ws_eq(x, y, hi, i);
    } else {
        let k = ws_end(x, j + 1);
        lemma_ws_end_ge(x, j + 1);
        let n = name_end(x, k);
        lemma_name_end(x, k);
        lemma_mixed_eq(x, y, hi, n, true);
        lemma_mixed_ascii(x, n, true);
        lemma_name_eq(x, y, hi, k);
        lemma_ws_eq(x, y, hi, j + 1);
        lemma_byte_is(x, y, 0, hi, 0, j, 0x29);
        lemma_byte_is(x, y, 0, hi, 0, j, 0x7C);
        lemma_ws_eq(x, y, hi, i);
    }
}

proof fn lemma_mixed_ascii(x: Seq<u8>, i: int, names: bool)
    requires
        mixed(x, i, names) is Some,
    ensures
        0 <= i < x.len() && x[i] < 0x80,
{
    let j = ws_end(x, i);
    lemma_ws_end_ws(x, i);
    if j > i {
        assert(is_ws(x[i]));
    }
}

pub proof fn lemma_contentspec_eq(x: Seq<u8>, y: Seq<u8>, hi: int, b: int)
    requires
        ag(x, y, hi),
        0 <= b,
        contentspec(x, b) matches Some(e) && e < hi,
    ensures
        contentspec(y, b) == contentspec(x, b),
        contentspec(x, b).unwrap() > b,
{
    assert(lit_empty() =~= seq![0x45u8, 0x4D, 0x50, 0x54, 0x59]);
    assert(lit_any() =~= seq![0x41u8, 0x4E, 0x59]);
    assert(lit_pcdata() =~= seq![0x23u8, 0x50, 0x43, 0x44, 0x41, 0x54, 0x41]);
    if has_lit(x, b, lit_empty()) {
        lemma_lit_eq(x, y, hi, b, lit_empty());
    } else if has_lit(x, b, lit_any()) {
        assert(x.subrange(b, b + 3)[0] == x[b]);
        lemma_not_lit(x, y, hi, b, lit_empty());
        lemma_lit_eq(x, y, hi, b, lit_any());
    } else {
        let k = ws_end(x, b + 1);
        lemma_ws_end_ge(x, b + 1);
        if has_lit(x, k, lit_pcdata()) {
            lemma_mixed_eq(x, y, hi, k + 7, false);
            lemma_lit_eq(x, y, hi, k, lit_pcdata());
        } else {
            lemma_cmodel_eq(x, y, hi, b, Seq::empty(), false);
            // A model's first particle is a name or `(`, never `#`.
            lemma_cmodel_first(x, b);
            lemma_not_lit(x, y, hi, k, lit_pcdata());
        }
        lemma_ws_eq(x, y, hi, b + 1);
        lemma_byte_eq(x, y, hi, b);
        lemma_not_lit(x, y, hi, b, lit_empty());
        lemma_not_lit(x, y, hi, b, lit_any());
    }
}

/// `children` at `b` (`x[b]` is `(`): the first particle, after white
/// space, is not `#`, and comes before the end.
proof fn lemma_cmodel_first(x: Seq<u8>, b: int)
    requires
        0 <= b < x.len(),
        x[b] == 0x28,
        cmodel(x, b, Seq::empty(), false) is Some,
    ensures
        ws_end(x, b + 1) < cmodel(x, b, Seq::empty(), false).unwrap(),
        x[ws_end(x, b + 1)] != 0x23,
{
    lemma_ws_end_ws(x, b);
    assert(ws_end(x, b) == b);
    let k = ws_end(x, b + 1);
    lemma_ws_end_ws(x, b + 1);
    lemma_cmodel_eq_end(x, b + 1, seq![0u8], false);
    if x[k] == 0x28 {
    } else {
        lemma_name_end(x, k);
    }
}

/// Where a model goes on from `i`, the first byte that is not white space
/// is before its end.
proof fn lemma_cmodel_eq_end(x: Seq<u8>, i: int, st: Seq<u8>, after: bool)
    requires
        0 <= i,
        cmodel(x, i, st, after) is Some,
    ensures
        ws_end(x, i) < cmodel(x, i, st, after).unwrap(),
    decreases x.len() - i,
{
    let j = ws_end(x, i);
    lemma_ws_end_ge(x, i);
    if !after {
        if x[j] == 0x28 {
            lemma_cmodel_eq_end(x, j + 1, st.push(0), false);
            lemma_ws_end_ge(x, j + 1);
        } else {
            let k = name_end(x, j);
            lemma_name_end(x, j);
            lemma_cmodel_eq_end(x, quant_end(x, k), st, true);
            lemma_ws_end_ge(x, quant_end(x, k));
        }
    } else if x[j] == 0x29 {
        let k = quant_end(x, j + 1);
        if st.len() != 1 {
            lemma_cmodel_eq_end(x, k, st.drop_last(), true);
            lemma_ws_end_ge(x, k);
        }
    } else {
        lemma_cmodel_eq_end(x, j + 1, st.drop_last().push(x[j]), false);
        lemma_ws_end_ge(x, j + 1);
    }
}

pub proof fn lemma_element_decl_eq(x: Seq<u8>, y: Seq<u8>, hi: int, j: int, t: Seq<XTok>)
    requires
        ag(x, y, hi),
        0 <= j,
        element_decl(x, j, t) matches Some((_, e)) && e <= hi,
    ensures
        element_decl(y, j, t) == element_decl(x, j, t),
        element_decl(x, j, t) matches Some((u, e)) && e > j + 9 && extends(t, u) && no_dflt(added(t, u)),
{
    let a = ws_end(x, j + 9);
    lemma_ws_end_ge(x, j + 9);
    let n = name_end(x, a);
    lemma_name_end(x, a);
    let b = ws_end(x, n);
    lemma_ws_end_ws(x, n);
    let c = contentspec(x, b).unwrap();
    let f = ws_end(x, c);
    lemma_ws_end_ge(x, c);
    lemma_contentspec_eq(x, y, hi, b);
    lemma_ws_eq(x, y, hi, c);
    lemma_byte_eq(x, y, hi, f);
    lemma_ws_eq(x, y, hi, n);
    lemma_name_eq(x, y, hi, a);
    lemma_ws_eq(x, y, hi, j + 9);
    let (u, e) = element_decl(x, j, t).unwrap();
    assert(u.subrange(0, t.len() as int) =~= t);
    assert(added(t, u) =~= seq![XTok::ElementDecl { start: a, end: n }]);
}

// ---------------------------------------------------------------------------
// Attribute-list declarations
// ---------------------------------------------------------------------------

pub proof fn lemma_alt_list_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, nm: bool)
    requires
        ag(x, y, hi),
        0 <= i,
        alt_list(x, i, nm) matches Some(e) && e <= hi,
    ensures
        alt_list(y, i, nm) == alt_list(x, i, nm),
        alt_list(x, i, nm).unwrap() > i,
    decreases x.len() - i,
{
    let j = ws_end(x, i);
    lemma_ws_end_ge(x, i);
    let n = if nm {
        nmtoken_end(x, j)
    } else {
        name_end(x, j)
    };
    lemma_name_rest(x, j);
    lemma_name_end(x, j);
    let k = ws_end(x, n);
    lemma_ws_end_ws(x, n);
    if byte_is(x, k, 0x29) {
    } else {
        lemma_alt_list_eq(x, y, hi, k + 1, nm);
    }
    lemma_byte_is(x, y, 0, hi, 0, k, 0x29);
    lemma_byte_is(x, y, 0, hi, 0, k, 0x7C);
    lemma_ws_eq(x, y, hi, n);
    if k > n {
        assert(is_ws(x[n]));
    }
    if nm {
        lemma_name_rest_mv(x, y, 0, hi, 0, j);
    } else {
        lemma_name_eq(x, y, hi, j);
    }
    lemma_ws_eq(x, y, hi, i);
}

/// An attribute type is followed by white space (at `e`, before `hi`),
/// which decides each keyword that does not match.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_att_type_eq(x: Seq<u8>, y: Seq<u8>, hi: int, k: int)
    requires
        ag(x, y, hi),
        0 <= k,
        att_type(x, k) matches Some((e, _)) && e < hi && is_ws(x[e]),
    ensures
        att_type(y, k) == att_type(x, k),
        att_type(x, k).unwrap().0 > k,
{
    assert(lit_cdata_ty() =~= seq![0x43u8, 0x44, 0x41, 0x54, 0x41]);
    assert(lit_idrefs() =~= seq![0x49u8, 0x44, 0x52, 0x45, 0x46, 0x53]);
    assert(lit_idref() =~= seq![0x49u8, 0x44, 0x52, 0x45, 0x46]);
    assert(lit_id() =~= seq![0x49u8, 0x44]);
    assert(lit_entities() =~= seq![0x45u8, 0x4E, 0x54, 0x49, 0x54, 0x49, 0x45, 0x53]);
    assert(lit_entity_ty() =~= seq![0x45u8, 0x4E, 0x54, 0x49, 0x54, 0x59]);
    assert(lit_nmtokens() =~= seq![0x4Eu8, 0x4D, 0x54, 0x4F, 0x4B, 0x45, 0x4E, 0x53]);
    assert(lit_nmtoken() =~= seq![0x4Eu8, 0x4D, 0x54, 0x4F, 0x4B, 0x45, 0x4E]);
    assert(lit_notation_ty() =~= seq![0x4Eu8, 0x4F, 0x54, 0x41, 0x54, 0x49, 0x4F, 0x4E]);
    let (e, ty) = att_type(x, k).unwrap();
    if has_lit(x, k, lit_cdata_ty()) {
        lemma_lit_eq(x, y, hi, k, lit_cdata_ty());
    } else if has_lit(x, k, lit_idrefs()) {
        assert(x.subrange(k, k + 6)[0] == x[k]);
        lemma_not_lit(x, y, hi, k, lit_cdata_ty());
        lemma_lit_eq(x, y, hi, k, lit_idrefs());
    } else if has_lit(x, k, lit_idref()) {
        assert(x.subrange(k, k + 5)[0] == x[k]);
        lemma_not_lit(x, y, hi, k, lit_cdata_ty());
        lemma_not_lit_at(x, y, hi, k, lit_idrefs(), 5);
        lemma_lit_eq(x, y, hi, k, lit_idref());
    } else if has_lit(x, k, lit_id()) {
        assert(x.subrange(k, k + 2)[0] == x[k]);
        lemma_not_lit(x, y, hi, k, lit_cdata_ty());
        lemma_not_lit_at(x, y, hi, k, lit_idrefs(), 2);
        lemma_not_lit_at(x, y, hi, k, lit_idref(), 2);
        lemma_lit_eq(x, y, hi, k, lit_id());
    } else if has_lit(x, k, lit_entities()) {
        assert(x.subrange(k, k + 8)[0] == x[k]);
        lemma_not_lit(x, y, hi, k, lit_cdata_ty());
        lemma_not_lit(x, y, hi, k, lit_idrefs());
        lemma_not_lit(x, y, hi, k, lit_idref());
        lemma_not_lit(x, y, hi, k, lit_id());
        lemma_lit_eq(x, y, hi, k, lit_entities());
    } else if has_lit(x, k, lit_entity_ty()) {
        assert(x.subrange(k, k + 6)[0] == x[k]);
        lemma_not_lit(x, y, hi, k, lit_cdata_ty());
        lemma_not_lit(x, y, hi, k, lit_idrefs());
        lemma_not_lit(x, y, hi, k, lit_idref());
        lemma_not_lit(x, y, hi, k, lit_id());
        lemma_not_lit_at(x, y, hi, k, lit_entities(), 6);
        lemma_lit_eq(x, y, hi, k, lit_entity_ty());
    } else if has_lit(x, k, lit_nmtokens()) {
        assert(x.subrange(k, k + 8)[0] == x[k]);
        lemma_not_lit(x, y, hi, k, lit_cdata_ty());
        lemma_not_lit(x, y, hi, k, lit_idrefs());
        lemma_not_lit(x, y, hi, k, lit_idref());
        lemma_not_lit(x, y, hi, k, lit_id());
        lemma_not_lit(x, y, hi, k, lit_entities());
        lemma_not_lit(x, y, hi, k, lit_entity_ty());
        lemma_lit_eq(x, y, hi, k, lit_nmtokens());
    } else if has_lit(x, k, lit_nmtoken()) {
        assert(x.subrange(k, k + 7)[0] == x[k]);
        lemma_not_lit(x, y, hi, k, lit_cdata_ty());
        lemma_not_lit(x, y, hi, k, lit_idrefs());
        lemma_not_lit(x, y, hi, k, lit_idref());
        lemma_not_lit(x, y, hi, k, lit_id());
        lemma_not_lit(x, y, hi, k, lit_entities());
        lemma_not_lit(x, y, hi, k, lit_entity_ty());
        lemma_not_lit_at(x, y, hi, k, lit_nmtokens(), 7);
        lemma_lit_eq(x, y, hi, k, lit_nmtoken());
    } else if has_lit(x, k, lit_notation_ty()) {
        assert(x.subrange(k, k + 8)[0] == x[k]);
        assert(x.subrange(k, k + 8)[1] == x[k + 1]);
        let j = ws_end(x, k + 8);
        lemma_ws_end_ge(x, k + 8);
        lemma_alt_list_eq(x, y, hi, j + 1, false);
        lemma_byte_is(x, y, 0, hi, 0, j, 0x28);
        lemma_ws_eq(x, y, hi, k + 8);
        lemma_not_lit(x, y, hi, k, lit_cdata_ty());
        lemma_not_lit(x, y, hi, k, lit_idrefs());
        lemma_not_lit(x, y, hi, k, lit_idref());
        lemma_not_lit(x, y, hi, k, lit_id());
        lemma_not_lit(x, y, hi, k, lit_entities());
        lemma_not_lit(x, y, hi, k, lit_entity_ty());
        lemma_not_lit_at(x, y, hi, k, lit_nmtokens(), 1);
        lemma_not_lit_at(x, y, hi, k, lit_nmtoken(), 1);
        lemma_lit_eq(x, y, hi, k, lit_notation_ty());
    } else {
        lemma_alt_list_eq(x, y, hi, k + 1, true);
        lemma_byte_is(x, y, 0, hi, 0, k, 0x28);
        lemma_not_lit(x, y, hi, k, lit_cdata_ty());
        lemma_not_lit(x, y, hi, k, lit_idrefs());
        lemma_not_lit(x, y, hi, k, lit_idref());
        lemma_not_lit(x, y, hi, k, lit_id());
        lemma_not_lit(x, y, hi, k, lit_entities());
        lemma_not_lit(x, y, hi, k, lit_entity_ty());
        lemma_not_lit(x, y, hi, k, lit_nmtokens());
        lemma_not_lit(x, y, hi, k, lit_nmtoken());
        lemma_not_lit(x, y, hi, k, lit_notation_ty());
    }
}

/// An attribute default's value, as `defaults_ok` will read it again.
pub open spec fn dflt_tok(x: Seq<u8>, tk: XTok, hi: int) -> bool {
    match tk {
        XTok::AttDefault { start, end, kind, .. } => kind < 3 || (0 <= start <= end < hi && att_chars(
            x,
            start,
            x[end],
            None,
        ) == Some(end)),
        _ => true,
    }
}

#[verifier::opaque]
pub open spec fn dflt_ok(x: Seq<u8>, t: Seq<XTok>, hi: int) -> bool {
    forall|k: int| 0 <= k < t.len() ==> dflt_tok(x, #[trigger] t[k], hi)
}

pub proof fn lemma_no_dflt_ok(x: Seq<u8>, t: Seq<XTok>, hi: int)
    requires
        no_dflt(t),
    ensures
        dflt_ok(x, t, hi),
{
    reveal(dflt_ok);
    assert forall|k: int| 0 <= k < t.len() implies dflt_tok(x, #[trigger] t[k], hi) by {
        assert(!(t[k] is AttDefault));
    }
}

pub proof fn lemma_dflt_ok_add(x: Seq<u8>, a: Seq<XTok>, b: Seq<XTok>, hi: int)
    requires
        dflt_ok(x, a, hi),
        dflt_ok(x, b, hi),
    ensures
        dflt_ok(x, a + b, hi),
{
    reveal(dflt_ok);
    assert forall|k: int| 0 <= k < (a + b).len() implies dflt_tok(x, #[trigger] (a + b)[k], hi) by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

pub proof fn lemma_dflt_ok_mono(x: Seq<u8>, t: Seq<XTok>, hi: int, hi2: int)
    requires
        dflt_ok(x, t, hi),
        hi <= hi2,
    ensures
        dflt_ok(x, t, hi2),
{
    reveal(dflt_ok);
    assert forall|k: int| 0 <= k < t.len() implies dflt_tok(x, #[trigger] t[k], hi2) by {
        assert(dflt_tok(x, t[k], hi));
    }
}

pub proof fn lemma_dflt_ok_two(x: Seq<u8>, a: XTok, b: XTok, hi: int)
    requires
        dflt_tok(x, a, hi),
        dflt_tok(x, b, hi),
    ensures
        dflt_ok(x, seq![a, b], hi),
{
    reveal(dflt_ok);
    let two = seq![a, b];
    assert forall|k: int| 0 <= k < two.len() implies dflt_tok(x, #[trigger] two[k], hi) by {
    }
}

pub proof fn lemma_att_chars_quote(s: Seq<u8>, i: int, q: u8, env: Option<Env>)
    requires
        att_chars(s, i, q, env) is Some,
    ensures
        0 <= att_chars(s, i, q, env).unwrap() < s.len(),
        s[att_chars(s, i, q, env).unwrap()] == q,
        att_chars(s, i, q, env).unwrap() >= i,
    decreases s.len() - i,
{
    if s[i] == q {
    } else if s[i] == 0x26 {
        let e = att_ref(s, i, env).unwrap();
        lemma_att_chars_quote(s, e, q, env);
    } else {
        lemma_att_chars_quote(s, i + 1, q, env);
    }
}

pub proof fn lemma_default_decl_eq(x: Seq<u8>, y: Seq<u8>, hi: int, m: int)
    requires
        ag(x, y, hi),
        0 <= m,
        default_decl(x, m) matches Some((e, _, _, _)) && e <= hi,
    ensures
        default_decl(y, m) == default_decl(x, m),
        default_decl(x, m) matches Some((e, kind, va, vb)) && e > m && (kind < 3 || (0 <= va <= vb < e && att_chars(
            x,
            va,
            x[vb],
            None,
        ) == Some(vb))),
{
    assert(lit_required() =~= seq![0x23u8, 0x52, 0x45, 0x51, 0x55, 0x49, 0x52, 0x45, 0x44]);
    assert(lit_implied() =~= seq![0x23u8, 0x49, 0x4D, 0x50, 0x4C, 0x49, 0x45, 0x44]);
    assert(lit_fixed() =~= seq![0x23u8, 0x46, 0x49, 0x58, 0x45, 0x44]);
    if has_lit(x, m, lit_required()) {
        lemma_lit_eq(x, y, hi, m, lit_required());
    } else if has_lit(x, m, lit_implied()) {
        assert(x.subrange(m, m + 8)[1] == x[m + 1]);
        lemma_not_lit_at(x, y, hi, m, lit_required(), 1);
        lemma_lit_eq(x, y, hi, m, lit_implied());
    } else {
        let fixed = has_lit(x, m, lit_fixed());
        let v = if fixed {
            ws_end(x, m + 6)
        } else {
            m
        };
        lemma_ws_end_ge(x, m + 6);
        let q = att_chars(x, v + 1, x[v], None).unwrap();
        lemma_att_chars_mv(x, y, 0, hi, 0, v + 1, x[v], None);
        lemma_att_chars_quote(x, v + 1, x[v], None);
        lemma_byte_eq(x, y, hi, v);
        if fixed {
            assert(x.subrange(m, m + 6)[1] == x[m + 1]);
            lemma_not_lit_at(x, y, hi, m, lit_required(), 1);
            lemma_not_lit_at(x, y, hi, m, lit_implied(), 1);
            lemma_lit_eq(x, y, hi, m, lit_fixed());
            lemma_ws_eq(x, y, hi, m + 6);
        } else {
            lemma_not_lit(x, y, hi, m, lit_required());
            lemma_not_lit(x, y, hi, m, lit_implied());
            lemma_not_lit(x, y, hi, m, lit_fixed());
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_att_defs_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, t: Seq<XTok>, nents: int)
    requires
        ag(x, y, hi),
        0 <= i,
        att_defs(x, i, t, nents) matches Some((_, e)) && e <= hi,
    ensures
        att_defs(y, i, t, nents) == att_defs(x, i, t, nents),
        att_defs(x, i, t, nents) matches Some((u, e)) && e > i && extends(t, u) && dflt_ok(x, added(t, u), hi),
    decreases x.len() - i,
{
    let j = ws_end(x, i);
    lemma_ws_end_ge(x, i);
    let (u, e) = att_defs(x, i, t, nents).unwrap();
    if byte_is(x, j, 0x3E) {
        lemma_byte_is(x, y, 0, hi, 0, j, 0x3E);
        lemma_ws_eq(x, y, hi, i);
        assert(u.subrange(0, t.len() as int) =~= t);
        assert(added(t, u) =~= Seq::<XTok>::empty());
        lemma_no_dflt_ok(x, added(t, u), hi);
    } else {
        let n = name_end(x, j);
        lemma_name_end(x, j);
        let k = ws_end(x, n);
        lemma_ws_end_ws(x, n);
        let (e1, ty) = att_type(x, k).unwrap();
        let m = ws_end(x, e1);
        lemma_ws_end_ws(x, e1);
        let (dd, kind, va, vb) = default_decl(x, m).unwrap();
        let ta = XTok::AttDef { start: j, end: n, ty };
        let tb = XTok::AttDefault { start: va, end: vb, kind, nents };
        let t1 = t.push(ta).push(tb);
        lemma_att_defs_eq(x, y, hi, dd, t1, nents);
        lemma_default_decl_eq(x, y, hi, m);
        lemma_ws_eq(x, y, hi, e1);
        lemma_att_type_eq(x, y, hi, k);
        lemma_ws_eq(x, y, hi, n);
        assert(is_ws(x[n]));
        lemma_name_eq(x, y, hi, j);
        lemma_byte_is(x, y, 0, hi, 0, j, 0x3E);
        lemma_ws_eq(x, y, hi, i);
        lemma_extends_push2(t, ta, tb, u);
        let r1 = added(t1, u);
        lemma_dflt_ok_two(x, ta, tb, hi);
        lemma_dflt_ok_add(x, seq![ta, tb], r1, hi);
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_attlist_decl_eq(x: Seq<u8>, y: Seq<u8>, hi: int, j: int, t: Seq<XTok>, nents: int)
    requires
        ag(x, y, hi),
        0 <= j,
        attlist_decl(x, j, t, nents) matches Some((_, e)) && e <= hi,
    ensures
        attlist_decl(y, j, t, nents) == attlist_decl(x, j, t, nents),
        attlist_decl(x, j, t, nents) matches Some((u, e)) && e > j + 9 && extends(t, u) && dflt_ok(x, added(t, u), hi),
{
    let a = ws_end(x, j + 9);
    lemma_ws_end_ge(x, j + 9);
    let n = name_end(x, a);
    lemma_name_end(x, a);
    let ta = XTok::AttlistDecl { start: a, end: n };
    let t1 = t.push(ta);
    lemma_att_defs_eq(x, y, hi, n, t1, nents);
    lemma_att_defs_ascii(x, n, t1, nents);
    lemma_name_eq(x, y, hi, a);
    lemma_ws_eq(x, y, hi, j + 9);
    let (u, e) = attlist_decl(x, j, t, nents).unwrap();
    lemma_extends_push1(t, ta, u);
    lemma_no_dflt_ok(x, seq![ta], hi);
    lemma_dflt_ok_add(x, seq![ta], added(t1, u), hi);
}

pub proof fn lemma_extends_push1(t: Seq<XTok>, a: XTok, u: Seq<XTok>)
    requires
        extends(t.push(a), u),
    ensures
        extends(t, u),
        added(t, u) == seq![a] + added(t.push(a), u),
{
    let t1 = t.push(a);
    assert(u.subrange(0, t1.len() as int) =~= t1);
    assert(u.subrange(0, t.len() as int) =~= t1.subrange(0, t.len() as int));
    assert(t1.subrange(0, t.len() as int) =~= t);
    assert(u[t.len() as int] == t1[t.len() as int]);
    assert(added(t, u) =~= seq![a] + added(t1, u));
}

proof fn lemma_att_defs_ascii(x: Seq<u8>, i: int, t: Seq<XTok>, nents: int)
    requires
        att_defs(x, i, t, nents) is Some,
    ensures
        0 <= i < x.len() && x[i] < 0x80,
{
    let j = ws_end(x, i);
    lemma_ws_end_ws(x, i);
    if j > i {
        assert(is_ws(x[i]));
    }
}

// ---------------------------------------------------------------------------
// Entity and notation declarations, the internal subset
// ---------------------------------------------------------------------------

/// The internal entities' literal values lie before `hi`.
pub open spec fn ents_in(ents: Seq<Ent>, hi: int) -> bool {
    forall|k: int|
        0 <= k < ents.len() ==> match #[trigger] ents[k].kind {
            EKind::Internal { start, end } => 0 <= start <= end < hi,
            _ => true,
        }
}

pub proof fn lemma_ent_value_end_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, q: u8)
    requires
        ag(x, y, hi),
        0 <= i,
        ent_value_end(x, i, q) matches Some(e) && e <= hi,
    ensures
        ent_value_end(y, i, q) == ent_value_end(x, i, q),
        ent_value_end(x, i, q).unwrap() > i,
    decreases x.len() - i,
{
    if x[i] == q {
        lemma_byte_eq(x, y, hi, i);
    } else if x[i] == 0x26 {
        let e = ref_syntax(x, i).unwrap();
        lemma_ref_syntax_end(x, i);
        lemma_ent_value_end_eq(x, y, hi, e, q);
        lemma_byte_eq(x, y, hi, i);
        lemma_ref_syntax_mv(x, y, 0, hi, 0, i);
    } else {
        lemma_ent_value_end_eq(x, y, hi, i + 1, q);
        lemma_byte_eq(x, y, hi, i);
    }
}

pub proof fn lemma_ref_syntax_end(s: Seq<u8>, i: int)
    requires
        0 <= i < s.len(),
        ref_syntax(s, i) is Some,
    ensures
        ref_syntax(s, i).unwrap() > i,
{
    lemma_hex_end_ge(s, i + 3);
    lemma_digits_end_ge(s, i + 2);
    lemma_name_end(s, i + 1);
}

/// An entity definition, followed (after white space, at `f`, before
/// `hi`) by the `>` that ends the declaration, which decides whether an
/// `NDATA` follows.
pub proof fn lemma_ent_def_eq(x: Seq<u8>, y: Seq<u8>, hi: int, c: int, t: Seq<XTok>, ge: bool)
    requires
        ag(x, y, hi),
        0 <= c,
        ent_def(x, c, t, ge) matches Some((_, e, _)) && ws_end(x, e) < hi && x[ws_end(x, e)] == 0x3E,
    ensures
        ent_def(y, c, t, ge) == ent_def(x, c, t, ge),
        ent_def(x, c, t, ge) matches Some((u, e, kind)) && e > c && extends(t, u) && no_dflt(added(t, u))
            && match kind {
            EKind::Internal { start, end } => 0 <= start <= end < e,
            _ => true,
        },
{
    let (u, e, kind) = ent_def(x, c, t, ge).unwrap();
    lemma_ws_end_ge(x, e);
    if 0 <= c < x.len() && quote(x[c]) {
        lemma_ent_value_end_eq(x, y, hi, c + 1, x[c]);
        lemma_byte_eq(x, y, hi, c);
        assert(u.subrange(0, t.len() as int) =~= t);
        assert(added(t, u) =~= seq![XTok::EntityValue { start: c + 1, end: e - 1 }]);
    } else {
        let (t1, e1) = external_id(x, c, t).unwrap();
        let k = ws_end(x, e1);
        lemma_ws_end_ge(x, e1);
        assert(lit_ndata() =~= seq![0x4Eu8, 0x44, 0x41, 0x54, 0x41]);
        if ge && k > e1 && has_lit(x, k, lit_ndata()) {
            let m = ws_end(x, k + 5);
            lemma_ws_end_ge(x, k + 5);
            let n = name_end(x, m);
            lemma_name_end(x, m);
            assert(e == n);
            if ws_end(x, n) > n {
                assert(is_ws(x[n]));
            }
            lemma_name_eq(x, y, hi, m);
            lemma_ws_eq(x, y, hi, k + 5);
            lemma_lit_eq(x, y, hi, k, lit_ndata());
            lemma_ws_eq(x, y, hi, e1);
            lemma_external_id_eq(x, y, hi, c, t);
            assert(u.subrange(0, u.len() as int) =~= u);
            lemma_extends_push1(t1, XTok::NData { start: m, end: n }, u);
            assert(u.subrange(0, t1.len() as int) =~= t1);
            assert(u.subrange(0, t.len() as int) =~= t1.subrange(0, t.len() as int));
            assert(added(t, u) =~= added(t, t1).push(XTok::NData { start: m, end: n }));
        } else {
            lemma_external_id_eq(x, y, hi, c, t);
            lemma_ws_eq(x, y, hi, e1);
            if ge && k > e1 {
                // The `>` is where `NDATA` would be.
                lemma_not_lit(x, y, hi, k, lit_ndata());
            }
        }
        lemma_byte_eq(x, y, hi, c);
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_entity_decl_eq(x: Seq<u8>, y: Seq<u8>, hi: int, j: int, t: Seq<XTok>, st: DtdSt)
    requires
        ag(x, y, hi),
        0 <= j,
        entity_decl(x, j, t, st) matches Some((_, _, e)) && e <= hi,
    ensures
        entity_decl(y, j, t, st) == entity_decl(x, j, t, st),
        entity_decl(x, j, t, st) matches Some((u, st2, e)) && e > j + 8 && extends(t, u) && no_dflt(added(t, u))
            && (ents_in(st.ents, hi) ==> ents_in(st2.ents, hi)) && st2.pe_seen == st.pe_seen && st2.sa == st.sa,
{
    let a = ws_end(x, j + 8);
    lemma_ws_end_ge(x, j + 8);
    let (u, st2, e) = entity_decl(x, j, t, st).unwrap();
    if byte_is(x, a, 0x25) {
        let b = ws_end(x, a + 1);
        lemma_ws_end_ge(x, a + 1);
        let n = name_end(x, b);
        lemma_name_end(x, b);
        let c = ws_end(x, n);
        lemma_ws_end_ws(x, n);
        let tk = XTok::EntityDecl { start: b, end: n, pe: true };
        let (t1, e1, _) = ent_def(x, c, t.push(tk), false).unwrap();
        lemma_ws_end_ge(x, e1);
        lemma_ent_def_eq(x, y, hi, c, t.push(tk), false);
        lemma_ws_eq(x, y, hi, e1);
        lemma_byte_eq(x, y, hi, ws_end(x, e1));
        lemma_ws_eq(x, y, hi, n);
        lemma_name_eq(x, y, hi, b);
        lemma_ws_eq(x, y, hi, a + 1);
        lemma_byte_is(x, y, 0, hi, 0, a, 0x25);
        lemma_ws_eq(x, y, hi, j + 8);
        lemma_extends_push1(t, tk, u);
        lemma_no_dflt_cons(tk, added(t.push(tk), u));
    } else {
        let n = name_end(x, a);
        lemma_name_end(x, a);
        let c = ws_end(x, n);
        lemma_ws_end_ws(x, n);
        let tk = XTok::EntityDecl { start: a, end: n, pe: false };
        let (t1, e1, kind) = ent_def(x, c, t.push(tk), true).unwrap();
        lemma_ws_end_ge(x, e1);
        lemma_ent_def_eq(x, y, hi, c, t.push(tk), true);
        lemma_ws_eq(x, y, hi, e1);
        lemma_byte_eq(x, y, hi, ws_end(x, e1));
        lemma_ws_eq(x, y, hi, n);
        lemma_name_eq(x, y, hi, a);
        lemma_span_eq(x, y, hi, a, n);
        lemma_byte_is(x, y, 0, hi, 0, a, 0x25);
        lemma_ws_eq(x, y, hi, j + 8);
        lemma_extends_push1(t, tk, u);
        lemma_no_dflt_cons(tk, added(t.push(tk), u));
        if ents_in(st.ents, hi) && (!st.pe_seen || st.sa) {
            let ents2 = st.ents.push(Ent { name: x.subrange(a, n), kind });
            assert(st2.ents == ents2);
            assert forall|k: int| 0 <= k < ents2.len() implies match #[trigger] ents2[k].kind {
                EKind::Internal { start, end } => 0 <= start <= end < hi,
                _ => true,
            } by {
                if k < st.ents.len() {
                    assert(ents2[k] == st.ents[k]);
                }
            }
        }
    }
}

pub proof fn lemma_no_dflt_cons(a: XTok, t: Seq<XTok>)
    requires
        !(a is AttDefault),
        no_dflt(t),
    ensures
        no_dflt(seq![a] + t),
{
    assert forall|k: int| 0 <= k < (seq![a] + t).len() implies !(#[trigger] (seq![a] + t)[k] is AttDefault) by {
        if k > 0 {
            assert((seq![a] + t)[k] == t[k - 1]);
        }
    }
}

pub proof fn lemma_notation_decl_eq(x: Seq<u8>, y: Seq<u8>, hi: int, j: int, t: Seq<XTok>)
    requires
        ag(x, y, hi),
        0 <= j,
        notation_decl(x, j, t) matches Some((_, e)) && e <= hi,
    ensures
        notation_decl(y, j, t) == notation_decl(x, j, t),
        notation_decl(x, j, t) matches Some((u, e)) && e > j + 10 && extends(t, u) && no_dflt(added(t, u)),
{
    assert(lit_public() =~= seq![0x50u8, 0x55, 0x42, 0x4C, 0x49, 0x43]);
    assert(lit_system() =~= seq![0x53u8, 0x59, 0x53, 0x54, 0x45, 0x4D]);
    let a = ws_end(x, j + 10);
    lemma_ws_end_ge(x, j + 10);
    let n = name_end(x, a);
    lemma_name_end(x, a);
    let b = ws_end(x, n);
    lemma_ws_end_ws(x, n);
    let t1 = t.push(XTok::NotationDecl { start: a, end: n });
    let (u, e) = notation_decl(x, j, t).unwrap();
    if has_lit(x, b, lit_public()) {
        let p = ws_end(x, b + 6);
        lemma_ws_end_ge(x, b + 6);
        let e1 = pubid_lit(x, p).unwrap();
        lemma_pubid_lit_eq_any(x, p);
        let t2 = t1.push(XTok::PubId { start: p + 1, end: e1 - 1 });
        let k = ws_end(x, e1);
        lemma_ws_end_ws(x, e1);
        if k > e1 && 0 <= k < x.len() && quote(x[k]) {
            let f1 = sys_lit(x, k).unwrap();
            lemma_ws_end_ge(x, f1);
            lemma_sys_lit_eq(x, y, hi, k);
            lemma_byte_eq(x, y, hi, k);
            lemma_ws_eq(x, y, hi, f1);
            lemma_byte_eq(x, y, hi, ws_end(x, f1));
            assert(u.subrange(0, t.len() as int) =~= t);
            assert(added(t, u) =~= seq![
                XTok::NotationDecl { start: a, end: n },
                XTok::PubId { start: p + 1, end: e1 - 1 },
                XTok::SysId { start: k + 1, end: f1 - 1 },
            ]);
        } else {
            lemma_byte_eq(x, y, hi, k);
            assert(u.subrange(0, t.len() as int) =~= t);
            assert(added(t, u) =~= seq![XTok::NotationDecl { start: a, end: n }, XTok::PubId { start: p + 1, end: e1 - 1 }]);
        }
        lemma_ws_eq(x, y, hi, e1);
        lemma_pubid_lit_eq(x, y, hi, p);
        lemma_ws_eq(x, y, hi, b + 6);
        lemma_lit_eq(x, y, hi, b, lit_public());
    } else {
        let (t2, e1) = external_id(x, b, t1).unwrap();
        lemma_ws_end_ge(x, e1);
        lemma_external_id_eq(x, y, hi, b, t1);
        lemma_ws_eq(x, y, hi, e1);
        lemma_byte_eq(x, y, hi, ws_end(x, e1));
        // An external identifier that is not `PUBLIC` starts with `S`.
        lemma_not_lit(x, y, hi, b, lit_public());
        lemma_extends_push1(t, XTok::NotationDecl { start: a, end: n }, u);
        lemma_no_dflt_cons(XTok::NotationDecl { start: a, end: n }, added(t1, u));
        assert(u.subrange(0, t1.len() as int) =~= t2.subrange(0, t1.len() as int));
    }
    lemma_ws_eq(x, y, hi, n);
    lemma_name_eq(x, y, hi, a);
    lemma_ws_eq(x, y, hi, j + 10);
}

pub proof fn lemma_pubid_lit_eq_any(x: Seq<u8>, i: int)
    requires
        pubid_lit(x, i) is Some,
    ensures
        pubid_lit(x, i).unwrap() > i + 1,
        0 <= i < x.len(),
    decreases x.len() - i,
{
    lemma_pubid_end_gt(x, i + 1, x[i]);
}

pub proof fn lemma_pubid_end_gt(x: Seq<u8>, i: int, q: u8)
    requires
        pubid_end(x, i, q) is Some,
    ensures
        pubid_end(x, i, q).unwrap() > i,
    decreases x.len() - i,
{
    if x[i] != q {
        lemma_pubid_end_gt(x, i + 1, q);
    }
}

pub proof fn lemma_pe_ref_eq(x: Seq<u8>, y: Seq<u8>, hi: int, j: int, t: Seq<XTok>, st: DtdSt)
    requires
        ag(x, y, hi),
        0 <= j,
        pe_ref(x, j, t, st) matches Some((_, _, e)) && e <= hi,
    ensures
        pe_ref(y, j, t, st) == pe_ref(x, j, t, st),
        pe_ref(x, j, t, st) matches Some((u, st2, e)) && e > j + 1 && extends(t, u) && no_dflt(added(t, u))
            && st2.ents == st.ents && st2.sa == st.sa,
{
    let n = name_end(x, j + 1);
    lemma_name_end(x, j + 1);
    lemma_name_eq(x, y, hi, j + 1);
    lemma_byte_is(x, y, 0, hi, 0, n, 0x3B);
    let (u, st2, e) = pe_ref(x, j, t, st).unwrap();
    assert(u.subrange(0, t.len() as int) =~= t);
    assert(added(t, u) =~= seq![XTok::PERef { start: j + 1, end: n }]);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_decl_eq(x: Seq<u8>, y: Seq<u8>, hi: int, j: int, t: Seq<XTok>, st: DtdSt)
    requires
        ag(x, y, hi),
        0 <= j,
        decl(x, j, t, st) matches Some((_, _, e)) && e <= hi,
    ensures
        decl(y, j, t, st) == decl(x, j, t, st),
        decl(x, j, t, st) matches Some((u, st2, e)) && e > j && extends(t, u) && dflt_ok(x, added(t, u), hi) && (
        ents_in(st.ents, hi) ==> ents_in(st2.ents, hi)) && st2.sa == st.sa,
{
    hide(element_decl);
    hide(attlist_decl);
    hide(entity_decl);
    hide(notation_decl);
    hide(comment);
    hide(pi);
    hide(pe_ref);
    lemma_lits_stable();
    assert(lit_element() =~= seq![0x3Cu8, 0x21, 0x45, 0x4C, 0x45, 0x4D, 0x45, 0x4E, 0x54]);
    assert(lit_attlist() =~= seq![0x3Cu8, 0x21, 0x41, 0x54, 0x54, 0x4C, 0x49, 0x53, 0x54]);
    assert(lit_entity() =~= seq![0x3Cu8, 0x21, 0x45, 0x4E, 0x54, 0x49, 0x54, 0x59]);
    assert(lit_notation() =~= seq![0x3Cu8, 0x21, 0x4E, 0x4F, 0x54, 0x41, 0x54, 0x49, 0x4F, 0x4E]);
    assert(lit_pi() =~= seq![0x3Cu8, 0x3F]);
    let (u, st2, e) = decl(x, j, t, st).unwrap();
    if byte_is(x, j, 0x25) {
        lemma_pe_ref_eq(x, y, hi, j, t, st);
        lemma_byte_is(x, y, 0, hi, 0, j, 0x25);
        lemma_no_dflt_ok(x, added(t, u), hi);
    } else if has_lit(x, j, lit_element()) {
        lemma_element_decl_eq(x, y, hi, j, t);
        lemma_byte_is(x, y, 0, hi, 0, j, 0x25);
        lemma_lit_eq(x, y, hi, j, lit_element());
        lemma_no_dflt_ok(x, added(t, u), hi);
    } else if has_lit(x, j, lit_attlist()) {
        assert(x.subrange(j, j + 9)[2] == x[j + 2]);
        lemma_attlist_decl_eq(x, y, hi, j, t, st.ents.len() as int);
        lemma_byte_is(x, y, 0, hi, 0, j, 0x25);
        lemma_not_lit_at(x, y, hi, j, lit_element(), 2);
        lemma_lit_eq(x, y, hi, j, lit_attlist());
    } else if has_lit(x, j, lit_entity()) {
        assert(x.subrange(j, j + 8)[2] == x[j + 2]);
        assert(x.subrange(j, j + 8)[3] == x[j + 3]);
        lemma_entity_decl_eq(x, y, hi, j, t, st);
        lemma_byte_is(x, y, 0, hi, 0, j, 0x25);
        lemma_not_lit_at(x, y, hi, j, lit_element(), 3);
        lemma_not_lit_at(x, y, hi, j, lit_attlist(), 2);
        lemma_lit_eq(x, y, hi, j, lit_entity());
        lemma_no_dflt_ok(x, added(t, u), hi);
    } else if has_lit(x, j, lit_notation()) {
        assert(x.subrange(j, j + 10)[2] == x[j + 2]);
        lemma_notation_decl_eq(x, y, hi, j, t);
        lemma_byte_is(x, y, 0, hi, 0, j, 0x25);
        lemma_not_lit_at(x, y, hi, j, lit_element(), 2);
        lemma_not_lit_at(x, y, hi, j, lit_attlist(), 2);
        lemma_not_lit_at(x, y, hi, j, lit_entity(), 2);
        lemma_lit_eq(x, y, hi, j, lit_notation());
        lemma_no_dflt_ok(x, added(t, u), hi);
    } else if has_lit(x, j, lit_comment()) {
        assert(x.subrange(j, j + 4)[2] == x[j + 2]);
        lemma_comment_mv(x, y, 0, hi, 0, j, t, t, 0);
        lemma_byte_is(x, y, 0, hi, 0, j, 0x25);
        lemma_mv_zero(added(t, u));
        assert(t + added(t, u) =~= u);
        lemma_not_lit_at(x, y, hi, j, lit_element(), 2);
        lemma_not_lit_at(x, y, hi, j, lit_attlist(), 2);
        lemma_not_lit_at(x, y, hi, j, lit_entity(), 2);
        lemma_not_lit_at(x, y, hi, j, lit_notation(), 2);
        lemma_lit_eq(x, y, hi, j, lit_comment());
        lemma_comment_tokens(x, j, t);
        lemma_no_dflt_ok(x, added(t, u), hi);
    } else {
        assert(x.subrange(j, j + 2)[1] == x[j + 1]);
        lemma_pi_mv(x, y, 0, hi, 0, j, t, t, 0);
        lemma_byte_is(x, y, 0, hi, 0, j, 0x25);
        lemma_mv_zero(added(t, u));
        assert(t + added(t, u) =~= u);
        lemma_not_lit_at(x, y, hi, j, lit_element(), 1);
        lemma_not_lit_at(x, y, hi, j, lit_attlist(), 1);
        lemma_not_lit_at(x, y, hi, j, lit_entity(), 1);
        lemma_not_lit_at(x, y, hi, j, lit_notation(), 1);
        lemma_not_lit_at(x, y, hi, j, lit_comment(), 1);
        lemma_lit_eq(x, y, hi, j, lit_pi());
        lemma_pi_tokens(x, j, t);
        lemma_no_dflt_ok(x, added(t, u), hi);
    }
}

proof fn lemma_comment_tokens(x: Seq<u8>, j: int, t: Seq<XTok>)
    requires
        comment(x, j, t) is Some,
    ensures
        no_dflt(added(t, comment(x, j, t).unwrap().0)),
{
    let (u, e) = comment(x, j, t).unwrap();
    assert(added(t, u) =~= seq![XTok::Comment { start: j + 4, end: e - 3 }]);
}

proof fn lemma_pi_tokens(x: Seq<u8>, j: int, t: Seq<XTok>)
    requires
        pi(x, j, t) is Some,
    ensures
        no_dflt(added(t, pi(x, j, t).unwrap().0)),
        extends(t, pi(x, j, t).unwrap().0),
{
    let u = pi(x, j, t).unwrap().0;
    assert(u.subrange(0, t.len() as int) =~= t);
    assert forall|k: int| 0 <= k < added(t, u).len() implies !(#[trigger] added(t, u)[k] is AttDefault) by {
        assert(added(t, u)[k] == u[t.len() + k]);
    }
}

pub proof fn lemma_int_subset_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, t: Seq<XTok>, st: DtdSt)
    requires
        ag(x, y, hi),
        0 <= i,
        int_subset(x, i, t, st) matches Some((_, _, q)) && q < hi,
    ensures
        int_subset(y, i, t, st) == int_subset(x, i, t, st),
        int_subset(x, i, t, st) matches Some((u, st2, q)) && q >= i && extends(t, u) && dflt_ok(x, added(t, u), hi)
            && (ents_in(st.ents, hi) ==> ents_in(st2.ents, hi)) && st2.sa == st.sa,
    decreases x.len() - i,
{
    hide(decl);
    let j = ws_end(x, i);
    lemma_ws_end_ge(x, i);
    let (u, st2, q) = int_subset(x, i, t, st).unwrap();
    if x[j] == 0x5D {
        lemma_byte_eq(x, y, hi, j);
        lemma_ws_eq(x, y, hi, i);
        assert(u.subrange(0, t.len() as int) =~= t);
        assert(added(t, u) =~= Seq::<XTok>::empty());
        lemma_no_dflt_ok(x, added(t, u), hi);
    } else {
        let (t1, st1, e) = decl(x, j, t, st).unwrap();
        lemma_int_subset_eq(x, y, hi, e, t1, st1);
        lemma_decl_eq(x, y, hi, j, t, st);
        lemma_byte_eq(x, y, hi, j);
        lemma_ws_eq(x, y, hi, i);
        lemma_extends_trans(t, t1, u);
        lemma_dflt_ok_add(x, added(t, t1), added(t1, u), hi);
    }
}

pub proof fn lemma_extends_trans(t: Seq<XTok>, t1: Seq<XTok>, u: Seq<XTok>)
    requires
        extends(t, t1),
        extends(t1, u),
    ensures
        extends(t, u),
        added(t, u) == added(t, t1) + added(t1, u),
{
    assert(u.subrange(0, t.len() as int) =~= t1.subrange(0, t.len() as int));
    assert(added(t, u) =~= added(t, t1) + added(t1, u)) by {
        assert forall|k: int| 0 <= k < added(t, u).len() implies #[trigger] added(t, u)[k] == (added(t, t1) + added(t1, u))[k] by {
            if k < t1.len() - t.len() {
                assert(u[t.len() + k] == u.subrange(0, t1.len() as int)[t.len() + k]);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Replacement text, and what may be referred to where
// ---------------------------------------------------------------------------

/// A character reference whose end, if it has one, is after `hi`.
pub open spec fn cut(s: Seq<u8>, i: int, hi: int) -> bool {
    match charref(s, i) {
        Some((_, e)) => e > hi,
        None => true,
    }
}

pub proof fn lemma_hex_run(x: Seq<u8>, y: Seq<u8>, hi: int, i: int)
    requires
        ag(x, y, hi),
        0 <= i <= hi,
        hex_end(x, i) >= hi,
    ensures
        hex_end(y, i) >= hi,
    decreases hi - i,
{
    if i < hi {
        lemma_byte_eq(x, y, hi, i);
        lemma_hex_run(x, y, hi, i + 1);
    }
    lemma_hex_end_ge(y, i);
}

pub proof fn lemma_digits_run(x: Seq<u8>, y: Seq<u8>, hi: int, i: int)
    requires
        ag(x, y, hi),
        0 <= i <= hi,
        digits_end(x, i) >= hi,
    ensures
        digits_end(y, i) >= hi,
    decreases hi - i,
{
    if i < hi {
        lemma_byte_eq(x, y, hi, i);
        lemma_digits_run(x, y, hi, i + 1);
    }
    lemma_digits_end_ge(y, i);
}

pub proof fn lemma_charref_min(s: Seq<u8>, i: int)
    requires
        charref(s, i) is Some,
    ensures
        charref(s, i).unwrap().1 >= i + 4,
{
    lemma_hex_end_ge(s, i + 3);
    lemma_digits_end_ge(s, i + 2);
}

/// A character reference reads the digits up to its `;`: it is the same in
/// both inputs, or in both it ends (if it does) after `hi`.
pub proof fn lemma_charref_cut(x: Seq<u8>, y: Seq<u8>, hi: int, i: int)
    requires
        ag(x, y, hi),
        0 <= i,
    ensures
        charref(y, i) == charref(x, i) || (cut(x, i, hi) && cut(y, i, hi)),
{
    if charref(x, i) is Some {
        lemma_charref_min(x, i);
    }
    if charref(y, i) is Some {
        lemma_charref_min(y, i);
    }
    if i + 2 < hi {
        lemma_byte_eq(x, y, hi, i + 2);
        if x[i + 2] == 0x78 {
            let dx = hex_end(x, i + 3);
            lemma_hex_end_ge(x, i + 3);
            lemma_hex_end_ge(y, i + 3);
            if dx < hi {
                lemma_hex_end_mv(x, y, 0, hi, 0, i + 3);
                lemma_byte_eq(x, y, hi, dx);
                lemma_hexv_mv(x, y, 0, hi, 0, i + 3, dx);
            } else {
                lemma_hex_run(x, y, hi, i + 3);
            }
        } else {
            let dx = digits_end(x, i + 2);
            lemma_digits_end_ge(x, i + 2);
            lemma_digits_end_ge(y, i + 2);
            if dx < hi {
                lemma_digits_end_mv(x, y, 0, hi, 0, i + 2);
                lemma_byte_eq(x, y, hi, dx);
                lemma_decv_mv(x, y, 0, hi, 0, i + 2, dx);
            } else {
                lemma_digits_run(x, y, hi, i + 2);
            }
        }
    }
}

/// The replacement text of a literal value that ends before `hi`.
pub proof fn lemma_repl_eq(x: Seq<u8>, y: Seq<u8>, hi: int, a: int, b: int)
    requires
        ag(x, y, hi),
        b < hi,
    ensures
        repl(y, a, b) == repl(x, a, b),
    decreases b - a,
{
    if 0 <= a < b {
        lemma_byte_eq(x, y, hi, a);
        lemma_byte_eq(x, y, hi, a + 1);
        if x[a] == 0x26 && byte_is(x, a + 1, 0x23) {
            lemma_charref_cut(x, y, hi, a);
            if charref(x, a) is Some {
                let e = charref(x, a).unwrap().1;
                if a < e <= b {
                    lemma_repl_eq(x, y, hi, e, b);
                }
            }
        } else if x[a] == 0x0D {
            lemma_repl_eq(x, y, hi, a + 1, b);
            if a + 1 < b {
                lemma_repl_eq(x, y, hi, a + 2, b);
            }
        } else {
            lemma_repl_eq(x, y, hi, a + 1, b);
        }
    }
}

pub proof fn lemma_oka_seq_eq(x: Seq<u8>, y: Seq<u8>, hi: int, ents: Seq<Ent>, wfc: bool, d: nat)
    requires
        ag(x, y, hi),
        ents_in(ents, hi),
    ensures
        oka_seq(y, ents, wfc, d) == oka_seq(x, ents, wfc, d),
    decreases d,
{
    if d > 0 {
        lemma_oka_seq_eq(x, y, hi, ents, wfc, (d - 1) as nat);
        let prev = oka_seq(x, ents, wfc, (d - 1) as nat);
        assert forall|k: int| 0 <= k < ents.len() implies ent_oka(y, ents, wfc, prev, k) == ent_oka(
            x,
            ents,
            wfc,
            prev,
            k,
        ) by {
            if let EKind::Internal { start, end } = ents[k].kind {
                assert(0 <= start <= end < hi);
                lemma_repl_eq(x, y, hi, start, end);
            }
        }
        assert(oka_seq(y, ents, wfc, d) =~= oka_seq(x, ents, wfc, d));
    } else {
        assert(oka_seq(y, ents, wfc, d) =~= oka_seq(x, ents, wfc, d));
    }
}

pub proof fn lemma_okc_seq_eq(x: Seq<u8>, y: Seq<u8>, hi: int, ents: Seq<Ent>, wfc: bool, oka: Seq<bool>, d: nat)
    requires
        ag(x, y, hi),
        ents_in(ents, hi),
    ensures
        okc_seq(y, ents, wfc, oka, d) == okc_seq(x, ents, wfc, oka, d),
    decreases d,
{
    if d > 0 {
        lemma_okc_seq_eq(x, y, hi, ents, wfc, oka, (d - 1) as nat);
        let prev = okc_seq(x, ents, wfc, oka, (d - 1) as nat);
        assert forall|k: int| 0 <= k < ents.len() implies ent_okc(y, ents, wfc, oka, prev, k) == ent_okc(
            x,
            ents,
            wfc,
            oka,
            prev,
            k,
        ) by {
            if let EKind::Internal { start, end } = ents[k].kind {
                assert(0 <= start <= end < hi);
                lemma_repl_eq(x, y, hi, start, end);
            }
        }
        assert(okc_seq(y, ents, wfc, oka, d) =~= okc_seq(x, ents, wfc, oka, d));
    } else {
        assert(okc_seq(y, ents, wfc, oka, d) =~= okc_seq(x, ents, wfc, oka, d));
    }
}

pub proof fn lemma_env_of_eq(x: Seq<u8>, y: Seq<u8>, hi: int, st: DtdSt, ext: bool)
    requires
        ag(x, y, hi),
        ents_in(st.ents, hi),
    ensures
        env_of(y, st, ext) == env_of(x, st, ext),
{
    let wfc = (!ext && !st.pe_seen) || st.sa;
    lemma_oka_seq_eq(x, y, hi, st.ents, wfc, st.ents.len());
    let oka = oka_seq(x, st.ents, wfc, st.ents.len());
    lemma_okc_seq_eq(x, y, hi, st.ents, wfc, oka, st.ents.len());
}

// ---------------------------------------------------------------------------
// The document type declaration, the defaults, the prolog
// ---------------------------------------------------------------------------

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_doctype_eq(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, t: Seq<XTok>, sa: bool)
    requires
        ag(x, y, hi),
        0 <= i,
        doctype(x, i, t, sa) matches Some((_, e, _)) && e <= hi,
    ensures
        doctype(y, i, t, sa) == doctype(x, i, t, sa),
        doctype(x, i, t, sa) matches Some((u, e, _)) && e > i + 9 && extends(t, u) && dflt_ok(x, added(t, u), hi),
{
    hide(external_id);
    hide(int_subset);
    hide(env_of);
    assert(lit_system() =~= seq![0x53u8, 0x59, 0x53, 0x54, 0x45, 0x4D]);
    assert(lit_public() =~= seq![0x50u8, 0x55, 0x42, 0x4C, 0x49, 0x43]);
    let j = ws_end(x, i + 9);
    lemma_ws_end_ge(x, i + 9);
    let n = name_end(x, j);
    lemma_name_end(x, j);
    let t1 = t.push(XTok::Doctype { start: j, end: n });
    let k = ws_end(x, n);
    lemma_ws_end_ws(x, n);
    let has_ext = k > n && (has_lit(x, k, lit_system()) || has_lit(x, k, lit_public()));
    let (u, e, env) = doctype(x, i, t, sa).unwrap();
    let (t2, e2, ext) = if has_ext {
        let (tt, ee) = external_id(x, k, t1).unwrap();
        (tt, ee, true)
    } else {
        (t1, n, false)
    };
    let m = ws_end(x, e2);
    lemma_ws_end_ge(x, e2);
    assert(ents_in(dtd_init(sa).ents, hi));
    if byte_is(x, m, 0x5B) {
        let (t3, st, q) = int_subset(x, m + 1, t2, dtd_init(sa)).unwrap();
        let r = ws_end(x, q + 1);
        lemma_ws_end_ge(x, q + 1);
        lemma_int_subset_eq(x, y, hi, m + 1, t2, dtd_init(sa));
        lemma_ws_eq(x, y, hi, q + 1);
        lemma_byte_eq(x, y, hi, r);
        lemma_env_of_eq(x, y, hi, st, ext);
        lemma_byte_is(x, y, 0, hi, 0, m, 0x5B);
        lemma_ws_eq(x, y, hi, e2);
        assert(u == t3.push(XTok::DoctypeEnd));
        assert(u.subrange(0, t3.len() as int) =~= t3);
        lemma_extends_trans(t2, t3, u);
        assert(added(t3, u) =~= seq![XTok::DoctypeEnd]);
        lemma_no_dflt_ok(x, added(t3, u), hi);
        lemma_dflt_ok_add(x, added(t2, t3), added(t3, u), hi);
    } else {
        lemma_byte_is(x, y, 0, hi, 0, m, 0x5B);
        lemma_byte_eq(x, y, hi, m);
        lemma_ws_eq(x, y, hi, e2);
        lemma_env_of_eq(x, y, hi, dtd_init(sa), ext);
        assert(u == t2.push(XTok::DoctypeEnd));
        assert(u.subrange(0, u.len() as int) =~= u);
        assert(u.subrange(0, t2.len() as int) =~= t2);
        assert(added(t2, u) =~= seq![XTok::DoctypeEnd]);
        lemma_no_dflt_ok(x, added(t2, u), hi);
    }
    if has_ext {
        lemma_external_id_eq(x, y, hi, k, t1);
        lemma_lit_eq(x, y, hi, k, lit_system());
        if !has_lit(x, k, lit_system()) {
            assert(x.subrange(k, k + 6)[0] == x[k]);
            lemma_not_lit(x, y, hi, k, lit_system());
            lemma_lit_eq(x, y, hi, k, lit_public());
        } else {
            lemma_lit_eq(x, y, hi, k, lit_system());
        }
        lemma_no_dflt_ok(x, added(t1, t2), hi);
    } else {
        if k > n {
            // No external identifier: `m == k`, where `[` or `>` is.
            lemma_not_lit(x, y, hi, k, lit_system());
            lemma_not_lit(x, y, hi, k, lit_public());
        }
        assert(t2.subrange(0, t2.len() as int) =~= t2);
        assert(added(t1, t2) =~= Seq::<XTok>::empty());
        lemma_no_dflt_ok(x, added(t1, t2), hi);
    }
    if k > n {
        assert(is_ws(x[n]));
    }
    lemma_ws_eq(x, y, hi, n);
    lemma_name_eq(x, y, hi, j);
    lemma_ws_eq(x, y, hi, i + 9);
    assert(t2.subrange(0, t1.len() as int) =~= t1);
    lemma_extends_push1(t, XTok::Doctype { start: j, end: n }, t2);
    lemma_extends_trans(t, t2, u);
    lemma_no_dflt_ok(x, seq![XTok::Doctype { start: j, end: n }], hi);
    lemma_dflt_ok_add(x, seq![XTok::Doctype { start: j, end: n }], added(t1, t2), hi);
    lemma_dflt_ok_add(x, added(t, t2), added(t2, u), hi);
}

/// A reference in an attribute value whose syntax ends before `hi`: the
/// same in both inputs, against any environment, and where it is allowed
/// it ends where its syntax does.
pub proof fn lemma_att_ref_env(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, env: Option<Env>)
    requires
        ag(x, y, hi),
        0 <= i < hi,
        att_ref(x, i, None) matches Some(e) && e <= hi,
    ensures
        att_ref(y, i, env) == att_ref(x, i, env),
        att_ref(x, i, env) is None || att_ref(x, i, env) == att_ref(x, i, None),
{
    lemma_name_end(x, i + 1);
    lemma_byte_is(x, y, 0, hi, 0, i + 1, 0x23);
    if byte_is(x, i + 1, 0x23) {
        lemma_charref_mv(x, y, 0, hi, 0, i);
    } else {
        let n = name_end(x, i + 1);
        lemma_name_end_mv(x, y, 0, hi, 0, i + 1);
        lemma_byte_is(x, y, 0, hi, 0, n, 0x3B);
        lemma_predef_mv(x, y, 0, hi, 0, i + 1, n);
        lemma_agree_span(x, y, 0, hi, 0, i + 1, n);
    }
}

/// An attribute value whose syntax ends before `hi`, against any
/// environment.
pub proof fn lemma_att_chars_env(x: Seq<u8>, y: Seq<u8>, hi: int, i: int, q: u8, env: Option<Env>)
    requires
        ag(x, y, hi),
        0 <= i,
        att_chars(x, i, q, None) matches Some(r) && r < hi,
    ensures
        att_chars(y, i, q, env) == att_chars(x, i, q, env),
    decreases x.len() - i,
{
    lemma_att_chars_quote(x, i, q, None);
    lemma_byte_eq(x, y, hi, i);
    if x[i] == q {
    } else if x[i] == 0x26 {
        let e = att_ref(x, i, None).unwrap();
        lemma_att_ref_end(x, i, None);
        lemma_att_chars_quote(x, e, q, None);
        lemma_att_ref_env(x, y, hi, i, env);
        if att_ref(x, i, env) is Some {
            lemma_att_chars_env(x, y, hi, e, q, env);
        }
    } else {
        lemma_att_chars_env(x, y, hi, i + 1, q, env);
    }
}

pub proof fn lemma_defaults_ok_eq(x: Seq<u8>, y: Seq<u8>, hi: int, t: Seq<XTok>, env: Env)
    requires
        ag(x, y, hi),
        dflt_ok(x, t, hi),
    ensures
        defaults_ok(y, t, env) == defaults_ok(x, t, env),
{
    reveal(dflt_ok);
    assert forall|k: int| 0 <= k < t.len() implies (match #[trigger] t[k] {
        XTok::AttDefault { start, end, kind, nents } => kind < 3 || (0 <= start <= end < y.len() && 0 <= nents
            <= env.ents.len() && att_chars(
            y,
            start,
            y[end],
            Some(Env { ents: env.ents.subrange(0, nents), wfc: env.wfc, oka: env.oka, okc: env.okc }),
        ) is Some),
        _ => true,
    }) == (match t[k] {
        XTok::AttDefault { start, end, kind, nents } => kind < 3 || (0 <= start <= end < x.len() && 0 <= nents
            <= env.ents.len() && att_chars(
            x,
            start,
            x[end],
            Some(Env { ents: env.ents.subrange(0, nents), wfc: env.wfc, oka: env.oka, okc: env.okc }),
        ) is Some),
        _ => true,
    }) by {
        assert(dflt_tok(x, t[k], hi));
        if let XTok::AttDefault { start, end, kind, nents } = t[k] {
            if kind >= 3 {
                lemma_byte_eq(x, y, hi, end);
                lemma_att_chars_env(
                    x,
                    y,
                    hi,
                    start,
                    x[end],
                    Some(Env { ents: env.ents.subrange(0, nents), wfc: env.wfc, oka: env.oka, okc: env.okc }),
                );
            }
        }
    }
}

/// `Misc` adds comments and processing instructions only.
pub proof fn lemma_misc_toks(x: Seq<u8>, i: int, t: Seq<XTok>)
    requires
        misc(x, i, t) is Some,
    ensures
        extends(t, misc(x, i, t).unwrap().0),
        no_dflt(added(t, misc(x, i, t).unwrap().0)),
    decreases x.len() - i,
{
    let j = ws_end(x, i);
    let u = misc(x, i, t).unwrap().0;
    if has_lit(x, j, lit_comment()) {
        let (t1, e) = comment(x, j, t).unwrap();
        lemma_misc_toks(x, e, t1);
        lemma_comment_tokens(x, j, t);
        assert(t1.subrange(0, t.len() as int) =~= t);
        lemma_extends_trans(t, t1, u);
        lemma_no_dflt_add(added(t, t1), added(t1, u));
    } else if has_lit(x, j, lit_pi()) {
        let (t1, e) = pi(x, j, t).unwrap();
        lemma_misc_toks(x, e, t1);
        lemma_pi_tokens(x, j, t);
        lemma_extends_trans(t, t1, u);
        lemma_no_dflt_add(added(t, t1), added(t1, u));
    } else {
        assert(u.subrange(0, t.len() as int) =~= t);
        assert(added(t, u) =~= Seq::<XTok>::empty());
    }
}

pub proof fn lemma_no_dflt_add(a: Seq<XTok>, b: Seq<XTok>)
    requires
        no_dflt(a),
        no_dflt(b),
    ensures
        no_dflt(a + b),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies !(#[trigger] (a + b)[k] is AttDefault) by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// Where the root element starts: `<` and a byte that is neither `!` nor
/// `?`, before `hi`. That decides every choice the prolog made.
pub open spec fn root_at(x: Seq<u8>, p: int, hi: int) -> bool {
    0 <= p && p + 1 < hi && hi <= x.len() && x[p] == 0x3C && x[p + 1] != 0x21 && x[p + 1] != 0x3F
}

pub proof fn lemma_misc_short(x: Seq<u8>, i: int, t: Seq<XTok>)
    requires
        0 <= i,
        misc(x, i, t) is Some,
        misc(x, i, t).unwrap().1 < i + 4,
        i < x.len(),
        x[i] == 0x3C,
    ensures
        misc(x, i, t).unwrap().1 == i,
{
    lemma_ws_end_ws(x, i);
    let j = ws_end(x, i);
    if has_lit(x, j, lit_comment()) {
        let (t1, e) = comment(x, j, t).unwrap();
        lemma_comment_end_ge(x, j + 4);
        lemma_misc_end_ge(x, e, t1);
    } else if has_lit(x, j, lit_pi()) {
        let (t1, e) = pi(x, j, t).unwrap();
        lemma_pi_min(x, j, t);
        lemma_misc_end_ge(x, e, t1);
    }
}

pub proof fn lemma_comment_end_ge(x: Seq<u8>, i: int)
    requires
        comment_end(x, i) is Some,
    ensures
        comment_end(x, i).unwrap() >= i + 3,
    decreases x.len() - i,
{
    if !(x[i] == 0x2D && byte_is(x, i + 1, 0x2D)) {
        lemma_comment_end_ge(x, i + 1);
    }
}

pub proof fn lemma_pi_end_ge(x: Seq<u8>, i: int)
    requires
        pi_end(x, i) is Some,
    ensures
        pi_end(x, i).unwrap() >= i + 2,
    decreases x.len() - i,
{
    if !(x[i] == 0x3F && byte_is(x, i + 1, 0x3E)) {
        lemma_pi_end_ge(x, i + 1);
    }
}

pub proof fn lemma_pi_min(x: Seq<u8>, i: int, t: Seq<XTok>)
    requires
        0 <= i,
        pi(x, i, t) is Some,
    ensures
        pi(x, i, t).unwrap().1 >= i + 5,
{
    let n = name_end(x, i + 2);
    lemma_name_end(x, i + 2);
    if !has_lit(x, n, lit_pi_end()) {
        lemma_ws_end_ge(x, n);
        lemma_pi_end_ge(x, ws_end(x, n));
    }
}

/// The prolog, once what follows it is known to be the root element.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
pub proof fn lemma_prolog_eq(x: Seq<u8>, y: Seq<u8>, hi: int, enc: Enc)
    requires
        ag(x, y, hi),
        prolog(x, enc) matches Some((_, p, _)) && root_at(x, p, hi),
    ensures
        prolog(y, enc) == prolog(x, enc),
{
    hide(xmldecl);
    hide(misc);
    hide(doctype);
    hide(defaults_ok);
    lemma_lits_stable();
    assert(lit_xmldecl() =~= seq![0x3Cu8, 0x3F, 0x78, 0x6D, 0x6C]);
    assert(lit_doctype() =~= seq![0x3Cu8, 0x21, 0x44, 0x4F, 0x43, 0x54, 0x59, 0x50, 0x45]);
    let (t3, p, env) = prolog(x, enc).unwrap();
    let (t0, p1, sd) = decl_head(x, enc).unwrap();
    let (t1, p2) = misc(x, p1, t0).unwrap();
    let (t2, p3, env2) = doctype_opt(x, p2, t1, sd).unwrap();
    let (t3b, p4) = misc(x, p3, t2).unwrap();
    assert(t3b == t3 && p4 == p && env2 == env);
    lemma_dflt_head(x, enc, hi);
    lemma_misc_end_ge(x, p1, t0);
    lemma_misc_end_ge(x, p3, t2);
    let p0 = bom_end(x);
    // The doctype, if any.
    let has_dt = has_lit(x, p2, lit_doctype());
    if has_dt {
        lemma_doctype_eq(x, y, hi, p2, t1, sd == 1);
        lemma_lit_eq(x, y, hi, p2, lit_doctype());
    } else {
        // Then the root element is at `p2`, which has `<` and not `!` after.
        assert(p3 == p2 && t2 == t1 && env == no_dtd());
        if p2 + 4 > hi && x[p2] == 0x3C {
            lemma_misc_short(x, p2, t1);
        }
        if x[p2] != 0x3C {
            lemma_not_lit(x, y, hi, p2, lit_doctype());
        } else if p2 + 9 <= hi {
            lemma_lit_eq(x, y, hi, p2, lit_doctype());
        } else if x[p2 + 1] != 0x21 {
            lemma_not_lit_at(x, y, hi, p2, lit_doctype(), 1);
        } else {
            // `<!` that is not the root: a comment, whose third byte is
            // `-`, not `D`.
            lemma_misc_bang(x, p2, t1);
            lemma_not_lit_at(x, y, hi, p2, lit_doctype(), 2);
        }
    }
    assert(p2 <= p3 <= p);
    // `Misc` after it.
    assert(misc_tail_ok(x, p, hi));
    lemma_misc_eq(x, y, hi, p3, t2);
    // `Misc` before it: what follows is a doctype or the root.
    if has_dt {
        assert(p2 + 9 <= hi);
    }
    assert(misc_tail_ok(x, p2, hi));
    lemma_misc_eq(x, y, hi, p1, t0);
    // The byte order mark and the XML declaration.
    if hi >= 3 {
        lemma_lit_eq(x, y, hi, 0, seq![0xEFu8, 0xBB, 0xBF]);
    } else {
        assert(p == 0);
        lemma_not_lit(x, y, hi, 0, seq![0xEFu8, 0xBB, 0xBF]);
    }
    assert(bom_end(y) == p0);
    let decl = has_lit(x, p0, lit_xmldecl()) && 0 <= p0 + 5 < x.len() && is_ws(x[p0 + 5]);
    if decl {
        lemma_xmldecl_end(x, p0, enc);
        lemma_xmldecl_eq(x, y, hi, p0, enc);
        lemma_lit_eq(x, y, hi, p0, lit_xmldecl());
        lemma_byte_eq(x, y, hi, p0 + 5);
    } else {
        assert(p1 == p0 && t0 == Seq::<XTok>::empty());
        if p0 + 6 <= hi {
            lemma_lit_eq(x, y, hi, p0, lit_xmldecl());
            lemma_byte_eq(x, y, hi, p0 + 5);
        } else if p == p0 {
            lemma_not_lit_at(x, y, hi, p0, lit_xmldecl(), 1);
        } else {
            // Something before the root in fewer than four bytes: white
            // space, since a comment, a processing instruction and a
            // doctype are longer.
            lemma_misc_short_ws(x, p0, t0, t1, p2, t2, p3, p);
            if x[p0] != 0x3C {
                lemma_not_lit(x, y, hi, p0, lit_xmldecl());
            } else {
                lemma_not_lit_at(x, y, hi, p0, lit_xmldecl(), 1);
            }
        }
    }
    // The defaults.
    lemma_misc_toks(x, p1, t0);
    lemma_misc_toks(x, p3, t2);
    if has_dt {
        lemma_extends_trans(t1, t2, t3);
    } else {
        assert(t2.subrange(0, t2.len() as int) =~= t2);
        assert(added(t1, t2) =~= Seq::<XTok>::empty());
        lemma_no_dflt_ok(x, added(t1, t2), hi);
    }
    lemma_no_dflt_ok(x, added(t0, t1), hi);
    lemma_no_dflt_ok(x, added(t2, t3), hi);
    lemma_dflt_ok_add(x, t0, added(t0, t1), hi);
    lemma_dflt_ok_add(x, added(t1, t2), added(t2, t3), hi);
    lemma_dflt_ok_add(x, t0 + added(t0, t1), added(t1, t2) + added(t2, t3), hi);
    assert(t3 =~= t0 + added(t0, t1) + (added(t1, t2) + added(t2, t3))) by {
        lemma_extends_trans(t0, t1, t2);
        lemma_extends_trans(t0, t2, t3);
        assert(t2 =~= t0 + added(t0, t2)) by {
            assert(t2.subrange(0, t0.len() as int) == t0);
        }
        assert(t3 =~= t0 + added(t0, t3)) by {
            assert(t3.subrange(0, t0.len() as int) == t0);
        }
    }
    lemma_defaults_ok_eq(x, y, hi, t3, env);
}

/// Before the root, in fewer than five bytes from `p0`: whatever is at
/// `p0` is not `<?`, since a processing instruction is longer.
proof fn lemma_misc_short_ws(
    x: Seq<u8>,
    p0: int,
    t0: Seq<XTok>,
    t1: Seq<XTok>,
    p2: int,
    t2: Seq<XTok>,
    p3: int,
    p: int,
)
    requires
        0 <= p0 < p <= p0 + 4,
        p + 1 < x.len(),
        misc(x, p0, t0) == Some((t1, p2)),
        has_lit(x, p2, lit_doctype()) ==> p3 > p2 + 9,
        !has_lit(x, p2, lit_doctype()) ==> p3 == p2 && t2 == t1,
        misc(x, p3, t2) matches Some((_, e)) && e == p,
    ensures
        x[p0] != 0x3C || x[p0 + 1] != 0x3F,
{
    lemma_misc_end_ge(x, p0, t0);
    lemma_misc_end_ge(x, p3, t2);
    if x[p0] == 0x3C {
        lemma_lits_stable();
        assert(!is_ws(x[p0]));
        assert(ws_end(x, p0) == p0);
        if has_lit(x, p0, lit_comment()) {
            assert(x.subrange(p0, p0 + 4)[1] == x[p0 + 1]);
        } else if has_lit(x, p0, lit_pi()) {
            let (t, e) = pi(x, p0, t0).unwrap();
            lemma_pi_min(x, p0, t0);
            lemma_misc_end_ge(x, e, t);
        } else {
            assert(p2 == p0 && t1 == t0);
            if has_lit(x, p2, lit_doctype()) {
                assert(x.subrange(p2, p2 + 9)[1] == x[p2 + 1]);
            }
        }
    }
}

proof fn lemma_misc_bang(x: Seq<u8>, i: int, t: Seq<XTok>)
    requires
        0 <= i,
        i + 1 < x.len(),
        x[i] == 0x3C,
        x[i + 1] == 0x21,
        misc(x, i, t) matches Some((_, e)) && e > i,
    ensures
        x[i + 2] == 0x2D,
        misc(x, i, t).unwrap().1 >= i + 7,
{
    lemma_lits_stable();
    assert(!is_ws(x[i]));
    assert(ws_end(x, i) == i);
    if has_lit(x, i, lit_comment()) {
        assert(x.subrange(i, i + 4)[2] == x[i + 2]);
        let (t1, e) = comment(x, i, t).unwrap();
        lemma_comment_end_ge(x, i + 4);
        lemma_misc_end_ge(x, e, t1);
    } else if has_lit(x, i, lit_pi()) {
        assert(x.subrange(i, i + 2)[1] == x[i + 1]);
    }
}

proof fn lemma_xmldecl_end(x: Seq<u8>, i: int, enc: Enc)
    requires
        xmldecl(x, i, enc) is Some,
    ensures
        xmldecl(x, i, enc).unwrap().1 >= 2,
        no_dflt(xmldecl(x, i, enc).unwrap().0),
{
}

proof fn lemma_dflt_head(x: Seq<u8>, enc: Enc, hi: int)
    requires
        decl_head(x, enc) is Some,
    ensures
        dflt_ok(x, decl_head(x, enc).unwrap().0, hi),
        decl_head(x, enc).unwrap().1 >= 0,
{
    let p0 = bom_end(x);
    if has_lit(x, p0, lit_xmldecl()) && 0 <= p0 + 5 < x.len() && is_ws(x[p0 + 5]) {
        lemma_xmldecl_end(x, p0, enc);
    }
    lemma_no_dflt_ok(x, decl_head(x, enc).unwrap().0, hi);
}

} // verus!

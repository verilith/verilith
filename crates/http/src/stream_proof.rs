//! The streaming head parser in `stream.rs` is the spec, byte at a time.
//!
//! - Soundness: whenever the machine accepts a head,
//!   `spec::parse_request` (or `parse_response`) accepts the same bytes,
//!   the head ends at the same byte, and the version, status and framing
//!   are the same. So everything proven about the spec parser, including
//!   the uniqueness theorems of `unique.rs`, holds for what the llhttp
//!   drop-in reports.
//! - Completeness: the machine accepts every head the spec accepts with a
//!   valid framing. So the drop-in's streaming path and its one-shot path
//!   (the verified `parse.rs` parser) accept exactly the same heads.
use crate::framing::*;
use crate::parse::*;
use crate::scan::*;
use crate::spec::*;
use crate::stream::*;
use crate::unique::*;
use crate::unique_chunked::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Runs by position
// ---------------------------------------------------------------------------

/// `hrun` from position `j` of `b`, with the position it stops at.
pub open spec fn hr(s: HS, b: Seq<u8>, j: int) -> Option<(HS, int)>
    decreases b.len() - j,
{
    if j < 0 || j >= b.len() || s.ph is Done {
        Some((s, j))
    } else {
        match hstep(s, b[j]) {
            None => None,
            Some(s2) => hr(s2, b, j + 1),
        }
    }
}

pub open spec fn fin(r: Option<(HS, int)>) -> bool {
    r matches Some((t, _)) && t.ph is Done
}

pub proof fn lemma_hr(s: HS, b: Seq<u8>, j: int)
    requires
        0 <= j <= b.len(),
    ensures
        hr(s, b, j) == match hrun(s, sfx(b, j)) {
            None => None,
            Some((t, k)) => Some((t, j + k)),
        },
    decreases b.len() - j,
{
    if j < b.len() && !(s.ph is Done) {
        assert(sfx(b, j)[0] == b[j]);
        assert(sfx(b, j).drop_first() =~= sfx(b, j + 1));
        if let Some(s2) = hstep(s, b[j]) {
            lemma_hr(s2, b, j + 1);
        }
    } else {
        assert(sfx(b, j).len() == 0 || s.ph is Done);
    }
}

/// The value check folded over `b[i..e]`.
pub open spec fn vr(v: VK, b: Seq<u8>, i: int, e: int) -> Option<VK>
    decreases e - i,
{
    if i >= e {
        Some(v)
    } else {
        match vstep(v, b[i]) {
            None => None,
            Some(v2) => vr(v2, b, i + 1, e),
        }
    }
}

/// The name matcher folded over `b[i..j]`.
pub open spec fn mf(b: Seq<u8>, i: int, j: int) -> NameM
    decreases j - i,
{
    if j <= i {
        name_start()
    } else {
        name_next(mf(b, i, j - 1), b[j - 1])
    }
}

// ---------------------------------------------------------------------------
// Small facts
// ---------------------------------------------------------------------------

proof fn lemma_crlf_at(b: Seq<u8>, i: int)
    requires
        0 <= i,
        i + 1 < b.len(),
        b[i] == CR,
        b[i + 1] == LF,
    ensures
        lit(b, i, crlf()) == Parsed::<()>::Done((), i + 2),
{
    assert(b.subrange(i, i + 2) =~= crlf().subrange(0, 2));
}

proof fn lemma_ci_sub(b: Seq<u8>, i: int, e: int, l: Seq<u8>)
    requires
        0 <= i <= e <= b.len(),
    ensures
        ci_eq(b.subrange(i, e), l) <==> (e - i == l.len() && forall|t: int|
            i <= t < e ==> lower(#[trigger] b[t]) == l[t - i]),
        ci_eq_dash(b.subrange(i, e), l) <==> (e - i == l.len() && forall|t: int|
            i <= t < e ==> dash_match(#[trigger] b[t], l[t - i])),
{
    let s = b.subrange(i, e);
    if e - i == l.len() {
        if ci_eq(s, l) {
            assert forall|t: int| i <= t < e implies lower(#[trigger] b[t]) == l[t - i] by {
                assert(s[t - i] == b[t]);
            }
        }
        if forall|t: int| i <= t < e ==> lower(#[trigger] b[t]) == l[t - i] {
            assert forall|k: int| 0 <= k < s.len() implies lower(#[trigger] s[k]) == l[k] by {
                assert(s[k] == b[i + k]);
            }
        }
        if ci_eq_dash(s, l) {
            assert forall|t: int| i <= t < e implies dash_match(#[trigger] b[t], l[t - i]) by {
                assert(s[t - i] == b[t]);
            }
        }
        if forall|t: int| i <= t < e ==> dash_match(#[trigger] b[t], l[t - i]) {
            assert forall|k: int| 0 <= k < s.len() implies lower(#[trigger] s[k]) == l[k] || (s[k]
                == 0x5F && l[k] == 0x2D) by {
                assert(s[k] == b[i + k]);
                assert(dash_match(b[i + k], l[(i + k) - i]));
            }
        }
    }
}

/// What the name matcher knows after `b[i..j]`.
proof fn lemma_mf(b: Seq<u8>, i: int, j: int)
    requires
        0 <= i <= j <= b.len(),
    ensures
        mf(b, i, j).len == (if j - i < 32 {
            j - i
        } else {
            32
        }),
        mf(b, i, j).cl <==> (j - i <= 14 && forall|t: int|
            i <= t < j ==> lower(#[trigger] b[t]) == name_content_length()[t - i]),
        mf(b, i, j).te <==> (j - i <= 17 && forall|t: int|
            i <= t < j ==> lower(#[trigger] b[t]) == name_transfer_encoding()[t - i]),
        mf(b, i, j).host <==> (j - i <= 4 && forall|t: int|
            i <= t < j ==> lower(#[trigger] b[t]) == name_host()[t - i]),
        mf(b, i, j).cld <==> (j - i <= 14 && forall|t: int|
            i <= t < j ==> dash_match(#[trigger] b[t], name_content_length()[t - i])),
        mf(b, i, j).ted <==> (j - i <= 17 && forall|t: int|
            i <= t < j ==> dash_match(#[trigger] b[t], name_transfer_encoding()[t - i])),
    decreases j - i,
{
    if j > i {
        lemma_mf(b, i, j - 1);
        let m = mf(b, i, j - 1);
        let c = b[j - 1];
        let l = m.len as int;
        // Each flag gains one conjunct for the byte at `j - 1`.
        if m.cl && l < 14 && lower(c) == name_content_length()[l] {
            assert(l == j - 1 - i);
        }
        if j - i <= 14 && forall|t: int|
            i <= t < j ==> lower(#[trigger] b[t]) == name_content_length()[t - i] {
            assert(lower(b[j - 1]) == name_content_length()[j - 1 - i]);
        }
        if m.te && l < 17 && lower(c) == name_transfer_encoding()[l] {
            assert(l == j - 1 - i);
        }
        if j - i <= 17 && forall|t: int|
            i <= t < j ==> lower(#[trigger] b[t]) == name_transfer_encoding()[t - i] {
            assert(lower(b[j - 1]) == name_transfer_encoding()[j - 1 - i]);
        }
        if m.host && l < 4 && lower(c) == name_host()[l] {
            assert(l == j - 1 - i);
        }
        if j - i <= 4 && forall|t: int| i <= t < j ==> lower(#[trigger] b[t]) == name_host()[t - i] {
            assert(lower(b[j - 1]) == name_host()[j - 1 - i]);
        }
        if m.cld && l < 14 && dash_match(c, name_content_length()[l]) {
            assert(l == j - 1 - i);
        }
        if j - i <= 14 && forall|t: int|
            i <= t < j ==> dash_match(#[trigger] b[t], name_content_length()[t - i]) {
            assert(dash_match(b[j - 1], name_content_length()[j - 1 - i]));
        }
        if m.ted && l < 17 && dash_match(c, name_transfer_encoding()[l]) {
            assert(l == j - 1 - i);
        }
        if j - i <= 17 && forall|t: int|
            i <= t < j ==> dash_match(#[trigger] b[t], name_transfer_encoding()[t - i]) {
            assert(dash_match(b[j - 1], name_transfer_encoding()[j - 1 - i]));
        }
    }
}

/// The matcher's verdicts are the spec's name comparisons.
proof fn lemma_name_kind(b: Seq<u8>, i: int, e: int)
    requires
        0 <= i <= e <= b.len(),
    ensures
        ({
            let m = mf(b, i, e);
            let name = b.subrange(i, e);
            &&& (m.len == 14 && m.cl) == ci_eq(name, name_content_length())
            &&& (m.len == 17 && m.te) == ci_eq(name, name_transfer_encoding())
            &&& (m.len == 4 && m.host) == ci_eq(name, name_host())
            &&& (m.len == 14 && m.cld) == ci_eq_dash(name, name_content_length())
            &&& (m.len == 17 && m.ted) == ci_eq_dash(name, name_transfer_encoding())
        }),
{
    lemma_mf(b, i, e);
    lemma_ci_sub(b, i, e, name_content_length());
    lemma_ci_sub(b, i, e, name_transfer_encoding());
    lemma_ci_sub(b, i, e, name_host());
}

// ---------------------------------------------------------------------------
// Field values
// ---------------------------------------------------------------------------

/// Which kind of check a value state belongs to.
pub open spec fn fam(v: VK) -> int {
    match v {
        VK::Other => 0,
        VK::Host => 1,
        VK::ClLead => 2,
        VK::ClDig { .. } => 2,
        VK::ClTrail { .. } => 2,
        _ => 3,
    }
}

/// The state that trailing OWS leads to; `apply` treats both alike.
pub open spec fn norm(v: VK) -> VK {
    match v {
        VK::ClDig { n, .. } => VK::ClTrail { n },
        VK::TeTok { k, m } => VK::TeAfter { last: tok_end(k, m) },
        VK::TeSep { last } => VK::TeAfter { last },
        _ => v,
    }
}

/// The Content-Length a value state stands for.
pub open spec fn clres(o: Option<VK>) -> Option<u64> {
    match o {
        Some(VK::ClDig { n, .. }) => Some(n),
        Some(VK::ClTrail { n }) => Some(n),
        _ => None,
    }
}

/// The transfer codings a value state stands for.
pub open spec fn teres(o: Option<VK>) -> Option<TeState> {
    match o {
        Some(VK::TeSep { last }) => Some(TeState { present: true, chunked_last: last }),
        Some(VK::TeTok { k, m }) => Some(TeState { present: true, chunked_last: tok_end(k, m) }),
        Some(VK::TeAfter { last }) => Some(TeState { present: true, chunked_last: last }),
        _ => None,
    }
}

proof fn lemma_norm(v: VK)
    ensures
        fam(norm(v)) == fam(v),
        clres(Some(norm(v))) == clres(Some(v)),
        teres(Some(norm(v))) == teres(Some(v)),
        forall|f: FieldsExec| apply(f, norm(v)) == apply(f, v),
{
}

proof fn lemma_fam(v: VK, b: Seq<u8>, i: int, e: int)
    ensures
        vr(v, b, i, e) matches Some(y) ==> fam(y) == fam(v),
    decreases e - i,
{
    if i < e {
        if let Some(v2) = vstep(v, b[i]) {
            lemma_fam(v2, b, i + 1, e);
        }
    }
}

/// `vr` over `b[i..e]` is `vr` over `b[i..m]`, then over `b[m..e]`.
proof fn lemma_vr_split(v: VK, b: Seq<u8>, i: int, m: int, e: int)
    requires
        i <= m <= e,
    ensures
        vr(v, b, i, e) == match vr(v, b, i, m) {
            None => None,
            Some(x) => vr(x, b, m, e),
        },
    decreases m - i,
{
    if i < m {
        if let Some(v2) = vstep(v, b[i]) {
            lemma_vr_split(v2, b, i + 1, m, e);
        }
    }
}

/// OWS that the state ignores.
proof fn lemma_vr_keep(v: VK, b: Seq<u8>, i: int, p: int, e: int)
    requires
        i <= p <= e,
        forall|t: int| i <= t < p ==> is_ows(#[trigger] b[t]),
        forall|c: u8| is_ows(c) ==> vstep(v, c) == Some(v),
    ensures
        vr(v, b, i, e) == vr(v, b, p, e),
    decreases p - i,
{
    if i < p {
        assert(is_ows(b[i]));
        lemma_vr_keep(v, b, i + 1, p, e);
    }
}

/// Trailing OWS changes the state only to an equivalent one.
proof fn lemma_vr_tail(v: VK, b: Seq<u8>, p: int, e: int)
    requires
        p <= e,
        forall|t: int| p <= t < e ==> is_ows(#[trigger] b[t]),
    ensures
        vr(v, b, p, e) matches Some(y) && norm(y) == norm(v),
    decreases e - p,
{
    if p < e {
        assert(is_ows(b[p]));
        let v2 = vstep(v, b[p])->Some_0;
        lemma_vr_tail(v2, b, p + 1, e);
    }
}

proof fn lemma_vr_shift(v: VK, b: Seq<u8>, p: int, q: int, k: int)
    requires
        0 <= p <= q <= b.len(),
        0 <= k <= q - p,
    ensures
        vr(v, b, p + k, q) == vr(v, b.subrange(p, q), k, q - p),
    decreases q - p - k,
{
    if k < q - p {
        assert(b.subrange(p, q)[k] == b[p + k]);
        if let Some(v2) = vstep(v, b[p + k]) {
            lemma_vr_shift(v2, b, p, q, k + 1);
        }
    }
}

/// A value read from just after the colon (`a`) to its CR (`e`) checks as
/// the spec's trimmed value does.
proof fn lemma_trimmed(v: VK, b: Seq<u8>, a: int, e: int)
    requires
        0 <= a <= e <= b.len(),
        run_end(b, a, Cls::Ows) <= e,
        v == VK::ClLead || v == (VK::TeSep { last: false }),
    ensures
        ({
            let vs = run_end(b, a, Cls::Ows);
            let w = b.subrange(vs, trim_end(b, vs, e));
            match vr(v, b, a, e) {
                None => vr(v, w, 0, w.len() as int) is None,
                Some(y) => vr(v, w, 0, w.len() as int) matches Some(z) && norm(y) == norm(z),
            }
        }),
{
    let vs = run_end(b, a, Cls::Ows);
    lemma_run_end_bounds(b, a, Cls::Ows);
    lemma_trim_end(b, vs, e);
    let te = trim_end(b, vs, e);
    lemma_vr_keep(v, b, a, vs, e);
    lemma_vr_split(v, b, vs, te, e);
    lemma_vr_shift(v, b, vs, te, 0);
    if let Some(x) = vr(v, b, vs, te) {
        lemma_vr_tail(x, b, te, e);
    }
}

proof fn lemma_pow10_19()
    ensures
        pow10(19) == 10000000000000000000nat,
{
    assert(pow10(19) == 10000000000000000000nat) by (compute_only);
}

/// The digits `w[0..i]` read so far.
proof fn lemma_cl_digits(w: Seq<u8>, i: int)
    requires
        1 <= i <= w.len(),
        i <= 19,
        forall|t: int| 0 <= t < i ==> is_digit(#[trigger] w[t]),
    ensures
        decimal(w.subrange(0, i)) < pow10(i as nat),
        vr(VK::ClLead, w, 0, w.len() as int) == vr(
            VK::ClDig { n: decimal(w.subrange(0, i)) as u64, cnt: i as u8 },
            w,
            i,
            w.len() as int,
        ),
    decreases i,
{
    let s = w.subrange(0, i);
    assert forall|t: int| 0 <= t < s.len() implies is_digit(#[trigger] s[t]) by {
        assert(s[t] == w[t]);
    }
    lemma_decimal_bound(s);
    if i == 1 {
        assert(s.drop_last() =~= Seq::<u8>::empty());
        assert(decimal(s) == (w[0] - 0x30) as nat);
    } else {
        lemma_cl_digits(w, i - 1);
        let s0 = w.subrange(0, i - 1);
        assert(s.drop_last() =~= s0);
        lemma_pow10_mono((i - 1) as nat, 18);
        lemma_pow10_19();
        lemma_pow10_mono(i as nat, 19);
        assert(pow10(18) == 10 * pow10(17));
        let n0 = decimal(s0);
        assert(decimal(s) == n0 * 10 + (w[i - 1] - 0x30) as nat);
    }
}

proof fn lemma_cl_trail(w: Seq<u8>, q: int, n: u64)
    requires
        0 <= q < w.len(),
        !is_ows(w[w.len() - 1]),
    ensures
        vr(VK::ClTrail { n }, w, q, w.len() as int) is None,
    decreases w.len() - q,
{
    if is_ows(w[q]) {
        lemma_cl_trail(w, q + 1, n);
    }
}

/// A trimmed Content-Length value.
proof fn lemma_cl_value(w: Seq<u8>)
    requires
        w.len() > 0 ==> !is_ows(w[0]) && !is_ows(w[w.len() - 1]),
    ensures
        clres(vr(VK::ClLead, w, 0, w.len() as int)) == content_length_value(w),
{
    let n = w.len() as int;
    if n == 0 {
        return ;
    }
    if !is_digit(w[0]) {
        return ;
    }
    // The leading digits, at most 20 of them.
    let p = run_end(w, 0, Cls::Digit);
    lemma_run_end_bounds(w, 0, Cls::Digit);
    lemma_pow10_19();
    if p > 19 {
        lemma_cl_digits(w, 19);
        assert(is_digit(w[19]));
        assert(!(w.len() <= MAX_CL_DIGITS));
    } else {
        lemma_cl_digits(w, p);
        let d = decimal(w.subrange(0, p));
        lemma_pow10_mono(p as nat, 19);
        if p == n {
            assert(w.subrange(0, p) =~= w);
        } else {
            assert(!is_digit(w[p]));
            if is_ows(w[p]) {
                lemma_cl_trail(w, p + 1, d as u64);
            }
        }
    }
}

/// The transfer codings in a chunked-prefix matcher after `w[a..j]`.
pub open spec fn tk(w: Seq<u8>, a: int, j: int) -> VK
    decreases j - a,
{
    if j <= a {
        VK::TeTok { k: 0, m: true }
    } else {
        match tk(w, a, j - 1) {
            VK::TeTok { k, m } => VK::TeTok {
                k: if k < 8 {
                    (k + 1) as u8
                } else {
                    8
                },
                m: m && k < 7 && lower(w[j - 1]) == coding_chunked()[k as int],
            },
            x => x,
        }
    }
}

proof fn lemma_tk(w: Seq<u8>, a: int, j: int)
    requires
        0 <= a <= j <= w.len(),
    ensures
        tk(w, a, j) matches VK::TeTok { k, m } && k == (if j - a < 8 {
            j - a
        } else {
            8
        }) && (m <==> (j - a <= 7 && forall|t: int|
            a <= t < j ==> lower(#[trigger] w[t]) == coding_chunked()[t - a])),
    decreases j - a,
{
    if j > a {
        lemma_tk(w, a, j - 1);
        if j - a <= 7 && forall|t: int|
            a <= t < j ==> lower(#[trigger] w[t]) == coding_chunked()[t - a] {
            assert(lower(w[j - 1]) == coding_chunked()[j - 1 - a]);
        }
    }
}

/// A coding `w[a..j]` read from the start of a list element.
proof fn lemma_tok_run(w: Seq<u8>, a: int, j: int)
    requires
        0 <= a < j <= w.len(),
        forall|t: int| a <= t < j ==> is_tchar(#[trigger] w[t]),
    ensures
        vr(VK::TeSep { last: false }, w, a, w.len() as int) == vr(tk(w, a, j), w, j, w.len() as int),
    decreases j - a,
{
    assert(is_tchar(w[j - 1]));
    if j > a + 1 {
        lemma_tok_run(w, a, j - 1);
        lemma_tk(w, a, j - 1);
    } else {
        assert(tk(w, a, a) == VK::TeTok { k: 0, m: true });
    }
}

/// The transfer-coding list `w[i..]`.
proof fn lemma_te_value(w: Seq<u8>, i: int, l: bool)
    requires
        0 <= i <= w.len(),
    ensures
        te_list(w, i, TeState { present: true, chunked_last: l }) == teres(
            vr(VK::TeSep { last: l }, w, i, w.len() as int),
        ),
    decreases w.len() - i,
{
    let n = w.len() as int;
    let a = run_end(w, i, Cls::Ows);
    lemma_run_end_bounds(w, i, Cls::Ows);
    lemma_vr_keep(VK::TeSep { last: l }, w, i, a, n);
    if a >= n {
    } else if w[a] == COMMA {
        lemma_te_value(w, a + 1, l);
    } else {
        let e = run_end(w, a, Cls::Token);
        lemma_run_end_bounds(w, a, Cls::Token);
        if e == a || l {
        } else {
            lemma_tok_run(w, a, e);
            lemma_tk(w, a, e);
            lemma_ci_sub(w, a, e, coding_chunked());
            let lst = ci_eq(w.subrange(a, e), coding_chunked());
            let x = tk(w, a, e);
            assert(tok_end(x->TeTok_k, x->TeTok_m) == lst);
            let f = run_end(w, e, Cls::Ows);
            lemma_run_end_bounds(w, e, Cls::Ows);
            if e < f {
                assert(is_ows(w[e]));
                lemma_vr_keep(VK::TeAfter { last: lst }, w, e + 1, f, n);
            }
            if f >= n {
            } else if w[f] == COMMA {
                lemma_te_value(w, f + 1, lst);
            } else {
            }
        }
    }
}

/// `apply` on a value state of each kind.
proof fn lemma_apply(f: FieldsExec, x: VK)
    ensures
        fam(x) == 2 ==> apply(f, x) == match clres(Some(x)) {
            Some(n) => if f.cl is None || f.cl == Some(n) {
                Some(FieldsExec { cl: Some(n), ..f })
            } else {
                None
            },
            None => None,
        },
        fam(x) == 3 ==> apply(f, x) == Some(FieldsExec { te: teres(Some(x))->Some_0, ..f }),
{
}

// ---------------------------------------------------------------------------
// Field lines
// ---------------------------------------------------------------------------

/// A value from `j` to its CR LF.
proof fn lemma_val(s: HS, v: VK, b: Seq<u8>, j: int)
    requires
        0 <= j <= b.len(),
        s.ph == (Ph::Val { v }),
        fin(hr(s, b, j)),
    ensures
        ({
            let e = run_end(b, j, Cls::Value);
            &&& e + 1 < b.len()
            &&& b[e] == CR
            &&& b[e + 1] == LF
            &&& vr(v, b, j, e) matches Some(x) && apply(s.f, x) matches Some(f2) && hr(s, b, j) == hr(
                HS { ph: Ph::Line, f: f2, ..s },
                b,
                e + 2,
            )
        }),
    decreases b.len() - j,
{
    lemma_run_end_bounds(b, j, Cls::Value);
    let c = b[j];
    if c == CR {
        let s1 = HS { ph: Ph::ValLf { v }, ..s };
        assert(hr(s, b, j) == hr(s1, b, j + 1));
    } else {
        let v2 = vstep(v, c)->Some_0;
        let s1 = HS { ph: Ph::Val { v: v2 }, ..s };
        assert(hr(s, b, j) == hr(s1, b, j + 1));
        lemma_val(s1, v2, b, j + 1);
    }
}

/// A field name from `i`, `b[i..j]` read so far.
proof fn lemma_name(s: HS, b: Seq<u8>, i: int, j: int)
    requires
        0 <= i < j <= b.len(),
        s.ph == (Ph::Name { m: mf(b, i, j) }),
        fin(hr(s, b, j)),
        forall|t: int| i <= t < j ==> is_tchar(#[trigger] b[t]),
    ensures
        ({
            let e = run_end(b, j, Cls::Token);
            &&& e < b.len()
            &&& b[e] == COLON
            &&& run_end(b, i, Cls::Token) == e
            &&& name_end(s.f, mf(b, i, e)) matches Some(v) && hr(s, b, j) == hr(
                HS { ph: Ph::Val { v }, ..s },
                b,
                e + 1,
            )
        }),
    decreases b.len() - j,
{
    let c = b[j];
    if is_tchar(c) {
        let s1 = HS { ph: Ph::Name { m: mf(b, i, j + 1) }, ..s };
        assert(hr(s, b, j) == hr(s1, b, j + 1));
        lemma_name(s1, b, i, j + 1);
    } else {
        lemma_run_skip(b, i, j, Cls::Token);
    }
}

/// One field line from `i`: the spec reads the same field, and the
/// machine's fields still agree with the spec's.
proof fn lemma_line(s: HS, b: Seq<u8>, i: int, g: Fields) -> (f2: FieldsExec)
    requires
        0 <= i < b.len(),
        s.ph == Ph::Line,
        b[i] != CR,
        fin(hr(s, b, i)),
        fields_agree(s.f, g),
    ensures
        parse_header(b, i) matches Parsed::Done(h, n) && (i < n && hr(s, b, i) == hr(
            HS { ph: Ph::Line, f: f2, ..s },
            b,
            n,
        ) && (fields_step(b, g, h) matches Some(g2) && fields_agree(f2, g2))),
{
    let c = b[i];
    let s1 = HS { ph: Ph::Name { m: mf(b, i, i + 1) }, ..s };
    assert(mf(b, i, i) == name_start());
    assert(hr(s, b, i) == hr(s1, b, i + 1));
    lemma_name(s1, b, i, i + 1);
    let ne = run_end(b, i + 1, Cls::Token);
    lemma_run_end_bounds(b, i + 1, Cls::Token);
    let m = mf(b, i, ne);
    let v = name_end(s.f, m)->Some_0;
    let s2 = HS { ph: Ph::Val { v }, ..s };
    let a = ne + 1;
    lemma_val(s2, v, b, a);
    let e = run_end(b, a, Cls::Value);
    let x = vr(v, b, a, e)->Some_0;
    let f2 = apply(s.f, x)->Some_0;
    // The spec's value: OWS, then the value, trimmed.
    let vs = run_end(b, a, Cls::Ows);
    lemma_run_end_bounds(b, a, Cls::Ows);
    assert forall|t: int| a <= t < vs implies in_cls(Cls::Value, #[trigger] b[t]) by {
        assert(in_cls(Cls::Ows, b[t]));
    }
    lemma_run_skip(b, a, vs, Cls::Value);
    lemma_run_end_bounds(b, vs, Cls::Value);
    lemma_trim_end(b, vs, e);
    lemma_crlf_at(b, e);
    let te = trim_end(b, vs, e);
    let h = SpecHeader { name: SpecSpan { start: i, end: ne }, value: SpecSpan { start: vs, end: te } };
    assert(parse_header(b, i) == Parsed::Done(h, e + 2));
    let w = b.subrange(vs, te);
    assert(span_bytes(b, h.value) == w);
    if te > vs {
        assert(w[0] == b[vs]);
        assert(w[w.len() - 1] == b[te - 1]);
    }
    lemma_name_kind(b, i, ne);
    lemma_fam(v, b, a, e);
    lemma_norm(x);
    lemma_apply(s.f, x);
    if v == VK::ClLead || v == (VK::TeSep { last: false }) {
        lemma_trimmed(v, b, a, e);
        let z = vr(v, w, 0, w.len() as int)->Some_0;
        lemma_norm(z);
        if v == VK::ClLead {
            lemma_cl_value(w);
        } else {
            lemma_te_value(w, 0, false);
        }
    }
    f2
}

/// A forward fold of `fields_step`.
pub open spec fn fields_from(b: Seq<u8>, g: Fields, hs: Seq<SpecHeader>) -> Option<Fields>
    decreases hs.len(),
{
    if hs.len() == 0 {
        Some(g)
    } else {
        match fields_step(b, g, hs[0]) {
            None => None,
            Some(g2) => fields_from(b, g2, hs.drop_first()),
        }
    }
}

proof fn lemma_fields_from(b: Seq<u8>, p: Seq<SpecHeader>, q: Seq<SpecHeader>)
    ensures
        fields_of(b, p + q) == match fields_of(b, p) {
            None => None,
            Some(g) => fields_from(b, g, q),
        },
    decreases q.len(),
{
    if q.len() == 0 {
        assert(p + q =~= p);
    } else {
        let p2 = p.push(q[0]);
        assert(p + q =~= p2 + q.drop_first());
        assert(p2.drop_last() =~= p);
        lemma_fields_from(b, p2, q.drop_first());
    }
}

/// The field lines from `i` to the empty line.
proof fn lemma_lines(s: HS, b: Seq<u8>, i: int, max: nat, g: Fields)
    requires
        0 <= i <= b.len(),
        s.ph == Ph::Line,
        fin(hr(s, b, i)),
        fields_agree(s.f, g),
        max >= b.len() - i,
    ensures
        parse_headers(b, i, max) matches Parsed::Done(hs, end) && (hr(s, b, i) matches Some((t, e))
            && (e == end && t.ph is Done && t.minor == s.minor && t.status == s.status && t.req
            == s.req && t.host == s.host && head_ok(t) && (fields_from(b, g, hs) matches Some(g2) && fields_agree(
            t.f,
            g2,
        )))),
    decreases b.len() - i,
{
    if b[i] == CR {
        let s1 = HS { ph: Ph::EndLf, ..s };
        assert(hr(s, b, i) == hr(s1, b, i + 1));
        let t = HS { ph: Ph::Done, ..s };
        assert(hr(s1, b, i + 1) == hr(t, b, i + 2));
        assert(hr(t, b, i + 2) == Some((t, i + 2)));
        lemma_crlf_at(b, i);
        assert(Seq::<SpecHeader>::empty().len() == 0);
    } else {
        let f2 = lemma_line(s, b, i, g);
        let h = parse_header(b, i)->Done_0;
        let n = parse_header(b, i)->Done_1;
        let g2 = fields_step(b, g, h)->Some_0;
        let s1 = HS { ph: Ph::Line, f: f2, ..s };
        lemma_lines(s1, b, n, (max - 1) as nat, g2);
        let hs = parse_headers(b, n, (max - 1) as nat)->Done_0;
        let hs2 = seq![h] + hs;
        assert(hs2[0] == h);
        assert(hs2.drop_first() =~= hs);
    }
}

// ---------------------------------------------------------------------------
// Start lines
// ---------------------------------------------------------------------------

proof fn lemma_rstart(s: HS, b: Seq<u8>, j: int)
    requires
        0 <= j <= b.len(),
        s.ph == Ph::RStart,
        fin(hr(s, b, j)),
    ensures
        skip_empty_lines(b, j) matches Parsed::Done(_, p) && j <= p < b.len() && is_tchar(b[p])
            && hr(s, b, j) == hr(HS { ph: Ph::Method, ..s }, b, p + 1),
    decreases b.len() - j,
{
    if b[j] == CR {
        let s1 = HS { ph: Ph::RStartLf, ..s };
        assert(hr(s, b, j) == hr(s1, b, j + 1));
        assert(hr(s1, b, j + 1) == hr(s, b, j + 2));
        lemma_rstart(s, b, j + 2);
    }
}

/// A run of class `k` in phase `ph`, ended by SP, which leads to `next`.
proof fn lemma_word(s: HS, b: Seq<u8>, j: int, k: Cls, next: Ph)
    requires
        0 <= j <= b.len(),
        fin(hr(s, b, j)),
        (s.ph == Ph::Method && k == Cls::Token && next == Ph::Target0) || (s.ph == Ph::Target && k
            == Cls::Target && next == (Ph::RVer { k: 0 })),
    ensures
        ({
            let e = run_end(b, j, k);
            &&& e < b.len()
            &&& b[e] == SP
            &&& hr(s, b, j) == hr(HS { ph: next, ..s }, b, e + 1)
        }),
    decreases b.len() - j,
{
    if in_cls(k, b[j]) {
        lemma_word(s, b, j + 1, k, next);
    }
}

/// `HTTP/1.x` with `k` bytes of it already read, in a request line
/// (`req`) or a status line.
proof fn lemma_ver(s: HS, b: Seq<u8>, j: int, k: int, req: bool)
    requires
        0 <= j <= b.len(),
        0 <= k <= 7,
        s.ph == (if req {
            Ph::RVer { k: k as u8 }
        } else {
            Ph::SVer { k: k as u8 }
        }),
        fin(hr(s, b, j)),
    ensures
        j + 7 - k < b.len(),
        forall|t: int| k <= t < 7 ==> b[j + t - k] == #[trigger] http1_prefix()[t],
        is_digit(b[j + 7 - k]),
        hr(s, b, j) == hr(
            HS {
                ph: if req {
                    Ph::RCr
                } else {
                    Ph::SSp
                },
                minor: (b[j + 7 - k] - 0x30) as u8,
                ..s
            },
            b,
            j + 8 - k,
        ),
    decreases 7 - k,
{
    if k < 7 {
        let s1 = HS {
            ph: if req {
                Ph::RVer { k: (k + 1) as u8 }
            } else {
                Ph::SVer { k: (k + 1) as u8 }
            },
            ..s
        };
        assert(hr(s, b, j) == hr(s1, b, j + 1));
        lemma_ver(s1, b, j + 1, k + 1, req);
    }
}

proof fn lemma_version_at(b: Seq<u8>, v: int)
    requires
        0 <= v,
        v + 7 < b.len(),
        forall|t: int| 0 <= t < 7 ==> b[v + t] == #[trigger] http1_prefix()[t],
        is_digit(b[v + 7]),
    ensures
        parse_version(b, v) == Parsed::Done((b[v + 7] - 0x30) as u8, v + 8),
{
    assert(b.subrange(v, v + 7) =~= http1_prefix().subrange(0, 7));
}

/// The reason phrase and the end of the status line.
proof fn lemma_reason(s: HS, b: Seq<u8>, j: int)
    requires
        0 <= j <= b.len(),
        s.ph == Ph::Reason,
        fin(hr(s, b, j)),
    ensures
        ({
            let e = run_end(b, j, Cls::Value);
            &&& e + 1 < b.len()
            &&& b[e] == CR
            &&& b[e + 1] == LF
            &&& hr(s, b, j) == hr(HS { ph: Ph::Line, ..s }, b, e + 2)
        }),
    decreases b.len() - j,
{
    if b[j] == CR {
        let s1 = HS { ph: Ph::SLf, ..s };
        assert(hr(s, b, j) == hr(s1, b, j + 1));
    } else {
        lemma_reason(s, b, j + 1);
    }
}

// ---------------------------------------------------------------------------
// Theorems
// ---------------------------------------------------------------------------

/// A head the streaming machine accepts is a head the spec accepts, with
/// the same end, version and framing.
///
/// With `host` false (the Host rule left to the caller), the same holds
/// with `request_framing` in place of `request_body`.
#[verifier::spinoff_prover]
pub proof fn theorem_stream_request(b: Seq<u8>, max: nat, host: bool)
    requires
        hrun(request_start_with(host), b) matches Some((t, _)) && t.ph is Done,
        max >= b.len(),
    ensures
        ({
            let (t, k) = hrun(request_start_with(host), b)->Some_0;
            parse_request(b, max) matches Parsed::Done(r, end) && (end == k && r.minor == t.minor
                && (fields_of(b, r.headers) matches Some(g) && (fields_agree(t.f, g) && request_framing(
                g,
                r.minor,
            ) == request_framing_x(t.f, t.minor) && request_framing(g, r.minor) is Some)) && (host
                ==> request_body(b, r) == request_framing_x(t.f, t.minor) && request_body(b, r) is Some))
        }),
{
    let s0 = request_start_with(host);
    let (t, k) = hrun(s0, b)->Some_0;
    lemma_hr(s0, b, 0);
    assert(sfx(b, 0) =~= b);
    lemma_rstart(s0, b, 0);
    let p = skip_empty_lines(b, 0)->Done_1;
    let s1 = HS { ph: Ph::Method, ..s0 };
    lemma_word(s1, b, p + 1, Cls::Token, Ph::Target0);
    let me = run_end(b, p + 1, Cls::Token);
    assert(run_end(b, p, Cls::Token) == me);
    lemma_run_end_bounds(b, p + 1, Cls::Token);
    let s2 = HS { ph: Ph::Target0, ..s0 };
    let t0 = me + 1;
    let s3 = HS { ph: Ph::Target, ..s0 };
    assert(hr(s2, b, t0) == hr(s3, b, t0 + 1));
    lemma_word(s3, b, t0 + 1, Cls::Target, Ph::RVer { k: 0 });
    let te = run_end(b, t0 + 1, Cls::Target);
    assert(run_end(b, t0, Cls::Target) == te);
    lemma_run_end_bounds(b, t0 + 1, Cls::Target);
    let v = te + 1;
    let s4 = HS { ph: Ph::RVer { k: 0 }, ..s0 };
    lemma_ver(s4, b, v, 0, true);
    lemma_version_at(b, v);
    let minor = (b[v + 7] - 0x30) as u8;
    let s5 = HS { ph: Ph::RCr, minor, ..s0 };
    let s6 = HS { ph: Ph::Line, minor, ..s0 };
    let s5b = HS { ph: Ph::RLf, minor, ..s0 };
    assert(hr(s5, b, v + 8) == hr(s5b, b, v + 9));
    assert(hr(s5b, b, v + 9) == hr(s6, b, v + 10));
    lemma_crlf_at(b, v + 8);
    lemma_lines(s6, b, v + 10, max, fields_init());
    let hs = parse_headers(b, v + 10, max)->Done_0;
    lemma_fields_from(b, Seq::empty(), hs);
    assert(Seq::<SpecHeader>::empty() + hs =~= hs);
}

/// The same for responses, whatever the request was.
pub proof fn theorem_stream_response(b: Seq<u8>, max: nat, head: bool, connect: bool)
    requires
        hrun(response_start(), b) matches Some((t, _)) && t.ph is Done,
        max >= b.len(),
    ensures
        ({
            let (t, k) = hrun(response_start(), b)->Some_0;
            parse_response(b, max) matches Parsed::Done(r, end) && (end == k && r.minor == t.minor
                && r.status == t.status && (fields_of(b, r.headers) matches Some(g) && fields_agree(
                t.f,
                g,
            )) && response_body(b, r, head, connect) == response_framing_x(
                t.f,
                t.minor,
                t.status,
                head,
                connect,
            ) && response_body(b, r, head, connect) is Some)
        }),
{
    let s0 = response_start();
    let (t, k) = hrun(s0, b)->Some_0;
    lemma_hr(s0, b, 0);
    assert(sfx(b, 0) =~= b);
    lemma_ver(s0, b, 0, 0, false);
    lemma_version_at(b, 0);
    let minor = (b[7] - 0x30) as u8;
    let s1 = HS { ph: Ph::SSp, minor, ..s0 };
    let s2 = HS { ph: Ph::Code { k: 0 }, minor, ..s0 };
    assert(hr(s1, b, 8) == hr(s2, b, 9));
    let d0 = (b[9] - 0x30) as u16;
    let s3 = HS { ph: Ph::Code { k: 1 }, minor, status: d0, ..s0 };
    assert(hr(s2, b, 9) == hr(s3, b, 10));
    let d1 = (d0 * 10 + (b[10] - 0x30)) as u16;
    let s4 = HS { ph: Ph::Code { k: 2 }, minor, status: d1, ..s0 };
    assert(hr(s3, b, 10) == hr(s4, b, 11));
    let st = (d1 * 10 + (b[11] - 0x30)) as u16;
    let s5 = HS { ph: Ph::Code { k: 3 }, minor, status: st, ..s0 };
    assert(hr(s4, b, 11) == hr(s5, b, 12));
    assert(parse_status(b, 9) == Parsed::Done(st, 12));
    let s6 = HS { ph: Ph::Line, minor, status: st, ..s0 };
    let he;
    if b[12] == SP {
        let s7 = HS { ph: Ph::Reason, minor, status: st, ..s0 };
        assert(hr(s5, b, 12) == hr(s7, b, 13));
        lemma_reason(s7, b, 13);
        lemma_run_end_bounds(b, 13, Cls::Value);
        he = run_end(b, 13, Cls::Value) + 2;
    } else {
        let s7 = HS { ph: Ph::SLf, minor, status: st, ..s0 };
        assert(hr(s5, b, 12) == hr(s7, b, 13));
        assert(hr(s7, b, 13) == hr(s6, b, 14));
        he = 14;
    }
    lemma_crlf_at(b, he - 2);
    assert(hr(s5, b, 12) == hr(s6, b, he));
    lemma_lines(s6, b, he, max, fields_init());
    let hs = parse_headers(b, he, max)->Done_0;
    lemma_fields_from(b, Seq::empty(), hs);
    assert(Seq::<SpecHeader>::empty() + hs =~= hs);
}

// ---------------------------------------------------------------------------
// Completeness: the machine accepts every head the spec accepts
// ---------------------------------------------------------------------------

proof fn lemma_crlf_inv(b: Seq<u8>, i: int)
    requires
        0 <= i,
        lit(b, i, crlf()) matches Parsed::Done(_, _),
    ensures
        i + 1 < b.len(),
        b[i] == CR,
        b[i + 1] == LF,
        lit(b, i, crlf()) == Parsed::<()>::Done((), i + 2),
{
    assert(b.subrange(i, i + 2) == crlf().subrange(0, 2));
    assert(b.subrange(i, i + 2)[0] == b[i]);
    assert(b.subrange(i, i + 2)[1] == b[i + 1]);
}

proof fn lemma_version_inv(b: Seq<u8>, v: int)
    requires
        0 <= v,
        parse_version(b, v) matches Parsed::Done(_, _),
    ensures
        v + 7 < b.len(),
        forall|t: int| 0 <= t < 7 ==> b[v + t] == #[trigger] http1_prefix()[t],
        is_digit(b[v + 7]),
        parse_version(b, v) == Parsed::Done((b[v + 7] - 0x30) as u8, v + 8),
{
    let p = http1_prefix();
    assert(b.subrange(v, v + 7) == p.subrange(0, 7));
    assert forall|t: int| 0 <= t < 7 implies b[v + t] == #[trigger] http1_prefix()[t] by {
        assert(b.subrange(v, v + 7)[t] == b[v + t]);
    }
}

proof fn lemma_vr_const(v: VK, b: Seq<u8>, i: int, e: int)
    requires
        v == VK::Other || v == VK::Host,
    ensures
        vr(v, b, i, e) == Some(v),
    decreases e - i,
{
    if i < e {
        lemma_vr_const(v, b, i + 1, e);
    }
}

proof fn lemma_val_c(s: HS, v: VK, b: Seq<u8>, j: int, f2: FieldsExec)
    requires
        0 <= j <= b.len(),
        s.ph == (Ph::Val { v }),
        run_end(b, j, Cls::Value) + 1 < b.len(),
        b[run_end(b, j, Cls::Value)] == CR,
        b[run_end(b, j, Cls::Value) + 1] == LF,
        vr(v, b, j, run_end(b, j, Cls::Value)) matches Some(x) && apply(s.f, x) == Some(f2),
    ensures
        hr(s, b, j) == hr(HS { ph: Ph::Line, f: f2, ..s }, b, run_end(b, j, Cls::Value) + 2),
    decreases b.len() - j,
{
    lemma_run_end_bounds(b, j, Cls::Value);
    let c = b[j];
    if c == CR {
        let s1 = HS { ph: Ph::ValLf { v }, ..s };
        assert(hr(s, b, j) == hr(s1, b, j + 1));
    } else {
        let v2 = vstep(v, c)->Some_0;
        let s1 = HS { ph: Ph::Val { v: v2 }, ..s };
        assert(hr(s, b, j) == hr(s1, b, j + 1));
        lemma_val_c(s1, v2, b, j + 1, f2);
    }
}

proof fn lemma_name_c(s: HS, b: Seq<u8>, i: int, j: int, v: VK)
    requires
        0 <= i < j <= b.len(),
        s.ph == (Ph::Name { m: mf(b, i, j) }),
        run_end(b, j, Cls::Token) < b.len(),
        b[run_end(b, j, Cls::Token)] == COLON,
        name_end(s.f, mf(b, i, run_end(b, j, Cls::Token))) == Some(v),
    ensures
        hr(s, b, j) == hr(HS { ph: Ph::Val { v }, ..s }, b, run_end(b, j, Cls::Token) + 1),
    decreases b.len() - j,
{
    let c = b[j];
    if is_tchar(c) {
        let s1 = HS { ph: Ph::Name { m: mf(b, i, j + 1) }, ..s };
        assert(hr(s, b, j) == hr(s1, b, j + 1));
        lemma_name_c(s1, b, i, j + 1, v);
    }
}

/// One field line the spec accepts and folds: the machine steps over it.
proof fn lemma_line_c(s: HS, b: Seq<u8>, i: int, g: Fields) -> (f2: FieldsExec)
    requires
        0 <= i < b.len(),
        s.ph == Ph::Line,
        fields_agree(s.f, g),
        parse_header(b, i) matches Parsed::Done(h, n) && fields_step(b, g, h) is Some,
    ensures
        parse_header(b, i) matches Parsed::Done(h, n) && (i < n && hr(s, b, i) == hr(
            HS { ph: Ph::Line, f: f2, ..s },
            b,
            n,
        ) && fields_agree(f2, fields_step(b, g, h)->Some_0)),
{
    let ne = run_end(b, i, Cls::Token);
    lemma_run_end_bounds(b, i, Cls::Token);
    let a = ne + 1;
    let vs = run_end(b, a, Cls::Ows);
    lemma_run_end_bounds(b, a, Cls::Ows);
    let e = run_end(b, vs, Cls::Value);
    assert forall|t: int| a <= t < vs implies in_cls(Cls::Value, #[trigger] b[t]) by {
        assert(in_cls(Cls::Ows, b[t]));
    }
    lemma_run_skip(b, a, vs, Cls::Value);
    lemma_run_end_bounds(b, vs, Cls::Value);
    lemma_crlf_inv(b, e);
    lemma_trim_end(b, vs, e);
    let te = trim_end(b, vs, e);
    let h = parse_header(b, i)->Done_0;
    let w = b.subrange(vs, te);
    assert(span_bytes(b, h.value) == w);
    assert(span_bytes(b, h.name) == b.subrange(i, ne));
    if te > vs {
        assert(w[0] == b[vs]);
        assert(w[w.len() - 1] == b[te - 1]);
    }
    let c = b[i];
    assert(is_tchar(c));
    let s1 = HS { ph: Ph::Name { m: mf(b, i, i + 1) }, ..s };
    assert(mf(b, i, i) == name_start());
    assert(hr(s, b, i) == hr(s1, b, i + 1));
    lemma_run_skip(b, i, i + 1, Cls::Token);
    lemma_name_kind(b, i, ne);
    let m = mf(b, i, ne);
    let v = name_end(s.f, m)->Some_0;
    lemma_name_c(s1, b, i, i + 1, v);
    let s2 = HS { ph: Ph::Val { v }, ..s };
    if v == VK::ClLead || v == (VK::TeSep { last: false }) {
        lemma_trimmed(v, b, a, e);
        if v == VK::ClLead {
            lemma_cl_value(w);
        } else {
            lemma_te_value(w, 0, false);
        }
        let z = vr(v, w, 0, w.len() as int)->Some_0;
        lemma_norm(z);
    } else {
        lemma_vr_const(v, b, a, e);
    }
    let x = vr(v, b, a, e)->Some_0;
    lemma_fam(v, b, a, e);
    lemma_norm(x);
    lemma_apply(s.f, x);
    let f2 = apply(s.f, x)->Some_0;
    lemma_val_c(s2, v, b, a, f2);
    f2
}

/// The field lines from `i`: the machine reaches the final LF with fields
/// that agree with the spec's.
proof fn lemma_lines_c(s: HS, b: Seq<u8>, i: int, max: nat, g: Fields) -> (ff: FieldsExec)
    requires
        0 <= i,
        s.ph == Ph::Line,
        fields_agree(s.f, g),
        parse_headers(b, i, max) matches Parsed::Done(hs, end) && fields_from(b, g, hs) is Some,
    ensures
        parse_headers(b, i, max) matches Parsed::Done(hs, end) && (i + 2 <= end <= b.len() && b[end
            - 1] == LF && hr(s, b, i) == hr(HS { ph: Ph::EndLf, f: ff, ..s }, b, end - 1)
            && fields_agree(ff, fields_from(b, g, hs)->Some_0)),
    decreases b.len() - i,
{
    if b[i] == CR {
        lemma_crlf_inv(b, i);
        let s1 = HS { ph: Ph::EndLf, ..s };
        assert(hr(s, b, i) == hr(s1, b, i + 1));
        s.f
    } else {
        let h = parse_header(b, i)->Done_0;
        let n = parse_header(b, i)->Done_1;
        let hs = parse_headers(b, n, (max - 1) as nat)->Done_0;
        let hs2 = seq![h] + hs;
        assert(hs2[0] == h);
        assert(hs2.drop_first() =~= hs);
        let f2 = lemma_line_c(s, b, i, g);
        let g2 = fields_step(b, g, h)->Some_0;
        let s1 = HS { ph: Ph::Line, f: f2, ..s };
        lemma_lines_c(s1, b, n, (max - 1) as nat, g2)
    }
}

proof fn lemma_rstart_c(s: HS, b: Seq<u8>, j: int)
    requires
        0 <= j,
        s.ph == Ph::RStart,
        skip_empty_lines(b, j) matches Parsed::Done(_, p) && p < b.len() && is_tchar(b[p]),
    ensures
        hr(s, b, j) == hr(HS { ph: Ph::Method, ..s }, b, skip_empty_lines(b, j)->Done_1 + 1),
    decreases b.len() - j,
{
    if b[j] == CR {
        let s1 = HS { ph: Ph::RStartLf, ..s };
        assert(hr(s, b, j) == hr(s1, b, j + 1));
        assert(hr(s1, b, j + 1) == hr(s, b, j + 2));
        lemma_rstart_c(s, b, j + 2);
    }
}

proof fn lemma_word_c(s: HS, b: Seq<u8>, j: int, k: Cls, next: Ph)
    requires
        0 <= j <= b.len(),
        run_end(b, j, k) < b.len(),
        b[run_end(b, j, k)] == SP,
        (s.ph == Ph::Method && k == Cls::Token && next == Ph::Target0) || (s.ph == Ph::Target && k
            == Cls::Target && next == (Ph::RVer { k: 0 })),
    ensures
        hr(s, b, j) == hr(HS { ph: next, ..s }, b, run_end(b, j, k) + 1),
    decreases b.len() - j,
{
    if in_cls(k, b[j]) {
        lemma_word_c(s, b, j + 1, k, next);
    }
}

proof fn lemma_ver_c(s: HS, b: Seq<u8>, j: int, k: int, req: bool)
    requires
        0 <= j,
        0 <= k <= 7,
        j + 7 - k < b.len(),
        forall|t: int| k <= t < 7 ==> b[j + t - k] == #[trigger] http1_prefix()[t],
        is_digit(b[j + 7 - k]),
        s.ph == (if req {
            Ph::RVer { k: k as u8 }
        } else {
            Ph::SVer { k: k as u8 }
        }),
    ensures
        hr(s, b, j) == hr(
            HS {
                ph: if req {
                    Ph::RCr
                } else {
                    Ph::SSp
                },
                minor: (b[j + 7 - k] - 0x30) as u8,
                ..s
            },
            b,
            j + 8 - k,
        ),
    decreases 7 - k,
{
    if k < 7 {
        assert(b[j + k - k] == http1_prefix()[k]);
        let s1 = HS {
            ph: if req {
                Ph::RVer { k: (k + 1) as u8 }
            } else {
                Ph::SVer { k: (k + 1) as u8 }
            },
            ..s
        };
        assert(hr(s, b, j) == hr(s1, b, j + 1));
        assert forall|t: int| k + 1 <= t < 7 implies b[(j + 1) + t - (k + 1)] == #[trigger] http1_prefix()[t] by {
            assert(b[j + t - k] == http1_prefix()[t]);
        }
        lemma_ver_c(s1, b, j + 1, k + 1, req);
    }
}

proof fn lemma_reason_c(s: HS, b: Seq<u8>, j: int)
    requires
        0 <= j <= b.len(),
        s.ph == Ph::Reason,
        run_end(b, j, Cls::Value) + 1 < b.len(),
        b[run_end(b, j, Cls::Value)] == CR,
        b[run_end(b, j, Cls::Value) + 1] == LF,
    ensures
        hr(s, b, j) == hr(HS { ph: Ph::Line, ..s }, b, run_end(b, j, Cls::Value) + 2),
    decreases b.len() - j,
{
    if b[j] == CR {
        let s1 = HS { ph: Ph::SLf, ..s };
        assert(hr(s, b, j) == hr(s1, b, j + 1));
    } else {
        lemma_reason_c(s, b, j + 1);
    }
}

/// The converse of `theorem_stream_request`: every head the spec accepts
/// (with a valid framing), the machine accepts, ending at the same byte.
/// So the streaming and one-shot parsers accept exactly the same heads.
///
/// With `host` false, every head whose `request_framing` is valid.
pub proof fn theorem_stream_request_complete(b: Seq<u8>, max: nat, host: bool)
    requires
        parse_request(b, max) matches Parsed::Done(r, _) && (if host {
            request_body(b, r) is Some
        } else {
            fields_of(b, r.headers) matches Some(g) && request_framing(g, r.minor) is Some
        }),
    ensures
        hrun(request_start_with(host), b) matches Some((t, k)) && t.ph is Done && k == parse_request(
            b,
            max,
        )->Done_1,
{
    let s0 = request_start_with(host);
    let r = parse_request(b, max)->Done_0;
    let end = parse_request(b, max)->Done_1;
    let p = skip_empty_lines(b, 0)->Done_1;
    lemma_skip_bounds(b, 0);
    let me = run_end(b, p, Cls::Token);
    lemma_run_end_bounds(b, p, Cls::Token);
    lemma_rstart_c(s0, b, 0);
    let s1 = HS { ph: Ph::Method, ..s0 };
    lemma_run_skip(b, p, p + 1, Cls::Token);
    lemma_word_c(s1, b, p + 1, Cls::Token, Ph::Target0);
    let t0 = me + 1;
    let te = run_end(b, t0, Cls::Target);
    lemma_run_end_bounds(b, t0, Cls::Target);
    let s2 = HS { ph: Ph::Target0, ..s0 };
    let s3 = HS { ph: Ph::Target, ..s0 };
    assert(hr(s2, b, t0) == hr(s3, b, t0 + 1));
    lemma_run_skip(b, t0, t0 + 1, Cls::Target);
    lemma_word_c(s3, b, t0 + 1, Cls::Target, Ph::RVer { k: 0 });
    let v = te + 1;
    lemma_version_inv(b, v);
    let s4 = HS { ph: Ph::RVer { k: 0 }, ..s0 };
    lemma_ver_c(s4, b, v, 0, true);
    let minor = (b[v + 7] - 0x30) as u8;
    lemma_crlf_inv(b, v + 8);
    let s5 = HS { ph: Ph::RCr, minor, ..s0 };
    let s5b = HS { ph: Ph::RLf, minor, ..s0 };
    let s6 = HS { ph: Ph::Line, minor, ..s0 };
    assert(hr(s5, b, v + 8) == hr(s5b, b, v + 9));
    assert(hr(s5b, b, v + 9) == hr(s6, b, v + 10));
    let hs = r.headers;
    lemma_fields_from(b, Seq::empty(), hs);
    assert(Seq::<SpecHeader>::empty() + hs =~= hs);
    let ff = lemma_lines_c(s6, b, v + 10, max, fields_init());
    let s7 = HS { ph: Ph::EndLf, f: ff, minor, ..s0 };
    let t = HS { ph: Ph::Done, f: ff, minor, ..s0 };
    assert(head_ok(s7));
    assert(hr(s7, b, end - 1) == hr(t, b, end));
    assert(hr(t, b, end) == Some((t, end)));
    lemma_hr(s0, b, 0);
    assert(sfx(b, 0) =~= b);
}

/// The converse of `theorem_stream_response`.
pub proof fn theorem_stream_response_complete(b: Seq<u8>, max: nat, head: bool, connect: bool)
    requires
        parse_response(b, max) matches Parsed::Done(r, _) && response_body(b, r, head, connect) is Some,
    ensures
        hrun(response_start(), b) matches Some((t, k)) && t.ph is Done && k == parse_response(
            b,
            max,
        )->Done_1,
{
    let s0 = response_start();
    let r = parse_response(b, max)->Done_0;
    let end = parse_response(b, max)->Done_1;
    lemma_version_inv(b, 0);
    lemma_ver_c(s0, b, 0, 0, false);
    let minor = (b[7] - 0x30) as u8;
    let s1 = HS { ph: Ph::SSp, minor, ..s0 };
    let s2 = HS { ph: Ph::Code { k: 0 }, minor, ..s0 };
    assert(hr(s1, b, 8) == hr(s2, b, 9));
    let d0 = (b[9] - 0x30) as u16;
    let s3 = HS { ph: Ph::Code { k: 1 }, minor, status: d0, ..s0 };
    assert(hr(s2, b, 9) == hr(s3, b, 10));
    let d1 = (d0 * 10 + (b[10] - 0x30)) as u16;
    let s4 = HS { ph: Ph::Code { k: 2 }, minor, status: d1, ..s0 };
    assert(hr(s3, b, 10) == hr(s4, b, 11));
    let st = (d1 * 10 + (b[11] - 0x30)) as u16;
    let s5 = HS { ph: Ph::Code { k: 3 }, minor, status: st, ..s0 };
    assert(hr(s4, b, 11) == hr(s5, b, 12));
    assert(st == r.status);
    let s6 = HS { ph: Ph::Line, minor, status: st, ..s0 };
    let he;
    if 12 < b.len() && b[12] == SP {
        let re = run_end(b, 13, Cls::Value);
        lemma_run_end_bounds(b, 13, Cls::Value);
        lemma_crlf_inv(b, re);
        let s7 = HS { ph: Ph::Reason, minor, status: st, ..s0 };
        assert(hr(s5, b, 12) == hr(s7, b, 13));
        lemma_reason_c(s7, b, 13);
        he = re + 2;
    } else {
        lemma_crlf_inv(b, 12);
        let s7 = HS { ph: Ph::SLf, minor, status: st, ..s0 };
        assert(hr(s5, b, 12) == hr(s7, b, 13));
        assert(hr(s7, b, 13) == hr(s6, b, 14));
        he = 14;
    }
    assert(hr(s5, b, 12) == hr(s6, b, he));
    let hs = r.headers;
    lemma_fields_from(b, Seq::empty(), hs);
    assert(Seq::<SpecHeader>::empty() + hs =~= hs);
    let ff = lemma_lines_c(s6, b, he, max, fields_init());
    let s8 = HS { ph: Ph::EndLf, f: ff, minor, status: st, ..s0 };
    let t = HS { ph: Ph::Done, f: ff, minor, status: st, ..s0 };
    assert(head_ok(s8));
    assert(hr(s8, b, end - 1) == hr(t, b, end));
    assert(hr(t, b, end) == Some((t, end)));
    lemma_hr(s0, b, 0);
    assert(sfx(b, 0) =~= b);
}

} // verus!

//! The on-demand reader: values are read straight from the stage 1
//! structural index, without building a tape.
//!
//! A `Cursor` stands between two tokens of the input. Its operations look
//! at the next token (`peek`), step over an operator (`eat`), read a
//! scalar (`num`, `lit`, `string`) or pass over a whole value (`skip`).
//! Each is specified against the grammar in `spec.rs` at the cursor's
//! position: a read succeeds exactly when the grammar's token is there,
//! returns that token's value, and leaves the cursor right after it.
//!
//! Skipping does not validate: a skipped scalar or string is one or more
//! index entries, a skipped container is everything up to its matching
//! bracket. `lemma_skip_value` shows that for a value the grammar accepts,
//! that is exactly where the value ends.
#[allow(unused_imports)]
use crate::index::*;
use crate::parser::*;
#[allow(unused_imports)]
use crate::spec::*;
use crate::stage2::*;
#[allow(unused_imports)]
use crate::simd::*;
use vstd::prelude::*;

verus! {

/// The first unescaped quote at or after `i`, or the end of the input.
pub open spec fn quote_from(s: Seq<u8>, st: int, i: int) -> int
    decreases s.len() - i,
{
    if i >= s.len() || uq(s, st, i) {
        i
    } else {
        quote_from(s, st, i + 1)
    }
}

/// What a bracket adds to the nesting depth.
pub open spec fn delta(c: u8) -> int {
    if c == 0x5B || c == 0x7B {
        1
    } else if c == 0x5D || c == 0x7D {
        -1
    } else {
        0
    }
}

/// Walking the index from entry `k` at nesting depth `d`: the entry after
/// the bracket that brings the depth to 0.
pub open spec fn close_k(s: Seq<u8>, idx: Seq<int>, k: int, d: int) -> Option<int>
    decreases idx.len() - k,
{
    if k < 0 || k >= idx.len() {
        None
    } else {
        let d2 = d + delta(byte(s, idx[k]));
        if d2 == 0 {
            Some(k + 1)
        } else {
            close_k(s, idx, k + 1, d2)
        }
    }
}

/// Opening brackets among the `m` index entries from `k`.
pub open spec fn opens(s: Seq<u8>, idx: Seq<int>, k: int, m: int) -> int
    decreases m,
{
    if m <= 0 {
        0
    } else {
        opens(s, idx, k, m - 1) + if delta(byte(s, idx[k + m - 1])) == 1 {
            1int
        } else {
            0
        }
    }
}

/// Closing brackets among the `m` index entries from `k`.
pub open spec fn closes(s: Seq<u8>, idx: Seq<int>, k: int, m: int) -> int
    decreases m,
{
    if m <= 0 {
        0
    } else {
        closes(s, idx, k, m - 1) + if delta(byte(s, idx[k + m - 1])) == -1 {
            1int
        } else {
            0
        }
    }
}

/// A run of entries with fewer closing brackets than the depth cannot
/// bring the depth to 0: the walk passes over it.
pub proof fn lemma_block(s: Seq<u8>, idx: Seq<int>, k: int, d: int, m: int)
    requires
        0 <= k,
        0 <= m,
        k + m <= idx.len(),
        closes(s, idx, k, m) < d,
    ensures
        0 <= opens(s, idx, k, m) <= m,
        0 <= closes(s, idx, k, m) <= m,
        close_k(s, idx, k, d) == close_k(s, idx, k + m, d + opens(s, idx, k, m) - closes(s, idx, k, m)),
    decreases m,
{
    if m > 0 {
        lemma_block(s, idx, k, d, m - 1);
        let d1 = d + opens(s, idx, k, m - 1) - closes(s, idx, k, m - 1);
        let dl = delta(byte(s, idx[k + m - 1]));
        assert(d1 + dl != 0);
        assert(close_k(s, idx, k + m - 1, d1) == close_k(s, idx, k + m, d1 + dl));
    }
}

/// Where `skip` takes a cursor at `p`: the index entry and the position
/// after the value, or `None` if it does not move.
pub open spec fn skip_to(s: Seq<u8>, st: int, idx: Seq<int>, p: int) -> Option<(int, int)> {
    let j = skip_ws(s, p);
    let k = cnt(s, st, p);
    if j >= s.len() {
        None
    } else if s[j] == 0x22 {
        let q = quote_from(s, st, j + 1);
        if q >= s.len() {
            None
        } else {
            Some((cnt(s, st, q + 1), q + 1))
        }
    } else if s[j] == 0x5B || s[j] == 0x7B {
        match close_k(s, idx, k + 1, 1) {
            Some(k1) => Some((k1, idx[k1 - 1] + 1)),
            None => None,
        }
    } else if s[j] == 0x2C || s[j] == 0x3A || s[j] == 0x5D || s[j] == 0x7D {
        None
    } else {
        let q = if k + 1 < idx.len() { idx[k + 1] } else { s.len() as int };
        if byte(s, q - 1) == 0x5C {
            None
        } else {
            Some((k + 1, q))
        }
    }
}

/// With no unescaped quote in `[a, b)`, the string state does not change.
pub proof fn lemma_no_quote(s: Seq<u8>, st: int, a: int, b: int)
    requires
        st <= a <= b <= s.len(),
        forall|m: int| a <= m < b ==> !#[trigger] structural(s, st, m),
    ensures
        instr(s, st, b - 1) == instr(s, st, a - 1),
        quote_from(s, st, a) == quote_from(s, st, b),
        forall|m: int| a <= m < b ==> !#[trigger] uq(s, st, m),
    decreases b - a,
{
    if a < b {
        assert(!structural(s, st, b - 1));
        lemma_no_quote(s, st, a, b - 1);
        lemma_quote_from(s, st, a, b);
    }
}

proof fn lemma_quote_from(s: Seq<u8>, st: int, a: int, b: int)
    requires
        a <= b <= s.len(),
        forall|m: int| a <= m < b ==> !#[trigger] uq(s, st, m),
    ensures
        quote_from(s, st, a) == quote_from(s, st, b),
    decreases b - a,
{
    if a < b {
        assert(!uq(s, st, a));
        lemma_quote_from(s, st, a + 1, b);
    }
}

/// After a scalar that starts at the structural position `j`, the next
/// structural position `q` (or the end of the input) is a place between
/// tokens, provided the byte before it is not a backslash.
pub proof fn lemma_after_scalar(s: Seq<u8>, st: int, j: int, q: int)
    requires
        0 <= st <= s.len(),
        st <= j < s.len(),
        structural(s, st, j),
        !instr(s, st, j - 1),
        !is_op(s[j]),
        s[j] != 0x22,
        cnt(s, st, j) + 1 < cnt(s, st, s.len() as int) ==> q == positions(s, st, st, s.len() as int)[cnt(
            s,
            st,
            j,
        ) + 1],
        cnt(s, st, j) + 1 >= cnt(s, st, s.len() as int) ==> q == s.len(),
    ensures
        j < q <= s.len(),
        cnt(s, st, q) == cnt(s, st, j) + 1,
        !instr(s, st, q - 1),
        bnd(s, st, q),
        forall|m: int| j < m < q ==> !#[trigger] structural(s, st, m),
{
    let full = positions(s, st, st, s.len() as int);
    lemma_at(s, st, j);
    lemma_cnt_bound(s, st, s.len() as int);
    assert(byte(s, j) == s[j]);
    assert(!uq(s, st, j));
    assert(!instr(s, st, j));
    if cnt(s, st, j) + 1 < cnt(s, st, s.len() as int) {
        lemma_entry(s, st, s.len() as int, cnt(s, st, j) + 1);
        // `q` is after `j`: counts are monotone.
        if q <= j {
            lemma_prefix(s, st, q, j);
        }
        lemma_between(s, st, j + 1, q);
        lemma_no_quote(s, st, j + 1, q);
        assert(byte(s, q) == s[q]);
        if scalar(s, st, q - 1) && !delim(byte(s, q)) {
            assert(!is_op(byte(s, q)));
            assert(!uq(s, st, q));
            assert(!instr(s, st, q));
            assert(!strs(s, st, q));
            assert(!escape_start(s, st, q));
            assert(scalar(s, st, q));
            assert(!scalar_start(s, st, q));
            assert(false);
        }
    } else {
        lemma_prefix(s, st, j + 1, s.len() as int);
        lemma_tail_empty(s, st, j + 1, s.len() as int);
        lemma_no_quote(s, st, j + 1, s.len() as int);
    }
}

/// Positions with the same count have no structural position between.
proof fn lemma_tail_empty(s: Seq<u8>, st: int, a: int, b: int)
    requires
        0 <= st <= a <= b,
        cnt(s, st, a) == cnt(s, st, b),
    ensures
        forall|m: int| a <= m < b ==> !#[trigger] structural(s, st, m),
    decreases b - a,
{
    if a < b {
        lemma_prefix(s, st, a, b - 1);
        lemma_cnt_step(s, st, b - 1);
        lemma_tail_empty(s, st, a, b - 1);
    }
}

/// No structural position lies strictly between two consecutive index
/// entries: here, in `[a, q)` when `q` is structural and counts one more
/// than... `cnt(q) == cnt(a)`.
proof fn lemma_between(s: Seq<u8>, st: int, a: int, q: int)
    requires
        0 <= st <= a <= q,
        cnt(s, st, q) == cnt(s, st, a),
    ensures
        forall|m: int| a <= m < q ==> !#[trigger] structural(s, st, m),
{
    lemma_tail_empty(s, st, a, q);
}

// ---------------------------------------------------------------------------
// Skipping a value the grammar accepts
// ---------------------------------------------------------------------------

/// The whole structural index of `s`.
pub open spec fn full(s: Seq<u8>, st: int) -> Seq<int> {
    positions(s, st, st, s.len() as int)
}

/// Index entries `a..b` leave the bracket walk as it was, at any depth:
/// they open and close nothing, or as much as they open.
pub open spec fn transparent(s: Seq<u8>, idx: Seq<int>, a: int, b: int) -> bool {
    forall|d: int| d >= 1 ==> #[trigger] close_k(s, idx, a, d) == close_k(s, idx, b, d)
}

/// `skip` from `p` ends where the value that ends at `e` does: at index
/// entry `cnt(e)`, with the same next token.
pub open spec fn skipped(s: Seq<u8>, st: int, p: int, e: int) -> bool {
    match skip_to(s, st, full(s, st), p) {
        Some((k1, p1)) => k1 == cnt(s, st, e) && skip_ws(s, p1) == skip_ws(s, e),
        None => false,
    }
}

proof fn lemma_trans(s: Seq<u8>, idx: Seq<int>, a: int, b: int, c: int)
    requires
        transparent(s, idx, a, b),
        transparent(s, idx, b, c),
    ensures
        transparent(s, idx, a, c),
{
    assert forall|d: int| d >= 1 implies #[trigger] close_k(s, idx, a, d) == close_k(s, idx, c, d) by {
        assert(close_k(s, idx, a, d) == close_k(s, idx, b, d));
        assert(close_k(s, idx, b, d) == close_k(s, idx, c, d));
    }
}

/// Positions `[a, b)` whose structural bytes are not brackets are
/// transparent.
proof fn lemma_flat(s: Seq<u8>, st: int, a: int, b: int)
    requires
        0 <= st <= a <= b <= s.len(),
        forall|m: int| a <= m < b && #[trigger] structural(s, st, m) ==> delta(byte(s, m)) == 0,
    ensures
        cnt(s, st, a) <= cnt(s, st, b),
        transparent(s, full(s, st), cnt(s, st, a), cnt(s, st, b)),
    decreases b - a,
{
    let idx = full(s, st);
    if a < b {
        lemma_flat(s, st, a, b - 1);
        lemma_cnt_step(s, st, b - 1);
        if structural(s, st, b - 1) {
            lemma_at(s, st, b - 1);
            let k = cnt(s, st, b - 1);
            assert forall|d: int| d >= 1 implies #[trigger] close_k(s, idx, cnt(s, st, a), d) == close_k(
                s,
                idx,
                cnt(s, st, b),
                d,
            ) by {
                assert(close_k(s, idx, cnt(s, st, a), d) == close_k(s, idx, k, d));
                assert(idx[k] == b - 1);
                assert(delta(byte(s, b - 1)) == 0);
                assert(close_k(s, idx, k, d) == close_k(s, idx, k + 1, d));
            }
        }
    }
}

/// The body of a string the grammar accepts runs to the first unescaped
/// quote, and every byte before it is inside the string.
proof fn lemma_body_quote(s: Seq<u8>, st: int, i: int, e: bool)
    requires
        0 <= st <= i <= s.len(),
        instr(s, st, i - 1),
        !esc(s, st, i),
        string_body(s, i, e) is Some,
    ensures
        ({
            let n = string_body(s, i, e).unwrap().0;
            &&& i < n <= s.len()
            &&& uq(s, st, n - 1)
            &&& forall|m: int| i <= m < n - 1 ==> #[trigger] instr(s, st, m)
        }),
    decreases s.len() - i,
{
    assert(byte(s, i) == s[i]);
    if s[i] != 0x22 {
        let n2 = string_char(s, i).unwrap().1;
        crate::lemmas::lemma_string_char_advances(s, i);
        if s[i] != 0x5C {
            assert(!uq(s, st, i));
            assert(instr(s, st, i));
            assert(!esc(s, st, i + 1));
        } else {
            lemma_escape(s, st, i, n2);
        }
        lemma_body_quote(s, st, n2, e || s[i] == 0x5C);
    }
}

/// A string the grammar accepts, at the structural position `j`.
proof fn lemma_sv_string(s: Seq<u8>, st: int, j: int)
    requires
        0 <= st <= s.len(),
        st <= j < s.len(),
        out(s, st, j),
        !esc(s, st, j),
        string(s, j) is Some,
    ensures
        ({
            let n = string(s, j).unwrap().0;
            &&& j + 1 < n <= s.len()
            &&& quote_from(s, st, j + 1) == n - 1
            &&& out(s, st, n)
            &&& bnd(s, st, n)
            &&& cnt(s, st, j) < cnt(s, st, n)
            &&& transparent(s, full(s, st), cnt(s, st, j), cnt(s, st, n))
        }),
{
    let n = string(s, j).unwrap().0;
    assert(byte(s, j) == s[j]);
    assert(uq(s, st, j));
    assert(instr(s, st, j));
    assert(!esc(s, st, j + 1));
    lemma_body_quote(s, st, j + 1, false);
    assert forall|m: int| j + 1 <= m < n - 1 implies !#[trigger] uq(s, st, m) by {
        assert(instr(s, st, m));
        assert(instr(s, st, m - 1));
    }
    lemma_quote_from(s, st, j + 1, n - 1);
    assert(quote_from(s, st, n - 1) == n - 1);
    assert(instr(s, st, n - 2));
    assert(!instr(s, st, n - 1));
    assert(byte(s, n - 1) == s[n - 1]);
    assert(!scalar(s, st, n - 1));
    assert forall|m: int| j <= m < n && #[trigger] structural(s, st, m) implies delta(byte(s, m)) == 0 by {
        if j < m < n - 1 {
            assert(instr(s, st, m));
            assert(instr(s, st, m - 1));
            assert(strs(s, st, m));
            assert(byte(s, m) == 0x5C || byte(s, m) < 0x20);
        }
    }
    lemma_flat(s, st, j, n);
    lemma_at(s, st, j);
    lemma_prefix(s, st, j + 1, n);
}

/// A number or literal the grammar accepts in `[j, e)`.
proof fn lemma_sv_scalar(s: Seq<u8>, st: int, p: int, e: int)
    requires
        0 <= st <= s.len(),
        st <= p <= s.len(),
        out(s, st, p),
        bnd(s, st, p),
        skip_ws(s, p) < e <= s.len(),
        forall|m: int| skip_ws(s, p) <= m < e ==> lexeme(#[trigger] s[m]),
        s[skip_ws(s, p)] != 0x5B && s[skip_ws(s, p)] != 0x7B && s[skip_ws(s, p)] != 0x5D && s[skip_ws(s, p)]
            != 0x7D,
        bnd(s, st, e),
    ensures
        out(s, st, e),
        cnt(s, st, e) == cnt(s, st, p) + 1,
        transparent(s, full(s, st), cnt(s, st, p), cnt(s, st, e)),
        skipped(s, st, p, e),
{
    let j = skip_ws(s, p);
    let idx = full(s, st);
    lemma_skip(s, st, p);
    lemma_close(s, st, p);
    lemma_scalar_run(s, st, j, e);
    assert(lexeme(s[j]));
    assert(byte(s, j) == s[j]);
    assert forall|m: int| j <= m < e && #[trigger] structural(s, st, m) implies delta(byte(s, m)) == 0 by {
        assert(m == j);
    }
    lemma_flat(s, st, j, e);
    // Where `skip` goes: the next index entry, which is where `skip_ws`
    // lands after `e`.
    lemma_close(s, st, e);
    crate::lemmas::lemma_skip_ws_bounds(s, e);
    let q = skip_ws(s, e);
    let k = cnt(s, st, p);
    assert(q == if k + 1 < idx.len() { idx[k + 1] } else { s.len() as int });
    if q > e {
        lemma_ws_run(s, e, q - 1);
    } else {
        assert(lexeme(s[e - 1]));
    }
    assert(byte(s, q - 1) == s[q - 1]);
    crate::lemmas::lemma_skip_ws_bounds(s, q);
    lemma_skip_ws_idem(s, e);
}

/// Every byte before where `skip_ws` lands is whitespace.
proof fn lemma_ws_run(s: Seq<u8>, i: int, m: int)
    requires
        0 <= i <= m < skip_ws(s, i),
        i <= s.len(),
    ensures
        m < s.len(),
        is_ws(s[m]),
    decreases s.len() - i,
{
    if i < s.len() && is_ws(s[i]) {
        if m > i {
            lemma_ws_run(s, i + 1, m);
        }
    }
}

proof fn lemma_skip_ws_idem(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        skip_ws(s, skip_ws(s, i)) == skip_ws(s, i),
    decreases s.len() - i,
{
    if i < s.len() && is_ws(s[i]) {
        lemma_skip_ws_idem(s, i + 1);
    }
}

/// The end of the value the grammar reads at `i`.
pub open spec fn vend(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>) -> int {
    value(s, i, depth, tape).unwrap().1
}

/// What the lemmas below say about a container body that ends at `n`
/// with the bracket `close`, read from the place `p` between tokens.
pub open spec fn body_ok(s: Seq<u8>, st: int, p: int, n: int, close: u8) -> bool {
    &&& p < n <= s.len()
    &&& s[n - 1] == close
    &&& structural(s, st, n - 1)
    &&& !strs(s, st, n - 1)
    &&& cnt(s, st, p) <= cnt(s, st, n - 1)
    &&& transparent(s, full(s, st), cnt(s, st, p), cnt(s, st, n - 1))
}

/// A container: an opening bracket at the cursor, then a body that ends
/// at `e` with the matching bracket.
proof fn lemma_sv_wrap(s: Seq<u8>, st: int, p: int, e: int, close: u8)
    requires
        0 <= st <= s.len(),
        st <= p <= s.len(),
        out(s, st, p),
        bnd(s, st, p),
        skip_ws(s, p) < s.len(),
        close == 0x5D || close == 0x7D,
        s[skip_ws(s, p)] == 0x5B || s[skip_ws(s, p)] == 0x7B,
        body_ok(s, st, skip_ws(s, p) + 1, e, close),
    ensures
        out(s, st, e),
        cnt(s, st, p) < cnt(s, st, e),
        transparent(s, full(s, st), cnt(s, st, p), cnt(s, st, e)),
        skipped(s, st, p, e),
{
    let i = skip_ws(s, p);
    let idx = full(s, st);
    lemma_skip(s, st, p);
    lemma_close(s, st, p);
    let kp = cnt(s, st, p);
    assert(byte(s, i) == s[i]);
    lemma_at(s, st, e - 1);
    let kc = cnt(s, st, e - 1);
    assert(byte(s, e - 1) == close);
    assert(!scalar(s, st, e - 1));
    assert(idx[kp] == i);
    assert(idx[kc] == e - 1);
    assert forall|d: int| d >= 1 implies #[trigger] close_k(s, idx, kp, d) == close_k(s, idx, kc + 1, d) by {
        assert(close_k(s, idx, kp, d) == close_k(s, idx, kp + 1, d + 1));
        assert(close_k(s, idx, kp + 1, d + 1) == close_k(s, idx, kc, d + 1));
        assert(close_k(s, idx, kc, d + 1) == close_k(s, idx, kc + 1, d));
    }
    assert(close_k(s, idx, kp + 1, 1) == close_k(s, idx, kc, 1));
    assert(close_k(s, idx, kc, 1) == Some(kc + 1));
}

/// **Skipping agrees with the grammar.** If the grammar reads a value at
/// the cursor, ending at `e` on a token boundary, then `skip` passes over
/// exactly that value.
#[verifier::rlimit(300)]
pub proof fn lemma_skip_value(s: Seq<u8>, st: int, p: int, depth: nat, tape: Seq<STok>)
    requires
        0 <= st <= s.len(),
        st <= p <= s.len(),
        out(s, st, p),
        bnd(s, st, p),
        value(s, skip_ws(s, p), depth, tape) is Some,
        bnd(s, st, vend(s, skip_ws(s, p), depth, tape)),
    ensures
        ({
            let e = vend(s, skip_ws(s, p), depth, tape);
            &&& p < e <= s.len()
            &&& out(s, st, e)
            &&& cnt(s, st, p) < cnt(s, st, e)
            &&& transparent(s, full(s, st), cnt(s, st, p), cnt(s, st, e))
            &&& skipped(s, st, p, e)
        }),
    decreases depth, s.len() - p, 2nat,
{
    let i = skip_ws(s, p);
    let idx = full(s, st);
    let e = vend(s, i, depth, tape);
    lemma_skip(s, st, p);
    lemma_close(s, st, p);
    crate::lemmas::lemma_value_advances(s, i, depth, tape);
    crate::lemmas::lemma_skip_ws_bounds(s, p);
    let kp = cnt(s, st, p);
    let c = s[i];
    assert(byte(s, i) == c);
    if c == 0x5B || c == 0x7B {
        let close = if c == 0x5B { 0x5Du8 } else { 0x7Du8 };
        if c == 0x5B {
            lemma_sv_array(s, st, i + 1, depth, tape.push(STok::ArrStart { end: 0 }));
        } else {
            lemma_sv_object(s, st, i + 1, depth, tape.push(STok::ObjStart { end: 0 }));
        }
        lemma_sv_wrap(s, st, p, e, close);
    } else if c == 0x22 {
        lemma_sv_string(s, st, i);
    } else if c == 0x74 || c == 0x66 || c == 0x6E {
        let lit = if c == 0x74 {
            seq![0x74u8, 0x72, 0x75, 0x65]
        } else if c == 0x66 {
            seq![0x66u8, 0x61, 0x6C, 0x73, 0x65]
        } else {
            seq![0x6Eu8, 0x75, 0x6C, 0x6C]
        };
        assert(has_lit(s, i, lit));
        assert(e == i + lit.len());
        assert forall|m: int| i <= m < e implies lexeme(#[trigger] s[m]) by {
            assert(s[m] == s.subrange(i, e)[m - i]);
            assert(s.subrange(i, e)[m - i] == lit[m - i]);
        }
        lemma_sv_scalar(s, st, p, e);
    } else {
        lemma_number_lexeme(s, i);
        assert(lexeme(s[i]));
        lemma_sv_scalar(s, st, p, e);
    }
}

proof fn lemma_sv_array(s: Seq<u8>, st: int, p: int, depth: nat, tape: Seq<STok>)
    requires
        0 <= st <= s.len(),
        st <= p <= s.len(),
        out(s, st, p),
        bnd(s, st, p),
        array(s, p, depth, tape) is Some,
    ensures
        body_ok(s, st, p, array(s, p, depth, tape).unwrap().1, 0x5D),
    decreases depth, s.len() - p, 1nat,
{
    let j = skip_ws(s, p);
    lemma_skip(s, st, p);
    lemma_close(s, st, p);
    if 0 <= j < s.len() && s[j] == 0x5D {
        assert(byte(s, j) == s[j]);
        assert(!scalar(s, st, j));
    } else {
        lemma_sv_elements(s, st, p, depth, tape);
    }
}

proof fn lemma_sv_elements(s: Seq<u8>, st: int, p: int, depth: nat, tape: Seq<STok>)
    requires
        0 <= st <= s.len(),
        st <= p <= s.len(),
        out(s, st, p),
        bnd(s, st, p),
        elements(s, p, depth, tape) is Some,
    ensures
        body_ok(s, st, p, elements(s, p, depth, tape).unwrap().1, 0x5D),
    decreases depth, s.len() - p, 0nat,
{
    let idx = full(s, st);
    let i = skip_ws(s, p);
    let (t, k) = value(s, i, (depth - 1) as nat, tape).unwrap();
    let k2 = skip_ws(s, k);
    crate::lemmas::lemma_value_advances(s, i, (depth - 1) as nat, tape);
    crate::lemmas::lemma_skip_ws_bounds(s, p);
    crate::lemmas::lemma_skip_ws_bounds(s, k);
    if !bnd(s, st, k) {
        lemma_not_bnd(s, st, k);
    }
    lemma_skip_value(s, st, p, (depth - 1) as nat, tape);
    lemma_skip(s, st, k);
    lemma_close(s, st, k);
    assert(byte(s, k2) == s[k2]);
    assert(!scalar(s, st, k2));
    if s[k2] == 0x2C {
        lemma_sv_elements(s, st, k2 + 1, depth, t);
        let n = elements(s, k2 + 1, depth, t).unwrap().1;
        lemma_step(s, st, k2);
        lemma_trans(s, idx, cnt(s, st, p), cnt(s, st, k), cnt(s, st, k2 + 1));
        lemma_trans(s, idx, cnt(s, st, p), cnt(s, st, k2 + 1), cnt(s, st, n - 1));
    }
}

/// One structural byte that is not a bracket is transparent.
proof fn lemma_step(s: Seq<u8>, st: int, q: int)
    requires
        0 <= st <= q < s.len(),
        structural(s, st, q),
        delta(s[q]) == 0,
    ensures
        cnt(s, st, q + 1) == cnt(s, st, q) + 1,
        transparent(s, full(s, st), cnt(s, st, q), cnt(s, st, q + 1)),
{
    assert(byte(s, q) == s[q]);
    lemma_flat(s, st, q, q + 1);
    lemma_at(s, st, q);
}

proof fn lemma_sv_object(s: Seq<u8>, st: int, p: int, depth: nat, tape: Seq<STok>)
    requires
        0 <= st <= s.len(),
        st <= p <= s.len(),
        out(s, st, p),
        bnd(s, st, p),
        object(s, p, depth, tape) is Some,
    ensures
        body_ok(s, st, p, object(s, p, depth, tape).unwrap().1, 0x7D),
    decreases depth, s.len() - p, 1nat,
{
    let j = skip_ws(s, p);
    lemma_skip(s, st, p);
    lemma_close(s, st, p);
    if 0 <= j < s.len() && s[j] == 0x7D {
        assert(byte(s, j) == s[j]);
        assert(!scalar(s, st, j));
    } else {
        lemma_sv_members(s, st, p, depth, tape);
    }
}

proof fn lemma_sv_members(s: Seq<u8>, st: int, p: int, depth: nat, tape: Seq<STok>)
    requires
        0 <= st <= s.len(),
        st <= p <= s.len(),
        out(s, st, p),
        bnd(s, st, p),
        members(s, p, depth, tape) is Some,
    ensures
        body_ok(s, st, p, members(s, p, depth, tape).unwrap().1, 0x7D),
    decreases depth, s.len() - p, 0nat,
{
    let idx = full(s, st);
    let j = skip_ws(s, p);
    lemma_skip(s, st, p);
    lemma_close(s, st, p);
    crate::lemmas::lemma_skip_ws_bounds(s, p);
    let (k, esc) = string(s, j).unwrap();
    lemma_sv_string(s, st, j);
    let c = skip_ws(s, k);
    lemma_skip(s, st, k);
    lemma_close(s, st, k);
    crate::lemmas::lemma_skip_ws_bounds(s, k);
    assert(byte(s, c) == s[c]);
    lemma_step(s, st, c);
    let tape2 = tape.push(STok::Key { start: j + 1, end: k - 1, escaped: esc });
    let i = skip_ws(s, c + 1);
    let (t, m) = value(s, i, (depth - 1) as nat, tape2).unwrap();
    let m2 = skip_ws(s, m);
    crate::lemmas::lemma_skip_ws_bounds(s, c + 1);
    crate::lemmas::lemma_value_advances(s, i, (depth - 1) as nat, tape2);
    crate::lemmas::lemma_skip_ws_bounds(s, m);
    if !bnd(s, st, m) {
        lemma_not_bnd(s, st, m);
    }
    lemma_skip_value(s, st, c + 1, (depth - 1) as nat, tape2);
    lemma_skip(s, st, m);
    lemma_close(s, st, m);
    assert(byte(s, m2) == s[m2]);
    assert(!scalar(s, st, m2));
    lemma_trans(s, idx, cnt(s, st, p), cnt(s, st, k), cnt(s, st, c + 1));
    lemma_trans(s, idx, cnt(s, st, p), cnt(s, st, c + 1), cnt(s, st, m));
    if s[m2] == 0x2C {
        lemma_sv_members(s, st, m2 + 1, depth, t);
        let n = members(s, m2 + 1, depth, t).unwrap().1;
        lemma_step(s, st, m2);
        lemma_trans(s, idx, cnt(s, st, p), cnt(s, st, m), cnt(s, st, m2 + 1));
        lemma_trans(s, idx, cnt(s, st, p), cnt(s, st, m2 + 1), cnt(s, st, n - 1));
    }
}

/// A position between two tokens of `s`, reading the structural index
/// through the window `w`.
pub struct Cursor<'a> {
    pub s: &'a [u8],
    pub w: Win<'a>,
    /// The next unread index entry.
    pub k: usize,
    /// Where entry `k` is: the next token, or the end of the input.
    pub j: usize,
    /// Where the index starts (after a byte order mark).
    pub st: Ghost<int>,
    /// The position in `s`: just after the last token read.
    pub p: Ghost<int>,
}

impl<'a> Cursor<'a> {
    /// The whole index.
    pub open spec fn idx(&self) -> Seq<int> {
        full(self.s@, self.st@)
    }

    /// The cursor is between tokens, outside any string, and `k` is the
    /// index entry of the next token, which is at `j`.
    pub open spec fn wf(&self) -> bool {
        &&& self.w.inv()
        &&& self.w.s == self.s
        &&& self.w.st == self.st@
        &&& self.st@ <= self.p@ <= self.s@.len()
        &&& self.s@.len() <= isize::MAX
        &&& self.idx().len() <= self.s@.len()
        &&& out(self.s@, self.st@, self.p@)
        &&& bnd(self.s@, self.st@, self.p@)
        &&& self.k == cnt(self.s@, self.st@, self.p@)
        &&& self.j == if self.k < self.idx().len() { self.idx()[self.k as int] } else { self.s@.len() as int }
    }

    /// Where the next token starts, or the end of the input.
    pub open spec fn tok(&self) -> int {
        skip_ws(self.s@, self.p@)
    }

    /// The first byte of the next token, or 0 at the end of the input.
    pub open spec fn next(&self) -> u8 {
        if self.tok() < self.s@.len() {
            self.s@[self.tok()]
        } else {
            0
        }
    }

    /// The same input and index, at position `p`.
    pub open spec fn moved(&self, old: &Self, p: int) -> bool {
        &&& self.s == old.s
        &&& self.st == old.st
        &&& self.p@ == p
    }

    /// The same place (the window may have moved).
    pub open spec fn same(&self, old: &Self) -> bool {
        &&& self.s == old.s
        &&& self.st == old.st
        &&& self.p == old.p
        &&& self.k == old.k
        &&& self.j == old.j
    }

    /// The cursor's entry is within the index.
    pub proof fn lemma_bound(&self)
        requires
            self.wf(),
        ensures
            self.k <= self.idx().len(),
    {
        lemma_cnt_bound(self.s@, self.st@, self.s@.len() as int);
        lemma_prefix(self.s@, self.st@, self.p@, self.s@.len() as int);
    }

    /// The next token is at `j`.
    pub proof fn lemma_tok(&self)
        requires
            self.wf(),
        ensures
            self.j == self.tok(),
            self.tok() < self.s@.len() <==> self.k < self.idx().len(),
            self.tok() <= self.s@.len(),
    {
        lemma_close(self.s@, self.st@, self.p@);
    }

    /// Reads entry `k` into `j`, once `k` and `p` have moved.
    #[inline(always)]
    fn fetch(&mut self)
        requires
            old(self).w.inv(),
            old(self).w.s == old(self).s,
            old(self).w.st == old(self).st@,
            old(self).st@ <= old(self).p@ <= old(self).s@.len(),
            old(self).s@.len() <= isize::MAX,
            old(self).idx().len() <= old(self).s@.len(),
            out(old(self).s@, old(self).st@, old(self).p@),
            bnd(old(self).s@, old(self).st@, old(self).p@),
            old(self).k == cnt(old(self).s@, old(self).st@, old(self).p@),
        ensures
            final(self).wf(),
            final(self).moved(old(self), old(self).p@),
            final(self).k == old(self).k,
    {
        self.j = match self.w.at(self.k) {
            Some(q) => q,
            None => self.s.len(),
        };
    }

    /// A cursor at the start of the input.
    pub fn new(s: &'a [u8], w: Win<'a>, Ghost(st): Ghost<int>) -> (r: Self)
        requires
            w.inv(),
            s@.len() <= isize::MAX,
            w.s == s,
            w.st == st,
        ensures
            r.wf(),
            r.s == s,
            r.st@ == st,
            r.p@ == st,
    {
        let _n = s.len();
        let mut c = Cursor { s, w, k: 0, j: 0, st: Ghost(st), p: Ghost(st) };
        proof {
            assert(positions(s@, st, st, st) =~= Seq::<int>::empty());
            lemma_positions_len(s@, st, st, s@.len() as int);
        }
        c.fetch();
        c
    }

    /// Gives back the window's buffer.
    pub fn into_buf(self) -> Vec<u32> {
        self.w.into_buf()
    }

    /// The first byte of the next token (0 at the end of the input).
    #[inline(always)]
    pub fn peek(&self) -> (c: u8)
        requires
            self.wf(),
        ensures
            c == self.next(),
            self.tok() < self.s@.len() <==> self.k < self.idx().len(),
            self.tok() < self.s@.len() ==> self.idx()[self.k as int] == self.tok(),
            self.j == self.tok(),
    {
        proof {
            self.lemma_tok();
        }
        if self.j < self.s.len() {
            get8(self.s, self.j)
        } else {
            0
        }
    }

    /// Whether no token is left.
    #[inline(always)]
    pub fn done(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == (self.tok() == self.s@.len()),
    {
        proof {
            self.lemma_tok();
        }
        self.j >= self.s.len()
    }

    /// Steps over the operator `c` if it is the next token.
    #[inline(always)]
    pub fn eat(&mut self, c: u8) -> (r: bool)
        requires
            old(self).wf(),
            is_op(c),
        ensures
            final(self).wf(),
            r == (old(self).next() == c),
            r ==> final(self).moved(old(self), old(self).tok() + 1),
            !r ==> *final(self) == *old(self),
            r ==> final(self).k == old(self).k + 1,
    {
        proof {
            lemma_close(self.s@, self.st@, self.p@);
        }
        if self.peek() == c {
            self.k = self.k + 1;
            self.p = Ghost(skip_ws(self.s@, self.p@) + 1);
            self.fetch();
            true
        } else {
            false
        }
    }

    /// Reads the literal `lit` (`true`, `false` or `null`) if it is the
    /// next token.
    #[inline(always)]
    pub fn lit(&mut self, lit: &[u8]) -> (r: bool)
        requires
            old(self).wf(),
            lit@.len() > 0,
            forall|m: int| 0 <= m < lit@.len() ==> lexeme(#[trigger] lit@[m]),
        ensures
            final(self).wf(),
            r == (has_lit(old(self).s@, old(self).tok(), lit@) && bnd(
                old(self).s@,
                old(self).st@,
                old(self).tok() + lit@.len(),
            )),
            r ==> final(self).moved(old(self), old(self).tok() + lit@.len()),
            !r ==> *final(self) == *old(self),
    {
        let ghost g = self.s@;
        let ghost st = self.st@;
        proof {
            lemma_close(g, st, self.p@);
            lemma_skip(g, st, self.p@);
            self.lemma_tok();
        }
        if self.j >= self.s.len() {
            return false;
        }
        let j = self.j;
        if !ex_has_lit(self.s, j, lit) {
            return false;
        }
        let e = j + lit.len();
        proof {
            assert forall|m: int| j <= m < e implies lexeme(#[trigger] g[m]) by {
                assert(g[m] == g.subrange(j as int, e as int)[m - j]);
            }
            lemma_scalar_run(g, st, j as int, e as int);
        }
        if e < self.s.len() && !ex_delim(get8(self.s, e)) {
            proof {
                assert(byte(g, e as int) == g[e as int]);
            }
            return false;
        }
        self.k = self.k + 1;
        self.p = Ghost(e as int);
        self.fetch();
        true
    }

    /// Reads the number that is the next token: its lexeme `s[a..b]`, and
    /// its significand and power of ten, with whether those are exact
    /// (`ex_number_scan`).
    #[inline(always)]
    pub fn num(&mut self) -> (r: Option<(usize, usize, NumVal, bool)>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            match number_end(old(self).s@, old(self).tok()) {
                Some(e) if bnd(old(self).s@, old(self).st@, e) => r matches Some((a, b, v, ok)) && a
                    == old(self).tok() && b == e && final(self).moved(old(self), e) && (ok
                    ==> number_value(old(self).s@, old(self).tok()) == (v.neg, v.w as int, v.q as int)),
                _ => r is None && *final(self) == *old(self),
            },
    {
        let ghost g = self.s@;
        let ghost st = self.st@;
        proof {
            lemma_close(g, st, self.p@);
            lemma_skip(g, st, self.p@);
            self.lemma_tok();
        }
        if self.j >= self.s.len() {
            return None;
        }
        let j = self.j;
        proof {
            lemma_number_lexeme(g, j as int);
        }
        match (if verilith_simd::neon::has_neon() { ex_number_scan_k(self.s, j) } else { ex_number_scan(self.s, j) }) {
            Some((e, v, ok)) => {
                proof {
                    lemma_scalar_run(g, st, j as int, e as int);
                }
                if e < self.s.len() && !ex_delim(get8(self.s, e)) {
                    proof {
                        assert(byte(g, e as int) == g[e as int]);
                    }
                    return None;
                }
                self.k = self.k + 1;
                self.p = Ghost(e as int);
                self.fetch();
                Some((j, e, v, ok))
            },
            None => None,
        }
    }

    /// Reads the string that is the next token. Returns its raw body
    /// `s[a..b]` and whether it has escapes; if it has, the decoded string
    /// is appended to `dst`.
    #[inline(always)]
    pub fn string(&mut self, dst: &mut Vec<u8>) -> (r: Option<(usize, usize, bool)>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).k >= old(self).k,
            r is Some ==> final(self).k > old(self).k,
            old(self).next() != 0x22 ==> r is None && *final(self) == *old(self) && final(dst)@ == old(dst)@,
            old(self).next() == 0x22 ==> match string(old(self).s@, old(self).tok()) {
                Some((n, esc)) => r == Some(((old(self).tok() + 1) as usize, (n - 1) as usize, esc))
                    && final(self).moved(old(self), n) && final(dst)@ == if esc {
                    old(dst)@ + decode(old(self).s@, old(self).tok() + 1, n - 1)
                } else {
                    old(dst)@
                },
                None => r is None && final(self).same(old(self)),
            },
    {
        proof {
            lemma_skip(self.s@, self.st@, self.p@);
        }
        if self.peek() != 0x22 {
            return None;
        }
        let j = self.j;
        proof {
            crate::lemmas::lemma_string_body_advances(self.s@, j + 1, false);
            if let Some((n, _)) = string(self.s@, j as int) {
                lemma_cnt_bound(self.s@, self.st@, n);
            }
        }
        // The scan reads forward from entry `k`: the window must not be past it.
        if self.w.kbase > self.k {
            let _ = self.w.at(self.k);
        }
        match ex2_string_dec(&mut self.w, self.k, j, Ghost(self.st@), dst) {
            Some((k2, e, esc)) => {
                self.k = k2;
                self.p = Ghost(e as int);
                self.fetch();
                Some((j + 1, e - 1, esc))
            },
            None => None,
        }
    }

    /// Passes over the next value without validating it: a string up to
    /// its closing quote, a container up to its matching bracket, anything
    /// else as one scalar. False (and the cursor stays) if there is no
    /// value to pass over: at an operator other than an opening bracket,
    /// at the end of the input, or when the brackets or quotes do not
    /// match up.
    #[inline(always)]
    pub fn skip(&mut self) -> (r: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).k >= old(self).k,
            final(self).s == old(self).s,
            final(self).st == old(self).st,
            match skip_to(old(self).s@, old(self).st@, old(self).idx(), old(self).p@) {
                Some((k1, p1)) => r && final(self).k == k1 && final(self).p@ == p1,
                None => !r && final(self).same(old(self)),
            },
    {
        let ghost g = self.s@;
        let ghost st = self.st@;
        let ghost p0 = self.p@;
        proof {
            lemma_close(g, st, p0);
            lemma_skip(g, st, p0);
            self.lemma_tok();
        }
        if self.j >= self.s.len() {
            return false;
        }
        let j = self.j;
        let c = get8(self.s, j);
        proof {
            assert(byte(g, j as int) == g[j as int]);
        }
        if c == 0x22 {
            let mut k = self.k + 1;
            let ghost mut lo: int = j + 1;
            proof {
                assert(uq(g, st, j as int));
                assert(instr(g, st, j as int));
                lemma_at(g, st, j as int);
            }
            loop
                invariant
                    g == self.s@,
                    st == self.st@,
                    self.w.inv(),
                    self.w.s == self.s,
                    self.w.st == st,
                    g.len() <= isize::MAX,
                    full(g, st).len() <= g.len(),
                    st <= j < lo <= g.len(),
                    j == skip_ws(g, p0),
                    g[j as int] == 0x22,
                    p0 == old(self).p@,
                    k == cnt(g, st, lo),
                    instr(g, st, lo - 1),
                    quote_from(g, st, j + 1) == quote_from(g, st, lo),
                    self.same(old(self)),
                    old(self).wf(),
                    k > self.k,
                decreases g.len() - lo,
            {
                let q = match self.w.at(k) {
                    Some(q) => q,
                    None => {
                        proof {
                            lemma_none_after(g, st, lo);
                            lemma_no_quote(g, st, lo, g.len() as int);
                            assert(quote_from(g, st, g.len() as int) == g.len());
                        }
                        return false;
                    },
                };
                let d = get8(self.s, q);
                proof {
                    lemma_next(g, st, lo, lo);
                    assert(byte(g, q as int) == g[q as int]);
                    lemma_no_quote(g, st, lo, q as int);
                }
                if d == 0x22 {
                    proof {
                        assert(uq(g, st, q as int));
                        assert(!instr(g, st, q as int));
                        assert(!scalar(g, st, q as int));
                        assert(quote_from(g, st, q as int) == q);
                    }
                    self.k = k + 1;
                    self.p = Ghost(q + 1);
                    self.fetch();
                    return true;
                }
                proof {
                    assert(!uq(g, st, q as int));
                    assert(instr(g, st, q as int));
                    assert(quote_from(g, st, q as int) == quote_from(g, st, q + 1));
                    lo = q + 1;
                }
                k = k + 1;
            }
        } else if c == 0x5B || c == 0x7B {
            proof {
                self.lemma_bound();
            }
            self.walk(self.k + 1)
        } else if c == 0x2C || c == 0x3A || c == 0x5D || c == 0x7D {
            false
        } else {
            // One scalar. The cursor moves to the next index entry; the
            // byte before it must not be a backslash, which would leave
            // that entry escaped.
            let q = match self.w.at(self.k + 1) {
                Some(q) => q,
                None => self.s.len(),
            };
            proof {
                lemma_after_scalar(g, st, j as int, q as int);
            }
            if get8(self.s, q - 1) == 0x5C {
                return false;
            }
            proof {
                assert(byte(g, q - 1) == g[q - 1]);
            }
            self.k = self.k + 1;
            self.p = Ghost(q as int);
            self.fetch();
            true
        }
    }

    /// Walks the index from entry `k` at nesting depth 1 and moves the
    /// cursor past the bracket that closes that depth.
    #[inline(always)]
    fn walk(&mut self, from: usize) -> (r: bool)
        requires
            old(self).wf(),
            old(self).k <= from <= old(self).idx().len(),
        ensures
            final(self).wf(),
            final(self).k >= old(self).k,
            final(self).s == old(self).s,
            final(self).st == old(self).st,
            match close_k(old(self).s@, old(self).idx(), from as int, 1) {
                Some(k1) => r && final(self).k == k1 && final(self).p@ == old(self).idx()[k1 - 1] + 1,
                None => !r && final(self).same(old(self)),
            },
    {
        let ghost g = self.s@;
        let ghost st = self.st@;
        let ghost k0 = from as int;
        let ghost idx = full(g, st);
        let mut k = from;
        let mut d: usize = 0;
        // Eight entries at a time where the window holds them: if they
        // hold no more closing brackets than the depth below the start,
        // the depth cannot reach 0 among them. Otherwise eight single
        // steps, and back to blocks.
        loop
            invariant
                g == self.s@,
                st == self.st@,
                idx == full(g, st),
                self.w.inv(),
                self.w.s == self.s,
                self.w.st == st,
                0 <= k0 <= k,
                k <= idx.len(),
                idx.len() <= g.len() <= isize::MAX,
                0 <= d <= k - k0,
                close_k(g, idx, k0, 1) == close_k(g, idx, k as int, d + 1),
                self.same(old(self)),
                old(self).wf(),
                g == old(self).s@,
                k0 == from,
                self.k <= k0,
            decreases idx.len() - k,
        {
            let ghost ks = k;
            while self.w.kbase <= k && k <= self.w.kend && 8 <= self.w.kend - k
                invariant
                    ks <= k,
                    k <= idx.len(),
                    idx.len() <= g.len() <= isize::MAX,
                    g == self.s@,
                    st == self.st@,
                    idx == full(g, st),
                    self.w.inv(),
                    self.w.s == self.s,
                    self.w.st == st,
                    0 <= k0 <= k,
                    0 <= d <= k - k0,
                    close_k(g, idx, k0, 1) == close_k(g, idx, k as int, d + 1),
                    self.same(old(self)),
                    old(self).wf(),
                decreases self.w.kend - k,
            {
                let mut o: usize = 0;
                let mut c: usize = 0;
                let mut j: usize = 0;
                let i0 = k - self.w.kbase;
                let w0 = self.w.w0;
                let src = self.s;
                let bs = self.w.buf.as_slice();
                proof {
                    lemma_win_entry(&self.w, k as int);
                    lemma_win_entry(&self.w, k + 7);
                }
                while j < 8
                    invariant
                        g == self.s@,
                        st == self.st@,
                        idx == full(g, st),
                        self.w.inv(),
                        self.w.s == self.s,
                        self.w.st == st,
                        self.w.kbase <= k,
                        k + 8 <= self.w.kend,
                        i0 == k - self.w.kbase,
                        w0 == self.w.w0,
                        src@ == g,
                        bs@ == self.w.buf@,
                        k + 8 <= idx.len(),
                        0 <= j <= 8,
                        o == opens(g, idx, k as int, j as int),
                        c == closes(g, idx, k as int, j as int),
                        o <= j,
                        c <= j,
                    decreases 8 - j,
                {
                    proof {
                        lemma_win_entry(&self.w, k + j);
                    }
                    let b = get8(src, w0 + get32(bs, i0 + j) as usize) & 0xDF;
                    proof {
                        let b0 = g[idx[k + j]];
                        assert(byte(g, idx[k + j]) == b0);
                        assert((b0 & 0xDF == 0x5B) == (b0 == 0x5B || b0 == 0x7B)) by (bit_vector);
                        assert((b0 & 0xDF == 0x5D) == (b0 == 0x5D || b0 == 0x7D)) by (bit_vector);
                    }
                    o = o + (if b == 0x5B { 1 } else { 0 });
                    c = c + (if b == 0x5D { 1 } else { 0 });
                    j = j + 1;
                }
                if c > d {
                    break;
                }
                proof {
                    lemma_block(g, idx, k as int, d + 1, 8);
                }
                d = d + o - c;
                k = k + 8;
            }
            let ghost kb = k;
            let stop = k + 8;
            while k < stop
                invariant
                    g == self.s@,
                    st == self.st@,
                    idx == full(g, st),
                    self.w.inv(),
                    self.w.s == self.s,
                    self.w.st == st,
                    0 <= k0 <= k,
                    0 <= d <= k - k0,
                    close_k(g, idx, k0, 1) == close_k(g, idx, k as int, d + 1),
                    self.same(old(self)),
                    old(self).wf(),
                    g == old(self).s@,
                    k0 == from,
                    self.k <= k0,
                    k <= stop,
                    stop == kb + 8,
                    ks <= kb <= k,
                    k <= idx.len(),
                    idx.len() <= g.len() <= isize::MAX,
                decreases stop - k,
            {
                let q = match self.w.at(k) {
                    Some(q) => q,
                    None => {
                        proof {
                            assert(close_k(g, idx, k as int, d + 1) is None);
                        }
                        return false;
                    },
                };
                let b = get8(self.s, q);
                proof {
                    assert(byte(g, q as int) == g[q as int]);
                    assert(close_k(g, idx, k as int, d + 1) == if d + 1 + delta(b) == 0 {
                        Some(k + 1)
                    } else {
                        close_k(g, idx, k + 1, d + 1 + delta(b))
                    });
                }
                k = k + 1;
                if b == 0x5B || b == 0x7B {
                    d = d + 1;
                } else if b == 0x5D || b == 0x7D {
                    if d == 0 {
                        proof {
                            assert(delta(b) == -1);
                            assert(close_k(g, idx, k0, 1) == Some(k as int));
                            lemma_entry(g, st, g.len() as int, k - 1);
                            lemma_at(g, st, q as int);
                            assert(!strs(g, st, q as int));
                            assert(!scalar(g, st, q as int));
                            assert(cnt(g, st, q + 1) == k);
                            assert(out(g, st, q + 1));
                            assert(bnd(g, st, q + 1));
                        }
                        self.k = k;
                        self.p = Ghost(q + 1);
                        self.fetch();
                        return true;
                    }
                    d = d - 1;
                }
            }
        }
    }

    /// Leaves the container the cursor is in: moves past the bracket that
    /// closes it, wherever in it the cursor is. Nothing passed over is
    /// validated. False (and the cursor stays) if no bracket closes it.
    #[inline(always)]
    pub fn leave(&mut self) -> (r: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).k >= old(self).k,
            final(self).s == old(self).s,
            final(self).st == old(self).st,
            match close_k(old(self).s@, old(self).idx(), old(self).k as int, 1) {
                Some(k1) => r && final(self).k == k1 && final(self).p@ == old(self).idx()[k1 - 1] + 1,
                None => !r && final(self).same(old(self)),
            },
    {
        proof {
            self.lemma_bound();
        }
        self.walk(self.k)
    }

    /// Offset in the input of the next token (the input's length at its
    /// end). For error reports.
    pub fn offset(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.tok(),
    {
        proof {
            self.lemma_tok();
        }
        self.j
    }
}

/// Where the index of `s` starts, after a byte order mark, if `s` is
/// UTF-8; the on-demand reader rejects other input at once. (The rest of
/// stage 1's checks need no pass of their own: a control character inside
/// a string is in the index, and a string left open runs out of index;
/// the reader rejects either when it reaches it.)
pub fn index_start(s: &[u8]) -> (r: Option<usize>)
    ensures
        r matches Some(st) ==> st == bom_end(s@) && utf8_from(s@, st as int),
        r is None ==> !utf8_from(s@, bom_end(s@)),
{
    let start: usize = if ex_has_lit(s, 0, &[0xEF, 0xBB, 0xBF]) { 3 } else { 0 };
    proof {
        assert([0xEFu8, 0xBB, 0xBF]@ == seq![0xEFu8, 0xBB, 0xBF]);
    }
    if !crate::utf8::utf8_valid(s, start) {
        return None;
    }
    Some(start)
}

/// Why a `Reader` call failed: the token it was asked for is not what is
/// at the cursor. `Reader::offset` says where.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Mismatch;

/// What the reader expects next.
const VALUE: u8 = 0;

const AFTER: u8 = 1;

const START: u8 = 2;

const KEY: u8 = 3;

/// The on-demand reader: a `Cursor` and what the caller may read next (a
/// value, a key, or a separator after a value). Every call is safe in any
/// state and on any input; a call that does not fit returns `Mismatch`.
pub struct Reader<'a> {
    c: Cursor<'a>,
    state: u8,
    scratch: Vec<u8>,
    /// Where the index window's buffer goes back to when the reader is
    /// dropped.
    home: &'a mut Vec<u32>,
}

impl<'a> Reader<'a> {
    pub closed spec fn inv(&self) -> bool {
        self.c.wf()
    }

    /// Index entries not yet read.
    pub closed spec fn left(&self) -> int {
        self.c.idx().len() - self.c.k
    }

    /// The input.
    pub closed spec fn src(&self) -> Seq<u8> {
        self.c.s@
    }

    /// Stands at the document's value in `s`, indexing it a window at a
    /// time into `idx`'s buffer, which is given back when the reader is
    /// dropped. `None` if `s` is not UTF-8 (see `index_start`).
    pub fn new(s: &'a [u8], idx: &'a mut Vec<u32>) -> (r: Option<Self>)
        ensures
            r matches Some(rd) ==> rd.inv(),
            r is None && s@.len() <= isize::MAX ==> !utf8_from(s@, bom_end(s@)),
    {
        Self::with_window(s, idx, WINDOW)
    }

    /// `new` with index windows of `win` bytes, a multiple of 128 from 128
    /// up to 2^30 (for tests; `None` otherwise).
    pub fn with_window(s: &'a [u8], idx: &'a mut Vec<u32>, win: usize) -> (r: Option<Self>)
        ensures
            r matches Some(rd) ==> rd.inv(),
            r is None && 128 <= win <= 0x4000_0000 && win % 128 == 0 && s@.len() <= isize::MAX ==> !utf8_from(
                s@,
                bom_end(s@),
            ),
    {
        // No slice is longer than `isize::MAX` bytes; the proofs need it
        // said.
        if win < 128 || win > 0x4000_0000 || win % 128 != 0 || s.len() > isize::MAX as usize {
            return None;
        }
        match index_start(s) {
            Some(st) => {
                let mut buf = Vec::new();
                std::mem::swap(idx, &mut buf);
                let w = Win::new(s, st, win, buf);
                Some(Reader { c: Cursor::new(s, w, Ghost(st as int)), state: VALUE, scratch: Vec::new(), home: idx })
            },
            None => None,
        }
    }

    /// First byte of the next token: for a value `"`, `{`, `[`, `t`, `f`,
    /// `n`, `-` or a digit. 0 at the end of the input (and at a NUL byte,
    /// which no reader accepts; `at_end` tells the two apart).
    #[inline(always)]
    pub fn peek(&self) -> u8
        requires
            self.inv(),
    {
        self.c.peek()
    }

    /// Offset in the input of the next token.
    pub fn offset(&self) -> usize
        requires
            self.inv(),
    {
        self.c.offset()
    }

    /// Whether a complete value has been read and nothing follows it.
    pub fn at_end(&self) -> bool
        requires
            self.inv(),
    {
        self.state == AFTER && self.c.done()
    }

    /// Passes over the value at the cursor without validating it.
    #[inline(always)]
    pub fn skip(&mut self) -> (r: Result<(), Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        if self.state != VALUE || !self.c.skip() {
            return Err(Mismatch);
        }
        self.state = AFTER;
        Ok(())
    }

    #[inline(always)]
    fn open(&mut self, c: u8) -> (r: Result<(), Mismatch>)
        requires
            old(self).inv(),
            is_op(c),
        ensures
            final(self).inv(),
    {
        if self.state != VALUE || !self.c.eat(c) {
            return Err(Mismatch);
        }
        self.state = START;
        Ok(())
    }

    #[inline(always)]
    fn step(&mut self, close: u8, to: u8) -> (r: Result<bool, Mismatch>)
        requires
            old(self).inv(),
            is_op(close),
        ensures
            final(self).inv(),
            final(self).left() <= old(self).left(),
    {
        if self.state == VALUE {
            if !self.c.skip() {
                return Err(Mismatch);
            }
            self.state = AFTER;
        }
        if self.state == KEY {
            return Err(Mismatch);
        }
        if self.c.eat(close) {
            self.state = AFTER;
            return Ok(false);
        }
        if self.state == START {
            self.state = to;
            return Ok(true);
        }
        if self.c.eat(0x2C) {
            self.state = to;
            return Ok(true);
        }
        Err(Mismatch)
    }

    /// Enters the array at the cursor.
    #[inline(always)]
    pub fn arr_begin(&mut self) -> (r: Result<(), Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        self.open(0x5B)
    }

    /// Steps to the next element, passing over the current one if it was
    /// not read. `false` once the array is closed.
    #[inline(always)]
    pub fn arr_next(&mut self) -> (r: Result<bool, Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).left() <= old(self).left(),
    {
        self.step(0x5D, VALUE)
    }

    /// Enters the object at the cursor.
    #[inline(always)]
    pub fn obj_begin(&mut self) -> (r: Result<(), Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        self.open(0x7B)
    }

    /// Steps to the next key, passing over the current value if it was
    /// not read. `false` once the object is closed.
    #[inline(always)]
    pub fn obj_next(&mut self) -> (r: Result<bool, Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).left() <= old(self).left(),
    {
        self.step(0x7D, KEY)
    }

    /// Leaves the innermost container the cursor is in, from anywhere in
    /// it, without validating the rest of it.
    #[inline(always)]
    pub fn leave(&mut self) -> (r: Result<(), Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        if !self.c.leave() {
            return Err(Mismatch);
        }
        self.state = AFTER;
        Ok(())
    }

    /// Reads the key at the cursor and the colon after it: the key's raw
    /// body `s[a..b]` and whether it has escapes (then the decoded key is
    /// in the reader's scratch buffer).
    #[inline(always)]
    fn key_raw(&mut self) -> (r: Result<(usize, usize, bool), Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).left() <= old(self).left(),
            r is Ok ==> final(self).left() < old(self).left(),
            r matches Ok((a, b, _)) ==> a <= b <= final(self).src().len(),
            final(self).src() == old(self).src(),
    {
        if self.state != KEY {
            return Err(Mismatch);
        }
        self.scratch.clear();
        let ghost g = self.c.s@;
        let ghost j = self.c.tok();
        proof {
            crate::lemmas::lemma_string_body_advances(g, j + 1, false);
        }
        match self.c.string(&mut self.scratch) {
            Some((a, b, esc)) => {
                if !self.c.eat(0x3A) {
                    return Err(Mismatch);
                }
                self.state = VALUE;
                Ok((a, b, esc))
            },
            None => Err(Mismatch),
        }
    }

    /// Passes over the key at the cursor, to its value.
    #[inline(always)]
    pub fn key_skip(&mut self) -> (r: Result<(), Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        match self.key_raw() {
            Ok(_) => Ok(()),
            Err(e) => Err(e),
        }
    }

    /// Whether the key at the cursor is `key` (compared decoded); moves to
    /// its value either way.
    #[inline(always)]
    pub fn key_is(&mut self, key: &[u8]) -> (r: Result<bool, Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            r is Ok ==> final(self).left() < old(self).left(),
    {
        match self.key_raw() {
            Ok((a, b, esc)) => {
                if esc {
                    Ok(self.scratch.len() == key.len() && ex_has_lit(self.scratch.as_slice(), 0, key))
                } else {
                    Ok(b - a == key.len() && ex_has_lit(self.c.s, a, key))
                }
            },
            Err(e) => Err(e),
        }
    }

    /// Moves to the value of the next field named `key`, searching
    /// forward only. `false` (and the object is closed) if there is none.
    #[inline(always)]
    pub fn find(&mut self, key: &[u8]) -> (r: Result<bool, Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        loop
            invariant
                self.inv(),
            decreases self.left(),
        {
            match self.obj_next() {
                Ok(true) => {},
                Ok(false) => {
                    return Ok(false);
                },
                Err(e) => {
                    return Err(e);
                },
            }
            match self.key_is(key) {
                Ok(true) => {
                    return Ok(true);
                },
                Ok(false) => {
                    proof {
                        self.c.lemma_bound();
                    }
                },
                Err(e) => {
                    return Err(e);
                },
            }
        }
    }

    /// Reads the string at the cursor: its raw body `s[a..b]` and whether
    /// it has escapes; if it has, the decoded string is appended to `dst`.
    #[inline(always)]
    pub fn str_raw(&mut self, dst: &mut Vec<u8>) -> (r: Result<(usize, usize, bool), Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            r matches Ok((a, b, _)) ==> a <= b <= final(self).src().len(),
            final(self).src() == old(self).src(),
    {
        if self.state != VALUE {
            return Err(Mismatch);
        }
        proof {
            crate::lemmas::lemma_string_body_advances(self.c.s@, self.c.tok() + 1, false);
        }
        match self.c.string(dst) {
            Some(r) => {
                self.state = AFTER;
                Ok(r)
            },
            None => Err(Mismatch),
        }
    }

    /// Reads the number at the cursor: its lexeme `s[a..b]`, and its
    /// significand and power of ten with whether those are exact.
    #[inline(always)]
    pub fn num_raw(&mut self) -> (r: Result<(usize, usize, NumVal, bool), Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            r matches Ok((a, b, _, _)) ==> a <= b <= final(self).src().len(),
            final(self).src() == old(self).src(),
    {
        if self.state != VALUE {
            return Err(Mismatch);
        }
        proof {
            crate::lemmas::lemma_skip_ws_bounds(self.c.s@, self.c.p@);
            lemma_number_lexeme(self.c.s@, self.c.tok());
        }
        match self.c.num() {
            Some(r) => {
                self.state = AFTER;
                Ok(r)
            },
            None => Err(Mismatch),
        }
    }

    #[inline(always)]
    fn lit(&mut self, lit: &[u8]) -> (r: bool)
        requires
            old(self).inv(),
            lit@.len() > 0,
            forall|m: int| 0 <= m < lit@.len() ==> lexeme(#[trigger] lit@[m]),
        ensures
            final(self).inv(),
    {
        if self.state == VALUE && self.c.lit(lit) {
            self.state = AFTER;
            true
        } else {
            false
        }
    }

    /// Reads `null` if it is the value at the cursor.
    #[inline(always)]
    pub fn null(&mut self) -> (r: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        let l = [0x6Eu8, 0x75, 0x6C, 0x6C];
        self.lit(&l)
    }

    /// Reads the `true` or `false` at the cursor.
    #[inline(always)]
    pub fn bool(&mut self) -> (r: Result<bool, Mismatch>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        let t = [0x74u8, 0x72, 0x75, 0x65];
        let f = [0x66u8, 0x61, 0x6C, 0x73, 0x65];
        if self.lit(&t) {
            Ok(true)
        } else if self.lit(&f) {
            Ok(false)
        } else {
            Err(Mismatch)
        }
    }
}

} // verus!

impl<'a> Reader<'a> {
    /// Reads the string at the cursor, decoded. Borrows the input unless
    /// the string has escapes; then it is decoded into `buf`.
    #[inline(always)]
    pub fn str<'b>(&mut self, buf: &'b mut Vec<u8>) -> Result<&'b [u8], Mismatch>
    where
        'a: 'b,
    {
        buf.clear();
        let (a, b, esc) = self.str_raw(buf)?;
        if esc {
            Ok(&buf[..])
        } else {
            let s: &'a [u8] = self.c.s;
            Ok(&s[a..b])
        }
    }

    /// Reads the number at the cursor as the nearest double.
    #[inline(always)]
    pub fn f64(&mut self) -> Result<f64, Mismatch> {
        let (a, b, v, ok) = self.num_raw()?;
        if ok {
            if let Some(x) = crate::number::from_parts(v.neg, v.w, v.q as i64) {
                return Ok(x);
            }
        }
        Ok(crate::number::parse_f64_at(self.c.s, a, b))
    }

    /// Reads the number at the cursor if it is an integer (no fraction or
    /// exponent) that fits in `i64`.
    #[inline(always)]
    pub fn i64(&mut self) -> Result<i64, Mismatch> {
        let (a, b, v, ok) = self.num_raw()?;
        let lex = &self.c.s[a..b];
        // An exact significand with no fraction or exponent is the integer.
        if ok && v.q == 0 && v.w <= i64::MAX as u64 && !lex.iter().any(|&c| c == b'.' || c | 0x20 == b'e') {
            return Ok(if v.neg { -(v.w as i64) } else { v.w as i64 });
        }
        crate::number::parse_i64(lex).ok_or(Mismatch)
    }

    /// Reads the key at the cursor, decoded, and moves to its value. The
    /// slice is valid until the reader is used again.
    #[inline(always)]
    pub fn key(&mut self) -> Result<&[u8], Mismatch> {
        let (a, b, esc) = self.key_raw()?;
        if esc {
            Ok(&self.scratch[..])
        } else {
            Ok(&self.c.s[a..b])
        }
    }

    /// The input.
    pub fn source(&self) -> &'a [u8] {
        self.c.s
    }
}

impl Drop for Reader<'_> {
    fn drop(&mut self) {
        std::mem::swap(self.home, &mut self.c.w.buf);
    }
}

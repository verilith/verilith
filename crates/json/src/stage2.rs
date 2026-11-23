//! Stage 2 of the two-pass parser: walking the structural index.
//!
//! Stage 2 follows the grammar in `spec.rs` exactly like the one-pass
//! parser does, but it never scans whitespace, string contents or the
//! inside of numbers: it jumps from one structural position to the next.
//! The lemmas here say why that is the same thing. The central one,
//! `lemma_skip`, says that after a token, the next structural position is
//! where `skip_ws` lands. The others say which positions inside a string,
//! a number or a literal are structural.
#[allow(unused_imports)]
use crate::index::*;
#[allow(unused_imports)]
use crate::lanes::*;
use crate::parser::*;
#[allow(unused_imports)]
use crate::simd::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// Stage 2 reads the input and its structural index through the window
/// (`Win`), which indexes the input as stage 2 goes.
pub type Ctx<'a> = Win<'a>;

/// The whole structural index of `s[st..]`.
pub open spec fn ix(s: Seq<u8>, st: int) -> Seq<int> {
    positions(s, st, st, s.len() as int)
}

/// Stage 2's window, before a read at entry `k`: `k` is not behind it.
pub open spec fn win_at(w: &Win, s: Seq<u8>, st: int, k: int) -> bool {
    &&& w.inv()
    &&& s.len() <= MAX_INPUT
    &&& w.s@ == s
    &&& w.st == st
    &&& w.kbase <= k
}

/// Entry `k` of the index through the window, with room on the tape kept
/// for a token per entry left in the window, counted from `k0`. Stage 2
/// reads forward only, so the fast path is one comparison; the tape is
/// topped up only when the window moves.
#[inline(always)]
pub fn at2<S: Sink>(w: &mut Win, k: usize, tape: &mut S, Ghost(k0): Ghost<int>) -> (r: Option<usize>)
    requires
        old(w).inv(),
        old(w).s@.len() <= MAX_INPUT,
        old(w).kbase <= k,
        k <= k0 + 2,
        old(tape).room() >= old(w).kend - k0,
    ensures
        final(w).inv(),
        final(w).same(old(w)),
        final(w).kbase <= k,
        r matches Some(q) ==> k < final(w).all().len() && q == final(w).all()[k as int]
            && q < final(w).wend && k < final(w).kend,
        old(w).kbase <= k < old(w).kend ==> *final(w) == *old(w) && r is Some && final(tape).room() == old(tape).room(),
        r is None ==> final(w).done && k >= final(w).all().len(),
        final(tape).room() >= final(w).kend - k0,
        final(tape).hist() == old(tape).hist(),
        forall|g: Seq<u8>| old(tape).inv(g) ==> #[trigger] final(tape).inv(g),
{
    if k < w.kend {
        proof {
            lemma_win_entry(w, k as int);
        }
        Some(w.w0 + get32(w.buf.as_slice(), k - w.kbase) as usize)
    } else {
        at2_slow(w, k, tape, Ghost(k0))
    }
}

/// Entry `k` of the index, known to be in the window. Stage 2's fast
/// paths check once that the next few entries are in the window and then
/// read them with this, so that the window's fields are loaded once and
/// stay in registers across the reads.
#[inline(always)]
pub fn ent(w: &Win, k: usize) -> (r: usize)
    requires
        w.inv(),
        w.kbase <= k < w.kend,
    ensures
        k < w.all().len(),
        r == w.all()[k as int],
        r < w.wend,
{
    proof {
        lemma_win_entry(w, k as int);
    }
    w.w0 + get32(w.buf.as_slice(), k - w.kbase) as usize
}

/// A string at `j` (entry `k`) whose next entry, in the window, is its
/// closing quote: no escape and no control character, which would be
/// entries of their own. Returns the position after it, or 0 when the
/// string is not that simple.
#[inline(always)]
pub fn str_quick(w: &Win, k: usize, j: usize, s: &[u8], Ghost(st): Ghost<int>) -> (r: usize)
    requires
        str_pre(w, st, k as int, j as int),
        s@ == w.s@,
        k + 1 < w.kend,
    ensures
        r != 0 ==> string(w.s@, j as int) == Some((r as int, false)) && cnt(w.s@, st, r as int) == k + 2
            && out(w.s@, st, r as int) && bnd(w.s@, st, r as int) && r <= w.s@.len(),
{
    let ghost g = s@;
    proof {
        lemma_open_quote(g, st, k as int, j as int);
    }
    let q = ent(w, k + 1);
    proof {
        lemma_string_next(w, st, j + 1, j + 1, k + 1, false, Some(q));
        lemma_plain_inside(g, st, j + 1, q as int);
        lemma_plain_run(g, j + 1, q as int, false);
        assert(byte(g, q as int) == g[q as int]);
    }
    if get8(s, q) == 0x22 {
        proof {
            assert(uq(g, st, q as int));
            assert(!instr(g, st, q as int));
            assert(!scalar(g, st, q as int));
        }
        q + 1
    } else {
        0
    }
}

/// The string at `j` (entry `k`) onto the tape as a token of `kind`.
#[inline(always)]
fn ex2_str_tok<S: Sink>(cx: &mut Ctx, k: usize, j: usize, tape: &mut S, Ghost(st): Ghost<int>, s: &[u8], kind: Kind) -> (r: Option<(usize, usize)>)
    requires
        str_pre(old(cx), st, k as int, j as int),
        s@ == old(cx).s@,
        old(cx).s@.len() <= MAX_INPUT,
        k < old(cx).kend,
        old(tape).room() >= old(cx).kend - k,
        old(tape).inv(old(cx).s@),
        kind == Kind::Str || kind == Kind::Key,
    ensures
        moved(old(cx), final(cx), final(tape), r),
        match string(old(cx).s@, j as int) {
            Some((n, esc)) => r == Some((cnt(old(cx).s@, st, n) as usize, n as usize)) && out(old(cx).s@, st, n)
                && bnd(old(cx).s@, st, n) && n <= old(cx).s@.len()
                && final(tape).hist() == old(tape).hist().push(if kind == Kind::Str {
                    STok::Str { start: j + 1, end: n - 1, escaped: esc }
                } else {
                    STok::Key { start: j + 1, end: n - 1, escaped: esc }
                }),
            None => r is None,
        },
{
    let ghost g = s@;
    // Most strings have no escape: their closing quote is the next entry.
    if k + 1 < cx.kend {
        let e = str_quick(cx, k, j, s, Ghost(st));
        if e != 0 {
            proof {
                crate::lemmas::lemma_string_body_advances(g, j + 1, false);
            }
            tape.push_str_fast(Tok::new(kind, false, (j + 1), (e - 1), NO), s);
            proof {
                lemma_win_entry(cx, k + 1);
            }
            return Some((k + 2, e));
        }
    }
    let kend0 = cx.kend;
    match tape.scan_str(cx, k, j, Ghost(st)) {
        Some((k2, n, esc)) => {
            proof {
                crate::lemmas::lemma_string_body_advances(g, j + 1, false);
            }
            tape.push_str_fast(Tok::new(kind, esc, (j + 1), (n - 1), NO), s);
            keep_room(cx, tape, kend0, Ghost(k2 as int));
            proof {
                lemma_prefix(g, st, cx.wend as int, g.len() as int);
            }
            Some((k2, n))
        },
        None => None,
    }
}

/// `at2` past the window: moves it on and tops up the tape.
#[inline(never)]
fn at2_slow<S: Sink>(w: &mut Win, k: usize, tape: &mut S, Ghost(k0): Ghost<int>) -> (r: Option<usize>)
    requires
        old(w).inv(),
        old(w).s@.len() <= MAX_INPUT,
        old(w).kbase <= k,
        old(w).kend <= k,
        k <= k0 + 2,
        old(tape).room() >= old(w).kend - k0,
    ensures
        final(w).inv(),
        final(w).same(old(w)),
        final(w).kbase <= k,
        r matches Some(q) ==> k < final(w).all().len() && q == final(w).all()[k as int]
            && q < final(w).wend && k < final(w).kend,
        r is None ==> final(w).done && k >= final(w).all().len(),
        final(tape).room() >= final(w).kend - k0,
        final(tape).hist() == old(tape).hist(),
        forall|g: Seq<u8>| old(tape).inv(g) ==> #[trigger] final(tape).inv(g),
{
    let r = w.refill(k);
    tape.reserve(w.kend - w.kbase + 2);
    r
}

/// After reads that may have moved the window on from `kend0`: room on
/// the tape for a token per entry left, counted from `k0`.
#[inline(always)]
pub fn keep_room<S: Sink>(w: &Win, tape: &mut S, kend0: usize, Ghost(k0): Ghost<int>)
    requires
        w.inv(),
        w.s@.len() <= MAX_INPUT,
        w.kbase <= k0 + 2,
        old(tape).room() >= kend0 - k0,
    ensures
        final(tape).room() >= w.kend - k0,
        w.kend == kend0 ==> final(tape).room() == old(tape).room(),
        final(tape).hist() == old(tape).hist(),
        forall|g: Seq<u8>| old(tape).inv(g) ==> #[trigger] final(tape).inv(g),
{
    if w.kend != kend0 {
        tape.reserve(w.kend - w.kbase + 2);
    }
}

/// At most one structural position per byte.
pub proof fn lemma_cnt_bound(s: Seq<u8>, st: int, i: int)
    requires
        0 <= st <= i,
    ensures
        0 <= cnt(s, st, i) <= i - st,
    decreases i - st,
{
    if i > st {
        lemma_cnt_bound(s, st, i - 1);
        lemma_cnt_step(s, st, i - 1);
    }
}

pub proof fn lemma_cnt_step(s: Seq<u8>, st: int, i: int)
    requires
        0 <= st,
        st <= i,
    ensures
        cnt(s, st, i + 1) == cnt(s, st, i) + (if structural(s, st, i) { 1int } else { 0int }),
        structural(s, st, i) ==> positions(s, st, st, i + 1)[cnt(s, st, i)] == i,
        positions(s, st, st, i + 1).subrange(0, cnt(s, st, i)) == positions(s, st, st, i),
{
    let p = positions(s, st, st, i);
    if structural(s, st, i) {
        assert(p.push(i).subrange(0, p.len() as int) =~= p);
    } else {
        assert(p.subrange(0, p.len() as int) =~= p);
    }
}

/// `positions` only grows: earlier prefixes are prefixes of later ones.
pub proof fn lemma_prefix(s: Seq<u8>, st: int, a: int, b: int)
    requires
        0 <= st,
        st <= a <= b,
    ensures
        cnt(s, st, a) <= cnt(s, st, b),
        positions(s, st, st, b).subrange(0, cnt(s, st, a)) == positions(s, st, st, a),
    decreases b - a,
{
    if a < b {
        lemma_prefix(s, st, a, b - 1);
        lemma_cnt_step(s, st, b - 1);
        let pb = positions(s, st, st, b);
        let pb1 = positions(s, st, st, b - 1);
        assert(pb.subrange(0, cnt(s, st, a)) =~= pb.subrange(0, cnt(s, st, b - 1)).subrange(
            0,
            cnt(s, st, a),
        ));
    } else {
        let p = positions(s, st, st, a);
        assert(p.subrange(0, p.len() as int) =~= p);
    }
}

/// With no structural positions in `[a, b)`, the count does not change.
pub proof fn lemma_none_between(s: Seq<u8>, st: int, a: int, b: int)
    requires
        0 <= st,
        st <= a <= b,
        forall|m: int| a <= m < b ==> !#[trigger] structural(s, st, m),
    ensures
        cnt(s, st, a) == cnt(s, st, b),
    decreases b - a,
{
    if a < b {
        lemma_none_between(s, st, a, b - 1);
        lemma_cnt_step(s, st, b - 1);
    }
}

/// The index entry `cnt(a)` is the first structural position at or after
/// `a`.
pub proof fn lemma_next(s: Seq<u8>, st: int, a: int, b: int)
    requires
        0 <= st,
        st <= a <= b <= s.len(),
        cnt(s, st, b) == cnt(s, st, a),
        forall|m: int| a <= m < b ==> !#[trigger] structural(s, st, m),
        cnt(s, st, a) < cnt(s, st, s.len() as int),
    ensures
        ({
            let q = positions(s, st, st, s.len() as int)[cnt(s, st, a)];
            &&& a <= q < s.len()
            &&& structural(s, st, q)
            &&& cnt(s, st, q) == cnt(s, st, a)
            &&& cnt(s, st, q + 1) == cnt(s, st, a) + 1
            &&& forall|m: int| a <= m < q ==> !#[trigger] structural(s, st, m)
        }),
    decreases s.len() - b,
{
    if b == s.len() {
        assert(false);
    } else {
        lemma_cnt_step(s, st, b);
        if structural(s, st, b) {
            lemma_at(s, st, b);
        } else {
            assert forall|m: int| a <= m < b + 1 implies !#[trigger] structural(s, st, m) by {
                if m < b {
                    assert(!structural(s, st, m));
                }
            }
            lemma_next(s, st, a, b + 1);
        }
    }
}

/// Entry `k` of the index is a structural position, and `k` of them come
/// before it.
pub proof fn lemma_entry(s: Seq<u8>, st: int, b: int, k: int)
    requires
        0 <= st <= b,
        0 <= k < cnt(s, st, b),
    ensures
        ({
            let p = positions(s, st, st, b)[k];
            &&& st <= p < b
            &&& structural(s, st, p)
            &&& cnt(s, st, p) == k
        }),
    decreases b - st,
{
    lemma_cnt_step(s, st, b - 1);
    if k < cnt(s, st, b - 1) {
        lemma_entry(s, st, b - 1, k);
        assert(positions(s, st, st, b)[k] == positions(s, st, st, b).subrange(0, cnt(s, st, b - 1))[k]);
    }
}

/// A structural position `q` is entry `cnt(q)` of the index.
pub proof fn lemma_at(s: Seq<u8>, st: int, q: int)
    requires
        0 <= st,
        st <= q < s.len(),
        structural(s, st, q),
    ensures
        cnt(s, st, q) < cnt(s, st, s.len() as int),
        positions(s, st, st, s.len() as int)[cnt(s, st, q)] == q,
        cnt(s, st, q + 1) == cnt(s, st, q) + 1,
{
    lemma_cnt_step(s, st, q);
    lemma_prefix(s, st, q + 1, s.len() as int);
    let full = positions(s, st, st, s.len() as int);
    assert(full.subrange(0, cnt(s, st, q + 1))[cnt(s, st, q)] == full[cnt(s, st, q)]);
}

// ---------------------------------------------------------------------------
// Between tokens
// ---------------------------------------------------------------------------

/// Outside any string, and not right after a backslash.
pub open spec fn out(s: Seq<u8>, st: int, p: int) -> bool {
    !instr(s, st, p - 1) && (p == st || byte(s, p - 1) != 0x5C)
}

/// Whitespace, an operator or a quote: a byte that ends a number or a
/// literal.
pub open spec fn delim(c: u8) -> bool {
    is_ws(c) || is_op(c) || c == 0x22
}

/// A token boundary: the byte before is not part of a scalar, or the byte
/// at `p` ends one.
pub open spec fn bnd(s: Seq<u8>, st: int, p: int) -> bool {
    p == st || !scalar(s, st, p - 1) || p >= s.len() || delim(byte(s, p))
}

/// After a token, `skip_ws` lands on the next structural position.
pub proof fn lemma_skip(s: Seq<u8>, st: int, p: int)
    requires
        0 <= st,
        st <= p <= s.len(),
        out(s, st, p),
        bnd(s, st, p),
    ensures
        ({
            let j = skip_ws(s, p);
            &&& p <= j <= s.len()
            &&& cnt(s, st, j) == cnt(s, st, p)
            &&& forall|m: int| p <= m < j ==> !#[trigger] structural(s, st, m)
            &&& j < s.len() ==> structural(s, st, j) && !esc(s, st, j) && !instr(s, st, j - 1)
                && !is_ws(s[j])
            &&& j == s.len() ==> cnt(s, st, p) == cnt(s, st, s.len() as int)
            &&& out(s, st, j)
        }),
    decreases s.len() - p,
{
    if p < s.len() && is_ws(s[p]) {
        assert(byte(s, p) == s[p]);
        assert(!structural(s, st, p));
        lemma_cnt_step(s, st, p);
        lemma_skip(s, st, p + 1);
        let j = skip_ws(s, p + 1);
        assert forall|m: int| p <= m < j implies !#[trigger] structural(s, st, m) by {
            if m > p {
                assert(!structural(s, st, m));
            }
        }
    } else if p < s.len() {
        assert(byte(s, p) == s[p]);
        assert(!esc(s, st, p));
        assert(structural(s, st, p));
    }
}

// ---------------------------------------------------------------------------
// Numbers and literals
// ---------------------------------------------------------------------------

/// A byte of a number or literal lexeme.
pub open spec fn lexeme(c: u8) -> bool {
    !(is_ws(c) || is_op(c) || c == 0x22 || c == 0x5C)
}

/// A scalar token in `[j, e)`: only its first byte is structural.
pub proof fn lemma_scalar_run(s: Seq<u8>, st: int, j: int, e: int)
    requires
        0 <= st,
        st <= j < e <= s.len(),
        !instr(s, st, j - 1),
        structural(s, st, j),
        forall|m: int| j <= m < e ==> lexeme(#[trigger] s[m]),
    ensures
        cnt(s, st, e) == cnt(s, st, j) + 1,
        out(s, st, e),
        scalar(s, st, e - 1),
        forall|m: int| j < m < e ==> !#[trigger] structural(s, st, m),
    decreases e - j,
{
    assert(byte(s, j) == s[j]);
    assert(lexeme(s[j]));
    assert(!uq(s, st, j));
    assert(!instr(s, st, j));
    assert(scalar(s, st, j));
    lemma_cnt_step(s, st, j);
    if e > j + 1 {
        lemma_run_tail(s, st, j, j + 1, e);
    }
}

proof fn lemma_run_tail(s: Seq<u8>, st: int, j: int, a: int, e: int)
    requires
        0 <= st,
        st <= j < a < e <= s.len(),
        !instr(s, st, a - 1),
        scalar(s, st, a - 1),
        cnt(s, st, a) == cnt(s, st, j) + 1,
        forall|m: int| j <= m < e ==> lexeme(#[trigger] s[m]),
        forall|m: int| j < m < a ==> !#[trigger] structural(s, st, m),
    ensures
        cnt(s, st, e) == cnt(s, st, j) + 1,
        !instr(s, st, e - 1),
        scalar(s, st, e - 1),
        forall|m: int| j < m < e ==> !#[trigger] structural(s, st, m),
    decreases e - a,
{
    assert(byte(s, a) == s[a]);
    assert(lexeme(s[a]));
    assert(!uq(s, st, a));
    assert(!instr(s, st, a));
    assert(scalar(s, st, a));
    assert(!structural(s, st, a));
    lemma_cnt_step(s, st, a);
    if a + 1 < e {
        assert forall|m: int| j < m < a + 1 implies !#[trigger] structural(s, st, m) by {
            if m < a {
                assert(!structural(s, st, m));
            }
        }
        lemma_run_tail(s, st, j, a + 1, e);
    } else {
        assert forall|m: int| j < m < e implies !#[trigger] structural(s, st, m) by {
            if m < a {
                assert(!structural(s, st, m));
            }
        }
    }
}

proof fn lemma_digits_lexeme(s: Seq<u8>, i: int)
    requires
        0 <= i,
    ensures
        i <= digits_end(s, i),
        forall|m: int| i <= m < digits_end(s, i) ==> is_digit(#[trigger] s[m]),
        digits_end(s, i) <= s.len() || digits_end(s, i) == i,
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_digit(s[i]) {
        lemma_digits_lexeme(s, i + 1);
    }
}

/// Every byte of a number is a lexeme byte.
pub proof fn lemma_number_lexeme(s: Seq<u8>, i: int)
    requires
        0 <= i,
    ensures
        number_end(s, i) matches Some(e) ==> i < e <= s.len() && forall|m: int|
            i <= m < e ==> lexeme(#[trigger] s[m]),
{
    let j = if 0 <= i < s.len() && s[i] == 0x2D { i + 1 } else { i };
    if 0 <= j < s.len() && is_digit(s[j]) {
        lemma_digits_lexeme(s, j);
        let k = if s[j] == 0x30 { j + 1 } else { digits_end(s, j) };
        lemma_digits_lexeme(s, k + 1);
        let frac = if 0 <= k < s.len() && s[k] == 0x2E {
            let d = digits_end(s, k + 1);
            if d == k + 1 { None } else { Some(d) }
        } else {
            Some(k)
        };
        if let Some(k2) = frac {
            lemma_digits_lexeme(s, k2 + 1);
            lemma_digits_lexeme(s, k2 + 2);
        }
        crate::lemmas::lemma_number_end_advances(s, i);
        if let Some(e) = number_end(s, i) {
            assert forall|m: int| i <= m < e implies lexeme(#[trigger] s[m]) by {
                if m >= j && m < k {
                    assert(is_digit(s[m]));
                }
                if let Some(k2) = frac {
                    if m > k && m < k2 {
                        assert(is_digit(s[m]));
                    }
                    if m > k2 + 1 && m < e {
                        let mm = if k2 + 1 < s.len() && (s[k2 + 1] == 0x2B || s[k2 + 1] == 0x2D) {
                            k2 + 2
                        } else {
                            k2 + 1
                        };
                        if m >= mm {
                            assert(is_digit(s[m]));
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Strings
// ---------------------------------------------------------------------------

/// A plain stretch inside a string: no structural position means no
/// closing quote, no escape and (stage 1 checked) no control character.
pub proof fn lemma_plain_inside(s: Seq<u8>, st: int, i: int, q: int)
    requires
        0 <= st <= i <= q <= s.len(),
        instr(s, st, i - 1),
        !esc(s, st, i),
        forall|m: int| i <= m < q ==> !#[trigger] structural(s, st, m),
    ensures
        forall|m: int| i <= m < q ==> plain(#[trigger] s[m]),
        instr(s, st, q - 1),
        !esc(s, st, q),
    decreases q - i,
{
    if i < q {
        assert(byte(s, i) == s[i]);
        assert(!structural(s, st, i));
        assert(!bad(s, st, i));
        assert(plain(s[i]));
        lemma_plain_inside(s, st, i + 1, q);
        assert forall|m: int| i <= m < q implies plain(#[trigger] s[m]) by {
            if m > i {
                assert(plain(s[m]));
            }
        }
    }
}

proof fn lemma_hex_not_special(c: u8)
    requires
        is_hex(c),
    ensures
        c != 0x22,
        c != 0x5C,
{
}

/// A valid escape sequence keeps us inside the string and ends at a byte
/// that is not escaped.
pub proof fn lemma_escape(s: Seq<u8>, st: int, q: int, q2: int)
    requires
        0 <= st <= q < s.len(),
        instr(s, st, q - 1),
        !esc(s, st, q),
        s[q] == 0x5C,
        string_char(s, q) matches Some((_, n)) && n == q2,
    ensures
        q < q2 <= s.len(),
        instr(s, st, q2 - 1),
        !esc(s, st, q2),
        forall|m: int| q <= m < q2 ==> #[trigger] instr(s, st, m),
{
    assert(byte(s, q) == s[q]);
    assert(instr(s, st, q));
    assert(esc(s, st, q + 1));
    assert(byte(s, q + 1) == s[q + 1]);
    if s[q + 1] != 0x75 {
        assert(q2 == q + 2);
        assert(!uq(s, st, q + 1));
        assert(instr(s, st, q + 1));
        assert(!esc(s, st, q + 2));
    } else {
        assert(hex4(s, q + 2) is Some);
        lemma_hex_not_special(s[q + 2]);
        lemma_hex_not_special(s[q + 3]);
        lemma_hex_not_special(s[q + 4]);
        lemma_hex_not_special(s[q + 5]);
        assert(byte(s, q + 2) == s[q + 2]);
        assert(byte(s, q + 3) == s[q + 3]);
        assert(byte(s, q + 4) == s[q + 4]);
        assert(byte(s, q + 5) == s[q + 5]);
        assert(!uq(s, st, q + 1));
        assert(instr(s, st, q + 1));
        assert(!esc(s, st, q + 2));
        assert(instr(s, st, q + 2));
        assert(!esc(s, st, q + 3));
        assert(instr(s, st, q + 3));
        assert(!esc(s, st, q + 4));
        assert(instr(s, st, q + 4));
        assert(!esc(s, st, q + 5));
        assert(instr(s, st, q + 5));
        assert(!esc(s, st, q + 6));
        if q2 == q + 12 {
            assert(hex4(s, q + 8) is Some);
            lemma_hex_not_special(s[q + 8]);
            lemma_hex_not_special(s[q + 9]);
            lemma_hex_not_special(s[q + 10]);
            lemma_hex_not_special(s[q + 11]);
            assert(byte(s, q + 6) == s[q + 6]);
            assert(byte(s, q + 7) == s[q + 7]);
            assert(byte(s, q + 8) == s[q + 8]);
            assert(byte(s, q + 9) == s[q + 9]);
            assert(byte(s, q + 10) == s[q + 10]);
            assert(byte(s, q + 11) == s[q + 11]);
            assert(instr(s, st, q + 6));
            assert(esc(s, st, q + 7));
            assert(instr(s, st, q + 7));
            assert(!esc(s, st, q + 8));
            assert(instr(s, st, q + 8));
            assert(!esc(s, st, q + 9));
            assert(instr(s, st, q + 9));
            assert(!esc(s, st, q + 10));
            assert(instr(s, st, q + 10));
            assert(!esc(s, st, q + 11));
            assert(instr(s, st, q + 11));
            assert(!esc(s, st, q + 12));
        } else {
            assert(q2 == q + 6);
        }
    }
}

/// Inside a string, the closing quote is still ahead.
pub proof fn lemma_close_ahead(s: Seq<u8>, st: int, i: int) -> (m: int)
    requires
        0 <= st <= i <= s.len(),
        instr(s, st, i - 1),
        !instr(s, st, s.len() - 1),
    ensures
        i <= m < s.len(),
        uq(s, st, m),
        structural(s, st, m),
    decreases s.len() - i,
{
    if i == s.len() {
        assert(false);
        i
    } else if uq(s, st, i) {
        i
    } else {
        assert(instr(s, st, i));
        lemma_close_ahead(s, st, i + 1)
    }
}

/// In the string loop the next index entry exists, and it is the first
/// structural position at or after `lo`.
pub proof fn lemma_string_step(s: Seq<u8>, st: int, i: int, lo: int)
    requires
        0 <= st,
        !instr(s, st, s.len() - 1),
        st <= lo <= i <= s.len(),
        instr(s, st, i - 1),
    ensures
        cnt(s, st, lo) < cnt(s, st, s.len() as int),
        ({
            let q = positions(s, st, st, s.len() as int)[cnt(s, st, lo)];
            &&& lo <= q < s.len()
            &&& structural(s, st, q)
            &&& cnt(s, st, q + 1) == cnt(s, st, lo) + 1
            &&& forall|m: int| lo <= m < q ==> !#[trigger] structural(s, st, m)
        }),
{
    let m = lemma_close_ahead(s, st, i);
    lemma_prefix(s, st, lo, m);
    lemma_at(s, st, m);
    lemma_prefix(s, st, m + 1, s.len() as int);
    lemma_next(s, st, lo, lo);
}

/// What a string scan needs: entry `k` of the index is the opening
/// quote of a string, at `j`.
pub open spec fn str_pre(w: &Win, st: int, k: int, j: int) -> bool {
    &&& w.inv()
    &&& w.kbase <= k + 1
    &&& w.s@.len() <= isize::MAX
    &&& w.st == st
    &&& k < ix(w.s@, st).len()
    &&& j == ix(w.s@, st)[k]
    &&& j < w.s@.len()
    &&& w.s@[j] == 0x22
    &&& out(w.s@, st, j)
}

/// What a string scan returns: the index entry after the closing quote,
/// the position after it, and whether the body has escapes.
pub open spec fn str_post(o: &Win, w: &Win, st: int, k: int, j: int, r: Option<(usize, usize, bool)>) -> bool {
    &&& w.inv()
    &&& w.same(o)
    &&& r matches Some((k2, _, _)) ==> k2 > k && w.kbase <= k2 && k2 <= w.kend
    &&& match string(w.s@, j) {
        Some((n, esc)) => r == Some((cnt(w.s@, st, n) as usize, n as usize, esc)) && out(w.s@, st, n)
            && bnd(w.s@, st, n) && n <= w.s@.len(),
        None => r is None,
    }
}

/// The opening quote at `j`, entry `k`: the body starts right after it.
proof fn lemma_open_quote(g: Seq<u8>, st: int, k: int, j: int)
    requires
        0 <= st <= g.len(),
        0 <= k < cnt(g, st, g.len() as int),
        j == ix(g, st)[k],
        j < g.len(),
        g[j] == 0x22,
        out(g, st, j),
    ensures
        st <= j,
        cnt(g, st, j + 1) == k + 1,
        uq(g, st, j),
        instr(g, st, j),
        !esc(g, st, j + 1),
        k + 1 <= g.len(),
{
    lemma_positions_len(g, st, st, g.len() as int);
    lemma_entry(g, st, g.len() as int, k);
    lemma_at(g, st, j);
    assert(byte(g, j) == g[j]);
}

/// With the count at `lo` already that of the whole input, nothing at or
/// after `lo` is structural.
pub proof fn lemma_none_after(s: Seq<u8>, st: int, lo: int)
    requires
        0 <= st <= lo <= s.len(),
        cnt(s, st, lo) >= cnt(s, st, s.len() as int),
    ensures
        forall|m: int| lo <= m < s.len() ==> !#[trigger] structural(s, st, m),
{
    assert forall|m: int| lo <= m < s.len() implies !#[trigger] structural(s, st, m) by {
        if structural(s, st, m) {
            lemma_prefix(s, st, lo, m);
            lemma_at(s, st, m);
            lemma_prefix(s, st, m + 1, s.len() as int);
        }
    }
}

/// The next entry of the string loop, `kk == cnt(lo)`, read through the
/// window: the first structural position at or after `lo`. When there is
/// none, the rest of the input is plain, and the string is not closed.
proof fn lemma_string_next(w: &Win, st: int, i: int, lo: int, kk: int, e: bool, r: Option<usize>)
    requires
        w.inv(),
        w.st == st,
        st <= lo <= i <= w.s@.len(),
        instr(w.s@, st, i - 1),
        !esc(w.s@, st, i),
        kk == cnt(w.s@, st, lo),
        r matches Some(q) ==> kk < w.all().len() && q == w.all()[kk],
        r is None ==> kk >= w.all().len(),
    ensures
        r is None ==> string_body(w.s@, i, e) is None,
        r matches Some(q) ==> {
            &&& lo <= q < w.s@.len()
            &&& structural(w.s@, st, q as int)
            &&& cnt(w.s@, st, q + 1) == kk + 1
            &&& forall|m: int| lo <= m < q ==> !#[trigger] structural(w.s@, st, m)
        },
{
    let g = w.s@;
    if let Some(q) = r {
        lemma_next(g, st, lo, lo);
    } else {
        lemma_none_after(g, st, lo);
        lemma_plain_inside(g, st, i, g.len() as int);
        lemma_plain_run(g, i, g.len() as int, e);
    }
}

/// A structural byte inside a string that is neither its closing quote
/// nor an escape is a control character, which ends the string as
/// invalid.
proof fn lemma_string_bad(g: Seq<u8>, st: int, q: int, esc: bool)
    requires
        0 <= st <= q < g.len(),
        instr(g, st, q - 1),
        structural(g, st, q),
        g[q] != 0x22,
        g[q] != 0x5C,
    ensures
        string_body(g, q, esc) is None,
{
    assert(byte(g, q) == g[q]);
    assert(!uq(g, st, q));
    assert(instr(g, st, q));
    assert(!sbase(g, st, q));
    assert(bad(g, st, q));
}

/// Scans the string whose opening quote, at `j`, is index entry `k`.
/// Returns the index entry after its closing quote, the position after
/// it, and whether it has escapes.
#[inline(always)]
pub fn ex2_string(cx: &mut Ctx, k: usize, j: usize, Ghost(st): Ghost<int>) -> (r: Option<
    (usize, usize, bool),
>)
    requires
        str_pre(old(cx), st, k as int, j as int),
    ensures
        str_post(old(cx), final(cx), st, k as int, j as int, r),
{
    let s = cx.s;
    let ghost g = s@;
    proof {
        lemma_open_quote(g, st, k as int, j as int);
    }
    let mut kk = k + 1;
    let mut i = j + 1;
    let mut escf = false;
    let ghost mut lo: int = j + 1;
    loop
        invariant
            g == s@,
            cx.inv(),
            cx.s@ == g,
            g.len() <= isize::MAX,
            cx.st == st,
            cx.same(old(cx)),
            cx.kbase <= kk,
            st <= j < i <= g.len(),
            j + 1 <= lo <= i,
            kk as int == cnt(g, st, lo),
            kk > k,
            instr(g, st, i - 1),
            !esc(g, st, i as int),
            string(g, j as int) == string_body(g, i as int, escf),
        decreases ix(g, st).len() - kk,
    {
        let r = cx.at_fwd(kk);
        proof {
            lemma_string_next(cx, st, i as int, lo, kk as int, escf, r);
        }
        let q = match r {
            Some(q) => q,
            None => return None,
        };
        if q < i {
            kk = kk + 1;
            proof {
                lo = q + 1;
            }
            continue;
        }
        proof {
            lemma_plain_inside(g, st, i as int, q as int);
            lemma_plain_run(g, i as int, q as int, escf);
            assert(byte(g, q as int) == g[q as int]);
        }
        let c = get8(s, q);
        if c == 0x22 {
            proof {
                assert(uq(g, st, q as int));
                assert(!instr(g, st, q as int));
                assert(!scalar(g, st, q as int));
            }
            return Some((kk + 1, q + 1, escf));
        }
        if c != 0x5C {
            proof {
                lemma_string_bad(g, st, q as int, escf);
            }
            return None;
        }
        match ex_escape_end(s, q) {
            None => return None,
            Some(q2) => {
                proof {
                    lemma_escape(g, st, q as int, q2 as int);
                    lo = q + 1;
                }
                escf = true;
                i = q2;
                kk = kk + 1;
            },
        }
    }
}

/// One step of `decode` over a string body that `string_body` accepts: the
/// char at `q` (not the closing quote) decodes to its bytes, followed by the
/// rest.
proof fn lemma_decode_body_step(s: Seq<u8>, q: int, esc: bool, n: int)
    requires
        0 <= q < s.len(),
        s[q] != 0x22,
        string_body(s, q, esc) matches Some((e, _)) && e == n,
    ensures
        string_char(s, q) matches Some((b, q2)) && q < q2 < n && decode(s, q, n - 1) == b + decode(
            s,
            q2,
            n - 1,
        ) && string_body(s, q2, esc || s[q] == 0x5C) == string_body(s, q, esc),
{
    let (b, q2) = string_char(s, q).unwrap();
    crate::lemmas::lemma_string_body_advances(s, q2, esc || s[q] == 0x5C);
}

/// What `ex2_string_dec` has decoded so far: `cur` is `o` followed by the
/// decoding of the body up to `i`, if the string at `j` is valid.
pub open spec fn dec_inv(g: Seq<u8>, j: int, i: int, o: Seq<u8>, cur: Seq<u8>) -> bool {
    match string(g, j) {
        Some((n, _)) => i < n && o + decode(g, j + 1, n - 1) == cur + decode(g, i, n - 1),
        None => true,
    }
}

/// Decodes the run of `\uXXXX` escapes outside the surrogates at `q` (as in
/// non-Latin text) for `ex2_string_dec`, and returns its end.
#[verifier::spinoff_prover]
#[inline(always)]
fn body_u_run(s: &[u8], Ghost(j): Ghost<int>, q: usize, dst: &mut Vec<u8>, Ghost(o): Ghost<Seq<u8>>, Ghost(st): Ghost<
    int,
>) -> (r: usize)
    requires
        0 <= st <= q <= s@.len(),
        j < q,
        instr(s@, st, q - 1),
        !esc(s@, st, q as int),
        string(s@, j as int) == string_body(s@, q as int, true),
        spare(*old(dst)) >= (s@.len() - q) + 16,
        dec_inv(s@, j as int, q as int, o, old(dst)@),
    ensures
        q <= r <= s@.len(),
        instr(s@, st, r - 1),
        !esc(s@, st, r as int),
        string(s@, j as int) == string_body(s@, r as int, true),
        spare(*final(dst)) >= (s@.len() - r) + 16,
        dec_inv(s@, j as int, r as int, o, final(dst)@),
{
    let ghost g = s@;
    let mut i = q;
    while s.len() - i >= 6 && get8(s, i) == 0x5C && get8(s, i + 1) == 0x75
        invariant
            g == s@,
            0 <= st <= q <= i <= g.len(),
            j < q,
            instr(g, st, i - 1),
            !esc(g, st, i as int),
            string(g, j as int) == string_body(g, i as int, true),
            spare(*dst) >= (g.len() - i) + 16,
            dec_inv(g, j as int, i as int, o, dst@),
        decreases g.len() - i,
    {
        let (ok, u) = ex_hex4_raw(s, i + 2);
        if !(ok && get8(s, i + 2) | 0x20 != 0x64) {
            return i;
        }
        proof {
            lemma_not_surrogate(g, i + 2);
            assert(string_char(g, i as int) == Some((utf8_encode(u), i as int + 6)));
            lemma_escape(g, st, i as int, i + 6);
            if let Some((n, _)) = string(g, j as int) {
                lemma_decode_body_step(g, i as int, true, n);
            } else {
                assert(string_body(g, i + 6, true) == string_body(g, i as int, true));
            }
        }
        let ghost d0 = dst@;
        ex_push_bmp_spare(dst, u);
        proof {
            assert(utf8_encode(u).len() <= 3);
            if let Some((n, _)) = string(g, j as int) {
                assert(dst@ + decode(g, i + 6, n - 1) =~= d0 + decode(g, i as int, n - 1));
            }
        }
        i = i + 6;
    }
    i
}

/// `ex2_string_dec` at the escape at `q`: copies the plain run `s[i..q]`
/// before it, then decodes the escape (and any `\u` run after it).
#[verifier::spinoff_prover]
#[inline(always)]
fn dec_escape_at(s: &[u8], j: usize, i: usize, q: usize, escf: bool, dst: &mut Vec<u8>, Ghost(o): Ghost<
    Seq<u8>,
>, Ghost(st): Ghost<int>) -> (r: Option<usize>)
    requires
        0 <= st <= q,
        j < i <= q < s@.len(),
        s@[q as int] == 0x5C,
        instr(s@, st, q - 1),
        !esc(s@, st, q as int),
        forall|m: int| i <= m < q ==> plain(#[trigger] s@[m]),
        string(s@, j as int) == string_body(s@, q as int, escf),
        string(s@, j as int) == string_body(s@, i as int, escf),
        !escf ==> i == j + 1 && old(dst)@ == o,
        escf ==> spare(*old(dst)) >= (s@.len() - i) + 16 && dec_inv(s@, j as int, i as int, o, old(dst)@),
    ensures
        r is None ==> string(s@, j as int) is None,
        r matches Some(q2) ==> q < q2 <= s@.len() && instr(s@, st, q2 - 1) && !esc(s@, st, q2 as int)
            && spare(*final(dst)) >= (s@.len() - q2) + 16 && dec_inv(s@, j as int, q2 as int, o, final(dst)@)
            && string(s@, j as int) == string_body(s@, q2 as int, true),
{
    let ghost g = s@;
    if !escf {
        // The first escape: the decoded body is never longer than the
        // input left.
        reserve_spare_plus(dst, s.len() - j, 16);
    }
    let ghost d0 = dst@;
    append_slice_spare(dst, s, i, q);
    proof {
        if let Some((n, _)) = string(g, j as int) {
            crate::lemmas::lemma_string_body_advances(g, q as int, escf);
            lemma_decode_plain_run(g, i as int, q as int, n - 1);
            assert(dst@ + decode(g, q as int, n - 1) =~= d0 + decode(g, i as int, n - 1));
        }
    }
    let ghost d1 = dst@;
    match ex_escape_spare(s, q, dst) {
        None => {
            proof {
                assert(string_body(g, q as int, escf) is None);
            }
            None
        },
        Some(q2) => {
            proof {
                lemma_escape(g, st, q as int, q2 as int);
                if let Some((n, _)) = string(g, j as int) {
                    lemma_decode_body_step(g, q as int, escf, n);
                    assert(dst@ + decode(g, q2 as int, n - 1) =~= d1 + decode(g, q as int, n - 1));
                } else {
                    assert(string_body(g, q2 as int, true) == string_body(g, q as int, escf));
                }
            }
            Some(body_u_run(s, Ghost(j as int), q2, dst, Ghost(o), Ghost(st)))
        },
    }
}

/// `ex2_string_dec` once the body is known to have an escape.
#[verifier::spinoff_prover]
#[inline(always)]
fn ex2_string_esc(cx: &mut Ctx, k: usize, j: usize, Ghost(st): Ghost<int>, dst: &mut Vec<u8>) -> (r:
    Option<(usize, usize, bool)>)
    requires
        str_pre(old(cx), st, k as int, j as int),
    ensures
        str_post(old(cx), final(cx), st, k as int, j as int, r),
        r matches Some((_, n, esc)) ==> if esc {
            final(dst)@ == old(dst)@ + decode(old(cx).s@, j + 1, n - 1)
        } else {
            final(dst)@ == old(dst)@
        },
{
    let s = cx.s;
    let ghost g = s@;
    let ghost o = dst@;
    proof {
        lemma_open_quote(g, st, k as int, j as int);
    }
    let mut kk = k + 1;
    let mut i = j + 1;
    let mut escf = false;
    let ghost mut lo: int = j + 1;
    loop
        invariant
            g == s@,
            o == old(dst)@,
            cx.inv(),
            cx.s@ == g,
            g.len() <= isize::MAX,
            cx.st == st,
            cx.same(old(cx)),
            cx.kbase <= kk,
            st <= j < i <= g.len(),
            j + 1 <= lo <= i,
            kk as int == cnt(g, st, lo),
            kk > k,
            instr(g, st, i - 1),
            !esc(g, st, i as int),
            string(g, j as int) == string_body(g, i as int, escf),
            !escf ==> i == j + 1 && dst@ == o,
            escf ==> spare(*dst) >= (g.len() - i) + 16 && dec_inv(g, j as int, i as int, o, dst@),
        decreases ix(g, st).len() - kk,
    {
        let r = cx.at_fwd(kk);
        proof {
            lemma_string_next(cx, st, i as int, lo, kk as int, escf, r);
        }
        let q = match r {
            Some(q) => q,
            None => return None,
        };
        if q < i {
            kk = kk + 1;
            proof {
                lo = q + 1;
            }
            continue;
        }
        proof {
            lemma_plain_inside(g, st, i as int, q as int);
            lemma_plain_run(g, i as int, q as int, escf);
            assert(byte(g, q as int) == g[q as int]);
        }
        let c = get8(s, q);
        if c == 0x22 {
            proof {
                assert(uq(g, st, q as int));
                assert(!instr(g, st, q as int));
                assert(!scalar(g, st, q as int));
            }
            if escf {
                let ghost d0 = dst@;
                append_slice_spare(dst, s, i, q);
                proof {
                    lemma_decode_plain_run(g, i as int, q as int, q as int);
                    assert(decode(g, q as int, q as int) == Seq::<u8>::empty());
                    assert(dst@ =~= d0 + decode(g, i as int, q as int));
                    assert(dst@ =~= o + decode(g, j + 1, q as int));
                }
            }
            return Some((kk + 1, q + 1, escf));
        }
        if c != 0x5C {
            proof {
                lemma_string_bad(g, st, q as int, escf);
            }
            return None;
        }
        match dec_escape_at(s, j, i, q, escf, dst, Ghost(o), Ghost(st)) {
            None => return None,
            Some(q2) => {
                proof {
                    lo = q + 1;
                }
                escf = true;
                i = q2;
                kk = kk + 1;
            },
        }
    }
}

/// `ex2_string` that also decodes an escaped body into `dst`, in the same
/// pass that validates it (eager mode). A body without escapes is left for
/// the caller to slice; `dst` is untouched then.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ex2_string_dec(cx: &mut Ctx, k: usize, j: usize, Ghost(st): Ghost<int>, dst: &mut Vec<u8>) -> (r:
    Option<(usize, usize, bool)>)
    requires
        str_pre(old(cx), st, k as int, j as int),
    ensures
        str_post(old(cx), final(cx), st, k as int, j as int, r),
        r matches Some((_, n, esc)) ==> if esc {
            final(dst)@ == old(dst)@ + decode(old(cx).s@, j + 1, n - 1)
        } else {
            final(dst)@ == old(dst)@
        },
{
    let s = cx.s;
    let ghost g = s@;
    proof {
        lemma_open_quote(g, st, k as int, j as int);
    }
    let _m = s.len();
    // The body's first entry: the closing quote unless there is an escape.
    let r = cx.at_fwd(k + 1);
    proof {
        lemma_string_next(cx, st, j + 1, j + 1, k + 1, false, r);
    }
    let q = match r {
        Some(q) => q,
        None => return None,
    };
    proof {
        lemma_plain_inside(g, st, j + 1, q as int);
        lemma_plain_run(g, j + 1, q as int, false);
        assert(byte(g, q as int) == g[q as int]);
    }
    let c = get8(s, q);
    if c == 0x22 {
        proof {
            assert(uq(g, st, q as int));
            assert(!instr(g, st, q as int));
            assert(!scalar(g, st, q as int));
        }
        return Some((k + 2, q + 1, false));
    }
    if c != 0x5C {
        proof {
            lemma_string_bad(g, st, q as int, false);
        }
        return None;
    }
    let (k2, ne) = ex2_string_esc_out(cx, k, j, Ghost(st), dst);
    if k2 == 0 {
        None
    } else {
        proof {
            if let Some((n, esc)) = string(g, j as int) {
                let e: int = if esc { 1 } else { 0 };
                assert(ne == 2 * n + e);
                assert(ne / 2 == n) by (nonlinear_arith) requires ne == 2 * n + e, 0 <= e <= 1;
                assert((ne % 2 == 1) == esc) by (nonlinear_arith) requires ne == 2 * n + e, 0 <= e <= 1, e == 1 <==> esc;
            }
        }
        Some((k2, (ne / 2) as usize, ne % 2 == 1))
    }
}

/// `ex2_string_esc` out of line, as most strings have none. The result is
/// packed in two words, so that it comes back in registers rather than
/// through memory: `(0, 0)` for `None`, else `(k2, 2 * n + esc)`.
#[inline(never)]
fn ex2_string_esc_out(cx: &mut Ctx, k: usize, j: usize, Ghost(st): Ghost<int>, dst: &mut Vec<u8>) -> (r:
    (usize, u64))
    requires
        str_pre(old(cx), st, k as int, j as int),
    ensures
        final(cx).inv(),
        final(cx).same(old(cx)),
        r.0 != 0 ==> r.0 > k && final(cx).kbase <= r.0 && r.0 <= final(cx).kend,
        match string(old(cx).s@, j as int) {
            Some((n, esc)) => r.0 == cnt(old(cx).s@, st, n) && r.1 == 2 * n + (if esc { 1int } else { 0 })
                && out(old(cx).s@, st, n) && bnd(old(cx).s@, st, n) && n <= old(cx).s@.len() && r.0 > k && if esc {
                final(dst)@ == old(dst)@ + decode(old(cx).s@, j + 1, n - 1)
            } else {
                final(dst)@ == old(dst)@
            },
            None => r.0 == 0,
        },
{
    proof {
        lemma_open_quote(cx.s@, st, k as int, j as int);
        crate::lemmas::lemma_string_body_advances(cx.s@, j + 1, false);
        if let Some((n, _)) = string(cx.s@, j as int) {
            lemma_cnt_bound(cx.s@, st, n);
        }
    }
    match ex2_string_esc(cx, k, j, Ghost(st), dst) {
        Some((k2, n, esc)) => (k2, 2 * (n as u64) + if esc { 1 } else { 0 }),
        None => (0, 0),
    }
}

// ---------------------------------------------------------------------------
// Values
// ---------------------------------------------------------------------------

/// A scalar that runs into a non-delimiter makes whatever follows fail.
pub proof fn lemma_not_bnd(s: Seq<u8>, st: int, e: int)
    requires
        0 <= st <= e,
        !bnd(s, st, e),
    ensures
        e < s.len(),
        skip_ws(s, e) == e,
        s[e] != 0x5D && s[e] != 0x7D && s[e] != 0x2C,
{
    assert(byte(s, e) == s[e]);
}

/// After a token, the next index entry is the byte `skip_ws` lands on, and
/// a closing bracket or separator there ends a token cleanly.
pub proof fn lemma_close(s: Seq<u8>, st: int, p: int)
    requires
        0 <= st,
        st <= p <= s.len(),
        out(s, st, p),
        bnd(s, st, p),
    ensures
        ({
            let j = skip_ws(s, p);
            &&& p <= j <= s.len()
            &&& cnt(s, st, j) == cnt(s, st, p)
            &&& cnt(s, st, p) <= cnt(s, st, s.len() as int)
            &&& j < s.len() <==> cnt(s, st, p) < cnt(s, st, s.len() as int)
            &&& j < s.len() ==> positions(s, st, st, s.len() as int)[cnt(s, st, p)] == j
                && cnt(s, st, j + 1) == cnt(s, st, p) + 1
            &&& j < s.len() && is_op(s[j]) ==> out(s, st, j + 1) && bnd(s, st, j + 1)
        }),
{
    lemma_skip(s, st, p);
    crate::lemmas::lemma_skip_ws_bounds(s, p);
    let j = skip_ws(s, p);
    lemma_prefix(s, st, j, s.len() as int);
    if j < s.len() {
        lemma_at(s, st, j);
        assert(byte(s, j) == s[j]);
        if is_op(s[j]) {
            assert(!uq(s, st, j));
            assert(!instr(s, st, j));
            assert(!scalar(s, st, j));
        }
    }
}

/// 1 for the bytes that may follow a scalar (whitespace, an operator or a
/// quote), else 0.
pub const DELIM: [u8; 256] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

pub open spec fn delim_tab_ok_below(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        (DELIM@[n - 1] == 1) == delim((n - 1) as u8) && (DELIM@[n - 1] == 0 || DELIM@[n - 1] == 1)
            && delim_tab_ok_below((n - 1) as nat)
    }
}

proof fn lemma_delim_tab_below(n: nat, c: u8)
    requires
        delim_tab_ok_below(n),
        (c as nat) < n,
    ensures
        (DELIM@[c as int] == 1) == delim(c),
    decreases n,
{
    if c as nat != n - 1 {
        lemma_delim_tab_below((n - 1) as nat, c);
    }
}

/// Whether `c` may follow a scalar, by table lookup (checked for all 256
/// entries by evaluation).
#[inline(always)]
pub fn ex_delim(c: u8) -> (r: bool)
    ensures
        r == delim(c),
{
    proof {
        assert(delim_tab_ok_below(256)) by (compute_only);
        lemma_delim_tab_below(256, c);
    }
    DELIM[c as usize] == 1
}

/// The spec value at `skip_ws(p)`, read through the index. `k` is the
/// index entry for `p`. A value that `bnd` says runs into garbage is
/// rejected here rather than by the caller. Scalars are handled inline;
/// only containers recurse, through `ex2_container`.
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
#[inline(always)]
pub fn ex2_value<S: Sink, const N: u8>(
    cx: &mut Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(p): Ghost<int>,
    jh: usize,
    s: &[u8],
) -> (r: Option<(usize, usize)>)
    requires
        s@ == old(cx).s@,
        win_at(old(cx), old(cx).s@, st, k as int),
        st <= p <= old(cx).s@.len(),
        out(old(cx).s@, st, p),
        bnd(old(cx).s@, st, p),
        k == cnt(old(cx).s@, st, p),
        old(tape).room() >= old(cx).kend - k,
        old(tape).inv(old(cx).s@),
        old(tape).hist().len() <= p,
        N == 0 ==> k < old(cx).kend && k < ix(old(cx).s@, st).len() && (old(cx).s@[ix(old(cx).s@, st)[k as int]] == 0x2D
            || is_digit(old(cx).s@[ix(old(cx).s@, st)[k as int]])) && jh == ix(old(cx).s@, st)[k as int],
        N != 1 ==> k < old(cx).kend && k < ix(old(cx).s@, st).len() && jh == ix(old(cx).s@, st)[k as int],
    ensures
        final(cx).inv(),
        final(cx).same(old(cx)),
        r is Some ==> final(tape).inv(old(cx).s@),
        r matches Some((k2, _)) ==> final(tape).room() >= final(cx).kend - k2 && final(cx).kbase <= k2
            && k2 <= final(cx).all().len(),
        match value(old(cx).s@, skip_ws(old(cx).s@, p), depth as nat, old(tape).hist()) {
            Some((t, e)) => if bnd(old(cx).s@, st, e) {
                r == Some((cnt(old(cx).s@, st, e) as usize, e as usize)) && final(tape).hist() == t && out(
                    old(cx).s@,
                    st,
                    e,
                ) && e <= old(cx).s@.len()
            } else {
                r is None
            },
            None => r is None,
        },
    decreases depth, old(cx).s@.len() - p, 4nat,
{
    let ghost g = s@;
    proof {
        lemma_skip(g, st, p);
        lemma_prefix(g, st, skip_ws(g, p), g.len() as int);
        if skip_ws(g, p) < g.len() {
            lemma_at(g, st, skip_ws(g, p));
        }
    }
    // In an array of numbers the caller has read the entry already.
    let j = if N != 1 {
        jh
    } else {
        match at2(cx, k, tape, Ghost(k as int)) {
            Some(j) => j,
            None => return None,
        }
    };
    proof {
        let jj = skip_ws(g, p);
        lemma_positions_len(g, st, st, g.len() as int);
        if N != 1 {
            assert(cnt(g, st, jj) == k);
            if jj < g.len() {
                assert(ix(g, st)[k as int] == jj);
            } else {
                assert(cnt(g, st, g.len() as int) == ix(g, st).len());
            }
        }
        assert(j == jj);
        crate::lemmas::lemma_value_advances(g, jj, depth as nat, old(tape).hist());
        crate::lemmas::lemma_string_body_advances(g, j + 1, false);
    }
    let c = get8(s, j);
    if N != 0 && c == 0x22 {
        ex2_str_tok(cx, k, j, tape, Ghost(st), s, Kind::Str)
    } else if N != 0 && (c == 0x5B || c == 0x7B) {
        proof {
            assert(byte(g, j as int) == g[j as int]);
            assert(!instr(g, st, j as int));
            assert(!scalar(g, st, j as int));
        }
        // Arrays are parsed in line, so that an array of scalars (such as
        // a coordinate pair) costs no call.
        if c == 0x5B && depth > 0 {
            proof {
                lemma_close(g, st, j + 1);
                lemma_prefix(g, st, j + 1, g.len() as int);
            }
            // One read of the entry after the bracket serves both the
            // empty array, which is common (most of citm_catalog's), and
            // the first element.
            if let Some(q) = at2(cx, k + 1, tape, Ghost(k as int)) {
                if get8(s, q) == 0x5D {
                    proof {
                        assert(byte(g, q as int) == g[q as int]);
                    }
                    let t = tape.count();
                    tape.push_fast(Tok::new(Kind::ArrStart, false, t + 1, 0, NO));
                    tape.push_fast(tok(Kind::ArrEnd));
                    assert(tape.hist() =~= close_at(old(tape).hist().push(STok::ArrStart { end: 0 }).push(STok::ArrEnd), t as int));
                    proof {
                        lemma_prefix(g, st, q + 1, g.len() as int);
                    }
                    return Some((k + 2, q + 1));
                }
                let t_idx = tape.count();
                tape.push_fast(tok(Kind::ArrStart));
                return match ex2_array_inl(cx, k + 1, depth, tape, Ghost(st), Ghost(j + 1), q, s) {
                    Some((k2, e)) => {
                        proof {
                            lemma_container_prefix(g, j as int, depth as nat, old(tape).hist(), c);
                            if let Some((_, e)) = value(g, j as int, depth as nat, old(tape).hist()) {
                                lemma_cnt_bound(g, st, e);
                            }
                        }
                        tape.close(t_idx);
                        Some((k2, e))
                    },
                    None => None,
                };
            }
        }
        unpack2(ex2_container(cx, k + 1, depth, tape, Ghost(st), j))
    } else {
        let e = if N != 0 && c == 0x74 {
            if !ex_has4(s, j, 0x74, 0x72, 0x75, 0x65) {
                return None;
            }
            proof {
                assert(g.subrange(j as int, j + 4) =~= seq![0x74u8, 0x72, 0x75, 0x65]);
                assert forall|m: int| j <= m < j + 4 implies lexeme(#[trigger] g[m]) by {
                    assert(g[m] == g.subrange(j as int, j + 4)[m - j]);
                }
            }
            tape.push_fast(tok(Kind::True));
            j + 4
        } else if N != 0 && c == 0x66 {
            if !ex_has4(s, j + 1, 0x61, 0x6C, 0x73, 0x65) {
                return None;
            }
            proof {
                assert(g.subrange(j as int, j + 5) =~= seq![0x66u8, 0x61, 0x6C, 0x73, 0x65]);
                assert forall|m: int| j <= m < j + 5 implies lexeme(#[trigger] g[m]) by {
                    assert(g[m] == g.subrange(j as int, j + 5)[m - j]);
                }
            }
            tape.push_fast(tok(Kind::False));
            j + 5
        } else if N != 0 && c == 0x6E {
            if !ex_has4(s, j, 0x6E, 0x75, 0x6C, 0x6C) {
                return None;
            }
            proof {
                assert(g.subrange(j as int, j + 4) =~= seq![0x6Eu8, 0x75, 0x6C, 0x6C]);
                assert forall|m: int| j <= m < j + 4 implies lexeme(#[trigger] g[m]) by {
                    assert(g[m] == g.subrange(j as int, j + 4)[m - j]);
                }
            }
            tape.push_fast(tok(Kind::Null));
            j + 4
        } else {
            proof {
                lemma_number_lexeme(g, j as int);
            }
            if tape.eager() {
                match (if N != 0 || verilith_simd::neon::has_neon() { ex_number_scan_k(s, j) } else { ex_number_scan(s, j) }) {
                    Some((e, v, ok)) => {
                        tape.push_num_fast(Tok::new(Kind::Num, false, j, e, NO), s, v, ok);
                        e
                    },
                    None => return None,
                }
            } else {
                match ex_number_end(s, j) {
                    Some(e) => {
                        tape.push_fast(Tok::new(Kind::Num, false, j, e, NO));
                        e
                    },
                    None => return None,
                }
            }
        };
        proof {
            lemma_scalar_run(g, st, j as int, e as int);
        }
        if e < s.len() && !ex_delim(get8(s, e)) {
            proof {
                assert(byte(g, e as int) == g[e as int]);
            }
            return None;
        }
        proof {
            assert(k < cx.all().len());
        }
        Some((k + 1, e))
    }
}

/// `[` at `j` followed by `]`: pushes both tokens and returns the position
/// after the `]`. Otherwise leaves the tape's tokens alone.
// `depth` and `j` appear only in the specification.

/// What the container functions keep, from `o` to `w`, for a result
/// `r` of the index entry and position after what they read.
pub open spec fn moved<S: Sink>(o: &Win, w: &Win, tape: &S, r: Option<(usize, usize)>) -> bool {
    &&& w.inv()
    &&& w.same(o)
    &&& r is Some ==> tape.inv(o.s@)
    &&& r matches Some((k2, _)) ==> tape.room() >= w.kend - k2 && w.kbase <= k2 && k2 <= w.all().len()
}

/// A result packed in two words, so that it comes back in registers:
/// `usize::MAX` in the first for `None`.
pub open spec fn unpack(r: (usize, usize)) -> Option<(usize, usize)> {
    if r.0 == usize::MAX {
        None
    } else {
        Some(r)
    }
}

#[inline(always)]
pub fn unpack2(r: (usize, usize)) -> (o: Option<(usize, usize)>)
    ensures
        o == unpack(r),
{
    if r.0 == usize::MAX {
        None
    } else {
        Some(r)
    }
}

/// `ex2_container_in` out of line, its result packed (see `unpack`).
#[inline(never)]
fn ex2_container<S: Sink>(
    cx: &mut Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    j: usize,
) -> (r: (usize, usize))
    requires
        win_at(old(cx), old(cx).s@, st, k as int),
        st <= j < old(cx).s@.len(),
        cnt(old(cx).s@, st, j as int + 1) == k,
        k >= 1,
        k - 1 < old(cx).kend,
        old(cx).s@[j as int] == 0x5B || old(cx).s@[j as int] == 0x7B,
        out(old(cx).s@, st, j as int + 1),
        bnd(old(cx).s@, st, j as int + 1),
        old(tape).room() >= old(cx).kend - (k - 1),
        old(tape).inv(old(cx).s@),
        old(tape).hist().len() <= j,
    ensures
        moved(old(cx), final(cx), final(tape), unpack(r)),
        match value(old(cx).s@, j as int, depth as nat, old(tape).hist()) {
            Some((t, e)) => unpack(r) == Some((cnt(old(cx).s@, st, e) as usize, e as usize)) && final(tape).hist() == t
                && out(old(cx).s@, st, e) && bnd(old(cx).s@, st, e) && e <= old(cx).s@.len(),
            None => unpack(r) is None,
        },
    decreases depth, old(cx).s@.len() - j, 3nat,
{
    let s = cx.s;
    match ex2_container_in(cx, k, depth, tape, Ghost(st), j, s) {
        Some(x) => {
            proof {
                lemma_positions_len(cx.s@, st, st, cx.s@.len() as int);
            }
            x
        },
        None => (usize::MAX, 0),
    }
}

/// `ex2_elements_in` out of line, its result packed (see `unpack`).
#[inline(never)]
fn ex2_elements<S: Sink>(
    cx: &mut Ctx,
    k0: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i0): Ghost<int>,
) -> (r: (usize, usize))
    requires
        cont_pre(old(cx), old(tape), st, k0 as int, i0),
    ensures
        moved(old(cx), final(cx), final(tape), unpack(r)),
        cont_post(old(cx).s@, st, elements(old(cx).s@, i0, depth as nat, old(tape).hist()), final(tape).hist(), unpack(r)),
    decreases depth, old(cx).s@.len() - i0, 1nat,
{
    let s = cx.s;
    match ex2_elements_in(cx, k0, depth, tape, Ghost(st), Ghost(i0), s) {
        Some(x) => {
            proof {
                lemma_positions_len(cx.s@, st, st, cx.s@.len() as int);
            }
            x
        },
        None => (usize::MAX, 0),
    }
}

/// An array or object at `j`, which is index entry `k - 1`.
#[inline(always)]
fn ex2_container_in<S: Sink>(
    cx: &mut Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    j: usize,
    s: &[u8],
) -> (r: Option<(usize, usize)>)
    requires
        s@ == old(cx).s@,
        win_at(old(cx), old(cx).s@, st, k as int),
        st <= j < old(cx).s@.len(),
        cnt(old(cx).s@, st, j as int + 1) == k,
        k >= 1,
        k - 1 < old(cx).kend,
        old(cx).s@[j as int] == 0x5B || old(cx).s@[j as int] == 0x7B,
        out(old(cx).s@, st, j as int + 1),
        bnd(old(cx).s@, st, j as int + 1),
        old(tape).room() >= old(cx).kend - (k - 1),
        old(tape).inv(old(cx).s@),
        old(tape).hist().len() <= j,
    ensures
        moved(old(cx), final(cx), final(tape), r),
        match value(old(cx).s@, j as int, depth as nat, old(tape).hist()) {
            Some((t, e)) => r == Some((cnt(old(cx).s@, st, e) as usize, e as usize)) && final(tape).hist() == t
                && out(old(cx).s@, st, e) && bnd(old(cx).s@, st, e) && e <= old(cx).s@.len(),
            None => r is None,
        },
    decreases depth, old(cx).s@.len() - j, 2nat,
{
    let ghost g = s@;
    if depth == 0 {
        return None;
    }
    let c = get8(s, j);
    let t_idx = tape.count();
    let r = if c == 0x5B {
        tape.push_fast(tok(Kind::ArrStart));
        ex2_array(cx, k, depth, tape, Ghost(st), Ghost(j + 1), s)
    } else {
        tape.push_fast(tok(Kind::ObjStart));
        ex2_object(cx, k, depth, tape, Ghost(st), Ghost(j + 1), s)
    };
    match r {
        Some((k2, e)) => {
            proof {
                lemma_container_prefix(g, j as int, depth as nat, old(tape).hist(), c);
                crate::lemmas::lemma_value_advances(g, j as int, depth as nat, old(tape).hist());
                if let Some((_, e)) = value(g, j as int, depth as nat, old(tape).hist()) {
                    lemma_cnt_bound(g, st, e);
                }
            }
            tape.close(t_idx);
            Some((k2, e))
        },
        None => None,
    }
}

/// The spec of the array and object functions, which start after the
/// opening bracket, at `i`, index entry `k`.
pub open spec fn cont_pre<S: Sink>(w: &Win, tape: &S, st: int, k: int, i: int) -> bool {
    &&& win_at(w, w.s@, st, k)
    &&& st < i <= w.s@.len()
    &&& out(w.s@, st, i)
    &&& bnd(w.s@, st, i)
    &&& k == cnt(w.s@, st, i)
    &&& tape.room() >= w.kend - k
    &&& tape.inv(w.s@)
    &&& tape.hist().len() <= i
}

pub open spec fn cont_post(g: Seq<u8>, st: int, spec: Option<(Seq<STok>, int)>, hist: Seq<STok>, r: Option<(usize, usize)>) -> bool {
    match spec {
        Some((t, e)) => r == Some((cnt(g, st, e) as usize, e as usize)) && hist == t && out(g, st, e) && bnd(g, st, e)
            && e <= g.len(),
        None => r is None,
    }
}

fn ex2_array<S: Sink>(
    cx: &mut Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i): Ghost<int>,
    s: &[u8],
) -> (r: Option<(usize, usize)>)
    requires
        s@ == old(cx).s@,
        cont_pre(old(cx), old(tape), st, k as int, i),
    ensures
        moved(old(cx), final(cx), final(tape), r),
        cont_post(old(cx).s@, st, array(old(cx).s@, i, depth as nat, old(tape).hist()), final(tape).hist(), r),
    decreases depth, old(cx).s@.len() - i, 2nat,
{
    let ghost g = s@;
    proof {
        lemma_close(g, st, i);
    }
    if let Some(q) = at2(cx, k, tape, Ghost(k as int)) {
        if get8(s, q) == 0x5D {
            tape.push_fast(tok(Kind::ArrEnd));
            return Some((k + 1, q + 1));
        }
    }
    unpack2(ex2_elements(cx, k, depth, tape, Ghost(st), Ghost(i)))
}

/// `ex2_array` in line: elements that are numbers are parsed here; at the
/// first element that is not, `ex2_elements` takes over.
#[allow(unused_variables)]
#[inline(always)]
fn ex2_array_inl<S: Sink>(
    cx: &mut Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i0): Ghost<int>,
    j0: usize,
    s: &[u8],
) -> (r: Option<(usize, usize)>)
    requires
        cont_pre(old(cx), old(tape), st, k as int, i0),
        s@ == old(cx).s@,
        k < old(cx).kend,
        k < ix(old(cx).s@, st).len(),
        j0 == ix(old(cx).s@, st)[k as int],
        old(cx).s@[j0 as int] != 0x5D,
    ensures
        moved(old(cx), final(cx), final(tape), r),
        cont_post(old(cx).s@, st, array(old(cx).s@, i0, depth as nat, old(tape).hist()), final(tape).hist(), r),
    decreases depth, old(cx).s@.len() - i0, 2nat,
{
    let ghost g = s@;
    proof {
        lemma_close(g, st, i0);
    }
    let c0 = get8(s, j0);
    if depth == 0 {
        return None;
    }
    let ghost t0 = tape.hist();
    assert(array(g, i0, depth as nat, t0) == elements(g, i0, depth as nat, t0));
    let ghost mut i = i0;
    let mut k = k;
    let mut c0 = c0;
    let mut j0 = j0;
    loop
        invariant
            array(g, i0, depth as nat, t0) == elements(g, i0, depth as nat, t0),
            g == s@,
            cx.inv(),
            cx.s@ == g,
            g.len() <= MAX_INPUT,
            cx.st == st,
            cx.same(old(cx)),
            cx.kbase <= k,
            st < i0 <= i <= g.len(),
            out(g, st, i),
            bnd(g, st, i),
            k == cnt(g, st, i),
            depth > 0,
            tape.room() >= cx.kend - k,
            tape.inv(g),
            tape.hist().len() <= i,
            t0 == old(tape).hist(),
            elements(g, i0, depth as nat, t0) == elements(g, i, depth as nat, tape.hist()),
            k < cx.kend,
            k < ix(g, st).len(),
            c0 == g[ix(g, st)[k as int]],
            j0 == ix(g, st)[k as int],
        decreases g.len() - i,
    {
        if !(c0 == 0x2D || ex_is_digit(c0)) {
            return unpack2(ex2_elements(cx, k, depth, tape, Ghost(st), Ghost(i)));
        }
        let ghost tb = tape.hist();
        let (k1, e) = match ex2_value::<S, 0>(cx, k, depth - 1, tape, Ghost(st), Ghost(i), j0, s) {
            Some(x) => x,
            None => {
                proof {
                    crate::lemmas::lemma_skip_ws_bounds(g, i);
                    crate::lemmas::lemma_value_advances(g, skip_ws(g, i), (depth - 1) as nat, tb);
                    if let Some((_, e)) = value(g, skip_ws(g, i), (depth - 1) as nat, tb) {
                        lemma_not_bnd(g, st, e);
                    }
                }
                return None;
            },
        };
        proof {
            crate::lemmas::lemma_skip_ws_bounds(g, i);
            crate::lemmas::lemma_value_advances(g, skip_ws(g, i), (depth - 1) as nat, tb);
            crate::lemmas::lemma_value_size(g, skip_ws(g, i), (depth - 1) as nat, tb);
            lemma_close(g, st, e as int);
            lemma_cnt_bound(g, st, e as int);
        }
        let ghost tk = tape.hist();
        let q = match at2(cx, k1, tape, Ghost(k1 as int)) {
            Some(q) => q,
            None => return None,
        };
        let c = get8(s, q);
        if c == 0x5D {
            tape.push_fast(tok(Kind::ArrEnd));
            return Some((k1 + 1, q + 1));
        }
        if c != 0x2C {
            return None;
        }
        proof {
            assert(elements(g, i, depth as nat, tb) == elements(g, q as int + 1, depth as nat, tk));
            i = q + 1;
            lemma_close(g, st, i);
        }
        k = k1 + 1;
        match at2(cx, k, tape, Ghost(k as int)) {
            Some(q) => {
                c0 = get8(s, q);
                j0 = q;
            },
            None => return unpack2(ex2_elements(cx, k, depth, tape, Ghost(st), Ghost(i))),
        }
    }
}

#[allow(unused_variables)]
#[inline(always)]
fn ex2_elements_in<S: Sink>(
    cx: &mut Ctx,
    k0: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i0): Ghost<int>,
    s: &[u8],
) -> (r: Option<(usize, usize)>)
    requires
        s@ == old(cx).s@,
        cont_pre(old(cx), old(tape), st, k0 as int, i0),
    ensures
        moved(old(cx), final(cx), final(tape), r),
        cont_post(old(cx).s@, st, elements(old(cx).s@, i0, depth as nat, old(tape).hist()), final(tape).hist(), r),
    decreases depth, old(cx).s@.len() - i0, 0nat,
{
    if depth == 0 {
        return None;
    }
    let ghost g = s@;
    let ghost t0 = tape.hist();
    let ghost mut i = i0;
    let mut k = k0;
    loop
        invariant
            g == s@,
            cx.inv(),
            cx.s@ == g,
            g.len() <= MAX_INPUT,
            cx.st == st,
            cx.same(old(cx)),
            cx.kbase <= k,
            st < i0 <= i <= g.len(),
            out(g, st, i),
            bnd(g, st, i),
            k == cnt(g, st, i),
            depth > 0,
            tape.room() >= cx.kend - k,
            tape.inv(g),
            tape.hist().len() <= i,
            t0 == old(tape).hist(),
            elements(g, i0, depth as nat, t0) == elements(g, i, depth as nat, tape.hist()),
        decreases g.len() - i,
    {
        let ghost tb = tape.hist();
        let (k1, e) = match ex2_value::<S, 1>(cx, k, depth - 1, tape, Ghost(st), Ghost(i), 0, s) {
            Some(x) => x,
            None => {
                proof {
                    crate::lemmas::lemma_skip_ws_bounds(g, i);
                    crate::lemmas::lemma_value_advances(g, skip_ws(g, i), (depth - 1) as nat, tb);
                    if let Some((_, e)) = value(g, skip_ws(g, i), (depth - 1) as nat, tb) {
                        lemma_not_bnd(g, st, e);
                    }
                }
                return None;
            },
        };
        proof {
            crate::lemmas::lemma_skip_ws_bounds(g, i);
            crate::lemmas::lemma_value_advances(g, skip_ws(g, i), (depth - 1) as nat, tb);
            crate::lemmas::lemma_value_size(g, skip_ws(g, i), (depth - 1) as nat, tb);
            lemma_close(g, st, e as int);
            lemma_cnt_bound(g, st, e as int);
        }
        let ghost tk = tape.hist();
        let q = match at2(cx, k1, tape, Ghost(k1 as int)) {
            Some(q) => q,
            None => return None,
        };
        let c = get8(s, q);
        if c == 0x5D {
            tape.push_fast(tok(Kind::ArrEnd));
            return Some((k1 + 1, q + 1));
        }
        if c != 0x2C {
            return None;
        }
        proof {
            assert(elements(g, i, depth as nat, tb) == elements(g, q as int + 1, depth as nat, tk));
            i = q + 1;
        }
        k = k1 + 1;
    }
}

fn ex2_object<S: Sink>(
    cx: &mut Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i): Ghost<int>,
    s: &[u8],
) -> (r: Option<(usize, usize)>)
    requires
        s@ == old(cx).s@,
        cont_pre(old(cx), old(tape), st, k as int, i),
    ensures
        moved(old(cx), final(cx), final(tape), r),
        cont_post(old(cx).s@, st, object(old(cx).s@, i, depth as nat, old(tape).hist()), final(tape).hist(), r),
    decreases depth, old(cx).s@.len() - i, 2nat,
{
    let ghost g = s@;
    proof {
        lemma_close(g, st, i);
    }
    if let Some(q) = at2(cx, k, tape, Ghost(k as int)) {
        if get8(s, q) == 0x7D {
            tape.push_fast(tok(Kind::ObjEnd));
            return Some((k + 1, q + 1));
        }
    }
    ex2_members(cx, k, depth, tape, Ghost(st), Ghost(i), s)
}

/// One member: name, colon and value, as `members` reads it.
pub open spec fn member(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>) -> Option<
    (Seq<STok>, int),
> {
    let j = skip_ws(s, i);
    match string(s, j) {
        None => None,
        Some((k, esc)) => {
            let c = skip_ws(s, k);
            if !(0 <= c < s.len() && s[c] == 0x3A) {
                None
            } else {
                value(
                    s,
                    skip_ws(s, c + 1),
                    (depth - 1) as nat,
                    tape.push(STok::Key { start: j + 1, end: k - 1, escaped: esc }),
                )
            }
        },
    }
}

/// A member's tokens are no more than the bytes it spans.
proof fn lemma_member_size(s: Seq<u8>, i: int, depth: nat, tape: Seq<STok>)
    requires
        0 <= i <= s.len(),
    ensures
        member(s, i, depth, tape) matches Some((t, e)) ==> t.len() - tape.len() <= e - i,
{
    crate::lemmas::lemma_skip_ws_bounds(s, i);
    let j = skip_ws(s, i);
    if 0 <= j < s.len() && s[j] == 0x22 {
        crate::lemmas::lemma_string_body_advances(s, j + 1, false);
    }
    if let Some((k, esc)) = string(s, j) {
        crate::lemmas::lemma_skip_ws_bounds(s, k);
        let c = skip_ws(s, k);
        if 0 <= c < s.len() && s[c] == 0x3A {
            crate::lemmas::lemma_skip_ws_bounds(s, c + 1);
            crate::lemmas::lemma_value_size(
                s,
                skip_ws(s, c + 1),
                (depth - 1) as nat,
                tape.push(STok::Key { start: j + 1, end: k - 1, escaped: esc }),
            );
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
#[inline(always)]
fn ex2_member<S: Sink>(
    cx: &mut Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i): Ghost<int>,
    s: &[u8],
) -> (r: Option<(usize, usize)>)
    requires
        s@ == old(cx).s@,
        cont_pre(old(cx), old(tape), st, k as int, i),
        depth > 0,
    ensures
        moved(old(cx), final(cx), final(tape), r),
        member(old(cx).s@, i, depth as nat, old(tape).hist()) matches Some((_, e)) ==> i < e <= old(cx).s@.len(),
        match member(old(cx).s@, i, depth as nat, old(tape).hist()) {
            Some((t, e)) => if bnd(old(cx).s@, st, e) {
                r == Some((cnt(old(cx).s@, st, e) as usize, e as usize)) && final(tape).hist() == t && out(
                    old(cx).s@,
                    st,
                    e,
                )
            } else {
                r is None
            },
            None => r is None,
        },
    decreases depth, old(cx).s@.len() - i, 0nat,
{
    let ghost g = s@;
    proof {
        lemma_close(g, st, i);
        crate::lemmas::lemma_skip_ws_bounds(g, i);
        lemma_skip(g, st, i);
    }
    // A member whose key has no escape and whose four entries (the key's
    // quotes, the colon and the value's first) are in the window: one
    // check, then plain reads.
    if k < cx.kend && cx.kend - k > 4 {
        let j = ent(cx, k);
        if get8(s, j) != 0x22 {
            return None;
        }
        let n = str_quick(cx, k, j, s, Ghost(st));
        if n != 0 {
            proof {
                crate::lemmas::lemma_string_body_advances(g, j + 1, false);
                lemma_close(g, st, n as int);
                lemma_cnt_bound(g, st, n as int);
            }
            let cpos = ent(cx, k + 2);
            proof {
                assert(j == skip_ws(g, i));
                assert(string(g, j as int) == Some((n as int, false)));
                lemma_skip(g, st, n as int);
                lemma_at(g, st, skip_ws(g, n as int));
                assert(cpos == skip_ws(g, n as int));
            }
            if get8(s, cpos) != 0x3A {
                proof {
                    assert(member(g, i, depth as nat, old(tape).hist()) is None);
                }
                return None;
            }
            tape.push_str_fast(Tok::new(Kind::Key, false, (j + 1), (n - 1), NO), s);
            let ghost tkey = tape.hist();
            let jv = ent(cx, k + 3);
            proof {
                crate::lemmas::lemma_skip_ws_bounds(g, cpos + 1);
                crate::lemmas::lemma_value_advances(g, skip_ws(g, cpos + 1), (depth - 1) as nat, tkey);
                lemma_at(g, st, cpos as int);
            }
            return ex2_value::<S, 2>(cx, k + 3, depth - 1, tape, Ghost(st), Ghost(cpos + 1), jv, s);
        }
    }
    let j = match at2(cx, k, tape, Ghost(k as int)) {
        Some(j) => j,
        None => return None,
    };
    if get8(s, j) != 0x22 {
        return None;
    }
    // The key goes on the tape before its colon is checked, while the
    // string scan's state is still the tape's; a missing colon fails the
    // parse anyway.
    let (k1, n) = match ex2_str_tok(cx, k, j, tape, Ghost(st), s, Kind::Key) {
        Some(x) => x,
        None => return None,
    };
    proof {
        crate::lemmas::lemma_string_body_advances(g, j + 1, false);
        lemma_close(g, st, n as int);
        lemma_cnt_bound(g, st, n as int);
    }
    let ghost tkey = tape.hist();
    let cpos = match at2(cx, k1, tape, Ghost(k1 as int)) {
        Some(q) => q,
        None => return None,
    };
    proof {
        assert(j == skip_ws(g, i));
        assert(cpos == skip_ws(g, n as int));
    }
    if get8(s, cpos) != 0x3A {
        proof {
            assert(member(g, i, depth as nat, old(tape).hist()) is None);
        }
        return None;
    }
    proof {
        crate::lemmas::lemma_skip_ws_bounds(g, cpos + 1);
        crate::lemmas::lemma_value_advances(g, skip_ws(g, cpos + 1), (depth - 1) as nat, tkey);
    }
    ex2_value::<S, 1>(cx, k1 + 1, depth - 1, tape, Ghost(st), Ghost(cpos + 1), 0, s)
}

#[allow(unused_variables)]
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
fn ex2_members<S: Sink>(
    cx: &mut Ctx,
    k0: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i0): Ghost<int>,
    s: &[u8],
) -> (r: Option<(usize, usize)>)
    requires
        s@ == old(cx).s@,
        cont_pre(old(cx), old(tape), st, k0 as int, i0),
    ensures
        moved(old(cx), final(cx), final(tape), r),
        cont_post(old(cx).s@, st, members(old(cx).s@, i0, depth as nat, old(tape).hist()), final(tape).hist(), r),
    decreases depth, old(cx).s@.len() - i0, 1nat,
{
    if depth == 0 {
        return None;
    }
    let ghost g = s@;
    let ghost t0 = tape.hist();
    let ghost mut i = i0;
    let mut k = k0;
    loop
        invariant
            g == s@,
            cx.inv(),
            cx.s@ == g,
            g.len() <= MAX_INPUT,
            cx.st == st,
            cx.same(old(cx)),
            cx.kbase <= k,
            st < i0 <= i <= g.len(),
            out(g, st, i),
            bnd(g, st, i),
            k == cnt(g, st, i),
            depth > 0,
            tape.room() >= cx.kend - k,
            tape.inv(g),
            tape.hist().len() <= i,
            t0 == old(tape).hist(),
            members(g, i0, depth as nat, t0) == members(g, i, depth as nat, tape.hist()),
        decreases g.len() - i,
    {
        let ghost tb = tape.hist();
        let (k2, e) = match ex2_member(cx, k, depth, tape, Ghost(st), Ghost(i), s) {
            Some(x) => x,
            None => {
                proof {
                    if let Some((_, e)) = member(g, i, depth as nat, tb) {
                        lemma_not_bnd(g, st, e);
                    }
                }
                return None;
            },
        };
        proof {
            lemma_close(g, st, e as int);
            lemma_cnt_bound(g, st, e as int);
            lemma_member_size(g, i, depth as nat, tb);
        }
        let ghost tk = tape.hist();
        let q = match at2(cx, k2, tape, Ghost(k2 as int)) {
            Some(q) => q,
            None => return None,
        };
        let c = get8(s, q);
        if c == 0x7D {
            tape.push_fast(tok(Kind::ObjEnd));
            return Some((k2 + 1, q + 1));
        }
        if c != 0x2C {
            return None;
        }
        proof {
            assert(members(g, i, depth as nat, tb) == members(g, q as int + 1, depth as nat, tk));
            i = q + 1;
        }
        k = k2 + 1;
    }
}

// ---------------------------------------------------------------------------
// Documents
// ---------------------------------------------------------------------------

/// Parses a complete JSON text (only whitespace may follow the value) in
/// two passes, interleaved: `Win` finds the structural bytes of the input
/// a window at a time, and the value is read through it, so the index
/// takes a fixed amount of memory however long the input. The result is
/// exactly `document(s, true)`. `idx` is the window's buffer, kept for the
/// next parse.
pub fn parse2_with<S: Sink>(s: &[u8], tape: &mut S, idx: &mut Vec<u32>, win: usize) -> (r: Result<usize, usize>)
    requires
        old(tape).hist() == Seq::<STok>::empty(),
        old(tape).inv(s@),
        128 <= win <= 0x4000_0000,
        win % 128 == 0,
    ensures
        r is Ok ==> final(tape).inv(s@),
        match document(s@, true) {
            Some((t, e)) => r is Ok && final(tape).hist() == t && r.unwrap() as int == e && e
                <= s@.len(),
            None => r is Err,
        },
{
    if s.len() > MAX_INPUT {
        return Err(MAX_INPUT);
    }
    let start = if ex_has_lit(s, 0, &[0xEF, 0xBB, 0xBF]) { 3 } else { 0 };
    proof {
        assert([0xEFu8, 0xBB, 0xBF]@ == seq![0xEFu8, 0xBB, 0xBF]);
    }
    let mut buf = Vec::new();
    std::mem::swap(idx, &mut buf);
    let mut cx = Win::new(s, start, win, buf);
    let r = parse2_win(s, tape, &mut cx, start);
    let mut buf = cx.into_buf();
    std::mem::swap(idx, &mut buf);
    r
}

/// `parse2_with` on the window `cx`, fresh at the start of the text.
pub fn parse2_win<S: Sink>(s: &[u8], tape: &mut S, cx: &mut Win, start: usize) -> (r: Result<usize, usize>)
    requires
        old(tape).hist() == Seq::<STok>::empty(),
        old(tape).inv(s@),
        old(cx).inv(),
        old(cx).s@ == s@,
        old(cx).st == start,
        old(cx).kbase == 0,
        old(cx).kend == 0,
        start == bom_end(s@),
        s@.len() <= MAX_INPUT,
    ensures
        r is Ok ==> final(tape).inv(s@),
        match document(s@, true) {
            Some((t, e)) => r is Ok && final(tape).hist() == t && r.unwrap() as int == e && e
                <= s@.len(),
            None => r is Err,
        },
{
    let ghost g = s@;
    let ghost st = start as int;
    proof {
        assert(positions(g, st, st, st) =~= Seq::<int>::empty());
        crate::lemmas::lemma_skip_ws_bounds(g, st);
        crate::lemmas::lemma_value_advances(g, skip_ws(g, st), MAX_DEPTH as nat, Seq::empty());
    }
    tape.reserve(2);
    let (k, e) = match ex2_value::<S, 1>(cx, 0, MAX_DEPTH, tape, Ghost(st), Ghost(st), 0, s) {
        Some(x) => x,
        None => {
            proof {
                if let Some((_, e)) = value(g, skip_ws(g, st), MAX_DEPTH as nat, Seq::empty()) {
                    lemma_not_bnd(g, st, e);
                }
            }
            return Err(0);
        },
    };
    proof {
        lemma_close(g, st, e as int);
        lemma_cnt_bound(g, st, e as int);
    }
    // Only whitespace may follow: the rest of the input indexes to nothing.
    if cx.at(k).is_some() {
        return Err(e);
    }
    proof {
        assert(g.subrange(0, g.len() as int) =~= g);
    }
    if !cx.utf8 {
        return Err(0);
    }
    Ok(e)
}

/// `parse2_with` into a `Tape`, which is cleared first.
pub fn parse2_into(s: &[u8], tape: &mut Tape, idx: &mut Vec<u32>) -> (r: Result<usize, usize>)
    ensures
        match document(s@, true) {
            Some((t, e)) => r is Ok && final(tape)@ == t && r.unwrap() as int == e && e <= s@.len()
                && crate::lemmas::in_bounds(s@.len() as int, t) && crate::lemmas::ends_value(t)
                && t.len() <= s@.len() && crate::lemmas::links_from(t, 0),
            None => r is Err,
        },
{
    parse2_window(s, tape, idx, WINDOW)
}

/// `parse2_into` with windows of `win` bytes, a multiple of 128 (for
/// tests; `WINDOW` otherwise).
pub fn parse2_window(s: &[u8], tape: &mut Tape, idx: &mut Vec<u32>, win: usize) -> (r: Result<usize, usize>)
    requires
        128 <= win <= 0x4000_0000,
        win % 128 == 0,
    ensures
        match document(s@, true) {
            Some((t, e)) => r is Ok && final(tape)@ == t && r.unwrap() as int == e && e <= s@.len()
                && crate::lemmas::in_bounds(s@.len() as int, t) && crate::lemmas::ends_value(t)
                && t.len() <= s@.len() && crate::lemmas::links_from(t, 0),
            None => r is Err,
        },
{
    proof {
        crate::lemmas::lemma_document_in_bounds(s@, true);
        crate::lemmas::lemma_document_size(s@, true);
        crate::lemmas::lemma_document_links(s@, true);
    }
    tape.clear();
    assert(tape@ =~= Seq::<STok>::empty());
    match parse2_with(s, tape, idx, win) {
        Ok(k) => Ok(k),
        Err(p) => Err(if p > tape.err_pos { p } else { tape.err_pos }),
    }
}

/// `parse2_into`, storing values while parsing (see `EagerTape`).
pub fn parse2_eager_into(s: &[u8], tape: &mut EagerTape, idx: &mut Vec<u32>) -> (r: Result<usize, usize>)
    ensures
        match document(s@, true) {
            Some((t, e)) => r is Ok && final(tape).tape@ == t && r.unwrap() as int == e && e <= s@.len()
                && crate::lemmas::in_bounds(s@.len() as int, t) && crate::lemmas::ends_value(t)
                && t.len() <= s@.len() && crate::lemmas::links_from(t, 0),
            None => r is Err,
        },
        // Every value stored while parsing is right, and the decoded
        // strings take no more bytes than the input.
        r is Ok ==> crate::parser::stored_ok(final(tape).tape, s@) && final(tape).tape.strs@.len()
            <= s@.len(),
{
    proof {
        crate::lemmas::lemma_document_in_bounds(s@, true);
        crate::lemmas::lemma_document_size(s@, true);
        crate::lemmas::lemma_document_links(s@, true);
    }
    tape.tape.clear();
    assert(tape.tape@ =~= Seq::<STok>::empty());
    assert(crate::lemmas::weight(Seq::<STok>::empty()) == 0);
    match parse2_with(s, tape, idx, WINDOW) {
        Ok(k) => Ok(k),
        Err(p) => Err(if p > tape.tape.err_pos { p } else { tape.tape.err_pos }),
    }
}

} // verus!

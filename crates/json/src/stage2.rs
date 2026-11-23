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

/// The input and its structural index, passed to stage 2 as one pointer.
pub struct Ctx<'a> {
    pub s: &'a [u8],
    pub idx: &'a [u32],
}

// ---------------------------------------------------------------------------
// Counting structural positions
// ---------------------------------------------------------------------------

/// Number of structural positions in `[st, i)`. Stage 2 keeps the index of
/// the next unread structural position equal to `cnt` of its spec position.
pub open spec fn cnt(s: Seq<u8>, st: int, i: int) -> int {
    positions(s, st, st, i).len() as int
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
        structural(s, st, i) ==> positions(s, st, st, i + 1)[cnt(s, st, i)] == i as u32,
        positions(s, st, st, i + 1).subrange(0, cnt(s, st, i)) == positions(s, st, st, i),
{
    let p = positions(s, st, st, i);
    if structural(s, st, i) {
        assert(p.push(i as u32).subrange(0, p.len() as int) =~= p);
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
        s.len() <= u32::MAX,
    ensures
        ({
            let q = positions(s, st, st, s.len() as int)[cnt(s, st, a)] as int;
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
        b <= u32::MAX,
    ensures
        ({
            let p = positions(s, st, st, b)[k] as int;
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
        s.len() <= u32::MAX,
    ensures
        cnt(s, st, q) < cnt(s, st, s.len() as int),
        positions(s, st, st, s.len() as int)[cnt(s, st, q)] == q as u32,
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

/// What stage 2 may assume after stage 1 succeeded.
pub open spec fn indexed(s: Seq<u8>, st: int, idx: Seq<u32>) -> bool {
    &&& 0 <= st <= s.len()
    &&& s.len() + 64 <= u32::MAX
    &&& idx == positions(s, st, st, s.len() as int)
    &&& clean(s, st, s.len() as int)
    &&& !instr(s, st, s.len() - 1)
}

/// A plain stretch inside a string: no structural position means no
/// closing quote, no escape and (stage 1 checked) no control character.
pub proof fn lemma_plain_inside(s: Seq<u8>, st: int, i: int, q: int)
    requires
        0 <= st <= i <= q <= s.len(),
        instr(s, st, i - 1),
        !esc(s, st, i),
        clean(s, st, s.len() as int),
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
        indexed(s, st, positions(s, st, st, s.len() as int)),
        st <= lo <= i <= s.len(),
        instr(s, st, i - 1),
    ensures
        cnt(s, st, lo) < cnt(s, st, s.len() as int),
        ({
            let q = positions(s, st, st, s.len() as int)[cnt(s, st, lo)] as int;
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

/// Scans the string whose opening quote is index entry `k`. Returns the
/// index entry after its closing quote, the position after it, and whether
/// it has escapes.
#[inline(always)]
pub fn ex2_string(s: &[u8], idx: &[u32], k: usize, Ghost(st): Ghost<int>) -> (r: Option<
    (usize, usize, bool),
>)
    requires
        indexed(s@, st, idx@),
        k < idx@.len(),
        (idx@[k as int] as int) < s@.len(),
        s@[idx@[k as int] as int] == 0x22,
        out(s@, st, idx@[k as int] as int),
    ensures
        match string(s@, idx@[k as int] as int) {
            Some((n, esc)) => r == Some((cnt(s@, st, n) as usize, n as usize, esc)) && out(s@, st, n)
                && bnd(s@, st, n) && n <= s@.len(),
            None => r is None,
        },
        r matches Some((k2, _, _)) ==> k2 > k,
{
    let ghost g = s@;
    let j = get32(idx, k) as usize;
    proof {
        lemma_entry(g, st, g.len() as int, k as int);
        lemma_at(g, st, j as int);
        assert(byte(g, j as int) == g[j as int]);
        assert(uq(g, st, j as int));
        assert(instr(g, st, j as int));
        assert(!esc(g, st, j + 1));
    }
    let _n = idx.len();
    let mut kk = k + 1;
    let mut i = j + 1;
    let mut escf = false;
    let ghost mut lo: int = j + 1;
    loop
        invariant
            g == s@,
            indexed(g, st, idx@),
            j as int == idx@[k as int] as int,
            st <= j < i <= g.len(),
            j + 1 <= lo <= i,
            kk as int == cnt(g, st, lo),
            kk <= idx@.len(),
            kk > k,
            _n == idx@.len(),
            instr(g, st, i - 1),
            !esc(g, st, i as int),
            string(g, j as int) == string_body(g, i as int, escf),
        decreases idx@.len() - kk,
    {
        proof {
            lemma_string_step(g, st, i as int, lo);
        }
        let q = get32(idx, kk) as usize;
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
                assert(instr(g, st, q as int));
                assert(!structural(g, st, q as int));
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
fn ex2_string_esc(s: &[u8], idx: &[u32], k: usize, Ghost(st): Ghost<int>, dst: &mut Vec<u8>) -> (r:
    Option<(usize, usize, bool)>)
    requires
        indexed(s@, st, idx@),
        k < idx@.len(),
        (idx@[k as int] as int) < s@.len(),
        s@[idx@[k as int] as int] == 0x22,
        out(s@, st, idx@[k as int] as int),
    ensures
        match string(s@, idx@[k as int] as int) {
            Some((n, esc)) => r == Some((cnt(s@, st, n) as usize, n as usize, esc)) && out(s@, st, n)
                && bnd(s@, st, n) && n <= s@.len(),
            None => r is None,
        },
        r matches Some((k2, _, _)) ==> k2 > k,
        r matches Some((_, n, esc)) ==> if esc {
            final(dst)@ == old(dst)@ + decode(s@, idx@[k as int] + 1, n - 1)
        } else {
            final(dst)@ == old(dst)@
        },
{
    let ghost g = s@;
    let ghost o = dst@;
    let j = get32(idx, k) as usize;
    proof {
        lemma_entry(g, st, g.len() as int, k as int);
        lemma_at(g, st, j as int);
        assert(byte(g, j as int) == g[j as int]);
        assert(uq(g, st, j as int));
        assert(instr(g, st, j as int));
        assert(!esc(g, st, j + 1));
    }
    let _n = idx.len();
    let mut kk = k + 1;
    let mut i = j + 1;
    let mut escf = false;
    let ghost mut lo: int = j + 1;
    loop
        invariant
            g == s@,
            o == old(dst)@,
            indexed(g, st, idx@),
            j as int == idx@[k as int] as int,
            st <= j < i <= g.len(),
            j + 1 <= lo <= i,
            kk as int == cnt(g, st, lo),
            kk <= idx@.len(),
            kk > k,
            _n == idx@.len(),
            instr(g, st, i - 1),
            !esc(g, st, i as int),
            string(g, j as int) == string_body(g, i as int, escf),
            !escf ==> i == j + 1 && dst@ == o,
            escf ==> spare(*dst) >= (g.len() - i) + 16 && dec_inv(g, j as int, i as int, o, dst@),
        decreases idx@.len() - kk,
    {
        proof {
            lemma_string_step(g, st, i as int, lo);
        }
        let q = get32(idx, kk) as usize;
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
                assert(instr(g, st, q as int));
                assert(!structural(g, st, q as int));
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
pub fn ex2_string_dec(s: &[u8], idx: &[u32], k: usize, Ghost(st): Ghost<int>, dst: &mut Vec<u8>) -> (r:
    Option<(usize, usize, bool)>)
    requires
        indexed(s@, st, idx@),
        k < idx@.len(),
        (idx@[k as int] as int) < s@.len(),
        s@[idx@[k as int] as int] == 0x22,
        out(s@, st, idx@[k as int] as int),
    ensures
        match string(s@, idx@[k as int] as int) {
            Some((n, esc)) => r == Some((cnt(s@, st, n) as usize, n as usize, esc)) && out(s@, st, n)
                && bnd(s@, st, n) && n <= s@.len(),
            None => r is None,
        },
        r matches Some((k2, _, _)) ==> k2 > k,
        r matches Some((_, n, esc)) ==> if esc {
            final(dst)@ == old(dst)@ + decode(s@, idx@[k as int] + 1, n - 1)
        } else {
            final(dst)@ == old(dst)@
        },
{
    let ghost g = s@;
    let ghost j: int = idx@[k as int] as int;
    proof {
        lemma_entry(g, st, g.len() as int, k as int);
        lemma_at(g, st, j as int);
        assert(byte(g, j as int) == g[j as int]);
        assert(uq(g, st, j as int));
        assert(instr(g, st, j as int));
        assert(!esc(g, st, j + 1));
        lemma_string_step(g, st, j + 1, j + 1);
        assert(cnt(g, st, j + 1) == k + 1);
        assert(k + 1 < idx@.len());
    }
    let _n = idx.len();
    let _m = s.len();
    // The body's first entry: the closing quote unless there is an escape.
    let q = get32(idx, k + 1) as usize;
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
            assert(instr(g, st, q as int));
            assert(!structural(g, st, q as int));
        }
        return None;
    }
    let (k2, ne) = ex2_string_esc_out(s, idx, k, Ghost(st), dst);
    if k2 == 0 {
        None
    } else {
        Some((k2, (ne / 2) as usize, ne % 2 == 1))
    }
}

/// `ex2_string_esc` out of line, as most strings have none. The result is
/// packed in two words, so that it comes back in registers rather than
/// through memory: `(0, 0)` for `None`, else `(k2, 2 * n + esc)`.
#[inline(never)]
fn ex2_string_esc_out(s: &[u8], idx: &[u32], k: usize, Ghost(st): Ghost<int>, dst: &mut Vec<u8>) -> (r:
    (usize, u64))
    requires
        indexed(s@, st, idx@),
        k < idx@.len(),
        (idx@[k as int] as int) < s@.len(),
        s@[idx@[k as int] as int] == 0x22,
        out(s@, st, idx@[k as int] as int),
    ensures
        match string(s@, idx@[k as int] as int) {
            Some((n, esc)) => r.0 == cnt(s@, st, n) && r.1 == 2 * n + (if esc { 1int } else { 0 })
                && out(s@, st, n) && bnd(s@, st, n) && n <= s@.len() && r.0 > k && if esc {
                final(dst)@ == old(dst)@ + decode(s@, idx@[k as int] + 1, n - 1)
            } else {
                final(dst)@ == old(dst)@
            },
            None => r.0 == 0,
        },
{
    proof {
        lemma_entry(s@, st, s@.len() as int, k as int);
        crate::lemmas::lemma_string_body_advances(s@, idx@[k as int] + 1, false);
        if let Some((n, _)) = string(s@, idx@[k as int] as int) {
            lemma_cnt_bound(s@, st, n);
        }
    }
    match ex2_string_esc(s, idx, k, Ghost(st), dst) {
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
        indexed(s, st, positions(s, st, st, s.len() as int)),
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
            &&& j < s.len() ==> positions(s, st, st, s.len() as int)[cnt(s, st, p)] == j as u32
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
    cx: &Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(p): Ghost<int>,
) -> (r: Option<(usize, usize)>)
    requires
        indexed(cx.s@, st, cx.idx@),
        st <= p <= cx.s@.len(),
        out(cx.s@, st, p),
        bnd(cx.s@, st, p),
        k == cnt(cx.s@, st, p),
        old(tape).room() >= cx.idx@.len() - k,
        old(tape).inv(cx.s@),
        old(tape).hist().len() <= p,
        N == 0 ==> k < cx.idx@.len() && (cx.s@[cx.idx@[k as int] as int] == 0x2D || is_digit(cx.s@[cx.idx@[k as int] as int])),
    ensures
        r is Some ==> final(tape).inv(cx.s@),
        r matches Some((k2, _)) ==> final(tape).room() >= cx.idx@.len() - k2,
        match value(cx.s@, skip_ws(cx.s@, p), depth as nat, old(tape).hist()) {
            Some((t, e)) => if bnd(cx.s@, st, e) {
                r == Some((cnt(cx.s@, st, e) as usize, e as usize)) && final(tape).hist() == t && out(
                    cx.s@,
                    st,
                    e,
                ) && e <= cx.s@.len()
            } else {
                r is None
            },
            None => r is None,
        },
    decreases depth, cx.s@.len() - p, 3nat,
{
    let s = cx.s;
    let idx = cx.idx;
    let ghost g = s@;
    proof {
        lemma_skip(g, st, p);
        lemma_prefix(g, st, skip_ws(g, p), g.len() as int);
        if skip_ws(g, p) < g.len() {
            lemma_at(g, st, skip_ws(g, p));
        }
    }
    if k >= idx.len() {
        return None;
    }
    let j = get32(idx, k) as usize;
    proof {
        let jj = skip_ws(g, p);
        assert(j == jj);
        crate::lemmas::lemma_value_advances(g, jj, depth as nat, old(tape).hist());
    }
    let c = get8(s, j);
    if N != 0 && c == 0x22 {
        match tape.scan_str(s, idx, k, Ghost(st)) {
            Some((k2, n, esc)) => {
                tape.push_str_fast(Tok::new(Kind::Str, esc, (j + 1), (n - 1), NO), s);
                Some((k2, n))
            },
            None => None,
        }
    } else if N != 0 && (c == 0x5B || c == 0x7B) {
        proof {
            assert(byte(g, j as int) == g[j as int]);
            assert(!instr(g, st, j as int));
            assert(!scalar(g, st, j as int));
        }
        // Empty arrays are common (most of citm_catalog's); finish them
        // without the call.
        if c == 0x5B && depth > 0 && ex2_empty_array(cx, k + 1, depth, tape, Ghost(st), j) {
            return Some((k + 2, get32(idx, k + 1) as usize + 1));
        }
        // Arrays are parsed in line, so that an array of scalars (such as
        // a coordinate pair) costs no call.
        if c == 0x5B && depth > 0 {
            let t_idx = tape.count();
            tape.push_fast(tok(Kind::ArrStart));
            proof {
                lemma_close(g, st, j + 1);
            }
            return match ex2_array_inl(cx, k + 1, depth, tape, Ghost(st), Ghost(j + 1)) {
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
        match ex2_container(cx, k + 1, depth, tape, Ghost(st), j) {
            Some(k2) => Some((k2, get32(idx, k2 - 1) as usize + 1)),
            None => None,
        }
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
        Some((k + 1, e))
    }
}

/// `[` at `j` followed by `]`: pushes both tokens and returns true.
/// Otherwise leaves the tape alone and returns false.
// `depth` and `j` appear only in the specification.
#[allow(unused_variables)]
#[inline(always)]
fn ex2_empty_array<S: Sink>(
    cx: &Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    j: usize,
) -> (r: bool)
    requires
        indexed(cx.s@, st, cx.idx@),
        st <= j < cx.s@.len(),
        cnt(cx.s@, st, j as int + 1) == k,
        cx.s@[j as int] == 0x5B,
        out(cx.s@, st, j as int + 1),
        bnd(cx.s@, st, j as int + 1),
        depth > 0,
        old(tape).room() >= cx.idx@.len() - (k - 1),
        old(tape).inv(cx.s@),
        old(tape).hist().len() <= j,
    ensures
        r ==> final(tape).inv(cx.s@),
        r ==> final(tape).room() >= cx.idx@.len() - (k + 1),
        r ==> k < cx.idx@.len() && match value(cx.s@, j as int, depth as nat, old(tape).hist()) {
            Some((t, e)) => final(tape).hist() == t && e == cx.idx@[k as int] as int + 1 && cnt(cx.s@, st, e) == k + 1
                && out(cx.s@, st, e) && bnd(cx.s@, st, e) && e <= cx.s@.len(),
            None => false,
        },
        !r ==> *final(tape) == *old(tape),
{
    let s = cx.s;
    let idx = cx.idx;
    let ghost g = s@;
    proof {
        lemma_close(g, st, j + 1);
    }
    if k < idx.len() {
        let q = get32(idx, k) as usize;
        if get8(s, q) == 0x5D {
            proof {
                assert(byte(g, q as int) == g[q as int]);
            }
            let t = tape.count();
            tape.push_fast(Tok::new(Kind::ArrStart, false, t + 1, 0, NO));
            tape.push_fast(tok(Kind::ArrEnd));
            assert(tape.hist() =~= close_at(old(tape).hist().push(STok::ArrStart { end: 0 }).push(STok::ArrEnd), t as int));
            return true;
        }
    }
    false
}

/// An array or object at `j`, which is index entry `k - 1`.
#[inline(never)]
fn ex2_container<S: Sink>(
    cx: &Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    j: usize,
) -> (r: Option<usize>)
    requires
        indexed(cx.s@, st, cx.idx@),
        st <= j < cx.s@.len(),
        cnt(cx.s@, st, j as int + 1) == k,
        cx.s@[j as int] == 0x5B || cx.s@[j as int] == 0x7B,
        out(cx.s@, st, j as int + 1),
        bnd(cx.s@, st, j as int + 1),
        old(tape).room() >= cx.idx@.len() - (k - 1),
        old(tape).inv(cx.s@),
        old(tape).hist().len() <= j,
        k <= cx.idx@.len(),
    ensures
        r is Some ==> final(tape).inv(cx.s@),
        r matches Some(k2) ==> final(tape).room() >= cx.idx@.len() - k2,
        match value(cx.s@, j as int, depth as nat, old(tape).hist()) {
            Some((t, e)) => r == Some(cnt(cx.s@, st, e) as usize) && final(tape).hist() == t
                && 1 <= cnt(cx.s@, st, e) <= cx.idx@.len() && cx.idx@[cnt(cx.s@, st, e) - 1] as int + 1 == e
                && out(cx.s@, st, e) && bnd(cx.s@, st, e) && e <= cx.s@.len(),
            None => r is None,
        },
    decreases depth, cx.s@.len() - j, 2nat,
{
    let s = cx.s;
    let ghost idx = cx.idx;
    let ghost g = s@;
    if depth == 0 {
        return None;
    }
    let c = get8(s, j);
    let t_idx = tape.count();
    let r = if c == 0x5B {
        tape.push_fast(tok(Kind::ArrStart));
        ex2_array(cx, k, depth, tape, Ghost(st), Ghost(j + 1))
    } else {
        tape.push_fast(tok(Kind::ObjStart));
        ex2_object(cx, k, depth, tape, Ghost(st), Ghost(j + 1))
    };
    match r {
        Some((k2, _)) => {
            proof {
                lemma_container_prefix(g, j as int, depth as nat, old(tape).hist(), c);
                if let Some((_, e)) = value(g, j as int, depth as nat, old(tape).hist()) {
                    lemma_cnt_bound(g, st, e);
                }
            }
            tape.close(t_idx);
            Some(k2)
        },
        None => None,
    }
}

fn ex2_array<S: Sink>(
    cx: &Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i): Ghost<int>,
) -> (r: Option<(usize, usize)>)
    requires
        indexed(cx.s@, st, cx.idx@),
        st < i <= cx.s@.len(),
        out(cx.s@, st, i),
        bnd(cx.s@, st, i),
        k == cnt(cx.s@, st, i),
        old(tape).room() >= cx.idx@.len() - k,
        old(tape).inv(cx.s@),
        old(tape).hist().len() <= i,
    ensures
        r is Some ==> final(tape).inv(cx.s@),
        r matches Some((k2, _)) ==> final(tape).room() >= cx.idx@.len() - k2,
        r matches Some((k2, e2)) ==> 1 <= k2 <= cx.idx@.len() && cx.idx@[k2 - 1] as int + 1 == e2,
        match array(cx.s@, i, depth as nat, old(tape).hist()) {
            Some((t, e)) => r == Some((cnt(cx.s@, st, e) as usize, e as usize)) && final(tape).hist() == t
                && out(cx.s@, st, e) && bnd(cx.s@, st, e) && e <= cx.s@.len(),
            None => r is None,
        },
    decreases depth, cx.s@.len() - i, 1nat,
{
    let s = cx.s;
    let idx = cx.idx;
    let ghost g = s@;
    proof {
        lemma_close(g, st, i);
    }
    if k < idx.len() && get8(s, get32(idx, k) as usize) == 0x5D {
        tape.push_fast(tok(Kind::ArrEnd));
        return Some((k + 1, get32(idx, k) as usize + 1));
    }
    let ghost t0 = tape.hist();
    match ex2_elements(cx, k, depth, tape, Ghost(st), Ghost(i)) {
        Some(k2) => {
            let e = get32(cx.idx, k2 - 1) as usize + 1;
            proof {
                if let Some((_, e0)) = elements(g, i, depth as nat, t0) {
                    lemma_cnt_bound(g, st, e0);
                    assert(e == e0);
                }
            }
            Some((k2, e))
        },
        None => None,
    }
}

/// `ex2_array` in line: elements that are numbers are parsed here; at the
/// first element that is not, `ex2_elements` takes over.
#[allow(unused_variables)]
#[inline(always)]
fn ex2_array_inl<S: Sink>(
    cx: &Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i0): Ghost<int>,
) -> (r: Option<(usize, usize)>)
    requires
        indexed(cx.s@, st, cx.idx@),
        st < i0 <= cx.s@.len(),
        out(cx.s@, st, i0),
        bnd(cx.s@, st, i0),
        k == cnt(cx.s@, st, i0),
        old(tape).room() >= cx.idx@.len() - k,
        old(tape).inv(cx.s@),
        old(tape).hist().len() <= i0,
    ensures
        r is Some ==> final(tape).inv(cx.s@),
        r matches Some((k2, _)) ==> final(tape).room() >= cx.idx@.len() - k2,
        r matches Some((k2, e2)) ==> 1 <= k2 <= cx.idx@.len() && cx.idx@[k2 - 1] as int + 1 == e2,
        match array(cx.s@, i0, depth as nat, old(tape).hist()) {
            Some((t, e)) => r == Some((cnt(cx.s@, st, e) as usize, e as usize)) && final(tape).hist() == t
                && out(cx.s@, st, e) && bnd(cx.s@, st, e) && e <= cx.s@.len(),
            None => r is None,
        },
    decreases depth, cx.s@.len() - i0, 1nat,
{
    let s = cx.s;
    let idx = cx.idx;
    let ghost g = s@;
    proof {
        lemma_close(g, st, i0);
    }
    if k < idx.len() && get8(s, get32(idx, k) as usize) == 0x5D {
        tape.push_fast(tok(Kind::ArrEnd));
        return Some((k + 1, get32(idx, k) as usize + 1));
    }
    if depth == 0 {
        return None;
    }
    let ghost t0 = tape.hist();
    assert(array(g, i0, depth as nat, t0) == elements(g, i0, depth as nat, t0));
    let ghost mut i = i0;
    let mut k = k;
    loop
        invariant
            array(g, i0, depth as nat, t0) == elements(g, i0, depth as nat, t0),
            g == s@,
            g == cx.s@,
            idx@ == cx.idx@,
            indexed(g, st, idx@),
            st < i0 <= i <= g.len(),
            out(g, st, i),
            bnd(g, st, i),
            k == cnt(g, st, i),
            depth > 0,
            tape.room() >= idx@.len() - k,
            tape.inv(g),
            tape.hist().len() <= i,
            t0 == old(tape).hist(),
            elements(g, i0, depth as nat, t0) == elements(g, i, depth as nat, tape.hist()),
        decreases g.len() - i,
    {
        if k >= idx.len() {
            let ghost t1 = tape.hist();
            return match ex2_elements(cx, k, depth, tape, Ghost(st), Ghost(i)) {
                Some(k2) => {
                    let e = get32(cx.idx, k2 - 1) as usize + 1;
                    proof {
                        if let Some((_, e0)) = elements(g, i, depth as nat, t1) {
                            lemma_cnt_bound(g, st, e0);
                            assert(e == e0);
                        }
                    }
                    Some((k2, e))
                },
                None => None,
            };
        }
        proof {
            lemma_entry(g, st, g.len() as int, k as int);
        }
        let c0 = get8(s, get32(idx, k) as usize);
        if !(c0 == 0x2D || ex_is_digit(c0)) {
            let ghost t1 = tape.hist();
            return match ex2_elements(cx, k, depth, tape, Ghost(st), Ghost(i)) {
                Some(k2) => {
                    let e = get32(cx.idx, k2 - 1) as usize + 1;
                    proof {
                        if let Some((_, e0)) = elements(g, i, depth as nat, t1) {
                            lemma_cnt_bound(g, st, e0);
                            assert(e == e0);
                        }
                    }
                    Some((k2, e))
                },
                None => None,
            };
        }
        let ghost tb = tape.hist();
        let (k1, e) = match ex2_value::<S, 0>(cx, k, depth - 1, tape, Ghost(st), Ghost(i)) {
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
        }
        let ghost tk = tape.hist();
        if k1 >= idx.len() {
            return None;
        }
        let q = get32(idx, k1) as usize;
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

#[allow(unused_variables)]
#[inline(never)]
fn ex2_elements<S: Sink>(
    cx: &Ctx,
    k0: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i0): Ghost<int>,
) -> (r: Option<usize>)
    requires
        indexed(cx.s@, st, cx.idx@),
        st < i0 <= cx.s@.len(),
        out(cx.s@, st, i0),
        bnd(cx.s@, st, i0),
        k0 == cnt(cx.s@, st, i0),
        old(tape).room() >= cx.idx@.len() - k0,
        old(tape).inv(cx.s@),
        old(tape).hist().len() <= i0,
    ensures
        r is Some ==> final(tape).inv(cx.s@),
        r matches Some(k2) ==> final(tape).room() >= cx.idx@.len() - k2,
        r matches Some(k2) ==> 1 <= k2 <= cx.idx@.len() && (cx.idx@[k2 - 1] as int) < cx.s@.len(),
        match elements(cx.s@, i0, depth as nat, old(tape).hist()) {
            Some((t, e)) => r == Some(cnt(cx.s@, st, e) as usize) && cx.idx@[cnt(cx.s@, st, e) - 1] as int
                + 1 == e && final(tape).hist() == t && out(cx.s@, st, e) && bnd(cx.s@, st, e) && e
                <= cx.s@.len(),
            None => r is None,
        },
    decreases depth, cx.s@.len() - i0, 0nat,
{
    let s = cx.s;
    let idx = cx.idx;
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
            g == cx.s@,
            idx@ == cx.idx@,
            indexed(g, st, idx@),
            st < i0 <= i <= g.len(),
            out(g, st, i),
            bnd(g, st, i),
            k == cnt(g, st, i),
            depth > 0,
            tape.room() >= idx@.len() - k,
            tape.inv(g),
            tape.hist().len() <= i,
            t0 == old(tape).hist(),
            elements(g, i0, depth as nat, t0) == elements(g, i, depth as nat, tape.hist()),
        decreases g.len() - i,
    {
        let ghost tb = tape.hist();
        let (k1, e) = match ex2_value::<S, 1>(cx, k, depth - 1, tape, Ghost(st), Ghost(i)) {
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
        }
        let ghost tk = tape.hist();
        if k1 >= idx.len() {
            return None;
        }
        let q = get32(idx, k1) as usize;
        let c = get8(s, q);
        if c == 0x5D {
            tape.push_fast(tok(Kind::ArrEnd));
            return Some(k1 + 1);
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
    cx: &Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i): Ghost<int>,
) -> (r: Option<(usize, usize)>)
    requires
        indexed(cx.s@, st, cx.idx@),
        st < i <= cx.s@.len(),
        out(cx.s@, st, i),
        bnd(cx.s@, st, i),
        k == cnt(cx.s@, st, i),
        old(tape).room() >= cx.idx@.len() - k,
        old(tape).inv(cx.s@),
        old(tape).hist().len() <= i,
    ensures
        r is Some ==> final(tape).inv(cx.s@),
        r matches Some((k2, _)) ==> final(tape).room() >= cx.idx@.len() - k2,
        r matches Some((k2, e2)) ==> 1 <= k2 <= cx.idx@.len() && cx.idx@[k2 - 1] as int + 1 == e2,
        match object(cx.s@, i, depth as nat, old(tape).hist()) {
            Some((t, e)) => r == Some((cnt(cx.s@, st, e) as usize, e as usize)) && final(tape).hist() == t
                && out(cx.s@, st, e) && bnd(cx.s@, st, e) && e <= cx.s@.len(),
            None => r is None,
        },
    decreases depth, cx.s@.len() - i, 2nat,
{
    let s = cx.s;
    let idx = cx.idx;
    let ghost g = s@;
    proof {
        lemma_close(g, st, i);
    }
    if k < idx.len() && get8(s, get32(idx, k) as usize) == 0x7D {
        tape.push_fast(tok(Kind::ObjEnd));
        return Some((k + 1, get32(idx, k) as usize + 1));
    }
    ex2_members(cx, k, depth, tape, Ghost(st), Ghost(i))
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

#[inline(always)]
fn ex2_member<S: Sink>(
    cx: &Ctx,
    k: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i): Ghost<int>,
) -> (r: Option<(usize, usize)>)
    requires
        indexed(cx.s@, st, cx.idx@),
        st < i <= cx.s@.len(),
        out(cx.s@, st, i),
        bnd(cx.s@, st, i),
        k == cnt(cx.s@, st, i),
        depth > 0,
        old(tape).room() >= cx.idx@.len() - k,
        old(tape).inv(cx.s@),
        old(tape).hist().len() <= i,
    ensures
        r is Some ==> final(tape).inv(cx.s@),
        r matches Some((k2, _)) ==> final(tape).room() >= cx.idx@.len() - k2,
        member(cx.s@, i, depth as nat, old(tape).hist()) matches Some((_, e)) ==> i < e <= cx.s@.len(),
        match member(cx.s@, i, depth as nat, old(tape).hist()) {
            Some((t, e)) => if bnd(cx.s@, st, e) {
                r == Some((cnt(cx.s@, st, e) as usize, e as usize)) && final(tape).hist() == t && out(
                    cx.s@,
                    st,
                    e,
                )
            } else {
                r is None
            },
            None => r is None,
        },
    decreases depth, cx.s@.len() - i, 0nat,
{
    let s = cx.s;
    let idx = cx.idx;
    let ghost g = s@;
    proof {
        lemma_close(g, st, i);
        crate::lemmas::lemma_skip_ws_bounds(g, i);
    }
    if k >= idx.len() {
        return None;
    }
    let j = get32(idx, k) as usize;
    if get8(s, j) != 0x22 {
        return None;
    }
    proof {
        lemma_skip(g, st, i);
    }
    let (k1, n, esc) = match tape.scan_str(s, idx, k, Ghost(st)) {
        Some(x) => x,
        None => return None,
    };
    proof {
        crate::lemmas::lemma_string_body_advances(g, j + 1, false);
        lemma_close(g, st, n as int);
    }
    if k1 >= idx.len() {
        return None;
    }
    let cpos = get32(idx, k1) as usize;
    if get8(s, cpos) != 0x3A {
        return None;
    }
    tape.push_str_fast(Tok::new(Kind::Key, esc, (j + 1), (n - 1), NO), s);
    let ghost tkey = tape.hist();
    proof {
        crate::lemmas::lemma_skip_ws_bounds(g, cpos + 1);
        crate::lemmas::lemma_value_advances(g, skip_ws(g, cpos + 1), (depth - 1) as nat, tkey);
    }
    ex2_value::<S, 1>(cx, k1 + 1, depth - 1, tape, Ghost(st), Ghost(cpos + 1))
}

#[allow(unused_variables)]
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
fn ex2_members<S: Sink>(
    cx: &Ctx,
    k0: usize,
    depth: usize,
    tape: &mut S,
    Ghost(st): Ghost<int>,
    Ghost(i0): Ghost<int>,
) -> (r: Option<(usize, usize)>)
    requires
        indexed(cx.s@, st, cx.idx@),
        st < i0 <= cx.s@.len(),
        out(cx.s@, st, i0),
        bnd(cx.s@, st, i0),
        k0 == cnt(cx.s@, st, i0),
        old(tape).room() >= cx.idx@.len() - k0,
        old(tape).inv(cx.s@),
        old(tape).hist().len() <= i0,
    ensures
        r is Some ==> final(tape).inv(cx.s@),
        r matches Some((k2, _)) ==> final(tape).room() >= cx.idx@.len() - k2,
        r matches Some((k2, e2)) ==> 1 <= k2 <= cx.idx@.len() && cx.idx@[k2 - 1] as int + 1 == e2,
        match members(cx.s@, i0, depth as nat, old(tape).hist()) {
            Some((t, e)) => r == Some((cnt(cx.s@, st, e) as usize, e as usize)) && final(tape).hist() == t
                && out(cx.s@, st, e) && bnd(cx.s@, st, e) && e <= cx.s@.len(),
            None => r is None,
        },
    decreases depth, cx.s@.len() - i0, 1nat,
{
    let s = cx.s;
    let idx = cx.idx;
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
            g == cx.s@,
            idx@ == cx.idx@,
            indexed(g, st, idx@),
            st < i0 <= i <= g.len(),
            out(g, st, i),
            bnd(g, st, i),
            k == cnt(g, st, i),
            depth > 0,
            tape.room() >= idx@.len() - k,
            tape.inv(g),
            tape.hist().len() <= i,
            t0 == old(tape).hist(),
            members(g, i0, depth as nat, t0) == members(g, i, depth as nat, tape.hist()),
        decreases g.len() - i,
    {
        let ghost tb = tape.hist();
        let (k2, e) = match ex2_member(cx, k, depth, tape, Ghost(st), Ghost(i)) {
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
            lemma_member_size(g, i, depth as nat, tb);
        }
        let ghost tk = tape.hist();
        if k2 >= idx.len() {
            return None;
        }
        let q = get32(idx, k2) as usize;
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
/// two passes: `index` finds the structural bytes, then the value is read
/// through that index. Falls back to the one-pass parser when the input is
/// too large to index or stage 1 rejects it, so the result is exactly
/// `document(s, true)` either way. `idx` is scratch space.
pub fn parse2_with<S: Sink>(s: &[u8], tape: &mut S, idx: &mut Vec<u32>) -> (r: Result<usize, usize>)
    requires
        old(tape).hist() == Seq::<STok>::empty(),
        old(tape).inv(s@),
    ensures
        r is Ok ==> final(tape).inv(s@),
        match document(s@, true) {
            Some((t, e)) => r is Ok && final(tape).hist() == t && r.unwrap() as int == e && e
                <= s@.len(),
            None => r is Err,
        },
{
    if s.len() > (u32::MAX - 64) as usize {
        return parse_with(s, true, tape);
    }
    let start = if ex_has_lit(s, 0, &[0xEF, 0xBB, 0xBF]) { 3 } else { 0 };
    proof {
        assert([0xEFu8, 0xBB, 0xBF]@ == seq![0xEFu8, 0xBB, 0xBF]);
    }
    let (n, ok, utf8) = crate::index::index(s, start, idx);
    if !ok {
        return parse_with(s, true, tape);
    }
    let idx = slice_prefix(idx.as_slice(), n);
    let ghost g = s@;
    let ghost st = start as int;
    proof {
        assert(positions(g, st, st, st) =~= Seq::<u32>::empty());
        assert(st == bom_end(g));
        crate::lemmas::lemma_skip_ws_bounds(g, st);
        crate::lemmas::lemma_value_advances(g, skip_ws(g, st), MAX_DEPTH as nat, Seq::empty());
    }
    // Every token stands for at least one index entry, so this is room
    // enough for `push_fast`.
    tape.reserve(n);
    let cx = Ctx { s, idx };
    let (k, e) = match ex2_value::<S, 1>(&cx, 0, MAX_DEPTH, tape, Ghost(st), Ghost(st)) {
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
    }
    if k != idx.len() {
        return Err(e);
    }
    proof {
        assert(g.subrange(0, g.len() as int) =~= g);
    }
    if !utf8 {
        return Err(0);
    }
    Ok(e)
}

/// `s[..n]`.
#[inline(always)]
pub fn slice_prefix(s: &[u32], n: usize) -> (r: &[u32])
    requires
        n <= s@.len(),
    ensures
        r@ == s@.subrange(0, n as int),
{
    &s[..n]
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
    proof {
        crate::lemmas::lemma_document_in_bounds(s@, true);
        crate::lemmas::lemma_document_size(s@, true);
        crate::lemmas::lemma_document_links(s@, true);
    }
    tape.clear();
    assert(tape@ =~= Seq::<STok>::empty());
    match parse2_with(s, tape, idx) {
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
    match parse2_with(s, tape, idx) {
        Ok(k) => Ok(k),
        Err(p) => Err(if p > tape.tape.err_pos { p } else { tape.tape.err_pos }),
    }
}

} // verus!

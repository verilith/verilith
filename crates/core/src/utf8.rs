//! UTF-8 (Unicode Table 3-7, well-formed byte sequences): the spec, the
//! local condition that decides it three bytes at a time (what SIMD
//! validators check), and a verified scalar validator.
use crate::prims::get;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// A continuation byte, `10xxxxxx`.
pub open spec fn cont(c: u8) -> bool {
    0x80 <= c <= 0xBF
}

/// Whether `s[i]` exists and lies in `lo..=hi`.
pub open spec fn byte_in(s: Seq<u8>, i: int, lo: u8, hi: u8) -> bool {
    0 <= i < s.len() && lo <= s[i] <= hi
}

/// Length of the well-formed sequence starting at `i`, if there is one.
/// Each arm is one row of Table 3-7.
pub open spec fn utf8_len(s: Seq<u8>, i: int) -> Option<int> {
    let b = s[i];
    if b <= 0x7F {
        Some(1)
    } else if 0xC2 <= b <= 0xDF {
        if byte_in(s, i + 1, 0x80, 0xBF) { Some(2) } else { None }
    } else if 0xE0 <= b <= 0xEF {
        let lo: u8 = if b == 0xE0 { 0xA0 } else { 0x80 };
        let hi: u8 = if b == 0xED { 0x9F } else { 0xBF };
        if byte_in(s, i + 1, lo, hi) && byte_in(s, i + 2, 0x80, 0xBF) { Some(3) } else { None }
    } else if 0xF0 <= b <= 0xF4 {
        let lo: u8 = if b == 0xF0 { 0x90 } else { 0x80 };
        let hi: u8 = if b == 0xF4 { 0x8F } else { 0xBF };
        if byte_in(s, i + 1, lo, hi) && byte_in(s, i + 2, 0x80, 0xBF) && byte_in(s, i + 3, 0x80, 0xBF) {
            Some(4)
        } else {
            None
        }
    } else {
        None
    }
}

/// `s[i..]` is a sequence of well-formed UTF-8 code unit sequences.
pub open spec fn utf8_from(s: Seq<u8>, i: int) -> bool
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        true
    } else {
        match utf8_len(s, i) {
            Some(l) => utf8_from(s, i + l),
            None => false,
        }
    }
}

/// UTF-8 encoding of a Unicode scalar value (`cp <= 0x10FFFF`, not a surrogate).
pub open spec fn utf8_encode(cp: u32) -> Seq<u8> {
    if cp < 0x80 {
        seq![cp as u8]
    } else if cp < 0x800 {
        seq![(0xC0 + cp / 64) as u8, (0x80 + cp % 64) as u8]
    } else if cp < 0x10000 {
        seq![(0xE0 + cp / 4096) as u8, (0x80 + (cp / 64) % 64) as u8, (0x80 + cp % 64) as u8]
    } else {
        seq![
            (0xF0 + cp / 262144) as u8,
            (0x80 + (cp / 4096) % 64) as u8,
            (0x80 + (cp / 64) % 64) as u8,
            (0x80 + cp % 64) as u8,
        ]
    }
}

// ---------------------------------------------------------------------------
// Local condition
// ---------------------------------------------------------------------------

/// What the validator checks at byte `c`, given the three bytes before it
/// (`p1` just before). Each line rules out one way to go wrong.
pub open spec fn loc_ok(p3: u8, p2: u8, p1: u8, c: u8) -> bool {
    let ct = cont(c);
    // A lead byte two or three back still needs this byte.
    let m23 = p2 >= 0xE0 || p3 >= 0xF0;
    &&& !(p1 >= 0xC0 && !ct)  // a lead byte without its continuation
    &&& !(p1 < 0x80 && ct)  // a continuation after ASCII
    &&& (cont(p1) && ct) == m23  // third and fourth bytes, and only those
    &&& !((p1 == 0xC0 || p1 == 0xC1) && ct)  // overlong two-byte form
    &&& !(p1 == 0xE0 && ct && c < 0xA0)  // overlong three-byte form
    &&& !(p1 == 0xED && ct && c >= 0xA0)  // surrogate
    &&& !(p1 == 0xF0 && ct && c < 0x90)  // overlong four-byte form
    &&& !(p1 >= 0xF4 && ct && c >= 0x90)  // above U+10FFFF
    &&& !(p1 >= 0xF5 && ct && c < 0x90)  // not a lead byte at all
}

/// Byte `j` of the text `s[st..]`, or 0 outside it.
pub open spec fn ub(s: Seq<u8>, st: int, j: int) -> u8 {
    if st <= j < s.len() {
        s[j]
    } else {
        0
    }
}

/// `loc_ok` at position `j` of the text `s[st..]`.
pub open spec fn loc(s: Seq<u8>, st: int, j: int) -> bool {
    loc_ok(ub(s, st, j - 3), ub(s, st, j - 2), ub(s, st, j - 1), ub(s, st, j))
}

/// `loc` holds on `[a, b)`.
pub open spec fn all_loc(s: Seq<u8>, st: int, a: int, b: int) -> bool {
    forall|j: int| a <= j < b ==> #[trigger] loc(s, st, j)
}

// ---------------------------------------------------------------------------
// The local checks decide well-formedness
// ---------------------------------------------------------------------------

pub proof fn lemma_all_loc_split(s: Seq<u8>, st: int, a: int, m: int, b: int)
    requires
        a <= m <= b,
    ensures
        all_loc(s, st, a, b) == (all_loc(s, st, a, m) && all_loc(s, st, m, b)),
{
}

/// Where a sequence may start: nothing before `i` still needs a byte at or
/// after `i`. Then the text from `i` is well-formed exactly when every local
/// check from `i` on passes, through three bytes past the end (which catch a
/// sequence the end cuts short).
pub proof fn lemma_utf8_local(s: Seq<u8>, st: int, i: int)
    requires
        0 <= st <= i <= s.len(),
        ub(s, st, i - 1) < 0xC0,
        ub(s, st, i - 2) < 0xE0,
        ub(s, st, i - 3) < 0xF0,
    ensures
        utf8_from(s, i) == all_loc(s, st, i, s.len() as int + 3),
    decreases s.len() - i,
{
    let n = s.len() as int;
    if i >= n {
        assert forall|j: int| i <= j < n + 3 implies #[trigger] loc(s, st, j) by {
            assert(ub(s, st, j) == 0);
            if j - 1 >= i {
                assert(ub(s, st, j - 1) == 0);
            }
            if j - 2 >= i {
                assert(ub(s, st, j - 2) == 0);
            }
            if j - 3 >= i {
                assert(ub(s, st, j - 3) == 0);
            }
        }
        return;
    }
    let b0 = s[i];
    assert(ub(s, st, i) == b0);
    if b0 < 0x80 {
        assert(loc(s, st, i));
        lemma_utf8_local(s, st, i + 1);
        lemma_all_loc_split(s, st, i, i + 1, n + 3);
    } else if b0 < 0xC2 || b0 >= 0xF5 {
        // A continuation, C0, C1 or F5..FF cannot start a sequence.
        if b0 < 0xC0 {
            assert(!loc(s, st, i));
        } else {
            assert(!loc(s, st, i + 1));
        }
        assert(!utf8_from(s, i));
    } else if b0 < 0xE0 {
        let c1 = ub(s, st, i + 1);
        assert(loc(s, st, i));
        assert(loc(s, st, i + 1) == (i + 1 < n && cont(s[i + 1])));
        if i + 1 < n && cont(s[i + 1]) {
            assert(c1 == s[i + 1]);
            lemma_utf8_local(s, st, i + 2);
            lemma_all_loc_split(s, st, i, i + 2, n + 3);
            assert(all_loc(s, st, i, i + 2) == (loc(s, st, i) && loc(s, st, i + 1)));
        } else {
            assert(!all_loc(s, st, i, n + 3));
        }
    } else if b0 < 0xF0 {
        let lo: u8 = if b0 == 0xE0 { 0xA0 } else { 0x80 };
        let hi: u8 = if b0 == 0xED { 0x9F } else { 0xBF };
        assert(loc(s, st, i));
        assert(loc(s, st, i + 1) == (i + 1 < n && lo <= s[i + 1] <= hi));
        if i + 1 < n && lo <= s[i + 1] <= hi {
            assert(loc(s, st, i + 2) == (i + 2 < n && cont(s[i + 2])));
            if i + 2 < n && cont(s[i + 2]) {
                lemma_utf8_local(s, st, i + 3);
                lemma_all_loc_split(s, st, i, i + 3, n + 3);
                assert(all_loc(s, st, i, i + 3) == (loc(s, st, i) && loc(s, st, i + 1) && loc(s, st, i + 2)));
            } else {
                assert(!all_loc(s, st, i, n + 3));
            }
        } else {
            assert(!all_loc(s, st, i, n + 3));
        }
    } else {
        let lo: u8 = if b0 == 0xF0 { 0x90 } else { 0x80 };
        let hi: u8 = if b0 == 0xF4 { 0x8F } else { 0xBF };
        assert(loc(s, st, i));
        assert(loc(s, st, i + 1) == (i + 1 < n && lo <= s[i + 1] <= hi));
        if i + 1 < n && lo <= s[i + 1] <= hi {
            assert(loc(s, st, i + 2) == (i + 2 < n && cont(s[i + 2])));
            if i + 2 < n && cont(s[i + 2]) {
                assert(loc(s, st, i + 3) == (i + 3 < n && cont(s[i + 3])));
                if i + 3 < n && cont(s[i + 3]) {
                    lemma_utf8_local(s, st, i + 4);
                    lemma_all_loc_split(s, st, i, i + 4, n + 3);
                    assert(all_loc(s, st, i, i + 4) == (loc(s, st, i) && loc(s, st, i + 1) && loc(s, st, i + 2)
                        && loc(s, st, i + 3)));
                } else {
                    assert(!all_loc(s, st, i, n + 3));
                }
            } else {
                assert(!all_loc(s, st, i, n + 3));
            }
        } else {
            assert(!all_loc(s, st, i, n + 3));
        }
    }
}

// ---------------------------------------------------------------------------
// Scalar validator
// ---------------------------------------------------------------------------

/// `ub` as code.
#[inline(always)]
fn ex_ub(s: &[u8], st: usize, j: usize, back: usize) -> (r: u8)
    requires
        st <= s@.len(),
        back <= 3,
    ensures
        r == ub(s@, st as int, j - back),
{
    if j >= back && j - back >= st && j - back < s.len() {
        get(s, j - back)
    } else {
        0
    }
}

/// `loc` as code, for positions where the four bytes may cross the ends.
#[inline(always)]
fn ex_loc(s: &[u8], st: usize, j: usize) -> (r: bool)
    requires
        st <= s@.len(),
    ensures
        r == loc(s@, st as int, j as int),
{
    let p3 = ex_ub(s, st, j, 3);
    let p2 = ex_ub(s, st, j, 2);
    let p1 = ex_ub(s, st, j, 1);
    let c = ex_ub(s, st, j, 0);
    let ct = 0x80 <= c && c <= 0xBF;
    let m23 = p2 >= 0xE0 || p3 >= 0xF0;
    !(p1 >= 0xC0 && !ct) && !(p1 < 0x80 && ct) && ((0x80 <= p1 && p1 <= 0xBF && ct) == m23) && !((p1
        == 0xC0 || p1 == 0xC1) && ct) && !(p1 == 0xE0 && ct && c < 0xA0) && !(p1 == 0xED && ct && c
        >= 0xA0) && !(p1 == 0xF0 && ct && c < 0x90) && !(p1 >= 0xF4 && ct && c >= 0x90) && !(p1
        >= 0xF5 && ct && c < 0x90)
}

/// `loc` on `[a, b)`, one byte at a time.
pub fn ex_all_loc(s: &[u8], st: usize, a: usize, b: usize) -> (r: bool)
    requires
        st <= s@.len(),
        a <= b,
    ensures
        r == all_loc(s@, st as int, a as int, b as int),
{
    let mut j = a;
    while j < b
        invariant
            st <= s@.len(),
            a <= j <= b,
            all_loc(s@, st as int, a as int, j as int),
        decreases b - j,
    {
        if !ex_loc(s, st, j) {
            return false;
        }
        j = j + 1;
    }
    true
}

/// `loc` on the three positions past the end, where it says that no
/// sequence is cut short.
#[inline(always)]
pub fn ex_tail(s: &[u8], st: usize) -> (r: bool)
    requires
        st <= s@.len(),
    ensures
        r == all_loc(s@, st as int, s@.len() as int, s@.len() as int + 3),
{
    let n = s.len();
    let p1 = ex_ub(s, st, n, 1);
    let p2 = ex_ub(s, st, n, 2);
    let p3 = ex_ub(s, st, n, 3);
    proof {
        let g = s@;
        let si = st as int;
        let ni = n as int;
        assert(ub(g, si, ni) == 0 && ub(g, si, ni + 1) == 0 && ub(g, si, ni + 2) == 0);
        assert(loc(g, si, ni) == (p1 < 0xC0 && p2 < 0xE0 && p3 < 0xF0));
        assert(loc(g, si, ni + 1) == (p1 < 0xE0 && p2 < 0xF0));
        assert(loc(g, si, ni + 2) == (p1 < 0xF0));
        assert(all_loc(g, si, ni, ni + 3) == (loc(g, si, ni) && loc(g, si, ni + 1) && loc(g, si, ni + 2)));
    }
    p1 < 0xC0 && p2 < 0xE0 && p3 < 0xF0
}

/// Whether `s[st..]` is well-formed UTF-8, one byte at a time.
pub fn utf8_valid_scalar(s: &[u8], st: usize) -> (r: bool)
    requires
        st <= s@.len(),
    ensures
        r == utf8_from(s@, st as int),
{
    proof {
        lemma_utf8_local(s@, st as int, st as int);
        lemma_all_loc_split(s@, st as int, st as int, s@.len() as int, s@.len() as int + 3);
    }
    ex_all_loc(s, st, st, s.len()) && ex_tail(s, st)
}

} // verus!

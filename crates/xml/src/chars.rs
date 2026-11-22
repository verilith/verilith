//! Characters (XML 1.0 Fifth Edition, §2.2 and §2.3): what may appear in a
//! document at all (`Char`), what may start and continue a `Name`, and the
//! verified code that decides each.
//!
//! The text is UTF-8. A code point is read from the bytes with
//! verilith-core's `utf8_len` (Unicode Table 3-7), so overlong forms,
//! surrogates and values above U+10FFFF are never code points here.
#[cfg(verus_keep_ghost)]
pub use verilith_core::utf8::{byte_in, utf8_len};
use verilith_core::prims::get;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// S ::= (#x20 | #x9 | #xD | #xA)+
pub open spec fn is_ws(c: u8) -> bool {
    c == 0x20 || c == 0x09 || c == 0x0D || c == 0x0A
}

/// The value of the well-formed sequence of `l` bytes at `i`.
pub open spec fn cp_val(s: Seq<u8>, i: int, l: int) -> int {
    if l == 1 {
        s[i] as int
    } else if l == 2 {
        (s[i] as int - 0xC0) * 64 + (s[i + 1] as int - 0x80)
    } else if l == 3 {
        (s[i] as int - 0xE0) * 4096 + (s[i + 1] as int - 0x80) * 64 + (s[i + 2] as int - 0x80)
    } else {
        (s[i] as int - 0xF0) * 262144 + (s[i + 1] as int - 0x80) * 4096 + (s[i + 2] as int - 0x80) * 64
            + (s[i + 3] as int - 0x80)
    }
}

/// The code point at `i` and the length of its encoding, if a well-formed
/// sequence starts there.
pub open spec fn cp_at(s: Seq<u8>, i: int) -> Option<(int, int)> {
    if !(0 <= i < s.len()) {
        None
    } else {
        match utf8_len(s, i) {
            None => None,
            Some(l) => Some((cp_val(s, i, l), l)),
        }
    }
}

/// Char ::= #x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF]
pub open spec fn is_char(c: int) -> bool {
    c == 0x9 || c == 0xA || c == 0xD || (0x20 <= c <= 0xD7FF) || (0xE000 <= c <= 0xFFFD) || (0x10000
        <= c <= 0x10FFFF)
}

/// A byte that is never part of an XML 1.0 document: the C0 controls other
/// than tab, line feed and carriage return.
pub open spec fn bad_byte(c: u8) -> bool {
    c < 0x20 && c != 0x09 && c != 0x0A && c != 0x0D
}

/// The well-formed sequence of `l` bytes at `i` encodes a `Char`. Among
/// the code points UTF-8 can encode, the ones that are not are the C0
/// controls (one byte) and U+FFFE and U+FFFF (`EF BF BE`, `EF BF BF`).
pub open spec fn char_seq_ok(s: Seq<u8>, i: int, l: int) -> bool {
    if l == 1 {
        !bad_byte(s[i])
    } else if l == 3 {
        !(s[i] == 0xEF && s[i + 1] == 0xBF && s[i + 2] >= 0xBE)
    } else {
        true
    }
}

/// `s[i..]` is well-formed UTF-8 and every code point in it is a `Char`.
pub open spec fn chars_from(s: Seq<u8>, i: int) -> bool
    decreases s.len() - i,
{
    if !(0 <= i < s.len()) {
        true
    } else {
        match utf8_len(s, i) {
            None => false,
            Some(l) => if i + l <= s.len() {
                char_seq_ok(s, i, l) && chars_from(s, i + l)
            } else {
                false
            },
        }
    }
}

/// The whole document is a sequence of `Char`s in UTF-8 (§2.2, §4.3.3).
pub open spec fn doc_chars(s: Seq<u8>) -> bool {
    chars_from(s, 0)
}

/// NameStartChar ::= ":" | [A-Z] | "_" | [a-z] | [#xC0-#xD6] | [#xD8-#xF6]
///   | [#xF8-#x2FF] | [#x370-#x37D] | [#x37F-#x1FFF] | [#x200C-#x200D]
///   | [#x2070-#x218F] | [#x2C00-#x2FEF] | [#x3001-#xD7FF] | [#xF900-#xFDCF]
///   | [#xFDF0-#xFFFD] | [#x10000-#xEFFFF]
pub open spec fn name_start_cp(c: int) -> bool {
    c == 0x3A || (0x41 <= c <= 0x5A) || c == 0x5F || (0x61 <= c <= 0x7A) || (0xC0 <= c <= 0xD6) || (0xD8
        <= c <= 0xF6) || (0xF8 <= c <= 0x2FF) || (0x370 <= c <= 0x37D) || (0x37F <= c <= 0x1FFF) || (0x200C
        <= c <= 0x200D) || (0x2070 <= c <= 0x218F) || (0x2C00 <= c <= 0x2FEF) || (0x3001 <= c <= 0xD7FF)
        || (0xF900 <= c <= 0xFDCF) || (0xFDF0 <= c <= 0xFFFD) || (0x10000 <= c <= 0xEFFFF)
}

/// NameChar ::= NameStartChar | "-" | "." | [0-9] | #xB7 | [#x0300-#x036F]
///   | [#x203F-#x2040]
pub open spec fn name_cp(c: int) -> bool {
    name_start_cp(c) || c == 0x2D || c == 0x2E || (0x30 <= c <= 0x39) || c == 0xB7 || (0x300 <= c
        <= 0x36F) || (0x203F <= c <= 0x2040)
}

/// The length of the sequence at `i`, or 1 where none is well-formed.
pub open spec fn cp_len(s: Seq<u8>, i: int) -> int {
    match cp_at(s, i) {
        Some((_, l)) => l,
        None => 1,
    }
}

pub open spec fn name_start_at(s: Seq<u8>, i: int) -> bool {
    match cp_at(s, i) {
        Some((c, _)) => name_start_cp(c),
        None => false,
    }
}

pub open spec fn name_char_at(s: Seq<u8>, i: int) -> bool {
    match cp_at(s, i) {
        Some((c, _)) => name_cp(c),
        None => false,
    }
}

/// The end of the run of `NameChar`s at `i`. (The guard `i + cp_len <=
/// s.len()` always holds where a code point is read; it is there so that
/// termination is syntactic. `lemma_cp_in_bounds` proves it.)
pub open spec fn name_rest(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if 0 <= i && i + cp_len(s, i) <= s.len() && name_char_at(s, i) {
        name_rest(s, i + cp_len(s, i))
    } else {
        i
    }
}

/// Name ::= NameStartChar (NameChar)*
///
/// The end of the name at `i`, or `i` if no name starts there.
pub open spec fn name_end(s: Seq<u8>, i: int) -> int {
    if name_start_at(s, i) {
        name_rest(s, i + cp_len(s, i))
    } else {
        i
    }
}

/// Nmtoken ::= (NameChar)+ : its end, or `i` if there is none.
pub open spec fn nmtoken_end(s: Seq<u8>, i: int) -> int {
    name_rest(s, i)
}

/// PubidChar ::= #x20 | #xD | #xA | [a-zA-Z0-9] | [-'()+,./:=?;!*#@$_%]
pub open spec fn pubid_char(c: u8) -> bool {
    c == 0x20 || c == 0x0D || c == 0x0A || (0x61 <= c <= 0x7A) || (0x41 <= c <= 0x5A) || (0x30 <= c
        <= 0x39) || c == 0x2D || c == 0x27 || c == 0x28 || c == 0x29 || c == 0x2B || c == 0x2C || c == 0x2E
        || c == 0x2F || c == 0x3A || c == 0x3D || c == 0x3F || c == 0x3B || c == 0x21 || c == 0x2A || c
        == 0x23 || c == 0x40 || c == 0x24 || c == 0x5F || c == 0x25
}

// ---------------------------------------------------------------------------
// Facts
// ---------------------------------------------------------------------------

/// A code point read at `i` lies within the input, and is at least one
/// byte long.
pub proof fn lemma_cp_in_bounds(s: Seq<u8>, i: int)
    ensures
        1 <= cp_len(s, i) <= 4,
        cp_at(s, i) is Some ==> 0 <= i && i + cp_len(s, i) <= s.len(),
{
}

/// `name_rest` moves forward and stays within the input.
pub proof fn lemma_name_rest(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= name_rest(s, i) <= s.len(),
    decreases s.len() - i,
{
    lemma_cp_in_bounds(s, i);
    if 0 <= i && i + cp_len(s, i) <= s.len() && name_char_at(s, i) {
        lemma_name_rest(s, i + cp_len(s, i));
    }
}

pub proof fn lemma_name_end(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= name_end(s, i) <= s.len(),
        name_end(s, i) > i <==> name_start_at(s, i),
{
    lemma_cp_in_bounds(s, i);
    if name_start_at(s, i) {
        lemma_name_rest(s, i + cp_len(s, i));
    }
}

// ---------------------------------------------------------------------------
// Tables
// ---------------------------------------------------------------------------

/// Per byte: bit 0 for an ASCII `NameStartChar`, bit 1 for an ASCII
/// `NameChar`, bit 2 for a byte of 0x80 or more (decode it), 0 otherwise.
pub const NAMECH: [u8; 256] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  // 00
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  // 10
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0,  // 20: - .
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 0, 0, 0, 0, 0,  // 30: 0-9 :
    0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,  // 40: A-O
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 0, 0, 0, 3,  // 50: P-Z _
    0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,  // 60: a-o
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 0, 0, 0, 0,  // 70: p-z
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
];

/// What `NAMECH` should hold for byte `c`.
pub open spec fn namech_of(c: u8) -> u8 {
    if c >= 0x80 {
        4
    } else if name_start_cp(c as int) {
        3
    } else if name_cp(c as int) {
        2
    } else {
        0
    }
}

pub open spec fn namech_ok_below(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        NAMECH@[n - 1] == namech_of((n - 1) as u8) && namech_ok_below((n - 1) as nat)
    }
}

proof fn lemma_namech_below(n: nat, c: u8)
    requires
        namech_ok_below(n),
        (c as nat) < n,
    ensures
        NAMECH@[c as int] == namech_of(c),
    decreases n,
{
    if c as nat != n - 1 {
        lemma_namech_below((n - 1) as nat, c);
    }
}

/// `NAMECH[c]`, checked against `namech_of` for all 256 bytes by
/// evaluation.
#[inline(always)]
pub fn namech(c: u8) -> (r: u8)
    ensures
        r == namech_of(c),
{
    proof {
        assert(namech_ok_below(256)) by (compute_only);
        lemma_namech_below(256, c);
    }
    NAMECH[c as usize]
}

// ---------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------

/// `cp_at` for a sequence that starts with a byte of 0x80 or more.
#[inline(never)]
pub fn ex_cp_at_hi(s: &[u8], i: usize) -> (r: Option<(u32, usize)>)
    requires
        i < s@.len(),
        s@[i as int] >= 0x80,
    ensures
        match cp_at(s@, i as int) {
            Some((c, l)) => r == Some((c as u32, l as usize)) && 0 <= c <= 0x10FFFF,
            None => r is None,
        },
{
    let n = s.len();
    let b = get(s, i);
    if 0xC2 <= b && b <= 0xDF {
        if n - i > 1 {
            let c1 = get(s, i + 1);
            if 0x80 <= c1 && c1 <= 0xBF {
                let v = (b - 0xC0) as u32 * 64 + (c1 - 0x80) as u32;
                return Some((v, 2));
            }
        }
        None
    } else if 0xE0 <= b && b <= 0xEF {
        let lo: u8 = if b == 0xE0 { 0xA0 } else { 0x80 };
        let hi: u8 = if b == 0xED { 0x9F } else { 0xBF };
        if n - i > 2 {
            let c1 = get(s, i + 1);
            let c2 = get(s, i + 2);
            if lo <= c1 && c1 <= hi && 0x80 <= c2 && c2 <= 0xBF {
                let v = (b - 0xE0) as u32 * 4096 + (c1 - 0x80) as u32 * 64 + (c2 - 0x80) as u32;
                return Some((v, 3));
            }
        }
        None
    } else if 0xF0 <= b && b <= 0xF4 {
        let lo: u8 = if b == 0xF0 { 0x90 } else { 0x80 };
        let hi: u8 = if b == 0xF4 { 0x8F } else { 0xBF };
        if n - i > 3 {
            let c1 = get(s, i + 1);
            let c2 = get(s, i + 2);
            let c3 = get(s, i + 3);
            if lo <= c1 && c1 <= hi && 0x80 <= c2 && c2 <= 0xBF && 0x80 <= c3 && c3 <= 0xBF {
                let v = (b - 0xF0) as u32 * 262144 + (c1 - 0x80) as u32 * 4096 + (c2 - 0x80) as u32 * 64 + (c3
                    - 0x80) as u32;
                return Some((v, 4));
            }
        }
        None
    } else {
        None
    }
}

#[inline(always)]
pub fn ex_name_start_cp(c: u32) -> (r: bool)
    ensures
        r == name_start_cp(c as int),
{
    c == 0x3A || (0x41 <= c && c <= 0x5A) || c == 0x5F || (0x61 <= c && c <= 0x7A) || (0xC0 <= c && c
        <= 0xD6) || (0xD8 <= c && c <= 0xF6) || (0xF8 <= c && c <= 0x2FF) || (0x370 <= c && c <= 0x37D)
        || (0x37F <= c && c <= 0x1FFF) || (0x200C <= c && c <= 0x200D) || (0x2070 <= c && c <= 0x218F) || (
    0x2C00 <= c && c <= 0x2FEF) || (0x3001 <= c && c <= 0xD7FF) || (0xF900 <= c && c <= 0xFDCF) || (0xFDF0
        <= c && c <= 0xFFFD) || (0x10000 <= c && c <= 0xEFFFF)
}

#[inline(always)]
pub fn ex_name_cp(c: u32) -> (r: bool)
    ensures
        r == name_cp(c as int),
{
    ex_name_start_cp(c) || c == 0x2D || c == 0x2E || (0x30 <= c && c <= 0x39) || c == 0xB7 || (0x300 <= c
        && c <= 0x36F) || (0x203F <= c && c <= 0x2040)
}

/// `name_rest` from `i`: ASCII by table, other code points decoded.
#[inline(always)]
pub fn ex_name_rest(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s@.len(),
    ensures
        r == name_rest(s@, i as int),
        i <= r <= s@.len(),
{
    let n = s.len();
    let mut j = i;
    while j < n
        invariant
            i <= j <= n,
            n == s@.len(),
            name_rest(s@, j as int) == name_rest(s@, i as int),
        decreases n - j,
    {
        let b = get(s, j);
        let t = namech(b);
        if t == 2 || t == 3 {
            proof {
                assert(cp_at(s@, j as int) == Some((b as int, 1int)));
            }
            j = j + 1;
        } else if t == 4 {
            match ex_cp_at_hi(s, j) {
                Some((c, l)) => {
                    if ex_name_cp(c) {
                        proof {
                            lemma_cp_in_bounds(s@, j as int);
                        }
                        j = j + l;
                    } else {
                        return j;
                    }
                },
                None => {
                    return j;
                },
            }
        } else {
            proof {
                assert(cp_at(s@, j as int) == Some((b as int, 1int)));
                assert(!name_cp(b as int));
            }
            return j;
        }
    }
    j
}

/// `name_end`: the end of the `Name` at `i`, or `i` if none starts there.
#[inline(always)]
pub fn ex_name_end(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s@.len(),
    ensures
        r == name_end(s@, i as int),
        i <= r <= s@.len(),
        r > i <==> name_start_at(s@, i as int),
{
    proof {
        lemma_name_end(s@, i as int);
    }
    if i >= s.len() {
        return i;
    }
    let b = get(s, i);
    let t = namech(b);
    if t == 3 {
        proof {
            assert(cp_at(s@, i as int) == Some((b as int, 1int)));
        }
        ex_name_rest(s, i + 1)
    } else if t == 4 {
        match ex_cp_at_hi(s, i) {
            Some((c, l)) => {
                if ex_name_start_cp(c) {
                    proof {
                        lemma_cp_in_bounds(s@, i as int);
                    }
                    ex_name_rest(s, i + l)
                } else {
                    i
                }
            },
            None => i,
        }
    } else {
        proof {
            assert(cp_at(s@, i as int) == Some((b as int, 1int)));
        }
        i
    }
}

/// `nmtoken_end`.
#[inline(always)]
pub fn ex_nmtoken_end(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s@.len(),
    ensures
        r == nmtoken_end(s@, i as int),
        i <= r <= s@.len(),
{
    ex_name_rest(s, i)
}

#[inline(always)]
pub fn ex_pubid_char(c: u8) -> (r: bool)
    ensures
        r == pubid_char(c),
{
    c == 0x20 || c == 0x0D || c == 0x0A || (0x61 <= c && c <= 0x7A) || (0x41 <= c && c <= 0x5A) || (0x30
        <= c && c <= 0x39) || c == 0x2D || c == 0x27 || c == 0x28 || c == 0x29 || c == 0x2B || c == 0x2C || c
        == 0x2E || c == 0x2F || c == 0x3A || c == 0x3D || c == 0x3F || c == 0x3B || c == 0x21 || c == 0x2A
        || c == 0x23 || c == 0x40 || c == 0x24 || c == 0x5F || c == 0x25
}

#[inline(always)]
pub fn ex_is_ws(c: u8) -> (r: bool)
    ensures
        r == is_ws(c),
{
    c == 0x20 || c == 0x09 || c == 0x0D || c == 0x0A
}

/// `chars_from` passes over one-byte characters.
pub proof fn lemma_chars_skip(s: Seq<u8>, i: int, k: int)
    requires
        0 <= i,
        0 <= k,
        i + k <= s.len(),
        forall|q: int| i <= q < i + k ==> !crate::scan::char_stop(#[trigger] s[q]),
    ensures
        chars_from(s, i) == chars_from(s, i + k),
    decreases k,
{
    if k > 0 {
        assert(!crate::scan::char_stop(s[i]));
        lemma_chars_skip(s, i + 1, k - 1);
    }
}

/// `doc_chars`, one code point at a time, with sixteen ASCII bytes at a
/// time where they are all characters.
pub fn ex_doc_chars(s: &[u8]) -> (r: bool)
    ensures
        r == doc_chars(s@),
{
    let n = s.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            chars_from(s@, i as int) == doc_chars(s@),
        decreases n - i,
    {
        if n - i >= 16 {
            let k = crate::scan::char_run16(s, i);
            proof {
                lemma_chars_skip(s@, i as int, k as int);
            }
            if k == 16 {
                i = i + 16;
                continue;
            }
            i = i + k;
        }
        let b = get(s, i);
        if b < 0x80 {
            if b < 0x20 && b != 0x09 && b != 0x0A && b != 0x0D {
                return false;
            }
            i = i + 1;
        } else {
            match ex_cp_at_hi(s, i) {
                None => {
                    return false;
                },
                Some((c, l)) => {
                    proof {
                        lemma_cp_in_bounds(s@, i as int);
                    }
                    if l == 3 && c >= 0xFFFE {
                        proof {
                            assert(s@[i as int] == 0xEF && s@[i as int + 1] == 0xBF && s@[i as int + 2] >= 0xBE);
                        }
                        return false;
                    }
                    proof {
                        if l == 3 {
                            assert(!(s@[i as int] == 0xEF && s@[i as int + 1] == 0xBF && s@[i as int + 2] >= 0xBE));
                        }
                    }
                    i = i + l;
                },
            }
        }
    }
    true
}

} // verus!

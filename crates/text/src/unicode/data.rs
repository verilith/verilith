//! The Unicode data the normalization spec is defined over: the generated
//! tables seen as uninterpreted functions, the per-character properties
//! read from them, and the facts about the data that the proofs rely on.
//!
//! Trusted here: each `*_at` accessor returns its table's entry (each is
//! one array read), and the `axiom_*` facts, which tests/unicode_data.rs
//! checks for every code point.
use super::tables::*;
use vstd::prelude::*;

verus! {

pub uninterp spec fn trie_index(i: int) -> u16;

pub uninterp spec fn trie_data(i: int) -> u32;

pub uninterp spec fn rec_ccc(r: int) -> u8;

pub uninterp spec fn rec_fd(r: int) -> u32;

pub uninterp spec fn rec_kd(r: int) -> u32;

pub uninterp spec fn rec_comp(r: int) -> u32;

pub uninterp spec fn pool(i: int) -> u32;

pub uninterp spec fn comp_second(i: int) -> u32;

pub uninterp spec fn comp_result(i: int) -> u32;

macro_rules! accessor {
    ($name:ident, $table:ident, $len:ident, $spec:ident, $ty:ty) => {
        verus! {
            #[verifier::external_body]
            #[inline(always)]
            pub fn $name(i: usize) -> (r: $ty)
                requires
                    i < $len,
                ensures
                    r == $spec(i as int),
            {
                // SAFETY: `i < $len`, the length of the table, is a precondition.
                unsafe { *$table.get_unchecked(i) }
            }
        }
    };
}

accessor!(trie_index_at, TRIE_INDEX, TRIE_INDEX_LEN, trie_index, u16);
accessor!(trie_data_at, TRIE_DATA, TRIE_DATA_LEN, trie_data, u32);
accessor!(rec_ccc_at, REC_CCC, REC_CCC_LEN, rec_ccc, u8);
accessor!(rec_fd_at, REC_FD, REC_FD_LEN, rec_fd, u32);
accessor!(rec_kd_at, REC_KD, REC_KD_LEN, rec_kd, u32);
accessor!(rec_comp_at, REC_COMP, REC_COMP_LEN, rec_comp, u32);
accessor!(pool_at, POOL, POOL_LEN, pool, u32);
accessor!(comp_second_at, COMP_SECOND, COMP_SECOND_LEN, comp_second, u32);
accessor!(comp_result_at, COMP_RESULT, COMP_RESULT_LEN, comp_result, u32);

// ---------------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------------

pub open spec fn is_scalar(c: u32) -> bool {
    c <= 0x10FFFF && !(0xD800 <= c <= 0xDFFF)
}

pub open spec fn scalars(cs: Seq<u32>) -> bool {
    forall|i: int| 0 <= i < cs.len() ==> is_scalar(#[trigger] cs[i])
}

/// The trie word of `c`: its flags and record, `record | flags << 16`.
pub open spec fn tword(c: u32) -> u32 {
    if c < TRIE_LIMIT {
        let i = trie_index((c >> TRIE_SHIFT) as int) as int + (c & 63) as int;
        if i < TRIE_DATA_LEN && (trie_data(i) & 0xFFFF) < REC_CCC_LEN {
            trie_data(i)
        } else {
            PLAIN_WORD
        }
    } else {
        PLAIN_WORD
    }
}

/// The record of `c`.
pub open spec fn rec(c: u32) -> int {
    (tword(c) & 0xFFFF) as int
}

pub open spec fn ccc(c: u32) -> u8 {
    rec_ccc(rec(c))
}

pub open spec fn flags(c: u32) -> u16 {
    (tword(c) >> 16) as u16
}

pub open spec fn has_flag(c: u32, f: u16) -> bool {
    flags(c) & f != 0
}

/// `c` may be the second character of a composition pair.
pub open spec fn second(c: u32) -> bool {
    has_flag(c, FLAG_SECOND)
}

pub open spec fn fast_flag(compose: bool, compat: bool) -> u16 {
    if compose {
        if compat { FLAG_FAST_NFKC } else { FLAG_FAST_NFC }
    } else {
        if compat { FLAG_FAST_NFKD } else { FLAG_FAST_NFD }
    }
}

pub open spec fn bb_flag(compose: bool, compat: bool) -> u16 {
    if compose {
        if compat { FLAG_BB_NFKC } else { FLAG_BB_NFC }
    } else {
        if compat { FLAG_BB_NFKD } else { FLAG_BB_NFD }
    }
}

pub const S_BASE: u32 = 0xAC00;
pub const L_BASE: u32 = 0x1100;
pub const V_BASE: u32 = 0x1161;
pub const T_BASE: u32 = 0x11A7;
pub const L_COUNT: u32 = 19;
pub const V_COUNT: u32 = 21;
pub const T_COUNT: u32 = 28;
pub const N_COUNT: u32 = 588;
pub const S_COUNT: u32 = 11172;

pub open spec fn is_hangul(c: u32) -> bool {
    S_BASE <= c < S_BASE + S_COUNT
}

pub open spec fn hangul_decomp(c: u32) -> Seq<u32> {
    let s = (c - S_BASE) as u32;
    let l = (L_BASE + s / N_COUNT) as u32;
    let v = (V_BASE + (s % N_COUNT) / T_COUNT) as u32;
    let t = (T_BASE + s % T_COUNT) as u32;
    if t == T_BASE {
        seq![l, v]
    } else {
        seq![l, v, t]
    }
}

/// The `(offset << 5) | len` word of `c`'s full decomposition.
pub open spec fn dword(c: u32, compat: bool) -> u32 {
    if compat {
        rec_kd(rec(c))
    } else {
        rec_fd(rec(c))
    }
}

pub open spec fn dword_ok(w: u32) -> bool {
    (w & 31) != 0 && (w >> 5) as int + (w & 31) as int <= POOL_LEN
}

/// Full canonical (or, with `compat`, compatibility) decomposition.
pub open spec fn decomp(c: u32, compat: bool) -> Seq<u32> {
    if is_hangul(c) {
        hangul_decomp(c)
    } else {
        let w = dword(c, compat);
        if dword_ok(w) {
            Seq::new((w & 31) as nat, |k: int| pool((w >> 5) as int + k) & 0xFFFFFF)
        } else {
            seq![c]
        }
    }
}

/// The composition pairs with first character `a` lie in `start..end`.
pub open spec fn comp_find(i: int, end: int, b: u32) -> Option<u32>
    decreases end - i,
{
    if i >= end || end > COMP_SECOND_LEN {
        None
    } else if comp_second(i) == b {
        Some(comp_result(i))
    } else {
        comp_find(i + 1, end, b)
    }
}

/// The primary composite of `a` and `b`, if there is one.
pub open spec fn comp(a: u32, b: u32) -> Option<u32> {
    if L_BASE <= a < L_BASE + L_COUNT && V_BASE <= b < V_BASE + V_COUNT {
        Some((S_BASE + ((a - L_BASE) * (V_COUNT as int) + (b - V_BASE)) * (T_COUNT as int)) as u32)
    } else if is_hangul(a) && ((a - S_BASE) as u32) % T_COUNT == 0 && T_BASE < b < T_BASE + T_COUNT {
        Some((a + (b - T_BASE)) as u32)
    } else {
        let w = rec_comp(rec(a));
        comp_find((w >> 8) as int, (w >> 8) as int + (w & 255) as int, b)
    }
}

pub proof fn lemma_tword(c: u32)
    ensures
        (tword(c) & 0xFFFF) < REC_CCC_LEN,
{
    assert((PLAIN_WORD & 0xFFFF) == 0) by (compute_only);
}

pub proof fn lemma_decomp_nonempty(c: u32, compat: bool)
    ensures
        decomp(c, compat).len() >= 1,
{
}

// ---------------------------------------------------------------------------
// Facts about the data, checked for every code point by tests/unicode_data.rs
// ---------------------------------------------------------------------------

/// Decompositions of scalars are scalars.
pub axiom fn axiom_decomp_scalar(c: u32, compat: bool)
    requires
        is_scalar(c),
    ensures
        scalars(decomp(c, compat));

/// Only a character flagged `second` is the second of a composition pair,
/// and composites are scalar starters.
pub axiom fn axiom_comp(a: u32, b: u32)
    requires
        comp(a, b) is Some,
    ensures
        second(b),
        is_scalar(comp(a, b)->0),
        ccc(comp(a, b)->0) == 0;

/// A character flagged as a boundary starts its decomposition with a
/// starter that, when composing, is never the second of a pair.
pub axiom fn axiom_bb(c: u32, compose: bool, compat: bool)
    requires
        is_scalar(c),
        has_flag(c, bb_flag(compose, compat)),
    ensures
        ccc(decomp(c, compat)[0]) == 0,
        compose ==> !second(decomp(c, compat)[0]);

/// Each pool entry carries the combining class of its character.
pub axiom fn axiom_pool(i: int)
    requires
        0 <= i < POOL_LEN,
    ensures
        (pool(i) >> 24) as u8 == ccc(pool(i) & 0xFFFFFF);

/// Conjoining jamo are starters.
pub axiom fn axiom_jamo(c: u32)
    requires
        L_BASE <= c < L_BASE + L_COUNT || V_BASE <= c < V_BASE + V_COUNT || T_BASE <= c < T_BASE + T_COUNT,
    ensures
        ccc(c) == 0;

/// Every block of the trie lies inside `TRIE_DATA`, and every entry names
/// a record.
pub axiom fn axiom_trie(j: int)
    requires
        0 <= j < TRIE_INDEX_LEN,
    ensures
        trie_index(j) + 64 <= TRIE_DATA_LEN,
        forall|k: int| 0 <= k < 64 ==> (#[trigger] trie_data(trie_index(j) + k) & 0xFFFF) < REC_CCC_LEN;

/// ASCII characters are fast in every form.
pub axiom fn axiom_ascii(c: u32, compose: bool, compat: bool)
    requires
        c < 0x80,
    ensures
        has_flag(c, fast_flag(compose, compat));

/// Below this code point, every character is fast in the form.
pub open spec fn fast_below(compose: bool, compat: bool) -> u32 {
    if compat {
        0xA0
    } else if compose {
        0x300
    } else {
        0xC0
    }
}

/// Characters below `fast_below` are fast.
pub axiom fn axiom_fast_below(c: u32, compose: bool, compat: bool)
    requires
        c < fast_below(compose, compat),
    ensures
        has_flag(c, fast_flag(compose, compat));

pub fn fast_below_of(compose: bool, compat: bool) -> (r: u32)
    ensures
        r == fast_below(compose, compat),
{
    if compat {
        0xA0
    } else if compose {
        0x300
    } else {
        0xC0
    }
}

// ---------------------------------------------------------------------------
// Lookups
// ---------------------------------------------------------------------------

/// `tword(c)`.
#[inline(always)]
pub fn word_of(c: u32) -> (r: u32)
    ensures
        r == tword(c),
        (r & 0xFFFF) < REC_CCC_LEN,
{
    if c < TRIE_LIMIT {
        assert(c < 0x30000 ==> (c >> 6u32) < 3072) by (bit_vector);
        assert((c & 63) <= 63) by (bit_vector);
        let j = (c >> TRIE_SHIFT) as usize;
        proof {
            axiom_trie(j as int);
        }
        trie_data_at(trie_index_at(j) as usize + (c & 63) as usize)
    } else {
        assert((PLAIN_WORD & 0xFFFF) == 0) by (compute_only);
        PLAIN_WORD
    }
}

#[inline(always)]
pub fn rec_of(c: u32) -> (r: usize)
    ensures
        r == rec(c),
        r < REC_CCC_LEN,
{
    (word_of(c) & 0xFFFF) as usize
}

#[inline(always)]
pub fn ccc_of(c: u32) -> (r: u8)
    ensures
        r == ccc(c),
{
    rec_ccc_at(rec_of(c))
}

#[inline(always)]
pub fn flags_of(c: u32) -> (r: u16)
    ensures
        r == flags(c),
{
    (word_of(c) >> 16) as u16
}

pub fn fast_flag_of(compose: bool, compat: bool) -> (r: u16)
    ensures
        r == fast_flag(compose, compat),
{
    if compose {
        if compat { FLAG_FAST_NFKC } else { FLAG_FAST_NFC }
    } else {
        if compat { FLAG_FAST_NFKD } else { FLAG_FAST_NFD }
    }
}

pub fn bb_flag_of(compose: bool, compat: bool) -> (r: u16)
    ensures
        r == bb_flag(compose, compat),
{
    if compose {
        if compat { FLAG_BB_NFKC } else { FLAG_BB_NFC }
    } else {
        if compat { FLAG_BB_NFKD } else { FLAG_BB_NFD }
    }
}

/// Where `decomp(c, compat)` is: a Hangul syllable (`0`), a run of `POOL`
/// (`(w >> 5, w & 31)`), or `c` itself (`len == 1`, `off == usize::MAX`).
pub struct Decomp {
    pub hangul: bool,
    pub off: usize,
    pub len: usize,
}

impl Decomp {
    pub open spec fn wf(&self, c: u32, compat: bool) -> bool {
        &&& self.len == decomp(c, compat).len()
        &&& self.hangul == is_hangul(c)
        &&& !self.hangul && self.len > 1 ==> self.off + self.len <= POOL_LEN
        &&& !self.hangul && self.len > 1 ==> dword_ok(dword(c, compat)) && self.off == (dword(c, compat) >> 5)
        &&& !self.hangul && self.len == 1 ==> (dword_ok(dword(c, compat)) && self.off < POOL_LEN && self.off
            == (dword(c, compat) >> 5)) || (!dword_ok(dword(c, compat)) && self.off == usize::MAX)
    }
}

#[inline(always)]
pub fn decomp_of(c: u32, compat: bool, w: u32) -> (r: Decomp)
    requires
        w == tword(c),
        (w & 0xFFFF) < REC_CCC_LEN,
    ensures
        r.wf(c, compat),
{
    if S_BASE <= c && c < S_BASE + S_COUNT {
        let t = (c - S_BASE) % T_COUNT;
        Decomp { hangul: true, off: 0, len: if t == 0 { 2 } else { 3 } }
    } else {
        let r = (w & 0xFFFF) as usize;
        let w = if compat { rec_kd_at(r) } else { rec_fd_at(r) };
        let n = (w & 31) as usize;
        let off = (w >> 5) as usize;
        if n != 0 && off <= POOL_LEN && n <= POOL_LEN - off {
            Decomp { hangul: false, off, len: n }
        } else {
            Decomp { hangul: false, off: usize::MAX, len: 1 }
        }
    }
}

/// Element `m` of `decomp(c, compat)`, and its combining class. `k` is
/// `ccc(c)`.
#[inline(always)]
pub fn decomp_elem(c: u32, k: u8, compat: bool, d: &Decomp, m: usize) -> (r: (u32, u8))
    requires
        d.wf(c, compat),
        m < d.len,
        k == ccc(c),
    ensures
        r.0 == decomp(c, compat)[m as int],
        r.1 == ccc(r.0),
{
    if d.hangul {
        let s = c - S_BASE;
        let x = if m == 0 {
            L_BASE + s / N_COUNT
        } else if m == 1 {
            V_BASE + (s % N_COUNT) / T_COUNT
        } else {
            T_BASE + s % T_COUNT
        };
        proof {
            axiom_jamo(x);
        }
        (x, 0)
    } else if d.off == usize::MAX {
        (c, k)
    } else {
        let p = pool_at(d.off + m);
        proof {
            axiom_pool(d.off + m);
        }
        (p & 0xFFFFFF, (p >> 24) as u8)
    }
}

/// `comp(a, b)`.
pub fn comp_of(a: u32, b: u32) -> (r: Option<u32>)
    ensures
        r == comp(a, b),
{
    if L_BASE <= a && a < L_BASE + L_COUNT && V_BASE <= b && b < V_BASE + V_COUNT {
        Some(S_BASE + ((a - L_BASE) * V_COUNT + (b - V_BASE)) * T_COUNT)
    } else if S_BASE <= a && a < S_BASE + S_COUNT && (a - S_BASE) % T_COUNT == 0 && T_BASE < b && b < T_BASE
        + T_COUNT {
        Some(a + (b - T_BASE))
    } else {
        let w = rec_comp_at(rec_of(a));
        assert((w >> 8u32) <= 0xFFFFFF && (w & 255) <= 255) by (bit_vector);
        let start = (w >> 8) as usize;
        let end = start + (w & 255) as usize;
        if end > COMP_SECOND_LEN {
            return None;
        }
        let mut i = start;
        while i < end
            invariant
                start <= i <= end <= COMP_SECOND_LEN,
                comp(a, b) == comp_find(i as int, end as int, b),
                start == (w >> 8) as int,
                end == (w >> 8) as int + (w & 255) as int,
            decreases end - i,
        {
            if comp_second_at(i) == b {
                return Some(comp_result_at(i));
            }
            i += 1;
        }
        None
    }
}

} // verus!

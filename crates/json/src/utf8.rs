//! UTF-8 validation (RFC 8259 §8.1: JSON text exchanged between systems
//! must be UTF-8).
//!
//! `utf8_from` is the definition, read straight off Unicode's table of
//! well-formed byte sequences (Table 3-7). The validator checks a local
//! condition at every byte instead, as simdjson's "lookup" algorithm does:
//! `loc_ok` looks only at a byte and the three before it. The main theorem,
//! `lemma_utf8_local`, says the local checks together accept exactly the
//! well-formed texts. `lemma_lookup` then shows that three table lookups and
//! a saturating subtraction compute `loc_ok`, which is how the SIMD kernels
//! check 32 or 64 bytes at once.
#[allow(unused_imports)]
use crate::lanes::*;
#[allow(unused_imports)]
use crate::simd::*;
#[allow(unused_imports)]
use crate::spec::*;
#[cfg(verus_keep_ghost)]
use verilith_core::utf8::*;
pub use verilith_core::utf8::{ex_all_loc, ex_tail, utf8_valid_scalar};
#[allow(unused_imports)]
use verilith_simd::cpu::*;
use vstd::prelude::*;

#[cfg(target_arch = "x86_64")]
#[allow(unused_imports)]
use core::arch::x86_64::{__m256i, __m512i};

verus! {

// The local condition, the proof that it decides well-formedness, and the
// scalar validator are in `verilith_core::utf8`.

// ---------------------------------------------------------------------------
// The lookup tables compute the local condition
// ---------------------------------------------------------------------------

// simdjson's tables. Each bit of an entry names an error class; a byte pair
// (p1, c) is in a class when all three lookups have its bit. Bit 7 is the
// pair "continuation, continuation", which is an error unless a lead byte two
// or three back asks for it, and an error to miss if one does.
pub const T1: [u8; 16] = [2, 2, 2, 2, 2, 2, 2, 2, 0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49];
pub const T2: [u8; 16] = [
    0xE7, 0xA3, 0x83, 0x83, 0x8B, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xDB, 0xCB, 0xCB,
];
pub const T3: [u8; 16] = [1, 1, 1, 1, 1, 1, 1, 1, 0xE6, 0xAE, 0xBA, 0xBA, 1, 1, 1, 1];

pub open spec fn t1() -> Seq<u8> {
    seq![2u8, 2, 2, 2, 2, 2, 2, 2, 0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49]
}

pub open spec fn t2() -> Seq<u8> {
    seq![0xE7u8, 0xA3, 0x83, 0x83, 0x8B, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xDB, 0xCB, 0xCB]
}

pub open spec fn t3() -> Seq<u8> {
    seq![1u8, 1, 1, 1, 1, 1, 1, 1, 0xE6, 0xAE, 0xBA, 0xBA, 1, 1, 1, 1]
}

/// The three lookups for the pair (p1, c), with `ch` the high nibble of c.
pub open spec fn tbl(p1: u8, ch: int) -> u8 {
    t1()[p1 as int / 16] & t2()[p1 as int % 16] & t3()[ch]
}

/// What the tables must give: bit 7 alone when a lead byte two or three
/// back needs this byte, else nothing.
pub open spec fn want(m23: bool) -> u8 {
    if m23 { 0x80 } else { 0 }
}

/// `loc_ok` with c replaced by its high nibble, which is all it looks at.
pub open spec fn loc_n(p1: u8, ch: int, m23: bool) -> bool {
    let ct = 8 <= ch <= 0xB;
    &&& !(p1 >= 0xC0 && !ct)
    &&& !(p1 < 0x80 && ct)
    &&& (cont(p1) && ct) == m23
    &&& !((p1 == 0xC0 || p1 == 0xC1) && ct)
    &&& !(p1 == 0xE0 && ct && ch < 0xA)
    &&& !(p1 == 0xED && ct && ch >= 0xA)
    &&& !(p1 == 0xF0 && ct && ch < 9)
    &&& !(p1 >= 0xF4 && ct && ch >= 9)
    &&& !(p1 >= 0xF5 && ct && ch < 9)
}

/// The tables agree with `loc_n` at pair `k`, numbered `p1 * 16 + ch`.
pub open spec fn table_ok_at(k: int) -> bool {
    let p1 = (k / 16) as u8;
    let ch = k % 16;
    &&& loc_n(p1, ch, true) == (tbl(p1, ch) == want(true))
    &&& loc_n(p1, ch, false) == (tbl(p1, ch) == want(false))
}

/// `table_ok_at` on `[lo, lo + n)`.
pub open spec fn tables_ok(lo: int, n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        table_ok_at(lo + n - 1) && tables_ok(lo, (n - 1) as nat)
    }
}

proof fn lemma_tables_ok_at(lo: int, n: nat, k: int)
    requires
        tables_ok(lo, n),
        lo <= k < lo + n,
    ensures
        table_ok_at(k),
    decreases n,
{
    if k < lo + n - 1 {
        lemma_tables_ok_at(lo, (n - 1) as nat, k);
    }
}

/// The table check, for every pair: all 256 * 16 of them, by evaluation.
pub proof fn lemma_lookup(p3: u8, p2: u8, p1: u8, c: u8)
    ensures
        loc_ok(p3, p2, p1, c) == (tbl(p1, c as int / 16) == want(p2 >= 0xE0 || p3 >= 0xF0)),
{
    let k = p1 as int * 16 + c as int / 16;
    let lo = k / 128 * 128;
    if lo == 0 { assert(tables_ok(0, 128)) by (compute_only); }
    else if lo == 128 { assert(tables_ok(128, 128)) by (compute_only); }
    else if lo == 256 { assert(tables_ok(256, 128)) by (compute_only); }
    else if lo == 384 { assert(tables_ok(384, 128)) by (compute_only); }
    else if lo == 512 { assert(tables_ok(512, 128)) by (compute_only); }
    else if lo == 640 { assert(tables_ok(640, 128)) by (compute_only); }
    else if lo == 768 { assert(tables_ok(768, 128)) by (compute_only); }
    else if lo == 896 { assert(tables_ok(896, 128)) by (compute_only); }
    else if lo == 1024 { assert(tables_ok(1024, 128)) by (compute_only); }
    else if lo == 1152 { assert(tables_ok(1152, 128)) by (compute_only); }
    else if lo == 1280 { assert(tables_ok(1280, 128)) by (compute_only); }
    else if lo == 1408 { assert(tables_ok(1408, 128)) by (compute_only); }
    else if lo == 1536 { assert(tables_ok(1536, 128)) by (compute_only); }
    else if lo == 1664 { assert(tables_ok(1664, 128)) by (compute_only); }
    else if lo == 1792 { assert(tables_ok(1792, 128)) by (compute_only); }
    else if lo == 1920 { assert(tables_ok(1920, 128)) by (compute_only); }
    else if lo == 2048 { assert(tables_ok(2048, 128)) by (compute_only); }
    else if lo == 2176 { assert(tables_ok(2176, 128)) by (compute_only); }
    else if lo == 2304 { assert(tables_ok(2304, 128)) by (compute_only); }
    else if lo == 2432 { assert(tables_ok(2432, 128)) by (compute_only); }
    else if lo == 2560 { assert(tables_ok(2560, 128)) by (compute_only); }
    else if lo == 2688 { assert(tables_ok(2688, 128)) by (compute_only); }
    else if lo == 2816 { assert(tables_ok(2816, 128)) by (compute_only); }
    else if lo == 2944 { assert(tables_ok(2944, 128)) by (compute_only); }
    else if lo == 3072 { assert(tables_ok(3072, 128)) by (compute_only); }
    else if lo == 3200 { assert(tables_ok(3200, 128)) by (compute_only); }
    else if lo == 3328 { assert(tables_ok(3328, 128)) by (compute_only); }
    else if lo == 3456 { assert(tables_ok(3456, 128)) by (compute_only); }
    else if lo == 3584 { assert(tables_ok(3584, 128)) by (compute_only); }
    else if lo == 3712 { assert(tables_ok(3712, 128)) by (compute_only); }
    else if lo == 3840 { assert(tables_ok(3840, 128)) by (compute_only); }
    else { assert(tables_ok(3968, 128)) by (compute_only); }
    lemma_tables_ok_at(lo, 128, k);
    assert(k / 16 == p1 as int && k % 16 == c as int / 16);
    let ch = c as int / 16;
    assert((0x80 <= c <= 0xBF) == (8 <= ch <= 0xB));
    assert((c < 0xA0) == (ch < 0xA));
    assert((c < 0x90) == (ch < 9));
}

/// Saturating subtraction, as `vpsubusb`.
pub open spec fn subs(a: u8, b: u8) -> u8 {
    if a >= b { (a - b) as u8 } else { 0 }
}

/// simdjson's test for "a lead byte two or three back".
pub proof fn lemma_must23(p3: u8, p2: u8)
    ensures
        ((subs(p2, 0x60) | subs(p3, 0x70)) & 0x80) == want(p2 >= 0xE0 || p3 >= 0xF0),
{
    let a = subs(p2, 0x60);
    let b = subs(p3, 0x70);
    assert(a >= 0x80 <==> p2 >= 0xE0);
    assert(b >= 0x80 <==> p3 >= 0xF0);
    assert(a <= 0x9F);
    assert(b <= 0x8F);
    assert((a | b) & 0x80 == if a >= 0x80 || b >= 0x80 { 0x80u8 } else { 0u8 }) by (bit_vector);
}

/// The error lane is zero exactly when the local check passes.
pub proof fn lemma_err_lane(p3: u8, p2: u8, p1: u8, c: u8)
    ensures
        ((tbl(p1, c as int / 16) ^ ((subs(p2, 0x60) | subs(p3, 0x70)) & 0x80)) == 0) == loc_ok(p3, p2, p1, c),
{
    lemma_lookup(p3, p2, p1, c);
    lemma_must23(p3, p2);
    let x = tbl(p1, c as int / 16);
    let y = (subs(p2, 0x60) | subs(p3, 0x70)) & 0x80;
    assert((x ^ y == 0) == (x == y)) by (bit_vector);
}

// ---------------------------------------------------------------------------
// SIMD validator
// ---------------------------------------------------------------------------

/// `loc` at `j`, away from the start of the text, as the error lane the
/// kernels compute.
pub proof fn lemma_lane(s: Seq<u8>, st: int, j: int, p3: u8, p2: u8, p1: u8, c: u8, e: u8)
    requires
        st + 3 <= j < s.len(),
        p3 == s[j - 3],
        p2 == s[j - 2],
        p1 == s[j - 1],
        c == s[j],
        e == ((t1()[(p1 / 16) as int] & t2()[(p1 & 0x0F) as int]) & t3()[(c / 16) as int]) ^ ((subs(p2, 0x60) | subs(p3, 0x70)) & 0x80),
    ensures
        (e == 0) == loc(s, st, j),
{
    assert(p1 & 0x0F == p1 % 16) by (bit_vector);
    lemma_err_lane(p3, p2, p1, c);
}

/// Every lane of `a` is zero, from `vptest` of `a` with itself.
proof fn lemma_self_and(y: u8)
    ensures
        (y & y == 0) == (y == 0),
{
    assert(y & y == y) by (bit_vector);
}

/// The three bytes below 0x80.
proof fn lemma_or3(x: u8, y: u8, z: u8)
    requires
        ((x | y) | z) & 0x80 == 0,
    ensures
        x < 0x80 && y < 0x80 && z < 0x80,
{
    assert(((x | y) | z) & 0x80 == 0 ==> x < 0x80 && y < 0x80 && z < 0x80) by (bit_vector);
}

/// Every byte of `[a, b)` is ASCII.
pub open spec fn ascii_span(s: Seq<u8>, a: int, b: int) -> bool {
    forall|t: int| a <= t < b ==> #[trigger] s[t] < 0x80
}

/// After an ASCII span, the local checks pass.
proof fn lemma_ascii_span(s: Seq<u8>, st: int, j: int, b: int)
    requires
        st + 3 <= j,
        b <= s.len(),
        ascii_span(s, j - 3, b),
    ensures
        all_loc(s, st, j, b),
{
    assert forall|k: int| j <= k < b implies #[trigger] loc(s, st, k) by {
        assert(s[k - 3] < 0x80 && s[k - 2] < 0x80 && s[k - 1] < 0x80 && s[k] < 0x80);
    }
}

/// Whether `s[j - 3 .. j + 64]` is all ASCII, in three loads.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn ascii64_avx2(s: &[u8], j: usize) -> (r: bool)
    requires
        avx2(),
        3 <= j,
        j + 64 <= s@.len(),
    ensures
        r ==> ascii_span(s@, j - 3, j + 64),
{
    let _n = s.len();
    let a = load32(s, j - 3);
    let b = load32(s, j + 29);
    let c = load32(s, j + 32);
    let hi = splat32(0x80);
    let o = or32(or32(a, b), c);
    let r = testz32(o, hi);
    proof {
        if r {
            assert forall|t: int| j - 3 <= t < j + 64 implies #[trigger] s@[t] < 0x80 by {
                let l = if t < j + 29 { t - (j - 3) } else if t < j + 61 { t - (j + 29) } else { t - (j + 32) };
                assert(0 <= l < 32);
                assert(b32(o)[l] & b32(hi)[l] == 0);
                lemma_or3(b32(a)[l], b32(b)[l], b32(c)[l]);
            }
        }
    }
    r
}

/// Whether `s[j - 3 .. j + 128]` is all ASCII, in three loads.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn ascii128_avx512(s: &[u8], j: usize) -> (r: bool)
    requires
        avx512bw(),
        3 <= j,
        j + 128 <= s@.len(),
    ensures
        r ==> ascii_span(s@, j - 3, j + 128),
{
    let _n = s.len();
    // The two blocks stage 1 has just loaded, then the three bytes past
    // them by a word load rather than a third, line-splitting vector load.
    let a = load64(s, j - 3);
    let b = load64(s, j + 61);
    let w = crate::simd::load4(s, j + 124);
    let hi = splat64(0x80);
    let o = or64(a, b);
    let r = testz64(o, hi) && w & 0x8080_8080u32 == 0;
    proof {
        if r {
            lemma_word_ascii(s@[j + 124], s@[j + 125], s@[j + 126], s@[j + 127]);
            assert forall|t: int| j - 3 <= t < j + 128 implies #[trigger] s@[t] < 0x80 by {
                if t < j + 125 {
                    let l = if t < j + 61 { t - (j - 3) } else { t - (j + 61) };
                    assert(0 <= l < 64);
                    assert(b64(o)[l] & b64(hi)[l] == 0);
                    let (x, y) = (b64(a)[l], b64(b)[l]);
                    assert((x | y) & 0x80 == 0 ==> x < 0x80 && y < 0x80) by (bit_vector);
                }
            }
        }
    }
    r
}

#[verifier::bit_vector]
proof fn lemma_word_ascii(a0: u8, a1: u8, a2: u8, a3: u8)
    requires
        (a0 as u32 | (a1 as u32) << 8u32 | (a2 as u32) << 16u32 | (a3 as u32) << 24u32) & 0x8080_8080u32 == 0,
    ensures
        a0 < 0x80 && a1 < 0x80 && a2 < 0x80 && a3 < 0x80,
{
}

/// The error lanes for `[j, j + 32)`: lane `l` is zero exactly when
/// `loc` holds at `j + l`.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
#[allow(unused_variables)]
fn err32(s: &[u8], st: usize, j: usize) -> (e: __m256i)
    requires
        avx2(),
        st + 3 <= j,
        j + 32 <= s@.len(),
    ensures
        forall|l: int| 0 <= l < 32 ==> (#[trigger] b32(e)[l] == 0) == loc(s@, st as int, j + l),
{
    let c = load32(s, j);
    let p1 = load32(s, j - 1);
    let p2 = load32(s, j - 2);
    let p3 = load32(s, j - 3);
    let a = shuffle32(table32(&T1), nibhi32(p1));
    let b = shuffle32(table32(&T2), and32(p1, splat32(0x0F)));
    let d = shuffle32(table32(&T3), nibhi32(c));
    let m = and32(or32(subs32(p2, splat32(0x60)), subs32(p3, splat32(0x70))), splat32(0x80));
    let e = xor32(and32(and32(a, b), d), m);
    proof {
        assert(T1@ == t1());
        assert(T2@ == t2());
        assert(T3@ == t3());
        assert forall|l: int| 0 <= l < 32 implies (#[trigger] b32(e)[l] == 0) == loc(s@, st as int, j + l) by {
            let k = j + l;
            let x1 = s@[k - 1];
            let x = s@[k];
            assert(b32(p1)[l] == x1);
            assert(b32(c)[l] == x);
            lemma_lane16(l, x1 / 16);
            lemma_lane16(l, x1 & 0x0F);
            lemma_lane16(l, x / 16);
            assert(x1 & 0x0F < 16) by (bit_vector);
            lemma_lane(s@, st as int, k, s@[k - 3], s@[k - 2], x1, x, b32(e)[l]);
        }
    }
    e
}

/// The error lanes for `[j, j + 64)`: lane `l` is zero exactly when
/// `loc` holds at `j + l`.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
#[allow(unused_variables)]
fn err64(s: &[u8], st: usize, j: usize) -> (e: __m512i)
    requires
        avx512bw(),
        st + 3 <= j,
        j + 64 <= s@.len(),
    ensures
        forall|l: int| 0 <= l < 64 ==> (#[trigger] b64(e)[l] == 0) == loc(s@, st as int, j + l),
{
    let c = load64(s, j);
    let p1 = load64(s, j - 1);
    let p2 = load64(s, j - 2);
    let p3 = load64(s, j - 3);
    let a = shuffle64(table64(&T1), nibhi64(p1));
    let b = shuffle64(table64(&T2), and64(p1, splat64(0x0F)));
    let d = shuffle64(table64(&T3), nibhi64(c));
    let m = and64(or64(subs64(p2, splat64(0x60)), subs64(p3, splat64(0x70))), splat64(0x80));
    let e = xor64(and64(and64(a, b), d), m);
    proof {
        assert(T1@ == t1());
        assert(T2@ == t2());
        assert(T3@ == t3());
        assert forall|l: int| 0 <= l < 64 implies (#[trigger] b64(e)[l] == 0) == loc(s@, st as int, j + l) by {
            let k = j + l;
            let x1 = s@[k - 1];
            let x = s@[k];
            assert(b64(p1)[l] == x1);
            assert(b64(c)[l] == x);
            lemma_lane16(l, x1 / 16);
            lemma_lane16(l, x1 & 0x0F);
            lemma_lane16(l, x / 16);
            assert(x1 & 0x0F < 16) by (bit_vector);
            lemma_lane(s@, st as int, k, s@[k - 3], s@[k - 2], x1, x, b64(e)[l]);
        }
    }
    e
}

// --- Driver ---------------------------------------------------------------

proof fn lemma_or_zero(x: u8, y: u8)
    ensures
        (((x | y) & (x | y)) == 0) == (x == 0 && y == 0),
{
    assert((((x | y) & (x | y)) == 0) == (x == 0 && y == 0)) by (bit_vector);
}

/// `loc` on `[j, j + 64)` from two error vectors, tested once.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn pair32_ok(s: &[u8], st: usize, j: usize) -> (r: bool)
    requires
        avx2(),
        st + 3 <= j,
        j + 64 <= s@.len(),
    ensures
        r == all_loc(s@, st as int, j as int, j + 64),
{
    let _n = s.len();
    let a = err32(s, st, j);
    let b = err32(s, st, j + 32);
    let e = or32(a, b);
    let r = testz32(e, e);
    proof {
        let g = s@;
        let si = st as int;
        let ji = j as int;
        assert forall|l: int| 0 <= l < 32 implies ((#[trigger] b32(e)[l] & b32(e)[l]) == 0) == (loc(g, si, ji + l)
            && loc(g, si, ji + 32 + l)) by {
            lemma_or_zero(b32(a)[l], b32(b)[l]);
            assert(b32(a)[l] == 0 <==> loc(g, si, ji + l));
            assert(b32(b)[l] == 0 <==> loc(g, si, ji + 32 + l));
        }
        if r {
            assert forall|k: int| ji <= k < ji + 64 implies #[trigger] loc(g, si, k) by {
                if k < ji + 32 {
                    assert(b32(e)[k - ji] & b32(e)[k - ji] == 0);
                } else {
                    assert(b32(e)[k - ji - 32] & b32(e)[k - ji - 32] == 0);
                }
            }
        } else {
            let l = choose|l: int| 0 <= l < 32 && #[trigger] (b32(e)[l] & b32(e)[l]) != 0;
            if !loc(g, si, ji + l) {
                assert(!all_loc(g, si, ji, ji + 64));
            } else {
                assert(!loc(g, si, ji + 32 + l));
                assert(!all_loc(g, si, ji, ji + 64));
            }
        }
    }
    r
}

/// `loc` on `[j, j + 128)` from two error vectors, tested once.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn pair64_ok(s: &[u8], st: usize, j: usize) -> (r: bool)
    requires
        avx512bw(),
        st + 3 <= j,
        j + 128 <= s@.len(),
    ensures
        r == all_loc(s@, st as int, j as int, j + 128),
{
    let _n = s.len();
    let a = err64(s, st, j);
    let b = err64(s, st, j + 64);
    let e = or64(a, b);
    let r = testz64(e, e);
    proof {
        let g = s@;
        let si = st as int;
        let ji = j as int;
        assert forall|l: int| 0 <= l < 64 implies ((#[trigger] b64(e)[l] & b64(e)[l]) == 0) == (loc(g, si, ji + l)
            && loc(g, si, ji + 64 + l)) by {
            lemma_or_zero(b64(a)[l], b64(b)[l]);
            assert(b64(a)[l] == 0 <==> loc(g, si, ji + l));
            assert(b64(b)[l] == 0 <==> loc(g, si, ji + 64 + l));
        }
        if r {
            assert forall|k: int| ji <= k < ji + 128 implies #[trigger] loc(g, si, k) by {
                if k < ji + 64 {
                    assert(b64(e)[k - ji] & b64(e)[k - ji] == 0);
                } else {
                    assert(b64(e)[k - ji - 64] & b64(e)[k - ji - 64] == 0);
                }
            }
        } else {
            let l = choose|l: int| 0 <= l < 64 && #[trigger] (b64(e)[l] & b64(e)[l]) != 0;
            if !loc(g, si, ji + l) {
                assert(!all_loc(g, si, ji, ji + 128));
            } else {
                assert(!loc(g, si, ji + 64 + l));
                assert(!all_loc(g, si, ji, ji + 128));
            }
        }
    }
    r
}

/// `loc` on `[j, j + 128)`, away from the start of the text.
#[inline(always)]
fn chunk128<const K: u8>(s: &[u8], st: usize, j: usize) -> (r: bool)
    requires
        utf8_cpu(K),
        K == AVX2 || K == AVX512 || K == NEON,
        K == NEON ==> verilith_simd::neon::neon(),
        st + 3 <= j,
        j + 128 <= s@.len(),
    ensures
        r == all_loc(s@, st as int, j as int, j + 128),
{
    let _n = s.len();
    let ghost g = s@;
    let ghost si = st as int;
    let ghost ji = j as int;
    proof {
        lemma_all_loc_split(g, si, ji, ji + 64, ji + 128);
        lemma_all_loc_split(g, si, ji, ji + 32, ji + 64);
        lemma_all_loc_split(g, si, ji + 64, ji + 96, ji + 128);
    }
    if K == NEON {
        // ASCII halves take five loads; the rest the table lookups.
        let lo = if crate::neon::ascii64_neon(s, j) {
            proof {
                lemma_ascii_span(g, si, ji, ji + 64);
            }
            true
        } else {
            crate::neon::utf8_64_neon(s, st, j)
        };
        if !lo {
            return false;
        }
        if crate::neon::ascii64_neon(s, j + 64) {
            proof {
                lemma_ascii_span(g, si, ji + 64, ji + 128);
            }
            return true;
        }
        return crate::neon::utf8_64_neon(s, st, j + 64);
    }
    #[cfg(target_arch = "x86_64")]
    {
        if K == AVX512 {
            if ascii128_avx512(s, j) {
                proof {
                    lemma_ascii_span(g, si, ji, ji + 128);
                }
                return true;
            }
            return pair64_ok(s, st, j);
        }
        let lo = if ascii64_avx2(s, j) {
            proof {
                lemma_ascii_span(g, si, ji, ji + 64);
            }
            true
        } else {
            pair32_ok(s, st, j)
        };
        if !lo {
            return false;
        }
        if ascii64_avx2(s, j + 64) {
            proof {
                lemma_ascii_span(g, si, ji + 64, ji + 128);
            }
            return true;
        }
        return pair32_ok(s, st, j + 64);
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        ex_all_loc(s, st, j, j + 128)
    }
}

/// The validator's state part way through `s[st..]`: `ok` says whether the
/// local checks pass on `[st, uj)`. Blocks need three bytes of history, so
/// `uj` starts three bytes in (or at the end, for shorter texts).
pub open spec fn u8_state(s: Seq<u8>, st: int, uj: int, ok: bool) -> bool {
    &&& st <= uj <= s.len()
    &&& (uj < st + 3 ==> uj == s.len())
    &&& ok == all_loc(s, st, st, uj)
}

/// The first three bytes, one at a time.
#[inline(always)]
pub fn utf8_start(s: &[u8], st: usize) -> (r: (usize, bool))
    requires
        st <= s@.len(),
    ensures
        u8_state(s@, st as int, r.0 as int, r.1),
        s@.len() - st >= 3 ==> r.0 == st + 3,
{
    if s.len() - st >= 3 && get8(s, st) < 0x80 && get8(s, st + 1) < 0x80 && get8(s, st + 2) < 0x80 {
        proof {
            assert forall|k: int| st <= k < st + 3 implies #[trigger] loc(s@, st as int, k) by {}
        }
        return (st + 3, true);
    }
    let h = if s.len() - st < 3 { s.len() } else { st + 3 };
    (h, ex_all_loc(s, st, st, h))
}

/// The next 128 bytes, if there are that many left.
#[inline(always)]
pub fn utf8_step<const K: u8>(s: &[u8], st: usize, uj: usize, ok: bool) -> (r: (usize, bool))
    requires
        utf8_cpu(K),
        u8_state(s@, st as int, uj as int, ok),
        K == NEON ==> verilith_simd::neon::neon(),
    ensures
        u8_state(s@, st as int, r.0 as int, r.1),
        (K == AVX2 || K == AVX512 || K == NEON) && s@.len() - uj >= 128 ==> r.0 == uj + 128,
{
    if (K != AVX2 && K != AVX512 && K != NEON) || s.len() - uj < 128 {
        return (uj, ok);
    }
    let c = ok && chunk128::<K>(s, st, uj);
    proof {
        lemma_all_loc_split(s@, st as int, st as int, uj as int, uj + 128);
    }
    (uj + 128, c)
}

/// The 64 bytes at `b`, for stage 1's NEON loop, which has them loaded
/// and knows from its own vectors whether they are ASCII (`hi`); `pa`
/// says the same of the bytes from `uj - 3` up to `b`. Returns the new
/// `ok` and `pa`; the state moves to `b + 64`.
#[inline(always)]
pub fn utf8_block_neon(s: &[u8], st: usize, b: usize, uj: usize, ok: bool, pa: bool, hi: bool) -> (r: (bool, bool))
    requires
        verilith_simd::neon::neon(),
        u8_state(s@, st as int, uj as int, ok),
        st <= b,
        b + 64 <= s@.len(),
        (uj == st + 3 && b == st) || (uj == b && st + 3 <= b),
        pa ==> ascii_span(s@, uj - 3, b as int),
        hi ==> ascii_span(s@, b as int, b + 64),
    ensures
        u8_state(s@, st as int, b + 64, r.0),
        r.1 ==> ascii_span(s@, b + 61, b + 64),
{
    let _n = s.len();
    proof {
        lemma_all_loc_split(s@, st as int, st as int, uj as int, b + 64);
    }
    if hi && pa {
        proof {
            lemma_ascii_span(s@, st as int, uj as int, b + 64);
        }
        return (ok, true);
    }
    let c = ok && if uj == b {
        crate::neon::utf8_64_neon(s, st, b)
    } else {
        ex_all_loc(s, st, uj, b + 64)
    };
    (c, hi)
}

/// The rest of the text, then the three positions past its end.
#[inline(always)]
pub fn utf8_finish<const K: u8>(s: &[u8], st: usize, uj: usize, ok: bool) -> (r: bool)
    requires
        utf8_cpu(K),
        u8_state(s@, st as int, uj as int, ok),
        K == NEON ==> verilith_simd::neon::neon(),
    ensures
        r == utf8_from(s@, st as int),
{
    let n = s.len();
    proof {
        lemma_utf8_local(s@, st as int, st as int);
        lemma_all_loc_split(s@, st as int, st as int, n as int, n + 3);
    }
    if !ok {
        proof {
            lemma_all_loc_split(s@, st as int, st as int, uj as int, n as int);
        }
        return false;
    }
    let mut j = uj;
    let mut ok = ok;
    while ok && 128 <= n - j && (K == AVX2 || K == AVX512 || K == NEON)
        invariant
            utf8_cpu(K),
            K == NEON ==> verilith_simd::neon::neon(),
            n == s@.len(),
            u8_state(s@, st as int, j as int, ok),
        decreases n - j,
    {
        let r = utf8_step::<K>(s, st, j, ok);
        j = r.0;
        ok = r.1;
    }
    if !ok {
        proof {
            lemma_all_loc_split(s@, st as int, st as int, j as int, n as int);
        }
        return false;
    }
    let rest = if K == AVX2 || K == AVX512 || K == NEON {
        if n - j >= 128 {
            // Not reached: the loop above ran while 128 bytes were left.
            ex_all_loc(s, st, j, n)
        } else if j < n && n - st >= 131 {
            // Once more, overlapping, to reach the end.
            let c = chunk128::<K>(s, st, n - 128);
            proof {
                lemma_all_loc_split(s@, st as int, st as int, n - 128, n as int);
                lemma_all_loc_split(s@, st as int, (n - 128) as int, j as int, n as int);
                lemma_all_loc_split(s@, st as int, st as int, n - 128, j as int);
            }
            c
        } else {
            ex_all_loc(s, st, j, n)
        }
    } else {
        ex_all_loc(s, st, j, n)
    };
    proof {
        lemma_all_loc_split(s@, st as int, st as int, j as int, n as int);
    }
    rest && ex_tail(s, st)
}

/// Whether `s[st..]` is well-formed UTF-8, 128 bytes at a time.
#[inline(always)]
fn utf8_blocks<const K: u8>(s: &[u8], st: usize) -> (r: bool)
    requires
        utf8_cpu(K),
        st <= s@.len(),
        K == NEON ==> verilith_simd::neon::neon(),
    ensures
        r == utf8_from(s@, st as int),
{
    let (uj, ok) = utf8_start(s, st);
    utf8_finish::<K>(s, st, uj, ok)
}

} // verus!

verus! {

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn utf8_avx512_body(s: &[u8], st: usize) -> (r: bool)
    requires
        avx512bw(),
        st <= s@.len(),
    ensures
        r == utf8_from(s@, st as int),
{
    utf8_blocks::<AVX512>(s, st)
}

/// Trusted: `utf8_avx512_body` compiled with `avx512f,avx512bw` enabled, through
/// `tf::utf8_avx512`; the contract is `utf8_avx512_body`'s, which is verified.
/// The caller checks the CPU first.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
fn utf8_avx512(s: &[u8], st: usize) -> (r: bool)
    requires
        avx512bw(),
        st <= s@.len(),
    ensures
        r == utf8_from(s@, st as int),
{
    // SAFETY: only called after the matching CPU check returned true.
    unsafe { tf::utf8_avx512(s, st) }
}

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn utf8_avx2_body(s: &[u8], st: usize) -> (r: bool)
    requires
        avx2(),
        st <= s@.len(),
    ensures
        r == utf8_from(s@, st as int),
{
    utf8_blocks::<AVX2>(s, st)
}

/// Trusted: `utf8_avx2_body` compiled with `avx2` enabled, through
/// `tf::utf8_avx2`; the contract is `utf8_avx2_body`'s, which is verified.
/// The caller checks the CPU first.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
fn utf8_avx2(s: &[u8], st: usize) -> (r: bool)
    requires
        avx2(),
        st <= s@.len(),
    ensures
        r == utf8_from(s@, st as int),
{
    // SAFETY: only called after the matching CPU check returned true.
    unsafe { tf::utf8_avx2(s, st) }
}

/// Whether this CPU has AVX-512BW.
#[cfg(target_arch = "x86_64")]
#[inline]
fn cpu_has_avx512bw() -> (r: bool)
    ensures
        r ==> avx512bw(),
{
    has_avx512bw()
}

/// Whether this CPU has AVX2.
#[cfg(target_arch = "x86_64")]
#[inline]
fn cpu_has_avx2() -> (r: bool)
    ensures
        r ==> avx2(),
{
    has_avx2()
}

/// Whether `s[st..]` is well-formed UTF-8, with the best kernel this CPU
/// supports.
pub fn utf8_valid(s: &[u8], st: usize) -> (r: bool)
    requires
        st <= s@.len(),
    ensures
        r == utf8_from(s@, st as int),
{
    #[cfg(target_arch = "x86_64")]
    {
        if cpu_has_avx512bw() {
            return utf8_avx512(s, st);
        }
        if cpu_has_avx2() {
            return utf8_avx2(s, st);
        }
    }
    if verilith_simd::neon::has_neon() {
        return utf8_blocks::<NEON>(s, st);
    }
    utf8_blocks::<SCALAR>(s, st)
}

/// Whether `s[st..k]` is well-formed UTF-8.
pub fn utf8_valid_upto(s: &[u8], st: usize, k: usize) -> (r: bool)
    requires
        st <= k <= s@.len(),
    ensures
        r == utf8_from(s@.subrange(0, k as int), st as int),
{
    if k == s.len() {
        proof {
            assert(s@.subrange(0, k as int) =~= s@);
        }
        utf8_valid(s, st)
    } else {
        utf8_valid(vstd::slice::slice_subrange(s, 0, k), st)
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    /// `is_x86_feature_detected!`, and false on other targets.
    #[allow(unused_macros)]
    macro_rules! detected {
        ($f:tt) => {{
            #[cfg(target_arch = "x86_64")]
            let r = std::is_x86_feature_detected!($f);
            #[cfg(not(target_arch = "x86_64"))]
            let r = false;
            r
        }};
    }

    fn all_kernels(s: &[u8], st: usize) -> bool {
        let want = std::str::from_utf8(&s[st..]).is_ok();
        assert_eq!(utf8_valid_scalar(s, st), want, "scalar {:x?}", &s[st..]);
        #[cfg(target_arch = "x86_64")]
        if detected!("avx2") {
            assert_eq!(utf8_avx2(s, st), want, "avx2 {:x?}", &s[st..]);
        }
        assert_eq!(utf8_blocks::<SCALAR>(s, st), want);
        // NEON runs natively on AArch64 and in vsimd's emulation elsewhere.
        assert_eq!(utf8_blocks::<NEON>(s, st), want, "neon {:x?}", &s[st..]);
        #[cfg(target_arch = "x86_64")]
        if detected!("avx512bw") {
            assert_eq!(utf8_avx512(s, st), want, "avx512 {:x?}", &s[st..]);
        }
        assert_eq!(utf8_valid(s, st), want);
        want
    }

    /// Every sequence of up to three bytes, and every four-byte sequence
    /// with a lead byte of F0..F7, at each position of a block and across a
    /// block edge, in front of ASCII and of non-ASCII text.
    #[test]
    fn agrees_with_std() {
        let fills: [&[u8]; 3] = [b"a", "\u{e9}".as_bytes(), "\u{20ac}".as_bytes()];
        let mut seqs: Vec<Vec<u8>> = Vec::new();
        for a in 0..=255u8 {
            seqs.push(vec![a]);
            for b in 0..=255u8 {
                seqs.push(vec![a, b]);
                if a >= 0xC0 {
                    for c in [0x00u8, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0, 0xFF] {
                        seqs.push(vec![a, b, c]);
                        if a >= 0xF0 {
                            for d in [0x7Fu8, 0x80, 0xBF, 0xC0] {
                                seqs.push(vec![a, b, c, d]);
                            }
                        }
                    }
                }
            }
        }
        let mut ok = 0;
        for (n, q) in seqs.iter().enumerate() {
            let fill = fills[n % 3];
            // Positions 0, 30, 61 and 100 cover a block start, both block
            // edges and the overlapping last block.
            for at in [0usize, 30, 61, 100] {
                let mut s: Vec<u8> = Vec::new();
                while s.len() < at {
                    s.extend_from_slice(fill);
                }
                s.extend_from_slice(q);
                while s.len() < 140 {
                    s.extend_from_slice(fill);
                }
                for st in [0usize, 1, 2] {
                    if std::str::from_utf8(&s[..st]).is_ok() && all_kernels(&s, st) {
                        ok += 1;
                    }
                }
            }
        }
        assert!(ok > 1000);
    }

    #[test]
    fn random_mutations() {
        let base = "plain ascii, caf\u{e9}, \u{20ac}100, \u{1F600}\u{10FFFF}\u{FFFF}\u{D7FF}\u{E000} and more text "
            .repeat(8);
        let base = base.as_bytes();
        let mut x: u64 = 0x9E3779B97F4A7C15;
        for _ in 0..200_000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let mut s = base[..(x as usize % base.len())].to_vec();
            if !s.is_empty() {
                let i = (x >> 20) as usize % s.len();
                s[i] = (x >> 40) as u8;
            }
            all_kernels(&s, 0);
        }
    }
}

/// Trampolines that compile a verified `*_body` function with the target
/// features its kernel needs. Each is one call; `#[target_feature]` only
/// changes code generation. Verus rejects the attribute on verified code
/// (verus-lang/verus#3362), so it lives outside `verus!`.
#[cfg(target_arch = "x86_64")]
mod tf {
    #[allow(unused_imports)]
    use super::*;

    #[target_feature(enable = "avx512f,avx512bw")]
    pub(super) unsafe fn utf8_avx512(s: &[u8], st: usize) -> bool {
        utf8_avx512_body(s, st)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn utf8_avx2(s: &[u8], st: usize) -> bool {
        utf8_avx2_body(s, st)
    }
}

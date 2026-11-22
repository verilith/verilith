//! UTF-8 validation, 128 bytes at a time with AVX2 or 64 with NEON.
//!
//! This is vjson's validator (simdjson's "lookup" algorithm, after Keiser
//! and Lemire, "Validating UTF-8 In Less Than One Instruction Per Byte",
//! 2021), moved onto vsimd's specifications of the intrinsics. The
//! definition is vcore's `utf8_from`, read off Unicode's Table 3-7. vcore
//! also proves the main theorem, `lemma_utf8_local`: well-formedness is
//! the conjunction of a local condition `loc_ok` at every byte, which looks
//! only at that byte and the three before it. Here `lemma_lookup` shows
//! that three table lookups and a saturating subtraction compute
//! `loc_ok`, which is how the kernel checks 32 bytes at once.
use super::avx2::*;
use crate::simd::*;
use verilith_simd::arch::*;
use verilith_core::prims::get;
#[allow(unused_imports)]
use verilith_core::utf8::*;
use verilith_simd::cpu::*;
use verilith_simd::lanes::*;
use verilith_simd::mem::*;
use verilith_simd::neon::*;
use verilith_simd::ops::*;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::cpu::group_cpu, verilith_simd::neon::group_neon};

// ---------------------------------------------------------------------------
// The lookup tables compute the local condition
// ---------------------------------------------------------------------------

// simdjson's tables, once per 128-bit lane. Each bit of an entry names an
// error class; a byte pair (p1, c) is in a class when all three lookups
// have its bit. Bit 7 is the pair "continuation, continuation", which is an
// error unless a lead byte two or three back asks for it, and an error to
// miss if one does.
pub const T1X: [u8; 32] = [
    2, 2, 2, 2, 2, 2, 2, 2, 0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49,
    2, 2, 2, 2, 2, 2, 2, 2, 0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49,
];

pub const T2X: [u8; 32] = [
    0xE7, 0xA3, 0x83, 0x83, 0x8B, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xDB, 0xCB, 0xCB,
    0xE7, 0xA3, 0x83, 0x83, 0x8B, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xDB, 0xCB, 0xCB,
];

pub const T3X: [u8; 32] = [
    1, 1, 1, 1, 1, 1, 1, 1, 0xE6, 0xAE, 0xBA, 0xBA, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 0xE6, 0xAE, 0xBA, 0xBA, 1, 1, 1, 1,
];

pub open spec fn t1() -> Seq<u8> {
    seq![2u8, 2, 2, 2, 2, 2, 2, 2, 0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49]
}

pub open spec fn t2() -> Seq<u8> {
    seq![0xE7u8, 0xA3, 0x83, 0x83, 0x8B, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xDB, 0xCB, 0xCB]
}

pub open spec fn t3() -> Seq<u8> {
    seq![1u8, 1, 1, 1, 1, 1, 1, 1, 0xE6, 0xAE, 0xBA, 0xBA, 1, 1, 1, 1]
}

/// Each 32-byte table is its 16-byte table twice.
proof fn lemma_tables_x()
    ensures
        forall|k: int| 0 <= k < 32 ==> #[trigger] T1X@[k] == t1()[k % 16] && T2X@[k] == t2()[k % 16] && T3X@[k]
            == t3()[k % 16],
{
    assert forall|k: int| 0 <= k < 32 implies #[trigger] T1X@[k] == t1()[k % 16] && T2X@[k] == t2()[k % 16] && T3X@[k]
        == t3()[k % 16] by {
        assert(T1X@ =~= t1() + t1());
        assert(T2X@ =~= t2() + t2());
        assert(T3X@ =~= t3() + t3());
    }
}

/// The three lookups for the pair (p1, c), with `ch` the high nibble of c.
pub open spec fn tbl(p1: u8, ch: int) -> u8 {
    t1()[p1 as int / 16] & t2()[p1 as int % 16] & t3()[ch]
}

/// What the tables must give: bit 7 alone when a lead byte two or three
/// back needs this byte, else nothing.
pub open spec fn want(m23: bool) -> u8 {
    if m23 {
        0x80
    } else {
        0
    }
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
    if a >= b {
        (a - b) as u8
    } else {
        0
    }
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
#[inline(always)]
fn ascii67(s: &[u8], j: usize) -> (r: bool)
    requires
        avx2(),
        3 <= j,
        j + 64 <= s@.len(),
    ensures
        r ==> ascii_span(s@, j - 3, j + 64),
{
    let r = ascii64(s, j - 3) && ascii32(s, j + 32);
    proof {
        if r {
            assert forall|t: int| j - 3 <= t < j + 64 implies #[trigger] s@[t] < 0x80 by {
                if t < j + 61 {
                    assert(super::spec::ascii(s@, j - 3, j + 61));
                } else {
                    assert(super::spec::ascii(s@, j + 32, j + 64));
                }
            }
        }
    }
    r
}

/// Lane `l` of the pshufb lookup of nibble vector `nb` in the doubled table
/// `tx` is entry `nb[l]` of the 16-byte table.
proof fn lemma_lookup_lanes(tx: Seq<u8>, t: Seq<u8>, nb: Seq<u8>, r: Seq<u8>)
    requires
        tx.len() == 32,
        t.len() == 16,
        nb.len() == 32,
        forall|k: int| 0 <= k < 32 ==> #[trigger] tx[k] == t[k % 16],
        forall|k: int| 0 <= k < 32 ==> #[trigger] nb[k] < 16,
        r == shuffle8_lanes(tx, nb),
    ensures
        forall|l: int| 0 <= l < 32 ==> #[trigger] r[l] == t[nb[l] as int],
{
    assert forall|l: int| 0 <= l < 32 implies #[trigger] r[l] == t[nb[l] as int] by {
        let ix = (l / 16) * 16 + (nb[l] % 16) as int;
        assert(nb[l] % 16 == nb[l]);
        assert(ix % 16 == nb[l] as int);
        assert(r[l] == tx[ix]);
    }
}

/// The low nibbles, `v & 0x0f`.
proof fn lemma_lo_nibbles(ib: Seq<u8>, k: Seq<u8>, lb: Seq<u8>)
    requires
        ib.len() == 32 && k.len() == 32,
        k == splat8(0x0f, 32),
        lb == and8(ib, k),
    ensures
        forall|i: int| 0 <= i < 32 ==> #[trigger] lb[i] == ib[i] % 16 && lb[i] < 16,
{
    assert forall|i: int| 0 <= i < 32 implies #[trigger] lb[i] == ib[i] % 16 && lb[i] < 16 by {
        let x = ib[i];
        assert(x & 0x0f == x % 16 && x & 0x0f < 16) by (bit_vector);
    }
}

/// The error lanes for `[j, j + 32)`: lane `l` is zero exactly when `loc`
/// holds at `j + l`.
#[inline(always)]
fn err32(s: &[u8], st: usize, j: usize, tb1: __m256i, tb2: __m256i, tb3: __m256i) -> (e: __m256i)
    requires
        avx2(),
        st + 3 <= j,
        j + 32 <= s@.len(),
        b256(tb1) == T1X@,
        b256(tb2) == T2X@,
        b256(tb3) == T3X@,
    ensures
        forall|l: int| 0 <= l < 32 ==> (#[trigger] b256(e)[l] == 0) == loc(s@, st as int, j + l),
{
    let c = load256_u8(s, j);
    let p1 = load256_u8(s, j - 1);
    let p2 = load256_u8(s, j - 2);
    let p3 = load256_u8(s, j - 3);
    let k0f = _mm256_set1_epi8(0x0f);
    let sr1 = _mm256_srli_epi32::<4>(p1);
    let h1 = _mm256_and_si256(sr1, k0f);
    let l1 = _mm256_and_si256(p1, k0f);
    let src = _mm256_srli_epi32::<4>(c);
    let hc = _mm256_and_si256(src, k0f);
    let a = _mm256_shuffle_epi8(tb1, h1);
    let b = _mm256_shuffle_epi8(tb2, l1);
    let d = _mm256_shuffle_epi8(tb3, hc);
    let s2 = _mm256_subs_epu8(p2, _mm256_set1_epi8(0x60));
    let s3 = _mm256_subs_epu8(p3, _mm256_set1_epi8(0x70));
    let m = _mm256_and_si256(_mm256_or_si256(s2, s3), _mm256_set1_epi8(-128));
    let e = _mm256_xor_si256(_mm256_and_si256(_mm256_and_si256(a, b), d), m);
    proof {
        assert(u8_of_i8(0x0fi8) == 0x0f);
        assert(u8_of_i8(0x60i8) == 0x60);
        assert(u8_of_i8(0x70i8) == 0x70);
        assert(u8_of_i8(-128i8) == 0x80);
        lemma_tables_x();
        lemma_hi_nibbles(b256(p1), b256(sr1), b256(k0f), b256(h1));
        lemma_hi_nibbles(b256(c), b256(src), b256(k0f), b256(hc));
        lemma_lo_nibbles(b256(p1), b256(k0f), b256(l1));
        assert forall|k: int| 0 <= k < 32 implies #[trigger] b256(h1)[k] < 16 by {
            let x = b256(p1)[k];
            assert(x >> 4 < 16) by (bit_vector);
        }
        assert forall|k: int| 0 <= k < 32 implies #[trigger] b256(hc)[k] < 16 by {
            let y = b256(c)[k];
            assert(y >> 4 < 16) by (bit_vector);
        }
        lemma_lookup_lanes(b256(tb1), t1(), b256(h1), b256(a));
        lemma_lookup_lanes(b256(tb2), t2(), b256(l1), b256(b));
        lemma_lookup_lanes(b256(tb3), t3(), b256(hc), b256(d));
        assert forall|l: int| 0 <= l < 32 implies (#[trigger] b256(e)[l] == 0) == loc(s@, st as int, j + l) by {
            let k = j + l;
            let (x3, x2, x1, x) = (s@[k - 3], s@[k - 2], s@[k - 1], s@[k]);
            assert(b256(p1)[l] == x1 && b256(c)[l] == x && b256(p2)[l] == x2 && b256(p3)[l] == x3);
            assert(x1 >> 4 == x1 / 16 && x >> 4 == x / 16) by (bit_vector);
            assert(b256(a)[l] == t1()[x1 as int / 16]);
            assert(b256(b)[l] == t2()[x1 as int % 16]);
            assert(b256(d)[l] == t3()[x as int / 16]);
            assert(b256(s2)[l] == subs(x2, 0x60));
            assert(b256(s3)[l] == subs(x3, 0x70));
            assert(b256(e)[l] == (tbl(x1, x as int / 16) ^ ((subs(x2, 0x60) | subs(x3, 0x70)) & 0x80)));
            lemma_err_lane(x3, x2, x1, x);
            assert(ub(s@, st as int, k - 3) == x3 && ub(s@, st as int, k - 2) == x2 && ub(s@, st as int, k - 1) == x1
                && ub(s@, st as int, k) == x);
        }
    }
    e
}

/// `loc` on `[j, j + 64)` from two error vectors, tested once.
#[inline(always)]
fn pair32_ok(s: &[u8], st: usize, j: usize, tb1: __m256i, tb2: __m256i, tb3: __m256i) -> (r: bool)
    requires
        avx2(),
        st + 3 <= j,
        j + 64 <= s.len(),
        b256(tb1) == T1X@,
        b256(tb2) == T2X@,
        b256(tb3) == T3X@,
    ensures
        r == all_loc(s@, st as int, j as int, j + 64),
{
    let a = err32(s, st, j, tb1, tb2, tb3);
    let b = err32(s, st, j + 32, tb1, tb2, tb3);
    let e = _mm256_or_si256(a, b);
    let zero = _mm256_setzero_si256();
    let c = _mm256_cmpeq_epi8(e, zero);
    let mm = _mm256_movemask_epi8(c);
    proof {
        lemma_all_zero(b256(e), b256(zero), b256(c), mm);
        let g = s@;
        let si = st as int;
        let ji = j as int;
        assert forall|l: int| 0 <= l < 32 implies (#[trigger] b256(e)[l] == 0) == (loc(g, si, ji + l) && loc(
            g,
            si,
            ji + 32 + l,
        )) by {
            let (x, y) = (b256(a)[l], b256(b)[l]);
            assert((x | y == 0) == (x == 0 && y == 0)) by (bit_vector);
        }
        if mm == -1 {
            assert forall|k: int| ji <= k < ji + 64 implies #[trigger] loc(g, si, k) by {
                if k < ji + 32 {
                    assert(b256(e)[k - ji] == 0);
                } else {
                    assert(b256(e)[k - ji - 32] == 0);
                }
            }
        } else {
            let l = choose|l: int| 0 <= l < 32 && #[trigger] b256(e)[l] != 0;
            if !loc(g, si, ji + l) {
                assert(!all_loc(g, si, ji, ji + 64));
            } else {
                assert(!loc(g, si, ji + 32 + l));
                assert(!all_loc(g, si, ji, ji + 64));
            }
        }
    }
    mm == -1
}

/// `loc` on `[j, j + 128)`, away from the start of the text.
#[inline(always)]
fn chunk128(s: &[u8], st: usize, j: usize, tb1: __m256i, tb2: __m256i, tb3: __m256i) -> (r: bool)
    requires
        avx2(),
        st + 3 <= j,
        j + 128 <= s.len(),
        b256(tb1) == T1X@,
        b256(tb2) == T2X@,
        b256(tb3) == T3X@,
    ensures
        r == all_loc(s@, st as int, j as int, j + 128),
{
    let ghost g = s@;
    let ghost si = st as int;
    let ghost ji = j as int;
    proof {
        lemma_all_loc_split(g, si, ji, ji + 64, ji + 128);
    }
    let lo = if ascii67(s, j) {
        proof {
            lemma_ascii_span(g, si, ji, ji + 64);
        }
        true
    } else {
        pair32_ok(s, st, j, tb1, tb2, tb3)
    };
    if !lo {
        return false;
    }
    if ascii67(s, j + 64) {
        proof {
            lemma_ascii_span(g, si, ji + 64, ji + 128);
        }
        return true;
    }
    pair32_ok(s, st, j + 64, tb1, tb2, tb3)
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
fn utf8_start(s: &[u8], st: usize) -> (r: (usize, bool))
    requires
        st <= s@.len(),
    ensures
        u8_state(s@, st as int, r.0 as int, r.1),
        s@.len() - st >= 3 ==> r.0 == st + 3,
{
    if s.len() - st >= 3 && get(s, st) < 0x80 && get(s, st + 1) < 0x80 && get(s, st + 2) < 0x80 {
        proof {
            assert forall|k: int| st <= k < st + 3 implies #[trigger] loc(s@, st as int, k) by {}
        }
        return (st + 3, true);
    }
    let h = if s.len() - st < 3 { s.len() } else { st + 3 };
    (h, ex_all_loc(s, st, st, h))
}

/// Whether `s[st..]` is well-formed UTF-8, 128 bytes at a time.
#[inline(always)]
fn utf8_avx2_body(s: &[u8], st: usize) -> (r: bool)
    requires
        avx2(),
        st <= s@.len(),
    ensures
        r == utf8_from(s@, st as int),
{
    let n = s.len();
    let (uj, ok) = utf8_start(s, st);
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
    let tb1 = load256_u8(T1X.as_slice(), 0);
    let tb2 = load256_u8(T2X.as_slice(), 0);
    let tb3 = load256_u8(T3X.as_slice(), 0);
    proof {
        assert(T1X@.subrange(0, 32) =~= T1X@);
        assert(T2X@.subrange(0, 32) =~= T2X@);
        assert(T3X@.subrange(0, 32) =~= T3X@);
    }
    let mut j = uj;
    let mut ok = ok;
    while ok && 128 <= n - j
        invariant
            avx2(),
            n == s@.len(),
            u8_state(s@, st as int, j as int, ok),
            b256(tb1) == T1X@,
            b256(tb2) == T2X@,
            b256(tb3) == T3X@,
        decreases n - j,
    {
        let c = chunk128(s, st, j, tb1, tb2, tb3);
        proof {
            lemma_all_loc_split(s@, st as int, st as int, j as int, j + 128);
        }
        ok = c;
        j = j + 128;
    }
    if !ok {
        proof {
            lemma_all_loc_split(s@, st as int, st as int, j as int, n as int);
        }
        return false;
    }
    let rest = if j < n && n - st >= 131 {
        // Once more, overlapping, to reach the end.
        let c = chunk128(s, st, n - 128, tb1, tb2, tb3);
        proof {
            lemma_all_loc_split(s@, st as int, st as int, n - 128, n as int);
            lemma_all_loc_split(s@, st as int, (n - 128) as int, j as int, n as int);
            lemma_all_loc_split(s@, st as int, st as int, n - 128, j as int);
        }
        c
    } else {
        ex_all_loc(s, st, j, n)
    };
    proof {
        lemma_all_loc_split(s@, st as int, st as int, j as int, n as int);
    }
    rest && ex_tail(s, st)
}

/// Trusted: `utf8_avx2_body` compiled with `avx2` enabled, through
/// `tf::utf8_avx2`; the contract is `utf8_avx2_body`'s, which is verified.
#[verifier::external_body]
fn utf8_avx2(s: &[u8], st: usize) -> (r: bool)
    requires
        avx2(),
        st <= s@.len(),
    ensures
        r == utf8_from(s@, st as int),
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::utf8_avx2(s, st) };
    #[cfg(not(target_arch = "x86_64"))]
    return utf8_avx2_body(s, st);
}

// ---------------------------------------------------------------------------
// NEON validator
// ---------------------------------------------------------------------------

pub const T1: [u8; 16] = [2, 2, 2, 2, 2, 2, 2, 2, 0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49];

pub const T2: [u8; 16] = [0xE7, 0xA3, 0x83, 0x83, 0x8B, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xDB, 0xCB, 0xCB];

pub const T3: [u8; 16] = [1, 1, 1, 1, 1, 1, 1, 1, 0xE6, 0xAE, 0xBA, 0xBA, 1, 1, 1, 1];

/// `ushr #4` gives the high nibble.
proof fn lemma_shr4(a: Seq<u8>, r: Seq<u8>)
    requires
        a.len() == 16,
        r == shr8(a, 4),
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] r[i] == a[i] / 16 && r[i] < 16,
{
    lemma_pow2_spec();
}

/// The error lanes for `[j, j + 16)`, as `err32`.
#[inline(always)]
fn err16(s: &[u8], st: usize, j: usize, tb1: uint8x16_t, tb2: uint8x16_t, tb3: uint8x16_t) -> (e: uint8x16_t)
    requires
        neon(),
        st + 3 <= j,
        j + 16 <= s@.len(),
        n8(tb1) == t1(),
        n8(tb2) == t2(),
        n8(tb3) == t3(),
    ensures
        forall|l: int| 0 <= l < 16 ==> (#[trigger] n8(e)[l] == 0) == loc(s@, st as int, j + l),
{
    let c = vld1q_u8_at(s, j);
    let p1 = vld1q_u8_at(s, j - 1);
    let p2 = vld1q_u8_at(s, j - 2);
    let p3 = vld1q_u8_at(s, j - 3);
    let h1 = vshrq_n_u8::<4>(p1);
    let l1 = vandq_u8(p1, vdupq_n_u8(0x0f));
    let hc = vshrq_n_u8::<4>(c);
    let a = vqtbl1q_u8(tb1, h1);
    let b = vqtbl1q_u8(tb2, l1);
    let d = vqtbl1q_u8(tb3, hc);
    let s2 = vqsubq_u8(p2, vdupq_n_u8(0x60));
    let s3 = vqsubq_u8(p3, vdupq_n_u8(0x70));
    let m = vandq_u8(vorrq_u8(s2, s3), vdupq_n_u8(0x80));
    let e = veorq_u8(vandq_u8(vandq_u8(a, b), d), m);
    proof {
        lemma_shr4(n8(p1), n8(h1));
        lemma_shr4(n8(c), n8(hc));
        assert forall|l: int| 0 <= l < 16 implies (#[trigger] n8(e)[l] == 0) == loc(s@, st as int, j + l) by {
            let k = j + l;
            let (x3, x2, x1, x) = (s@[k - 3], s@[k - 2], s@[k - 1], s@[k]);
            assert(n8(p1)[l] == x1 && n8(c)[l] == x && n8(p2)[l] == x2 && n8(p3)[l] == x3);
            assert(x1 & 0x0f == x1 % 16 && x1 & 0x0f < 16) by (bit_vector);
            assert(n8(l1)[l] == x1 % 16);
            assert(n8(a)[l] == t1()[x1 as int / 16]);
            assert(n8(b)[l] == t2()[x1 as int % 16]);
            assert(n8(d)[l] == t3()[x as int / 16]);
            assert(n8(s2)[l] == subs(x2, 0x60));
            assert(n8(s3)[l] == subs(x3, 0x70));
            assert(n8(e)[l] == (tbl(x1, x as int / 16) ^ ((subs(x2, 0x60) | subs(x3, 0x70)) & 0x80)));
            lemma_err_lane(x3, x2, x1, x);
            assert(ub(s@, st as int, k - 3) == x3 && ub(s@, st as int, k - 2) == x2 && ub(s@, st as int, k - 1) == x1
                && ub(s@, st as int, k) == x);
        }
    }
    e
}

/// The OR of two vectors is zero in a lane exactly when both are.
proof fn lemma_or_zero(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>)
    requires
        a.len() == 16 && b.len() == 16,
        r == or8(a, b),
    ensures
        forall|l: int| 0 <= l < 16 ==> (#[trigger] r[l] == 0) == (a[l] == 0 && b[l] == 0),
{
    assert forall|l: int| 0 <= l < 16 implies (#[trigger] r[l] == 0) == (a[l] == 0 && b[l] == 0) by {
        let (x, y) = (a[l], b[l]);
        assert((x | y == 0) == (x == 0 && y == 0)) by (bit_vector);
    }
}

/// `loc` on `[j, j + 64)` from four error vectors, tested once.
#[inline(always)]
fn quad16_ok(s: &[u8], st: usize, j: usize, tb1: uint8x16_t, tb2: uint8x16_t, tb3: uint8x16_t) -> (r: bool)
    requires
        neon(),
        st + 3 <= j,
        j + 64 <= s.len(),
        n8(tb1) == t1(),
        n8(tb2) == t2(),
        n8(tb3) == t3(),
    ensures
        r == all_loc(s@, st as int, j as int, j + 64),
{
    let e0 = err16(s, st, j, tb1, tb2, tb3);
    let e1 = err16(s, st, j + 16, tb1, tb2, tb3);
    let e2 = err16(s, st, j + 32, tb1, tb2, tb3);
    let e3 = err16(s, st, j + 48, tb1, tb2, tb3);
    let a = vorrq_u8(e0, e1);
    let b = vorrq_u8(e2, e3);
    let e = vorrq_u8(a, b);
    let mx = vmaxvq_u8(e);
    proof {
        let g = s@;
        let si = st as int;
        let ji = j as int;
        lemma_or_zero(n8(e0), n8(e1), n8(a));
        lemma_or_zero(n8(e2), n8(e3), n8(b));
        lemma_or_zero(n8(a), n8(b), n8(e));
        if mx == 0 {
            assert forall|k: int| ji <= k < ji + 64 implies #[trigger] loc(g, si, k) by {
                let l = (k - ji) % 16;
                assert(n8(e)[l] <= mx);
                assert(n8(e)[l] == 0);
                if k < ji + 16 {
                    assert(n8(e0)[k - ji] == 0);
                } else if k < ji + 32 {
                    assert(n8(e1)[k - ji - 16] == 0);
                } else if k < ji + 48 {
                    assert(n8(e2)[k - ji - 32] == 0);
                } else {
                    assert(n8(e3)[k - ji - 48] == 0);
                }
            }
        } else {
            let l = choose|l: int| 0 <= l < 16 && #[trigger] n8(e)[l] == mx;
            assert(n8(e)[l] != 0);
            if !loc(g, si, ji + l) {
            } else if !loc(g, si, ji + 16 + l) {
            } else if !loc(g, si, ji + 32 + l) {
            } else {
                assert(!loc(g, si, ji + 48 + l));
            }
            assert(!all_loc(g, si, ji, ji + 64));
        }
    }
    mx == 0
}

/// No byte of the OR of two vectors has its top bit unless one does.
proof fn lemma_or_ascii(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>)
    requires
        a.len() == 16 && b.len() == 16,
        r == or8(a, b),
    ensures
        forall|l: int| 0 <= l < 16 ==> (#[trigger] r[l] < 0x80 ==> a[l] < 0x80 && b[l] < 0x80),
{
    assert forall|l: int| 0 <= l < 16 implies #[trigger] r[l] >= 0x80 || (a[l] < 0x80 && b[l] < 0x80) by {
        let (x, y) = (a[l], b[l]);
        assert((x | y) >= 0x80 || (x < 0x80 && y < 0x80)) by (bit_vector);
    }
}

/// Whether `s[j - 3 .. j + 64]` is all ASCII, in five loads.
#[inline(always)]
fn ascii67_neon(s: &[u8], j: usize) -> (r: bool)
    requires
        neon(),
        3 <= j,
        j + 64 <= s.len(),
    ensures
        r ==> ascii_span(s@, j - 3, j + 64),
{
    let v0 = vld1q_u8_at(s, j - 3);
    let v1 = vld1q_u8_at(s, j + 13);
    let v2 = vld1q_u8_at(s, j + 29);
    let v3 = vld1q_u8_at(s, j + 45);
    let v4 = vld1q_u8_at(s, j + 48);
    let a = vorrq_u8(v0, v1);
    let b = vorrq_u8(v2, v3);
    let c = vorrq_u8(a, b);
    let e = vorrq_u8(c, v4);
    let mx = vmaxvq_u8(e);
    proof {
        if mx < 0x80 {
            lemma_or_ascii(n8(v0), n8(v1), n8(a));
            lemma_or_ascii(n8(v2), n8(v3), n8(b));
            lemma_or_ascii(n8(a), n8(b), n8(c));
            lemma_or_ascii(n8(c), n8(v4), n8(e));
            assert forall|t: int| j - 3 <= t < j + 64 implies #[trigger] s@[t] < 0x80 by {
                if t < j + 13 {
                    assert(n8(e)[t - (j - 3)] <= mx);
                    assert(n8(v0)[t - (j - 3)] == s@[t]);
                } else if t < j + 29 {
                    assert(n8(e)[t - (j + 13)] <= mx);
                    assert(n8(v1)[t - (j + 13)] == s@[t]);
                } else if t < j + 45 {
                    assert(n8(e)[t - (j + 29)] <= mx);
                    assert(n8(v2)[t - (j + 29)] == s@[t]);
                } else if t < j + 61 {
                    assert(n8(e)[t - (j + 45)] <= mx);
                    assert(n8(v3)[t - (j + 45)] == s@[t]);
                } else {
                    assert(n8(e)[t - (j + 48)] <= mx);
                    assert(n8(v4)[t - (j + 48)] == s@[t]);
                }
            }
        }
    }
    mx < 0x80
}

/// `loc` on `[j, j + 64)`, away from the start of the text.
#[inline(always)]
fn chunk64_neon(s: &[u8], st: usize, j: usize, tb1: uint8x16_t, tb2: uint8x16_t, tb3: uint8x16_t) -> (r: bool)
    requires
        neon(),
        st + 3 <= j,
        j + 64 <= s.len(),
        n8(tb1) == t1(),
        n8(tb2) == t2(),
        n8(tb3) == t3(),
    ensures
        r == all_loc(s@, st as int, j as int, j + 64),
{
    if ascii67_neon(s, j) {
        proof {
            lemma_ascii_span(s@, st as int, j as int, j + 64);
        }
        return true;
    }
    quad16_ok(s, st, j, tb1, tb2, tb3)
}

/// Whether `s[st..]` is well-formed UTF-8, 64 bytes at a time with NEON.
fn utf8_neon(s: &[u8], st: usize) -> (r: bool)
    requires
        neon(),
        st <= s@.len(),
    ensures
        r == utf8_from(s@, st as int),
{
    let n = s.len();
    let (uj, ok) = utf8_start(s, st);
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
    let tb1 = vld1q_u8_at(T1.as_slice(), 0);
    let tb2 = vld1q_u8_at(T2.as_slice(), 0);
    let tb3 = vld1q_u8_at(T3.as_slice(), 0);
    proof {
        assert(T1@.subrange(0, 16) =~= t1());
        assert(T2@.subrange(0, 16) =~= t2());
        assert(T3@.subrange(0, 16) =~= t3());
    }
    let mut j = uj;
    let mut ok = ok;
    while ok && 64 <= n - j
        invariant
            neon(),
            n == s@.len(),
            u8_state(s@, st as int, j as int, ok),
            n8(tb1) == t1(),
            n8(tb2) == t2(),
            n8(tb3) == t3(),
        decreases n - j,
    {
        let c = chunk64_neon(s, st, j, tb1, tb2, tb3);
        proof {
            lemma_all_loc_split(s@, st as int, st as int, j as int, j + 64);
        }
        ok = c;
        j = j + 64;
    }
    if !ok {
        proof {
            lemma_all_loc_split(s@, st as int, st as int, j as int, n as int);
        }
        return false;
    }
    let rest = if j < n && n - st >= 67 {
        // Once more, overlapping, to reach the end.
        let c = chunk64_neon(s, st, n - 64, tb1, tb2, tb3);
        proof {
            lemma_all_loc_split(s@, st as int, st as int, n - 64, n as int);
            lemma_all_loc_split(s@, st as int, (n - 64) as int, j as int, n as int);
            lemma_all_loc_split(s@, st as int, st as int, n - 64, j as int);
        }
        c
    } else {
        ex_all_loc(s, st, j, n)
    };
    proof {
        lemma_all_loc_split(s@, st as int, st as int, j as int, n as int);
    }
    rest && ex_tail(s, st)
}

/// Whether `s` is well-formed UTF-8.
pub fn utf8_valid(s: &[u8]) -> (r: bool)
    ensures
        r == utf8_from(s@, 0),
{
    if has_avx2() {
        // SAFETY: the CPU has AVX2.
        unsafe { utf8_avx2(s, 0) }
    } else if has_neon() {
        utf8_neon(s, 0)
    } else {
        utf8_valid_scalar(s, 0)
    }
}

} // verus!

/// Trampolines that compile a verified `*_body` function with the target
/// features its kernel needs. Each is one call; `#[target_feature]` only
/// changes code generation. Verus rejects the attribute on verified code
/// (verus-lang/verus#3362), so it lives outside `verus!`.
#[cfg(target_arch = "x86_64")]
mod tf {
    #[allow(unused_imports)]
    use super::*;

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn utf8_avx2(s: &[u8], st: usize) -> bool {
        utf8_avx2_body(s, st)
    }
}

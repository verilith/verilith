//! Correctly rounded conversion of `w * 10^q` to a binary64 bit pattern.
//!
//! Everything here is integer arithmetic, so it is verified like the rest
//! of the parser. The result is a `u64` bit pattern; turning it into an
//! `f64` (`f64::from_bits`) is the only step outside the proof, and it is
//! the definition of the binary64 format.
#[allow(unused_imports)]
use crate::pow5::{POW5_HI, POW5_LO};
#[allow(unused_imports)]
use vstd::arithmetic::power::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use verilith_core::binary64 as b64;

verus! {

// ---------------------------------------------------------------------------
// Powers, fast enough to evaluate
// ---------------------------------------------------------------------------

/// `b^e` by squaring, so that `by (compute_only)` can evaluate it for the
/// exponents of the table (up to about 1000).
pub open spec fn fpow(b: int, e: nat) -> int
    decreases e,
{
    if e == 0 {
        1
    } else if e % 2 == 0 {
        let h = fpow(b, e / 2);
        h * h
    } else {
        b * fpow(b, (e - 1) as nat)
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_fpow(b: int, e: nat)
    ensures
        fpow(b, e) == pow(b, e),
    decreases e,
{
    reveal(pow);
    if e == 0 {
    } else if e % 2 == 0 {
        lemma_fpow(b, e / 2);
        lemma_pow_adds(b, e / 2, e / 2);
    } else {
        lemma_fpow(b, (e - 1) as nat);
    }
}

// ---------------------------------------------------------------------------
// The power-of-five table
// ---------------------------------------------------------------------------

/// `floor(q * log2(10))` for `q` in `-342..=308`, as the code computes it:
/// `(q * 217706) >> 16`.
pub open spec fn flog10(q: int) -> int {
    (q * 217706) / 65536
}

/// The table entry for `q` is 5^q scaled by 2^`shift(q)` into
/// `[2^127, 2^128)`.
pub open spec fn shift(q: int) -> int {
    127 + q - flog10(q)
}

/// The 128-bit table entry for `q`.
pub open spec fn tab(q: int) -> int {
    POW5_HI@[q + 342] as int * 0x1_0000_0000_0000_0000 + POW5_LO@[q + 342] as int
}

/// What the entry for `q` is, with `p5 = 5^|q|` and `p2 = 2^|shift(q)|`:
/// within 1 of `5^q * 2^shift(q)`, which itself lies in `[2^127, 2^128)`;
/// exactly equal when that is an integer.
pub open spec fn tab_ok_with(q: int, t: int, p5: int, p2: int) -> bool {
    let lo = fpow(2, 127);
    let hi = fpow(2, 128);
    if q >= 0 && shift(q) >= 0 {
        t == p5 * p2 && lo <= t < hi
    } else if q >= 0 {
        // t = floor(5^q / 2^-shift)
        t * p2 <= p5 < (t + 1) * p2 && lo * p2 <= p5 < hi * p2
    } else {
        // |t - 2^shift / 5^-q| < 1
        p2 - p5 < t * p5 < p2 + p5 && lo * p5 <= p2 < hi * p5
    }
}

pub open spec fn tab_ok(q: int) -> bool {
    let s = shift(q);
    (0 <= q <= 55 ==> s >= 0) && (q < 0 ==> s >= 0) && -600 <= s <= 1000 && fpow(2, 127) <= tab(q) < fpow(2, 128) && tab_ok_with(
        q,
        tab(q),
        fpow(5, (if q >= 0 { q } else { -q }) as nat),
        fpow(2, (if s >= 0 { s } else { -s }) as nat),
    )
}

pub open spec fn tab_ok_from(q: int, n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        tab_ok(q) && tab_ok_from(q + 1, (n - 1) as nat)
    }
}

#[verifier::spinoff_prover]
proof fn lemma_tab_from(q: int, n: nat, k: int)
    requires
        tab_ok_from(q, n),
        q <= k < q + n,
    ensures
        tab_ok(k),
    decreases n,
{
    if k != q {
        lemma_tab_from(q + 1, (n - 1) as nat, k);
    }
}

/// The table is right: every entry checked by evaluation.
#[verifier::spinoff_prover]
pub proof fn lemma_tab(q: int)
    requires
        -342 <= q <= 308,
    ensures
        tab_ok(q),
{
    assert(tab_ok_from(-342, 651)) by (compute_only);
    lemma_tab_from(-342, 651, q);
}

// ---------------------------------------------------------------------------
// What correct rounding means
// ---------------------------------------------------------------------------

pub open spec fn pos(x: int) -> nat {
    if x > 0 { x as nat } else { 0 }
}

/// `w * 10^q` times `5^-q * 2^(2048 - q)` (only the factors that are not
/// already cancelled), an integer.
pub open spec fn vs(w: int, q: int) -> int {
    w * pow(5, pos(q)) * pow2(pos(q) + 2048) as int
}

/// `2^f` times the same factor, for `f >= -2048`: `vs(w, q) < z * cz(q, f)`
/// exactly when `w * 10^q < z * 2^f`.
pub open spec fn cz(q: int, f: int) -> int {
    pow(5, pos(-q)) * pow2((pos(-q) + f + 2048) as nat) as int
}

/// `w * 10^q < z * 2^f`.
pub open spec fn below(w: int, q: int, z: int, f: int) -> bool {
    vs(w, q) < z * cz(q, f)
}

/// `w * 10^q == z * 2^f`.
pub open spec fn equal(w: int, q: int, z: int, f: int) -> bool {
    vs(w, q) == z * cz(q, f)
}

/// The bit pattern of +infinity.
pub const INF: u64 = 0x7FF0_0000_0000_0000;

/// The biased exponent and the fraction of a bit pattern.
pub open spec fn bexp(b: u64) -> int {
    b as int / 0x10_0000_0000_0000
}

pub open spec fn frac(b: u64) -> int {
    b as int % 0x10_0000_0000_0000
}

/// A finite non-negative double `b` is `sig(b) * 2^ex(b)`.
pub open spec fn sig(b: u64) -> int {
    if bexp(b) == 0 { frac(b) } else { frac(b) + 0x10_0000_0000_0000 }
}

pub open spec fn ex(b: u64) -> int {
    if bexp(b) == 0 { -1074 } else { bexp(b) - 1075 }
}

/// `b` is `w * 10^q` rounded to the nearest double, ties to even: the
/// value lies between the midpoints to the neighbouring doubles, and on a
/// midpoint only if `b`'s significand is even. The midpoint below is a
/// quarter step down at the bottom of a binade, where the double below is
/// half a step away. Values from the midpoint above the largest double,
/// `(2^54 - 1) * 2^970`, round to infinity.
pub open spec fn is_round(w: int, q: int, b: u64) -> bool {
    if b == INF {
        !below(w, q, 0x3F_FFFF_FFFF_FFFF, 970)
    } else if b < INF {
        let m = sig(b);
        let e = ex(b);
        let even = m % 2 == 0;
        let (zl, fl) = if frac(b) == 0 && bexp(b) > 1 { (4 * m - 1, e - 2) } else { (2 * m - 1, e - 1) };
        (!below(w, q, zl, fl) && (even || !equal(w, q, zl, fl)))
            && (below(w, q, 2 * m + 1, e - 1) || (even && equal(w, q, 2 * m + 1, e - 1)))
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// Integer steps
// ---------------------------------------------------------------------------

pub open spec fn two64() -> int {
    0x1_0000_0000_0000_0000
}

#[verifier::bit_vector]
proof fn bv_top(w: u64, lz: u64)
    requires
        lz < 64,
        (w >> sub(63u64, lz)) & 1u64 != 0u64,
    ensures
        (w << lz) >= 0x8000_0000_0000_0000,
{
}

/// `w` shifted left until its top bit is set, and the shift.
#[inline(always)]
#[verifier::spinoff_prover]
fn norm(w: u64) -> (r: (u64, u32))
    requires
        w != 0,
    ensures
        r.1 < 64,
        r.0 as int == w as int * pow2(r.1 as nat),
        r.0 >= 0x8000_0000_0000_0000,
{
    let lz = w.leading_zeros();
    proof {
        vstd::std_specs::bits::axiom_u64_leading_zeros(w);
        reveal(vstd::std_specs::bits::u64_leading_zeros);
        assert(lz < 64);
        bv_top(w, lz as u64);
        if lz > 0 {
            vstd::bits::lemma_u64_shr_is_div(w, (64 - lz) as u64);
            lemma_pow2_adds(lz as nat, (64 - lz) as nat);
            lemma_pow2_pos(lz as nat);
            lemma_pow2_pos((64 - lz) as nat);
            // w / 2^(64 - lz) == 0, so w < 2^(64 - lz).
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(w as int, pow2((64 - lz) as nat) as int);
            assert(w < pow2((64 - lz) as nat)) by (nonlinear_arith)
                requires
                    w as int / pow2((64 - lz) as nat) as int == 0,
                    w as int == pow2((64 - lz) as nat) * (w as int / pow2((64 - lz) as nat) as int) + w as int % pow2((64 - lz) as nat) as int,
                    (w as int % pow2((64 - lz) as nat) as int) < pow2((64 - lz) as nat),
            ;
            assert(w * pow2(lz as nat) < pow2(64)) by (nonlinear_arith)
                requires
                    w < pow2((64 - lz) as nat),
                    pow2(lz as nat) > 0,
                    pow2(lz as nat) * pow2((64 - lz) as nat) == pow2(64),
            ;
        }
        lemma2_to64();
        lemma2_to64_rest();
        assert(pow2(64) == 0x1_0000_0000_0000_0000);
        if lz == 0 {
            assert(pow2(lz as nat) == 1);
        }
        assert(w * pow2(lz as nat) <= u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(w, lz as u64);
    }
    (w << lz, lz)
}

#[verifier::bit_vector]
proof fn bv_split128(a: u128)
    ensures
        (a >> 64u32) as u64 as u128 * 0x1_0000_0000_0000_0000u128 + a as u64 as u128 == a,
{
}

/// The 192-bit product `wn * (th * 2^64 + tl)`, as three 64-bit limbs,
/// high first.
#[inline(always)]
#[verifier::spinoff_prover]
fn mul192(wn: u64, th: u64, tl: u64) -> (r: (u64, u64, u64))
    ensures
        r.0 as int * two64() * two64() + r.1 as int * two64() + r.2 as int
            == wn as int * (th as int * two64() + tl as int),
{
    proof {
        assert((wn as int * th as int) <= u128::MAX && (wn as int * tl as int) <= u128::MAX) by (nonlinear_arith)
            requires wn <= u64::MAX, th <= u64::MAX, tl <= u64::MAX;
    }
    let a = (wn as u128) * (th as u128);
    let b = (wn as u128) * (tl as u128);
    let ah = (a >> 64u32) as u64;
    let al = a as u64;
    let bh = (b >> 64u32) as u64;
    let p0 = b as u64;
    proof {
        bv_split128(a);
        bv_split128(b);
    }
    let mid = al as u128 + bh as u128;
    let mc = (mid >> 64u32) as u64;
    let p1 = mid as u64;
    proof {
        bv_split128(mid);
        lemma_carry(wn as int, th as int, ah as int, al as int, bh as int, mc as int, p1 as int);
    }
    let p2 = ah + mc;
    proof {
        lemma_limbs(wn as int, th as int, tl as int, ah as int, al as int, bh as int, p0 as int, mc as int, p1 as int, p2 as int);
    }
    (p2, p1, p0)
}

#[verifier::spinoff_prover]
proof fn lemma_carry(wn: int, th: int, ah: int, al: int, bh: int, mc: int, p1: int)
    requires
        0 <= wn < two64(),
        0 <= th < two64(),
        0 <= al < two64(),
        0 <= bh < two64(),
        0 <= p1,
        ah * two64() + al == wn * th,
        mc * two64() + p1 == al + bh,
    ensures
        ah + mc < two64(),
{
    let t = two64();
    assert(wn * th <= (t - 1) * (t - 1)) by (nonlinear_arith)
        requires 0 <= wn < t, 0 <= th < t;
    assert(ah <= t - 2) by (nonlinear_arith)
        requires ah * t + al <= (t - 1) * (t - 1), 0 <= al, t == two64();
    assert(mc <= 1) by (nonlinear_arith)
        requires mc * t + p1 == al + bh, 0 <= p1, al < t, bh < t, t == two64();
}

#[verifier::spinoff_prover]
proof fn lemma_limbs(wn: int, th: int, tl: int, ah: int, al: int, bh: int, p0: int, mc: int, p1: int, p2: int)
    requires
        ah * two64() + al == wn * th,
        bh * two64() + p0 == wn * tl,
        mc * two64() + p1 == al + bh,
        p2 == ah + mc,
    ensures
        p2 * two64() * two64() + p1 * two64() + p0 == wn * (th * two64() + tl),
{
    let t = two64();
    assert(wn * (th * t + tl) == (wn * th) * t + wn * tl) by (nonlinear_arith);
    assert((ah * t + al) * t == ah * t * t + al * t) by (nonlinear_arith);
    assert((ah + mc) * t * t == ah * t * t + mc * t * t) by (nonlinear_arith);
    assert((mc * t + p1) * t == mc * t * t + p1 * t) by (nonlinear_arith);
    assert((al + bh) * t == al * t + bh * t) by (nonlinear_arith);
}

pub open spec fn r_eq(p2: u64, p1: u64, p0: u64, wn: u64, th: u64, tl: u64) -> bool {
    p2 as int * two64() * two64() + p1 as int * two64() + p0 as int
        == wn as int * (th as int * two64() + tl as int)
}


// ---------------------------------------------------------------------------
// From the table to the value
// ---------------------------------------------------------------------------

#[verifier::spinoff_prover]
pub proof fn lemma_cz_shift(q: int, f: int, j: nat)
    requires
        pos(-q) + f + 2048 >= 0,
    ensures
        cz(q, f + j) == cz(q, f) * pow2(j),
        cz(q, f) > 0,
{
    let n = (pos(-q) + f + 2048) as nat;
    lemma_pow2_adds(n, j);
    assert((pos(-q) + (f + j) + 2048) as nat == n + j);
    lemma_pow_positive(5, pos(-q));
    lemma_pow2_pos(n);
    let a = pow(5, pos(-q));
    assert(a * (pow2(n) * pow2(j)) == (a * pow2(n)) * pow2(j)) by (nonlinear_arith);
    assert(a * pow2(n) > 0) by (nonlinear_arith) requires a > 0, pow2(n) > 0;
}

#[verifier::spinoff_prover]
proof fn lemma_pow2_fpow(n: nat)
    ensures
        fpow(2, n) == pow2(n),
{
    lemma_fpow(2, n);
    lemma_pow_positive(2, n);
}

/// The product of the normalized significand and the table entry, `p`,
/// approximates the value: `w * 10^q` lies strictly within `2^64` units of
/// `p * 2^k`, and equals it when the entry is exact.
#[verifier::spinoff_prover]
pub proof fn lemma_interval(w: int, q: int, lz: nat, wn: int, p: int)
    requires
        -342 <= q <= 308,
        1 <= w,
        lz < 64,
        wn == w * pow2(lz),
        wn < two64(),
        p == wn * tab(q),
    ensures
        ({
            let c = cz(q, q - shift(q) - lz);
            &&& c > 0
            &&& (p - two64()) * c < vs(w, q) < (p + two64()) * c
            &&& (0 <= q <= 55 ==> vs(w, q) == p * c)
        }),
{
    lemma_tab(q);
    let s = shift(q);
    let k = q - s - lz;
    let c = cz(q, k);
    let t = tab(q);
    lemma_pow2_pos(lz);
    if q >= 0 {
        lemma_fpow(5, q as nat);
        let p5 = pow(5, q as nat);
        assert(pos(-q) == 0);
        reveal(pow);
        assert(pow(5, 0) == 1);
        let n = (k + 2048) as nat;
        assert(c == pow2(n));
        let v2 = pow2((q + 2048) as nat);
        assert(vs(w, q) == w * p5 * v2);
        if s >= 0 {
            lemma_pow2_fpow(s as nat);
            assert(t == p5 * pow2(s as nat));
            // p * c = w * 2^lz * 5^q * 2^s * 2^(q - s - lz + 2048) = w * 5^q * 2^(q + 2048)
            lemma_pow2_adds(lz, s as nat);
            lemma_pow2_adds(lz + s as nat, n);
            assert(lz + s + n == q + 2048);
            assert(p * c == w * p5 * v2) by (nonlinear_arith)
                requires
                    p == wn * t, wn == w * pow2(lz), t == p5 * pow2(s as nat), c == pow2(n),
                    pow2(lz) * pow2(s as nat) == pow2(lz + s as nat),
                    pow2(lz + s as nat) * pow2(n) == v2,
                    v2 == pow2((q + 2048) as nat), (lz + s as nat + n) == (q + 2048),
            ;
            lemma_pow2_pos(n);
            assert((p - two64()) * c < p * c < (p + two64()) * c) by (nonlinear_arith)
                requires c > 0, two64() > 0;
        } else {
            let d = (-s) as nat;
            lemma_pow2_fpow(d);
            let p2d = pow2(d);
            assert(t * p2d <= p5 < (t + 1) * p2d);
            // c = 2^(q + d - lz + 2048); 2^lz * c = 2^d * 2^(q + 2048)
            lemma_pow2_adds(lz, n);
            lemma_pow2_adds(d, (q + 2048) as nat);
            assert(lz + n == d + q + 2048);
            let wc = wn * c;
            assert(wc == w * p2d * v2) by (nonlinear_arith)
                requires
                    wc == wn * c, wn == w * pow2(lz), c == pow2(n),
                    pow2(lz) * pow2(n) == pow2(lz + n),
                    pow2(d) * pow2((q + 2048) as nat) == pow2(d + (q + 2048) as nat),
                    lz + n == d + (q + 2048) as nat, p2d == pow2(d), v2 == pow2((q + 2048) as nat);
            assert(p * c == w * t * p2d * v2) by (nonlinear_arith)
                requires p == wn * t, wc == wn * c, wc == w * p2d * v2;
            lemma_pow2_pos((q + 2048) as nat);
            lemma_pow2_pos(n);
            assert(p * c <= vs(w, q) < (p + wn) * c) by (nonlinear_arith)
                requires
                    p * c == w * t * p2d * v2, vs(w, q) == w * p5 * v2,
                    t * p2d <= p5, p5 < (t + 1) * p2d, w >= 1, v2 > 0,
                    wc == wn * c, wc == w * p2d * v2;
            assert((p - two64()) * c < p * c) by (nonlinear_arith) requires c > 0, two64() > 0;
            assert((p + wn) * c <= (p + two64()) * c) by (nonlinear_arith) requires c > 0, wn < two64();
        }
    } else {
        let kk = (-q) as nat;
        lemma_fpow(5, kk);
        let p5 = pow(5, kk);
        lemma_pow2_fpow(s as nat);
        let p2s = pow2(s as nat);
        assert(p2s - p5 < t * p5 < p2s + p5);
        assert(pos(q) == 0);
        reveal(pow);
        assert(pow(5, 0) == 1);
        let v2 = pow2(2048);
        assert(vs(w, q) == w * v2);
        let n = (kk + k + 2048) as nat;
        assert(n == 2048 - s - lz);
        assert(c == p5 * pow2(n));
        let r = (2048 - s) as nat;
        // 2^lz * 2^n == 2^r, 2^s * 2^r == 2^2048
        lemma_pow2_adds(lz, n);
        lemma_pow2_adds(s as nat, r);
        let pr = pow2(r);
        lemma_pow2_pos(r);
        let wc = wn * c;
        assert(wc == w * p5 * pr) by (nonlinear_arith)
            requires wc == wn * c, wn == w * pow2(lz), c == p5 * pow2(n), pow2(lz) * pow2(n) == pow2(lz + n),
                lz + n == r, pr == pow2(r);
        assert(p * c == w * (t * p5) * pr) by (nonlinear_arith)
            requires p == wn * t, wn == w * pow2(lz), c == p5 * pow2(n), pow2(lz) * pow2(n) == pow2(lz + n),
                lz + n == r, pr == pow2(r);
        assert(vs(w, q) == w * p2s * pr) by (nonlinear_arith)
            requires vs(w, q) == w * v2, v2 == pow2(2048), p2s * pr == pow2(s as nat + r), s as nat + r == 2048,
                p2s == pow2(s as nat), pr == pow2(r);
        assert((p - wn) * c < vs(w, q) < (p + wn) * c) by (nonlinear_arith)
            requires
                p * c == w * (t * p5) * pr, vs(w, q) == w * p2s * pr, wc == wn * c, wc == w * p5 * pr,
                p2s - p5 < t * p5, t * p5 < p2s + p5, w >= 1, pr > 0;
        lemma_pow_positive(5, kk);
        lemma_pow2_pos(n);
        assert(c > 0) by (nonlinear_arith) requires c == p5 * pow2(n), p5 > 0, pow2(n) > 0;
        assert((p - two64()) * c <= (p - wn) * c) by (nonlinear_arith) requires c > 0, wn < two64();
        assert((p + wn) * c <= (p + two64()) * c) by (nonlinear_arith) requires c > 0, wn < two64();
    }
}


// ---------------------------------------------------------------------------
// Rounding
// ---------------------------------------------------------------------------

/// The significand the code picks, `mt`, from the bits `m` kept above the
/// cut and the rest `r`: `m`'s last bit is the rounding bit. Inexact
/// products round half up (the rest is never zero there); exact ones
/// round half to even.
pub open spec fn pick(m: int, r: int, exact: bool) -> int {
    if m % 2 == 1 && (!exact || r != 0 || (m / 2) % 2 == 1) { m / 2 + 1 } else { m / 2 }
}

/// In units `u` of the step below the kept bits (`u = g * c`, where `g`
/// is 2^cut and `c` the scale of one unit of the product `p`): the value
/// `v` lies within half a step of `pick(...)` steps, on the boundary only
/// when the pick is even, and at or above `m` half-steps.
#[verifier::spinoff_prover]
pub proof fn lemma_round(v: int, c: int, g: int, u: int, p: int, m: int, r: int, exact: bool)
    requires
        c > 0,
        g > 0,
        !exact ==> g >= 2 * two64(),
        u == g * c,
        p == m * g + r,
        0 <= r < g,
        m >= 0,
        (p - two64()) * c < v < (p + two64()) * c,
        exact ==> v == p * c,
        !exact ==> two64() <= r <= g - two64(),
    ensures
        ({
            let mt = pick(m, r, exact);
            &&& (2 * mt - 1) * u < v || ((2 * mt - 1) * u == v && mt % 2 == 0)
            &&& v < (2 * mt + 1) * u || (v == (2 * mt + 1) * u && mt % 2 == 0)
            &&& m * u <= v
            &&& v < (m + 1) * u
        }),
{
    let mt = pick(m, r, exact);
    // v - m * u, in units of c, lies in (r - 2^64, r + 2^64).
    assert(p * c == m * u + r * c) by (nonlinear_arith) requires p == m * g + r, u == g * c;
    assert((p - two64()) * c == m * u + (r - two64()) * c) by (nonlinear_arith) requires p == m * g + r, u == g * c;
    assert((p + two64()) * c == m * u + (r + two64()) * c) by (nonlinear_arith) requires p == m * g + r, u == g * c;
    if exact {
        assert(0 <= r * c < u) by (nonlinear_arith) requires 0 <= r < g, c > 0, u == g * c;
        if m % 2 == 0 {
            assert(2 * mt == m);
            assert(r * c < u);
        } else {
            assert(2 * (m / 2) + 1 == m);
            if r == 0 {
                assert(v == m * u);
            } else {
                assert(r * c > 0) by (nonlinear_arith) requires r > 0, c > 0;
            }
        }
        assert((2 * mt - 1) * u == 2 * mt * u - u && (2 * mt + 1) * u == 2 * mt * u + u) by (nonlinear_arith);
        assert((m + 1) * u == m * u + u) by (nonlinear_arith);
        assert(2 * (m / 2) * u == m * u || 2 * (m / 2) * u == m * u - u) by (nonlinear_arith)
            requires 2 * (m / 2) == m || 2 * (m / 2) == m - 1;
        assert(2 * (m / 2 + 1) * u == 2 * (m / 2) * u + 2 * u) by (nonlinear_arith);
    } else {
        // m * u < v < (m + 1) * u.
        assert((r - two64()) * c >= 0) by (nonlinear_arith) requires r >= two64(), c > 0;
        assert((r + two64()) * c <= u) by (nonlinear_arith) requires r + two64() <= g, c > 0, u == g * c;
        assert((2 * mt - 1) * u == 2 * mt * u - u && (2 * mt + 1) * u == 2 * mt * u + u) by (nonlinear_arith);
        assert((m + 1) * u == m * u + u) by (nonlinear_arith);
        assert(2 * (m / 2) * u == m * u || 2 * (m / 2) * u == m * u - u) by (nonlinear_arith)
            requires 2 * (m / 2) == m || 2 * (m / 2) == m - 1;
        assert(2 * (m / 2 + 1) * u == 2 * (m / 2) * u + 2 * u) by (nonlinear_arith);
        assert(u > 0) by (nonlinear_arith) requires g > 0, c > 0, u == g * c;
    }
}


// ---------------------------------------------------------------------------
// Assembling the bit pattern
// ---------------------------------------------------------------------------

#[verifier::spinoff_prover]
proof fn lemma_split52(b: int, e: int, x: int)
    requires
        b == e * 0x10_0000_0000_0000 + x,
        0 <= x < 0x10_0000_0000_0000,
        e >= 0,
    ensures
        b / 0x10_0000_0000_0000 == e,
        b % 0x10_0000_0000_0000 == x,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(b, 0x10_0000_0000_0000, e, x);
}

/// A rounded significand `mt` and half-step exponent `f` (the value is
/// within half a step of `mt * 2^(f + 1)`), assembled into `b`.
#[verifier::spinoff_prover]
pub proof fn lemma_finish(w: int, q: int, e2: int, mt: int, m: int, f: int, u: int, b: u64)
    requires
        u == cz(q, f),
        pos(-q) + f + 2048 >= 1,
        (2 * mt - 1) * u < vs(w, q) || ((2 * mt - 1) * u == vs(w, q) && mt % 2 == 0),
        vs(w, q) < (2 * mt + 1) * u || (vs(w, q) == (2 * mt + 1) * u && mt % 2 == 0),
        m * u <= vs(w, q),
        e2 >= 1 ==> e2 <= 2046 && f == e2 - 1076 && m >= 0x20_0000_0000_0000
            && 0x10_0000_0000_0000 <= mt <= 0x20_0000_0000_0000,
        e2 <= 0 ==> f == -1075 && 0 <= mt <= 0x10_0000_0000_0000,
        b as int == (if e2 >= 1 { e2 - 1 } else { 0 }) * 0x10_0000_0000_0000 + mt,
        b < INF,
    ensures
        is_round(w, q, b),
{
    let v = vs(w, q);
    let h = 0x10_0000_0000_0000int;
    let e = if e2 >= 1 { e2 - 1 } else { 0 };
    lemma_cz_shift(q, f - 1, 1);
    lemma_cz_shift(q, f, 1);
    lemma_pow2_unfold(1);
    reveal(pow);
    assert(pow2(1) == 2) by { lemma2_to64(); }
    let u0 = cz(q, f - 1);
    let u2 = cz(q, f + 1);
    assert(u == u0 * 2 && u2 == u * 2);
    if mt < h {
        assert(e2 <= 0);
        lemma_split52(b as int, 0, mt);
        assert(sig(b) == mt && ex(b) == -1074 && frac(b) == mt && bexp(b) == 0);
    } else if mt < 2 * h {
        lemma_split52(b as int, e + 1, mt - h);
        assert(sig(b) == mt);
        if e2 >= 1 {
            assert(ex(b) == f + 1);
            if frac(b) == 0 && bexp(b) > 1 {
                // The bottom of a binade: the midpoint below is a quarter step down.
                assert(mt == h);
                assert(m * u >= 2 * h * u) by (nonlinear_arith) requires m >= 2 * h, u > 0;
                assert((4 * mt - 1) * u0 < 2 * h * u) by (nonlinear_arith)
                    requires mt == h, u == u0 * 2, u0 > 0;
            }
        } else {
            assert(mt == h && bexp(b) == 1 && ex(b) == -1074);
        }
    } else {
        // Rounded up into the next binade.
        assert(mt == 2 * h && e2 >= 1);
        lemma_split52(b as int, e + 2, 0);
        assert(bexp(b) == e2 + 1 && frac(b) == 0 && sig(b) == h && ex(b) == f + 2);
        assert((4 * h - 1) * u == (2 * mt - 1) * u);
        assert((2 * h + 1) * u2 == (2 * mt + 2) * u) by (nonlinear_arith) requires u2 == u * 2, mt == 2 * h;
        assert((2 * mt + 1) * u < (2 * mt + 2) * u) by (nonlinear_arith) requires u > 0;
        assert(cz(q, ex(b) - 2) == u);
        assert(cz(q, ex(b) - 1) == u2);
    }
}

/// Values at or above `2^53` steps of `2^(f + 1)`, `f >= 970`, round to
/// infinity; so do values at the midpoint above the largest double.
#[verifier::spinoff_prover]
pub proof fn lemma_finish_inf(w: int, q: int, f: int, z: int, u: int)
    requires
        u == cz(q, f),
        f >= 970,
        pos(-q) + 970 + 2048 >= 0,
        z >= 0x3F_FFFF_FFFF_FFFF,
        z * u <= vs(w, q),
    ensures
        is_round(w, q, INF),
{
    lemma_cz_shift(q, 970, (f - 970) as nat);
    lemma_pow2_pos((f - 970) as nat);
    let u9 = cz(q, 970);
    assert(u >= u9) by (nonlinear_arith) requires u == u9 * pow2((f - 970) as nat), pow2((f - 970) as nat) >= 1, u9 > 0;
    assert(0x3F_FFFF_FFFF_FFFF * u9 <= z * u) by (nonlinear_arith)
        requires z >= 0x3F_FFFF_FFFF_FFFF, u >= u9, u9 > 0;
}

/// Values below half the smallest subnormal round to zero.
#[verifier::spinoff_prover]
pub proof fn lemma_finish_zero(w: int, q: int)
    requires
        pos(-q) - 1075 + 2048 >= 0,
        0 <= vs(w, q) <= cz(q, -1075),
    ensures
        is_round(w, q, 0),
{
    lemma_split52(0, 0, 0);
    lemma_cz_shift(q, -1075, 0);
    assert(bexp(0) == 0 && frac(0) == 0 && sig(0) == 0 && ex(0) == -1074);
    assert(!below(w, q, -1, -1075));
    assert(!equal(w, q, -1, -1075));
    assert(below(w, q, 1, -1075) || equal(w, q, 1, -1075));
}


// ---------------------------------------------------------------------------
// Steps of `to_bits`
// ---------------------------------------------------------------------------

/// Below `10^-342`, every `w < 2^64` is less than half the smallest
/// subnormal.
#[verifier::spinoff_prover]
proof fn lemma_q_small(w: int, q: int)
    requires
        1 <= w < two64(),
        q < -342,
    ensures
        is_round(w, q, 0),
{
    let k = (-q) as nat;
    assert(fpow(2, 64 + 2048) <= fpow(5, 343) * fpow(2, 343 + 973)) by (compute_only);
    lemma_pow2_fpow(64 + 2048);
    lemma_pow2_fpow(343 + 973);
    lemma_fpow(5, 343);
    lemma_pow_increases(5, 343, k);
    lemma_pow2_increases(343 + 973, k + 973);
    lemma_pow2_adds(64, 2048);
    lemma_pow2(64);
    assert(pow2(64) == two64()) by { lemma2_to64_rest(); }
    reveal(pow);
    assert(pow(5, 0) == 1);
    assert(vs(w, q) == w * pow2(2048));
    assert(cz(q, -1075) == pow(5, k) * pow2(k + 973));
    lemma_pow2_pos(2048);
    lemma_pow_positive(5, 343);
    assert(w * pow2(2048) <= pow(5, k) * pow2(k + 973)) by (nonlinear_arith)
        requires
            w < pow2(64), pow2(64) * pow2(2048) == pow2(64 + 2048),
            pow2(64 + 2048) <= pow(5, 343) * pow2(343 + 973),
            pow(5, 343) <= pow(5, k), pow2(343 + 973) <= pow2(k + 973), pow2(2048) > 0,
            pow(5, 343) >= 0;
    lemma_finish_zero(w, q);
}

#[verifier::spinoff_prover]
proof fn lemma_double(m: int, u: int, x: int, v: int)
    requires
        u == x * 2,
        m * u <= v,
    ensures
        2 * m * x <= v,
{
    assert(m * u == 2 * m * x) by (nonlinear_arith) requires u == x * 2;
}

#[verifier::spinoff_prover]
proof fn lemma_pow2_increases(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow2(a) <= pow2(b),
{
    if a < b {
        lemma_pow2_strictly_increases(a, b);
    }
}

/// Above `10^308`, every `w >= 1` rounds to infinity.
#[verifier::spinoff_prover]
proof fn lemma_q_big(w: int, q: int)
    requires
        1 <= w,
        q > 308,
    ensures
        is_round(w, q, INF),
{
    let qn = q as nat;
    assert(0x3F_FFFF_FFFF_FFFF * fpow(2, 970 + 2048) <= fpow(5, 309) * fpow(2, 309 + 2048)) by (compute_only);
    lemma_pow2_fpow(970 + 2048);
    lemma_pow2_fpow(309 + 2048);
    lemma_fpow(5, 309);
    lemma_pow_increases(5, 309, qn);
    lemma_pow2_increases(309 + 2048, qn + 2048);
    reveal(pow);
    assert(pow(5, 0) == 1);
    assert(cz(q, 970) == pow2(970 + 2048));
    assert(vs(w, q) == w * pow(5, qn) * pow2(qn + 2048));
    lemma_pow_positive(5, 309);
    lemma_pow2_pos(309 + 2048);
    assert(pow(5, 309) * pow2(309 + 2048) <= w * pow(5, qn) * pow2(qn + 2048)) by (nonlinear_arith)
        requires
            w >= 1, pow(5, 309) <= pow(5, qn), pow2(309 + 2048) <= pow2(qn + 2048),
            pow(5, 309) > 0, pow2(309 + 2048) > 0;
    lemma_finish_inf(w, q, 970, 0x3F_FFFF_FFFF_FFFF, cz(q, 970));
}

/// The product lies in `[2^190, 2^192 - 2^64]`, so its top limb has one of
/// its top two bits set.
#[verifier::spinoff_prover]
proof fn lemma_p_range(wn: int, q: int, p2: int, p1: int, p0: int, p: int)
    requires
        0x8000_0000_0000_0000 <= wn < two64(),
        -342 <= q <= 308,
        p == wn * tab(q),
        p == p2 * two64() * two64() + p1 * two64() + p0,
        0 <= p1 < two64(),
        0 <= p0 < two64(),
    ensures
        p2 >= 0x4000_0000_0000_0000,
        p + two64() <= two64() * two64() * two64(),
{
    lemma_tab(q);
    assert(fpow(2, 127) == 0x8000_0000_0000_0000_0000_0000_0000_0000int) by (compute_only);
    assert(fpow(2, 128) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000int) by (compute_only);
    let t = two64();
    let tb = tab(q);
    assert(p >= 0x8000_0000_0000_0000 * 0x8000_0000_0000_0000_0000_0000_0000_0000int) by (nonlinear_arith)
        requires p == wn * tb, wn >= 0x8000_0000_0000_0000, tb >= 0x8000_0000_0000_0000_0000_0000_0000_0000int;
    assert(p <= (t - 1) * (t * t - 1)) by (nonlinear_arith)
        requires p == wn * tb, 0 <= wn <= t - 1, 0 <= tb <= t * t - 1, t == two64();
    assert(p1 * t + p0 < t * t) by (nonlinear_arith) requires 0 <= p1 < t, 0 <= p0 < t, t == two64();
    assert(p2 >= 0x4000_0000_0000_0000) by (nonlinear_arith)
        requires
            p == p2 * t * t + p1 * t + p0, p1 * t + p0 < t * t, p0 >= 0, p1 >= 0,
            p >= 0x8000_0000_0000_0000 * 0x8000_0000_0000_0000_0000_0000_0000_0000int, t == two64();
    assert((t - 1) * (t * t - 1) + t <= t * t * t) by (nonlinear_arith) requires t == two64();
}

#[verifier::bit_vector]
proof fn bv_upper(p2: u64)
    ensures
        p2 >> 63u32 <= 1,
        (p2 >> 63u32 == 0) == (p2 < 0x8000_0000_0000_0000),
{
}

#[verifier::spinoff_prover]
proof fn lemma_flog(q: int, fl: int)
    requires
        -342 <= q <= 308,
        fl == (q * 217706 + 65536 * 2000) / 65536 - 2000,
    ensures
        fl == flog10(q),
        -1137 <= fl <= 1023,
{
    let x = q * 217706;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, 65536);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x + 65536 * 2000, 65536, x / 65536 + 2000, x % 65536);
}

/// The bits kept above a cut of `sh` bits in the top limb, a mask of the
/// bits below it, and those bits.
#[inline(always)]
#[verifier::spinoff_prover]
fn cut(p2: u64, sh: u64) -> (r: (u64, u64, u64))
    requires
        sh < 64,
    ensures
        r.0 as int == p2 as int / pow2(sh as nat) as int,
        r.1 as int == pow2(sh as nat) - 1,
        r.2 as int == p2 as int % pow2(sh as nat) as int,
        r.0 == p2 >> sh,
        r.1 == sub(1u64 << sh, 1),
        r.2 == p2 & r.1,
{
    proof {
        assert((1u64 << sh) >= 1) by (bit_vector)
            requires sh < 64;
        vstd::bits::lemma_u64_pow2_no_overflow(sh as nat);
        vstd::bits::lemma_u64_shr_is_div(p2, sh);
        lemma_pow2_pos(sh as nat);
        vstd::bits::lemma_u64_shl_is_mul(1, sh);
        vstd::bits::lemma_u64_low_bits_mask_is_mod(p2, sh as nat);
    }
    let ones = (1u64 << sh) - 1;
    (p2 >> sh, ones, p2 & ones)
}

#[verifier::spinoff_prover]
proof fn lemma_cut(p2: int, p1: int, p0: int, sh: nat, m: int, hb: int, p: int, r: int, g: int)
    requires
        sh < 64,
        0 <= p1 < two64(),
        0 <= p0 < two64(),
        p2 >= 0,
        m == p2 / pow2(sh) as int,
        hb == p2 % pow2(sh) as int,
        p == p2 * two64() * two64() + p1 * two64() + p0,
        r == hb * two64() * two64() + p1 * two64() + p0,
        g == pow2(128 + sh) as int,
    ensures
        p == m * g + r,
        0 <= r < g,
        g >= 2 * two64(),
        g == two64() * two64() * pow2(sh),
{
    let t = two64();
    let d = pow2(sh) as int;
    lemma_pow2_pos(sh);
    lemma_pow2_adds(128, sh);
    assert(pow2(128) == t * t) by {
        lemma_pow2_adds(64, 64);
        lemma2_to64_rest();
    }
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p2, d);
    assert(0 <= hb < d);
    assert(p2 == d * m + hb);
    assert(p == m * g + r) by (nonlinear_arith)
        requires p == p2 * t * t + p1 * t + p0, r == hb * t * t + p1 * t + p0, p2 == d * m + hb, g == t * t * d;
    assert(p1 * t + p0 < t * t) by (nonlinear_arith) requires 0 <= p1 < t, 0 <= p0 < t, t == two64();
    assert(r < g) by (nonlinear_arith)
        requires r == hb * t * t + p1 * t + p0, p1 * t + p0 < t * t, hb + 1 <= d, g == t * t * d;
    assert(r >= 0) by (nonlinear_arith) requires r == hb * t * t + p1 * t + p0, hb >= 0, p1 >= 0, p0 >= 0, t > 0;
    assert(g >= 2 * t) by (nonlinear_arith) requires g == t * t * d, d >= 1, t == two64();
}

/// The check that the product is not within `2^64` of a cut boundary.
#[verifier::spinoff_prover]
proof fn lemma_near(hb: int, ones: int, p1: int, p0: int, r: int, g: int, sh: nat)
    requires
        0 <= hb <= ones,
        ones == pow2(sh) - 1,
        0 <= p1 < two64(),
        0 <= p0 < two64(),
        r == hb * two64() * two64() + p1 * two64() + p0,
        g == two64() * two64() * pow2(sh),
    ensures
        !(hb == 0 && p1 == 0) ==> two64() <= r,
        !(hb == ones && p1 == two64() - 1) ==> r <= g - two64(),
{
    let t = two64();
    if !(hb == 0 && p1 == 0) {
        assert(two64() <= r) by (nonlinear_arith)
            requires r == hb * t * t + p1 * t + p0, hb >= 0, p1 >= 0, p0 >= 0, hb > 0 || p1 > 0, t == two64();
    }
    if !(hb == ones && p1 == t - 1) {
        assert(r <= g - two64()) by (nonlinear_arith)
            requires
                r == hb * t * t + p1 * t + p0, g == t * t * (ones + 1), hb <= ones, p1 <= t - 1, p0 <= t - 1,
                hb < ones || p1 < t - 1, t == two64();
    }
}

/// Without a subnormal shift, the kept bits are a 54-bit number with its
/// top bit set.
#[verifier::bit_vector]
proof fn bv_normal(p2: u64, sh: u64, upper: u64)
    requires
        p2 >= 0x4000_0000_0000_0000,
        upper == p2 >> 63u64,
        sh == 9 + upper,
    ensures
        0x20_0000_0000_0000 <= (p2 >> sh) < 0x40_0000_0000_0000,
{
}

/// With a subnormal shift of one or more, fewer than 53 bits are kept.
#[verifier::bit_vector]
proof fn bv_sub(p2: u64, sh: u64, upper: u64)
    requires
        upper == p2 >> 63u64,
        10 + upper <= sh < 64,
    ensures
        (p2 >> sh) < 0x20_0000_0000_0000,
{
}

/// The 64 bits below a cut of 9 or 10 bits are all zeros (all ones) when
/// the cut-off bits of `p2` and all of `p1` are.
#[verifier::bit_vector]
proof fn bv_edge(p2: u64, p1: u64, sh: u64, ones: u64, hb: u64, y: u64)
    requires
        9 <= sh <= 10,
        ones == sub(1u64 << sh, 1),
        hb == p2 & ones,
        y == (p2 << sub(64u64, sh)) | (p1 >> sh),
    ensures
        (hb == 0 && p1 == 0) ==> y == 0,
        (hb == ones && p1 == 0xFFFF_FFFF_FFFF_FFFFu64) ==> y == 0xFFFF_FFFF_FFFF_FFFFu64,
{
}

#[verifier::bit_vector]
proof fn bv_pick(m: u64)
    ensures
        m >> 1u64 == m / 2,
        (m & 1 == 1) == (m % 2 == 1),
        ((m >> 1u64) & 1 == 1) == ((m / 2) % 2 == 1),
{
}

/// Rounding up without a branch: `s` is 1 when the discarded bits below the
/// half are not all zero.
#[verifier::bit_vector]
proof fn bv_round_up(m: u64, s: u64)
    requires
        s <= 1,
    ensures
        (m & (s | (m >> 1u64)) & 1) == (if (m & 1 == 1) && (s == 1 || (m >> 1u64) & 1 == 1) { 1u64 } else { 0u64 }),
{
}

#[verifier::bit_vector]
proof fn bv_or3(a: u64, b: u64, c: u64)
    ensures
        ((a | b | c) == 0) == (a == 0 && b == 0 && c == 0),
{
}

#[verifier::bit_vector]
proof fn bv_shl52(e: u64)
    requires
        e <= 2045,
    ensures
        e << 52u64 == e * 0x10_0000_0000_0000,
{
}

/// Far below the subnormals (a cut of 64 bits or more), the value is less
/// than half the smallest subnormal.
#[verifier::spinoff_prover]
proof fn lemma_far(w: int, q: int, k: int, p: int, e2: int, upper: int)
    requires
        k == e2 - upper - 1213,
        0 <= upper <= 1,
        9 + upper + 1 - e2 >= 64,
        p + two64() <= two64() * two64() * two64(),
        vs(w, q) < (p + two64()) * cz(q, k),
        pos(-q) + k + 2048 >= 0,
        cz(q, k) > 0,
        w >= 0,
    ensures
        is_round(w, q, 0),
{
    let c = cz(q, k);
    lemma_cz_shift(q, k, 192);
    lemma_cz_shift(q, k + 192, (-1075 - (k + 192)) as nat);
    lemma_pow2_pos((-1075 - (k + 192)) as nat);
    assert(pow2(192) == two64() * two64() * two64()) by {
        lemma_pow2_adds(64, 128);
        lemma_pow2_adds(64, 64);
        lemma2_to64_rest();
    }
    assert((p + two64()) * c <= cz(q, k + 192)) by (nonlinear_arith)
        requires p + two64() <= pow2(192), cz(q, k + 192) == c * pow2(192), c > 0;
    assert(cz(q, k + 192) <= cz(q, -1075)) by (nonlinear_arith)
        requires
            cz(q, -1075) == cz(q, k + 192) * pow2((-1075 - (k + 192)) as nat),
            pow2((-1075 - (k + 192)) as nat) >= 1, cz(q, k + 192) > 0;
    lemma_pow_positive(5, pos(q));
    assert(vs(w, q) >= 0) by (nonlinear_arith)
        requires w >= 0, pow(5, pos(q)) >= 0, pow2(pos(q) + 2048) >= 0;
    lemma_finish_zero(w, q);
}


// ---------------------------------------------------------------------------
// Exact short decimals
// ---------------------------------------------------------------------------

/// 5^k for k = 0..=27, the powers that fit in 64 bits.
pub const P5: [u64; 28] = [1, 5, 25, 125, 625, 3125, 15625, 78125, 390625, 1953125, 9765625, 48828125, 244140625, 1220703125, 6103515625, 30517578125, 152587890625, 762939453125, 3814697265625, 19073486328125, 95367431640625, 476837158203125, 2384185791015625, 11920928955078125, 59604644775390625, 298023223876953125, 1490116119384765625, 7450580596923828125];

pub open spec fn p5_ok(k: int) -> bool {
    P5@[k] as int == fpow(5, k as nat)
}

pub open spec fn p5_ok_below(n: nat) -> bool
    decreases n,
{
    if n == 0 { true } else { p5_ok(n - 1) && p5_ok_below((n - 1) as nat) }
}

#[verifier::spinoff_prover]
proof fn lemma_p5_below(n: nat, k: int)
    requires
        p5_ok_below(n),
        0 <= k < n,
    ensures
        p5_ok(k),
    decreases n,
{
    if k != n - 1 {
        lemma_p5_below((n - 1) as nat, k);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_p5(k: int)
    requires
        0 <= k < 28,
    ensures
        P5@[k] as int == pow(5, k as nat),
{
    assert(p5_ok_below(28)) by (compute_only);
    lemma_p5_below(28, k);
    lemma_fpow(5, k as nat);
}

/// `w2 * 2^-k`, which is `w * 10^-k` when `w = w2 * 5^k`, rounded exactly.
/// With `k = 0` this is any integer.
/// Such values (0.5, 2.25, ...) can lie exactly on a rounding boundary,
/// where the table's product cannot decide.
#[verifier::spinoff_prover]
#[inline(always)]
fn dyadic(#[allow(unused_variables)] w: u64, k: u64, w2: u64) -> (b: u64)
    requires
        k <= 27,
        w2 >= 1,
        w as int == w2 as int * pow(5, k as nat),
    ensures
        is_round(w as int, -(k as int), b),
{
    let (wn, lz) = norm(w2);
    let m = wn >> 10u64;
    let r = wn & 1023;
    proof {
        bv_cut10(wn);
        bv_pick(m);
    }
    // Round up without a branch: rounding is a coin flip on real data.
    let s: u64 = if r != 0 { 1 } else { 0 };
    proof {
        bv_round_up(m, s);
        bv_pick(m);
    }
    let mant = (m >> 1u64) + (m & (s | (m >> 1u64)) & 1);
    // The value is wn * 2^(-k - lz), with wn's top bit at 63.
    let e2 = 1086 - k - lz as u64;
    proof {
        let q = -(k as int);
        let kk = -(k as int) - lz as int;
        let c = cz(q, kk);
        let g = 1024int;
        let u = g * c;
        lemma_cz_shift(q, kk, 10);
        assert(pow2(10) == 1024) by { lemma2_to64(); }
        lemma_dyadic_exact(w as int, w2 as int, k as nat, lz as nat, wn as int);
        assert(wn as int == m as int * g + r as int);
        assert((wn as int - two64()) * c < vs(w as int, q) < (wn as int + two64()) * c) by (nonlinear_arith)
            requires vs(w as int, q) == wn as int * c, c > 0, two64() > 0;
        lemma_round(vs(w as int, q), c, g, u, wn as int, m as int, r as int, true);
        assert(mant as int == pick(m as int, r as int, true));
        bv_shl52((e2 - 1) as u64);
    }
    let b = ((e2 - 1) << 52u64) + mant;
    proof {
        lemma_finish(w as int, -(k as int), e2 as int, mant as int, m as int, -(k as int) - lz as int + 10, 1024 * cz(-(k as int), -(k as int) - lz as int), b);
    }
    b
}

#[verifier::bit_vector]
proof fn bv_cut10(wn: u64)
    requires
        wn >= 0x8000_0000_0000_0000,
    ensures
        wn == (wn >> 10u64) * 1024 + (wn & 1023),
        0x20_0000_0000_0000 <= (wn >> 10u64) < 0x40_0000_0000_0000,
        (wn & 1023) < 1024,
{
}

#[verifier::spinoff_prover]
proof fn lemma_dyadic_exact(w: int, w2: int, k: nat, lz: nat, wn: int)
    requires
        k <= 27,
        lz < 64,
        w == w2 * pow(5, k),
        wn == w2 * pow2(lz),
    ensures
        vs(w, -(k as int)) == wn * cz(-(k as int), -(k as int) - lz),
{
    let q = -(k as int);
    reveal(pow);
    assert(pow(5, 0) == 1);
    assert(pos(q) == 0 && pos(-q) == k);
    assert(vs(w, q) == w * pow2(2048));
    assert(cz(q, q - lz) == pow(5, k) * pow2((2048 - lz) as nat));
    lemma_pow2_adds(lz, (2048 - lz) as nat);
    assert(vs(w, q) == wn * cz(q, q - lz)) by (nonlinear_arith)
        requires
            vs(w, q) == w * pow2(2048), w == w2 * pow(5, k), wn == w2 * pow2(lz),
            cz(q, q - lz) == pow(5, k) * pow2((2048 - lz) as nat),
            pow2(lz) * pow2((2048 - lz) as nat) == pow2(2048);
}

// ---------------------------------------------------------------------------
// Eisel-Lemire
// ---------------------------------------------------------------------------

/// The value `w * 10^q` as vcore's exact rationals `n * 2^q / d`.
pub open spec fn qn(w: int, q: int) -> int {
    if q >= 0 { w * pow(5, q as nat) } else { w }
}

pub open spec fn qd(q: int) -> int {
    if q >= 0 { 1 } else { pow(5, (-q) as nat) }
}

/// `below` and `equal` are vcore's `lt` and `eq` against `z * 2^f`.
#[verifier::spinoff_prover]
proof fn lemma_below_b64(w: int, q: int, z: int, f: int)
    requires
        -2048 <= q <= 900,
        f >= -1100,
    ensures
        below(w, q, z, f) == b64::lt(qn(w, q), qd(q), q, z, 1, f),
        equal(w, q, z, f) == b64::eq(qn(w, q), qd(q), q, z, 1, f),
{
    reveal(pow);
    assert(pow(5, 0) == 1);
    if q >= 0 {
        b64::lemma_at(qn(w, q), 1, q, z, 1, f, -2048);
        assert((q - -2048) as nat == pos(q) + 2048);
        assert((f - -2048) as nat == (pos(-q) + f + 2048) as nat);
        let a = pow(5, q as nat);
        let p = pow2((q + 2048) as nat);
        assert(vs(w, q) == w * a * p);
        assert(w * a * 1 * p == w * a * p) by (nonlinear_arith);
        assert(cz(q, f) == pow2((f + 2048) as nat));
    } else {
        let k = (-q) as nat;
        b64::lemma_at(w, qd(q), q, z, 1, f, q - 2048);
        assert((q - (q - 2048)) as nat == 2048);
        assert((f - (q - 2048)) as nat == (pos(-q) + f + 2048) as nat);
        let a = pow(5, k);
        let p = pow2((pos(-q) + f + 2048) as nat);
        assert(vs(w, q) == w * pow2(2048));
        assert(cz(q, f) == a * p);
        assert(z * (a * p) == z * a * p) by (nonlinear_arith);
    }
}

/// `is_round` is vcore's round-to-nearest-even of `w * 10^q`.
#[verifier::spinoff_prover]
proof fn lemma_round_b64(w: int, q: int, b: u64)
    requires
        -2048 <= q <= 900,
        b <= INF,
    ensures
        is_round(w, q, b) == b64::rne(b, qn(w, q), qd(q), q),
{
    assert(b64::mag(b) == b);
    assert(bexp(b) == b64::bexp(b) && frac(b) == b64::frac(b));
    assert(sig(b) == b64::sig(b) && ex(b) == b64::ex(b));
    let m = sig(b);
    let e = ex(b);
    assert(e >= -1074);
    lemma_below_b64(w, q, 0x3F_FFFF_FFFF_FFFF, 970);
    lemma_below_b64(w, q, 4 * m - 1, e - 2);
    lemma_below_b64(w, q, 2 * m - 1, e - 1);
    lemma_below_b64(w, q, 2 * m + 1, e - 1);
}

/// Clinger's fast path: when `w < 2^53` and `|q| <= 22`, both `w` and
/// `10^|q|` are exact doubles, so one IEEE 754 multiplication or division,
/// which rounds its exact result to the nearest double, ties to even, gives
/// `w * 10^q` correctly rounded.
///
/// Proven against vcore's binary64 model: the only assumptions are the
/// model's statements of what `u64 as f64`, `*` and `/` return.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn clinger(w: u64, q: i64) -> (b: u64)
    requires
        0 < w < 0x20_0000_0000_0000,
        -22 <= q <= 22,
    ensures
        is_round(w as int, q as int, b),
{
    let x = b64::from_u64(w);
    proof {
        b64::lemma_from_u64_exact(w as int, x);
        lemma_pow_positive(5, pos(q as int));
        lemma_pow_positive(5, pos(-q as int));
    }
    let k: usize = if q < 0 { (-q) as usize } else { q as usize };
    proof { b64::lemma_p10(k as int); }
    let p = b64::P10[k];
    let ghost ki = k as int;
    let ghost p5 = pow(5, k as nat);
    let r = if q < 0 {
        let r = b64::div(x, p);
        proof {
            b64::lemma_eq_div(b64::sig(x), 1, b64::ex(x), w as int, 1, 0, b64::sig(p), 1, b64::ex(p), p5, 1, ki);
            assert(b64::sig(x) * 1 == b64::sig(x) && 1 * b64::sig(p) == b64::sig(p));
            assert(w as int * 1 == qn(w as int, q as int) && 1 * p5 == qd(q as int) && 0 - ki == q);
            b64::lemma_rne_eq(b64::mag(r), b64::sig(x), b64::sig(p), b64::ex(x) - b64::ex(p), qn(w as int, q as int), qd(q as int), q as int);
        }
        r
    } else {
        let r = b64::mul(x, p);
        proof {
            b64::lemma_eq_mul(b64::sig(x), 1, b64::ex(x), w as int, 1, 0, b64::sig(p), 1, b64::ex(p), p5, 1, ki);
            assert(w as int * p5 == qn(w as int, q as int) && 1 * 1 == qd(q as int) && 0 + ki == q);
            b64::lemma_rne_eq(b64::mag(r), b64::sig(x) * b64::sig(p), 1, b64::ex(x) + b64::ex(p), qn(w as int, q as int), qd(q as int), q as int);
        }
        r
    };
    proof {
        assert(r == b64::mag(r));
        lemma_round_b64(w as int, q as int, r);
    }
    r
}

/// `w * 10^q` correctly rounded to a double, as a bit pattern, or `None`
/// in the rare cases the 128-bit table cannot decide (the caller then uses
/// a slower exact method).
///
/// The algorithm is Eisel and Lemire's, as in fast_float, with one
/// simplification for the proof: the full 192-bit product is always
/// formed, and when the product is within the table's error of a rounding
/// boundary the function gives up instead of reasoning about which side
/// it is on. Products are exact for `0 <= q <= 55`, where the table holds
/// 5^q exactly, so ties are decided exactly there.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn to_bits(w: u64, q: i64) -> (r: Option<u64>)
    ensures
        r matches Some(b) ==> is_round(w as int, q as int, b),
{
    if w == 0 {
        proof {
            lemma_cz_shift(q as int, -1075, 0);
            assert(vs(0, q as int) == 0) by (nonlinear_arith);
            lemma_finish_zero(w as int, q as int);
        }
        return Some(0);
    }
    if w < 0x20_0000_0000_0000 && -22 <= q && q <= 22 && q != 0 {
        return Some(clinger(w, q));
    }
    if q == 0 {
        proof {
            reveal(pow);
            assert(pow(5, 0) == 1);
            assert(w as int == w as int * pow(5, 0u64 as nat));
        }
        return Some(dyadic(w, 0, w));
    }
    if q < -342 {
        proof { lemma_q_small(w as int, q as int); }
        return Some(0);
    }
    if q > 308 {
        proof { lemma_q_big(w as int, q as int); }
        return Some(INF);
    }
    let (wn, lz) = norm(w);
    let i = (q + 342) as usize;
    let th = POW5_HI[i];
    let tl = POW5_LO[i];
    let (p2, p1, p0) = mul192(wn, th, tl);
    let ghost t = two64();
    let ghost p = p2 as int * t * t + p1 as int * t + p0 as int;
    proof {
        assert(tab(q as int) == th as int * t + tl as int);
        lemma_interval(w as int, q as int, lz as nat, wn as int, p);
        lemma_p_range(wn as int, q as int, p2 as int, p1 as int, p0 as int, p);
    }
    let upper = (p2 >> 63u32) as i64;
    proof { bv_upper(p2); }
    // floor(q * log2(10)), with the numerator made positive.
    let fl = (((q * 217706 + 65536 * 2000) as u64) >> 16u64) as i64 - 2000;
    proof {
        vstd::bits::lemma_u64_shr_is_div((q * 217706 + 65536 * 2000) as u64, 16);
        assert(pow2(16) == 65536) by { lemma2_to64(); }
        lemma_flog(q as int, fl as int);
    }
    let e2 = fl + 63 + upper - lz as i64 + 1023;
    // The usual case first: a normal double, below the largest exponent,
    // with the product clear of a rounding boundary. The cut is then 9 or
    // 10 bits, nothing can overflow, and the general path's subnormal and
    // infinity handling is not needed. Anything else falls through to it.
    if 1 <= e2 && e2 <= 2045 {
        let sh = (9 + upper) as u64;
        let ghost k = q - shift(q as int) - lz;
        let ghost c = cz(q as int, k);
        let (m, ones, hb) = cut(p2, sh);
        let ghost g = pow2((128 + sh) as nat) as int;
        let ghost r = hb as int * t * t + p1 as int * t + p0 as int;
        proof { lemma_cut(p2 as int, p1 as int, p0 as int, sh as nat, m as int, hb as int, p, r, g); }
        let exact = 0 <= q && q <= 55;
        // The 64 bits below the cut: all zeros or all ones whenever the
        // bits below the cut in `p2` and all of `p1` are.
        let y = (p2 << (64 - sh)) | (p1 >> sh);
        if exact || (y != 0 && y != u64::MAX) {
            let ghost u = g * c;
            proof {
                bv_edge(p2, p1, sh, ones, hb, y);
                lemma_near(hb as int, ones as int, p1 as int, p0 as int, r, g, sh as nat);
                lemma_cz_shift(q as int, k, (128 + sh) as nat);
                lemma_round(vs(w as int, q as int), c, g, u, p, m as int, r, exact);
                bv_pick(m);
            }
            let s: u64 = if !exact || (hb | p1 | p0) != 0 { 1 } else { 0 };
            proof {
                bv_or3(hb, p1, p0);
                bv_round_up(m, s);
                bv_pick(m);
            }
            let mant = (m >> 1u64) + (m & (s | (m >> 1u64)) & 1);
            let e = (e2 - 1) as u64;
            proof {
                assert(mant as int == pick(m as int, r, exact));
                bv_normal(p2, sh, upper as u64);
                bv_shl52(e);
            }
            let bits = (e << 52u64) + mant;
            proof {
                lemma_finish(w as int, q as int, e2 as int, mant as int, m as int, k + 128 + sh, u, bits);
            }
            return Some(bits);
        }
    }
    let extra = if e2 <= 0 { 1 - e2 } else { 0 };
    let sh = 9 + upper + extra;
    let ghost k = q - shift(q as int) - lz;
    let ghost c = cz(q as int, k);
    if sh >= 64 {
        proof { lemma_far(w as int, q as int, k, p, e2 as int, upper as int); }
        return Some(0);
    }
    let sh = sh as u64;
    let (m, ones, hb) = cut(p2, sh);
    let ghost g = pow2((128 + sh) as nat) as int;
    let ghost r = hb as int * t * t + p1 as int * t + p0 as int;
    proof { lemma_cut(p2 as int, p1 as int, p0 as int, sh as nat, m as int, hb as int, p, r, g); }
    let exact = 0 <= q && q <= 55;
    if !exact && ((hb == 0 && p1 == 0) || (hb == ones && p1 == u64::MAX)) {
        // Only a value that is exactly a fraction with a power-of-two
        // denominator can lie on a boundary; that needs 5^-q to divide w.
        if -27 <= q && q < 0 {
            let k = (-q) as u64;
            proof { lemma_p5(k as int); }
            let d = P5[k as usize];
            if w % d == 0 {
                proof {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(w as int, d as int);
                    assert(w as int == (w / d) as int * pow(5, k as nat)) by (nonlinear_arith)
                        requires w as int == d as int * (w as int / d as int) + 0, d as int == pow(5, k as nat);
                }
                return Some(dyadic(w, k, w / d));
            }
        }
        return None;
    }
    let ghost u = g * c;
    proof {
        lemma_near(hb as int, ones as int, p1 as int, p0 as int, r, g, sh as nat);
        lemma_cz_shift(q as int, k, (128 + sh) as nat);
        lemma_round(vs(w as int, q as int), c, g, u, p, m as int, r, exact);
    }
    if e2 >= 2047 {
        proof {
            bv_normal(p2, sh, upper as u64);
            lemma_cz_shift(q as int, k + 128 + sh - 1, 1);
            lemma_pow2_unfold(1);
            assert(pow2(1) == 2) by { lemma2_to64(); }
            lemma_double(m as int, u, cz(q as int, k + 128 + sh - 1), vs(w as int, q as int));
            lemma_finish_inf(w as int, q as int, k + 128 + sh - 1, 2 * m as int, cz(q as int, k + 128 + sh - 1));
        }
        return Some(INF);
    }
    proof { bv_pick(m); }
    // Round up without a branch: rounding is a coin flip on real data.
    let s: u64 = if !exact || (hb | p1 | p0) != 0 { 1 } else { 0 };
    proof {
        bv_or3(hb, p1, p0);
        bv_round_up(m, s);
        bv_pick(m);
    }
    let mant = (m >> 1u64) + (m & (s | (m >> 1u64)) & 1);
    proof {
        assert(mant as int == pick(m as int, r, exact));
        if e2 >= 1 {
            bv_normal(p2, sh, upper as u64);
        } else {
            bv_sub(p2, sh, upper as u64);
        }
    }
    let e = if e2 <= 0 { 0 } else { e2 - 1 };
    proof { bv_shl52(e as u64); }
    let bits = ((e as u64) << 52u64) + mant;
    if bits >= INF {
        proof {
            assert(e2 == 2046 && mant == 0x20_0000_0000_0000);
            lemma_finish_inf(w as int, q as int, 970, 0x3F_FFFF_FFFF_FFFF, u);
        }
        return Some(INF);
    }
    proof {
        lemma_finish(w as int, q as int, e2 as int, mant as int, m as int, k + 128 + sh, u, bits);
    }
    Some(bits)
}

} // verus!

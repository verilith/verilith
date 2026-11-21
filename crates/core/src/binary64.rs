//! IEEE 754 binary64 (`f64`), as a model in spec integers, in the style of
//! Flocq: a double is its 64-bit pattern, its value is an exact rational,
//! and an arithmetic operation's result is its exact value rounded to the
//! nearest double, ties to even.
//!
//! Everything here is proven except three one-line wrappers, the trusted
//! base, which state that Rust's `*`, `/` and `u64 as f64` on finite inputs
//! return that rounded result (IEEE 754-2019 §4.3.1, §5.4.1, §5.4.1's
//! `convertFromInt`; the Rust reference says the same of `as`). They hold on
//! every target where Rust's `f64` is IEEE 754 binary64 in its default
//! environment (round to nearest even, subnormals not flushed), which is
//! every target with SSE2 or NEON. Values are bit patterns (`u64`), so no
//! other `f64` operation is assumed; turning a pattern into an `f64` is
//! `f64::from_bits`, the definition of the format.
//!
//! Exact values are rationals `n * 2^e / d` with `d > 0`, written as the
//! three integers `(n, d, e)`.
#[allow(unused_imports)]
use vstd::arithmetic::power::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// The sign bit.
pub const SIGN: u64 = 0x8000_0000_0000_0000;

/// The bit pattern of +infinity, the first one above the finite doubles.
pub const INF: u64 = 0x7FF0_0000_0000_0000;

// ---------------------------------------------------------------------------
// The format
// ---------------------------------------------------------------------------

/// The pattern without its sign bit.
pub open spec fn mag(b: u64) -> u64 {
    (b as int % 0x8000_0000_0000_0000) as u64
}

pub open spec fn neg(b: u64) -> bool {
    b >= SIGN
}

/// Zero, subnormal or normal: not infinite, not NaN.
pub open spec fn finite(b: u64) -> bool {
    mag(b) < INF
}

/// The biased exponent and the fraction field.
pub open spec fn bexp(b: u64) -> int {
    mag(b) as int / 0x10_0000_0000_0000
}

pub open spec fn frac(b: u64) -> int {
    b as int % 0x10_0000_0000_0000
}

/// A finite double `b` is worth `(-1)^neg(b) * sig(b) * 2^ex(b)`.
pub open spec fn sig(b: u64) -> int {
    if bexp(b) == 0 { frac(b) } else { frac(b) + 0x10_0000_0000_0000 }
}

pub open spec fn ex(b: u64) -> int {
    if bexp(b) == 0 { -1074 } else { bexp(b) - 1075 }
}

// ---------------------------------------------------------------------------
// Exact values
// ---------------------------------------------------------------------------

pub open spec fn min(a: int, b: int) -> int {
    if a < b { a } else { b }
}

/// `n1 * 2^e1 / d1 < n2 * 2^e2 / d2`, for positive `d1`, `d2`.
pub open spec fn lt(n1: int, d1: int, e1: int, n2: int, d2: int, e2: int) -> bool {
    let g = min(e1, e2);
    n1 * d2 * pow2((e1 - g) as nat) < n2 * d1 * pow2((e2 - g) as nat)
}

/// `n1 * 2^e1 / d1 == n2 * 2^e2 / d2`, for positive `d1`, `d2`.
pub open spec fn eq(n1: int, d1: int, e1: int, n2: int, d2: int, e2: int) -> bool {
    let g = min(e1, e2);
    n1 * d2 * pow2((e1 - g) as nat) == n2 * d1 * pow2((e2 - g) as nat)
}

// ---------------------------------------------------------------------------
// Rounding
// ---------------------------------------------------------------------------

/// `b`, a pattern with the sign bit clear, is `x = n * 2^e / d >= 0`
/// rounded to the nearest double, ties to even (IEEE 754 §4.3.1
/// roundTiesToEven): `x` lies between the midpoints to the neighbouring
/// doubles, and on a midpoint only if `b`'s significand is even. The
/// midpoint below is a quarter step down at the bottom of a binade, where
/// the double below is half a step away. Values from the midpoint above the
/// largest double, `(2^54 - 1) * 2^970`, round to infinity (§7.4).
pub open spec fn rne(b: u64, n: int, d: int, e: int) -> bool {
    if b == INF {
        !lt(n, d, e, 0x3F_FFFF_FFFF_FFFF, 1, 970)
    } else if b < INF {
        let m = sig(b);
        let f = ex(b);
        let even = m % 2 == 0;
        let (zl, fl) = if frac(b) == 0 && bexp(b) > 1 { (4 * m - 1, f - 2) } else { (2 * m - 1, f - 1) };
        (!lt(n, d, e, zl, 1, fl) && (even || !eq(n, d, e, zl, 1, fl)))
            && (lt(n, d, e, 2 * m + 1, 1, f - 1) || (even && eq(n, d, e, 2 * m + 1, 1, f - 1)))
    } else {
        false
    }
}

/// `r` is the IEEE 754 result of an operation whose exact result is
/// `(-1)^s * n * 2^e / d`: the sign is `s` (also when the result is zero),
/// and the magnitude is rounded to nearest, ties to even.
pub open spec fn rounds(r: u64, s: bool, n: int, d: int, e: int) -> bool {
    neg(r) == s && rne(mag(r), n, d, e)
}

// ---------------------------------------------------------------------------
// Trusted base: the hardware operations
// ---------------------------------------------------------------------------

/// `a * b` (IEEE 754 multiplication), on finite doubles. The exact product
/// is `sig(a) * sig(b) * 2^(ex(a) + ex(b))` with the sign the exclusive or
/// of theirs.
///
/// Trusted: the `ensures` restates IEEE 754's definition of
/// multiplication in round-to-nearest-even mode.
#[verifier::external_body]
#[inline(always)]
pub fn mul(a: u64, b: u64) -> (r: u64)
    requires
        finite(a),
        finite(b),
    ensures
        rounds(r, neg(a) != neg(b), sig(a) * sig(b), 1, ex(a) + ex(b)),
{
    (f64::from_bits(a) * f64::from_bits(b)).to_bits()
}

/// `a / b` (IEEE 754 division), on finite doubles with `b` not zero. The
/// exact quotient is `sig(a) * 2^(ex(a) - ex(b)) / sig(b)`.
///
/// Trusted: the `ensures` restates IEEE 754's definition of division in
/// round-to-nearest-even mode.
#[verifier::external_body]
#[inline(always)]
pub fn div(a: u64, b: u64) -> (r: u64)
    requires
        finite(a),
        finite(b),
        sig(b) != 0,
    ensures
        rounds(r, neg(a) != neg(b), sig(a), sig(b), ex(a) - ex(b)),
{
    (f64::from_bits(a) / f64::from_bits(b)).to_bits()
}

/// `w as f64`, as a bit pattern: the nearest double, ties to even.
///
/// Trusted: the `ensures` restates IEEE 754's `convertFromInt` and the
/// Rust reference's definition of integer-to-float `as` casts.
#[verifier::external_body]
#[inline(always)]
pub fn from_u64(w: u64) -> (r: u64)
    ensures
        rounds(r, false, w as int, 1, 0),
{
    (w as f64).to_bits()
}

// ---------------------------------------------------------------------------
// Exact values: proofs
// ---------------------------------------------------------------------------

/// `lt` and `eq` at any common exponent `G` at or below both exponents.
pub proof fn lemma_at(n1: int, d1: int, e1: int, n2: int, d2: int, e2: int, g0: int)
    requires
        g0 <= e1,
        g0 <= e2,
    ensures
        lt(n1, d1, e1, n2, d2, e2) == (n1 * d2 * pow2((e1 - g0) as nat) < n2 * d1 * pow2((e2 - g0) as nat)),
        eq(n1, d1, e1, n2, d2, e2) == (n1 * d2 * pow2((e1 - g0) as nat) == n2 * d1 * pow2((e2 - g0) as nat)),
{
    let g = min(e1, e2);
    let h = (g - g0) as nat;
    let p1 = pow2((e1 - g) as nat);
    let p2 = pow2((e2 - g) as nat);
    let ph = pow2(h);
    lemma_pow2_adds((e1 - g) as nat, h);
    lemma_pow2_adds((e2 - g) as nat, h);
    assert(((e1 - g) as nat + h) as nat == (e1 - g0) as nat);
    assert(((e2 - g) as nat + h) as nat == (e2 - g0) as nat);
    lemma_pow2_pos(h);
    let a = n1 * d2 * p1;
    let b = n2 * d1 * p2;
    assert(n1 * d2 * (p1 * ph) == a * ph) by (nonlinear_arith) requires a == n1 * d2 * p1;
    assert(n2 * d1 * (p2 * ph) == b * ph) by (nonlinear_arith) requires b == n2 * d1 * p2;
    assert((a < b) == (a * ph < b * ph)) by (nonlinear_arith)
        requires ph > 0;
    assert((a == b) == (a * ph == b * ph)) by (nonlinear_arith)
        requires ph > 0;
}

/// Equal values compare the same way with anything.
pub proof fn lemma_eq_transfer(
    n1: int, d1: int, e1: int,
    n2: int, d2: int, e2: int,
    n3: int, d3: int, e3: int,
)
    requires
        d1 > 0,
        d2 > 0,
        d3 > 0,
        eq(n1, d1, e1, n2, d2, e2),
    ensures
        lt(n1, d1, e1, n3, d3, e3) == lt(n2, d2, e2, n3, d3, e3),
        eq(n1, d1, e1, n3, d3, e3) == eq(n2, d2, e2, n3, d3, e3),
{
    let g = min(min(e1, e2), e3);
    lemma_at(n1, d1, e1, n2, d2, e2, g);
    lemma_at(n1, d1, e1, n3, d3, e3, g);
    lemma_at(n2, d2, e2, n3, d3, e3, g);
    let a = n1 * pow2((e1 - g) as nat);
    let b = n2 * pow2((e2 - g) as nat);
    let c = n3 * pow2((e3 - g) as nat);
    assert(n1 * d2 * pow2((e1 - g) as nat) == a * d2) by (nonlinear_arith) requires a == n1 * pow2((e1 - g) as nat);
    assert(n2 * d1 * pow2((e2 - g) as nat) == b * d1) by (nonlinear_arith) requires b == n2 * pow2((e2 - g) as nat);
    assert(n1 * d3 * pow2((e1 - g) as nat) == a * d3) by (nonlinear_arith) requires a == n1 * pow2((e1 - g) as nat);
    assert(n3 * d1 * pow2((e3 - g) as nat) == c * d1) by (nonlinear_arith) requires c == n3 * pow2((e3 - g) as nat);
    assert(n2 * d3 * pow2((e2 - g) as nat) == b * d3) by (nonlinear_arith) requires b == n2 * pow2((e2 - g) as nat);
    assert(n3 * d2 * pow2((e3 - g) as nat) == c * d2) by (nonlinear_arith) requires c == n3 * pow2((e3 - g) as nat);
    // a / d1 == b / d2; compare both with c / d3.
    assert((a * d3 < c * d1) == (b * d3 < c * d2)) by (nonlinear_arith)
        requires a * d2 == b * d1, d1 > 0, d2 > 0, d3 > 0;
    assert((a * d3 == c * d1) == (b * d3 == c * d2)) by (nonlinear_arith)
        requires a * d2 == b * d1, d1 > 0, d2 > 0, d3 > 0;
}

/// Rounding depends only on the value.
pub proof fn lemma_rne_eq(b: u64, n1: int, d1: int, e1: int, n2: int, d2: int, e2: int)
    requires
        d1 > 0,
        d2 > 0,
        eq(n1, d1, e1, n2, d2, e2),
    ensures
        rne(b, n1, d1, e1) == rne(b, n2, d2, e2),
{
    lemma_eq_transfer(n1, d1, e1, n2, d2, e2, 0x3F_FFFF_FFFF_FFFF, 1, 970);
    let m = sig(b);
    let f = ex(b);
    lemma_eq_transfer(n1, d1, e1, n2, d2, e2, 4 * m - 1, 1, f - 2);
    lemma_eq_transfer(n1, d1, e1, n2, d2, e2, 2 * m - 1, 1, f - 1);
    lemma_eq_transfer(n1, d1, e1, n2, d2, e2, 2 * m + 1, 1, f - 1);
}

/// `eq` is symmetric.
pub proof fn lemma_eq_sym(n1: int, d1: int, e1: int, n2: int, d2: int, e2: int)
    requires
        eq(n1, d1, e1, n2, d2, e2),
    ensures
        eq(n2, d2, e2, n1, d1, e1),
{
}

/// The product of equal values is equal: `x1 * y1 == x2 * y2`.
pub proof fn lemma_eq_mul(
    n1: int, d1: int, e1: int, n2: int, d2: int, e2: int,
    m1: int, c1: int, f1: int, m2: int, c2: int, f2: int,
)
    requires
        eq(n1, d1, e1, n2, d2, e2),
        eq(m1, c1, f1, m2, c2, f2),
    ensures
        eq(n1 * m1, d1 * c1, e1 + f1, n2 * m2, d2 * c2, e2 + f2),
{
    let g = min(e1, e2);
    let h = min(f1, f2);
    let pa = pow2((e1 - g) as nat);
    let pb = pow2((e2 - g) as nat);
    let qa = pow2((f1 - h) as nat);
    let qb = pow2((f2 - h) as nat);
    lemma_at(n1 * m1, d1 * c1, e1 + f1, n2 * m2, d2 * c2, e2 + f2, g + h);
    lemma_pow2_adds((e1 - g) as nat, (f1 - h) as nat);
    lemma_pow2_adds((e2 - g) as nat, (f2 - h) as nat);
    assert(((e1 - g) as nat + (f1 - h) as nat) as nat == (e1 + f1 - (g + h)) as nat);
    assert(((e2 - g) as nat + (f2 - h) as nat) as nat == (e2 + f2 - (g + h)) as nat);
    assert(n1 * m1 * (d2 * c2) * (pa * qa) == (n1 * d2 * pa) * (m1 * c2 * qa)) by (nonlinear_arith);
    assert(n2 * m2 * (d1 * c1) * (pb * qb) == (n2 * d1 * pb) * (m2 * c1 * qb)) by (nonlinear_arith);
}

/// The reciprocal of equal positive values is equal: `d / n * 2^-e`.
pub proof fn lemma_eq_inv(n1: int, d1: int, e1: int, n2: int, d2: int, e2: int)
    requires
        eq(n1, d1, e1, n2, d2, e2),
    ensures
        eq(d1, n1, -e1, d2, n2, -e2),
{
    let g = min(e1, e2);
    let h = min(-e1, -e2);
    assert((-e1 - h) as nat == (e2 - g) as nat);
    assert((-e2 - h) as nat == (e1 - g) as nat);
    let p1 = pow2((e1 - g) as nat);
    let p2 = pow2((e2 - g) as nat);
    assert(d1 * n2 * p2 == n2 * d1 * p2) by (nonlinear_arith);
    assert(d2 * n1 * p1 == n1 * d2 * p1) by (nonlinear_arith);
}

/// The quotient of equal values is equal: `x1 / y1 == x2 / y2`, in the
/// form `div` gives it.
pub proof fn lemma_eq_div(
    n1: int, d1: int, e1: int, n2: int, d2: int, e2: int,
    m1: int, c1: int, f1: int, m2: int, c2: int, f2: int,
)
    requires
        eq(n1, d1, e1, n2, d2, e2),
        eq(m1, c1, f1, m2, c2, f2),
    ensures
        eq(n1 * c1, d1 * m1, e1 - f1, n2 * c2, d2 * m2, e2 - f2),
{
    lemma_eq_inv(m1, c1, f1, m2, c2, f2);
    lemma_eq_mul(n1, d1, e1, n2, d2, e2, c1, m1, -f1, c2, m2, -f2);
    assert(e1 + -f1 == e1 - f1);
    assert(e2 + -f2 == e2 - f2);
}

/// A finite double's value as `(sig, 1, ex)` against a scaled integer:
/// `m * 2^-k == v` when `m == v * 2^k`.
pub proof fn lemma_eq_scaled(m: int, v: int, k: nat, e: int)
    requires
        m == v * pow2(k),
    ensures
        eq(m, 1, e - k, v, 1, e),
{
    lemma_at(m, 1, e - k, v, 1, e, e - k);
    assert((e - k - (e - k)) as nat == 0nat);
    assert(((e - (e - k)) as nat) == k);
    lemma2_to64();
}

// ---------------------------------------------------------------------------
// Exact conversions
// ---------------------------------------------------------------------------

/// An integer below `2^53` converts exactly: the double's value is `w`,
/// with `ex <= 0`.
pub proof fn lemma_from_u64_exact(w: int, r: u64)
    requires
        0 < w < 0x20_0000_0000_0000,
        rounds(r, false, w, 1, 0),
    ensures
        r == mag(r),
        finite(r),
        bexp(r) > 0,
        sig(r) > 0,
        ex(r) <= 0,
        sig(r) == w * pow2((-ex(r)) as nat),
        eq(sig(r), 1, ex(r), w, 1, 0),
{
    let b = mag(r);
    assert(r == b);
    lemma_pow2_pos(970);
    if b == INF {
        lemma_at(w, 1, 0, 0x3F_FFFF_FFFF_FFFF, 1, 970, 0);
        assert(pow2(0) == 1) by { lemma2_to64(); }
        assert(0x3F_FFFF_FFFF_FFFF * 1 * pow2(970) >= 0x3F_FFFF_FFFF_FFFF) by (nonlinear_arith)
            requires pow2(970) > 0;
        assert(false);
    }
    assert(b < INF);
    let m = sig(b);
    let f = ex(b);
    let even = m % 2 == 0;
    let lo4 = frac(b) == 0 && bexp(b) > 1;
    if f > 0 {
        // Then b >= 2^53 > w, and even its lower midpoint is above w.
        assert(bexp(b) >= 1076);
        assert(m >= 0x10_0000_0000_0000);
        assert(pow2(1) == 2 && pow2(0) == 1) by { lemma2_to64(); }
        assert(rne(b, w, 1, 0));
        if lo4 {
            assert(w < 4 * m - 1);
            if f >= 2 {
                lemma_at(w, 1, 0, 4 * m - 1, 1, f - 2, 0);
                lemma_pow2_pos((f - 2) as nat);
                assert(w * 1 * pow2(0) < (4 * m - 1) * 1 * pow2((f - 2) as nat)) by (nonlinear_arith)
                    requires pow2((f - 2) as nat) >= 1, pow2(0) == 1, w < 4 * m - 1, w > 0;
                assert(lt(w, 1, 0, 4 * m - 1, 1, f - 2));
            } else {
                assert(f == 1);
                lemma_at(w, 1, 0, 4 * m - 1, 1, f - 2, -1);
                assert((0 - -1) as nat == 1 && (f - 2 - -1) as nat == 0);
                assert(w * 1 * pow2(1) < (4 * m - 1) * 1 * pow2(0));
                assert(lt(w, 1, 0, 4 * m - 1, 1, f - 2));
            }
        } else {
            assert(frac(b) > 0);
            assert(w < 2 * m - 1);
            lemma_at(w, 1, 0, 2 * m - 1, 1, f - 1, 0);
            lemma_pow2_pos((f - 1) as nat);
            assert(pow2(0) == 1) by { lemma2_to64(); }
            assert(w * 1 * pow2(0) < (2 * m - 1) * 1 * pow2((f - 1) as nat)) by (nonlinear_arith)
                requires pow2((f - 1) as nat) >= 1, pow2(0) == 1, w < 2 * m - 1, w > 0;
            assert(lt(w, 1, 0, 2 * m - 1, 1, f - 1));
        }
        assert(false);
    }
    // f <= 0: on the grid 2^f, w is the integer wp = w * 2^-f.
    let k = (-f) as nat;
    let p = pow2(k);
    lemma_pow2_pos(k);
    let wp = w * p;
    lemma_pow2_adds(k, 1);
    lemma_pow2_adds(k, 2);
    assert(pow2(1) == 2 && pow2(2) == 4 && pow2(0) == 1) by { lemma2_to64(); }
    assert(pow2(k + 1) == 2 * p) by (nonlinear_arith) requires pow2(k + 1) == p * pow2(1), pow2(1) == 2;
    assert(pow2(k + 2) == 4 * p) by (nonlinear_arith) requires pow2(k + 2) == p * pow2(2), pow2(2) == 4;
    // Lower midpoint: wp >= m.
    if lo4 {
        lemma_at(w, 1, 0, 4 * m - 1, 1, f - 2, f - 2);
        assert((0 - (f - 2)) as nat == k + 2);
        assert(w * 1 * (4 * p) == 4 * wp) by (nonlinear_arith) requires wp == w * p;
        assert(wp >= m);
    } else {
        lemma_at(w, 1, 0, 2 * m - 1, 1, f - 1, f - 1);
        assert((0 - (f - 1)) as nat == k + 1);
        assert(w * 1 * (2 * p) == 2 * wp) by (nonlinear_arith) requires wp == w * p;
        assert(wp >= m);
    }
    // Upper midpoint: wp <= m.
    lemma_at(w, 1, 0, 2 * m + 1, 1, f - 1, f - 1);
    assert((0 - (f - 1)) as nat == k + 1);
    assert(w * 1 * (2 * p) == 2 * wp) by (nonlinear_arith) requires wp == w * p;
    assert(wp <= m);
    assert(m == wp);
    assert(m > 0) by (nonlinear_arith) requires m == w * p, w > 0, p > 0;
    if bexp(b) == 0 {
        // A subnormal has ex = -1074 and sig < 2^52, but w * 2^1074 is far bigger.
        lemma_pow2_strictly_increases(52, k);
        assert(0x10_0000_0000_0000 == pow2(52)) by { lemma2_to64(); lemma2_to64_rest(); }
        assert(wp >= p) by (nonlinear_arith) requires wp == w * p, w >= 1, p > 0;
        assert(false);
    }
    lemma_eq_scaled(m, w, k, 0);
}

// ---------------------------------------------------------------------------
// Exact powers of ten
// ---------------------------------------------------------------------------

/// `10^k` as a double, for `k = 0..=22`: exact, since `10^k = 5^k * 2^k`
/// and `5^22 < 2^53`.
pub const P10: [u64; 23] = [
    0x3ff0000000000000, 0x4024000000000000, 0x4059000000000000, 0x408f400000000000,
    0x40c3880000000000, 0x40f86a0000000000, 0x412e848000000000, 0x416312d000000000,
    0x4197d78400000000, 0x41cdcd6500000000, 0x4202a05f20000000, 0x42374876e8000000,
    0x426d1a94a2000000, 0x42a2309ce5400000, 0x42d6bcc41e900000, 0x430c6bf526340000,
    0x4341c37937e08000, 0x4376345785d8a000, 0x43abc16d674ec800, 0x43e158e460913d00,
    0x4415af1d78b58c40, 0x444b1ae4d6e2ef50, 0x4480f0cf064dd592,
];

/// `b^e`, by recursion `compute_only` can evaluate.
pub open spec fn cpow(b: int, e: nat) -> int
    decreases e,
{
    if e == 0 { 1 } else { b * cpow(b, (e - 1) as nat) }
}

proof fn lemma_cpow(b: int, e: nat)
    ensures
        cpow(b, e) == pow(b, e),
    decreases e,
{
    reveal(pow);
    if e > 0 {
        lemma_cpow(b, (e - 1) as nat);
    }
}

/// Entry `k` is a finite positive normal double `5^k * 2^s * 2^(k - s)`.
pub open spec fn p10_ok(k: int) -> bool {
    let b = P10@[k];
    &&& b < INF
    &&& bexp(b) > 0
    &&& ex(b) <= k
    &&& sig(b) == cpow(5, k as nat) * cpow(2, (k - ex(b)) as nat)
}

pub open spec fn p10_ok_below(n: nat) -> bool
    decreases n,
{
    if n == 0 { true } else { p10_ok(n - 1) && p10_ok_below((n - 1) as nat) }
}

proof fn lemma_p10_below(n: nat, k: int)
    requires
        p10_ok_below(n),
        0 <= k < n,
    ensures
        p10_ok(k),
    decreases n,
{
    if k != n - 1 {
        lemma_p10_below((n - 1) as nat, k);
    }
}

/// `P10[k]` is a finite positive double worth exactly `10^k`, i.e.
/// `5^k * 2^k`.
pub proof fn lemma_p10(k: int)
    requires
        0 <= k <= 22,
    ensures
        P10@[k] == mag(P10@[k]),
        finite(P10@[k]),
        !neg(P10@[k]),
        sig(P10@[k]) > 0,
        eq(sig(P10@[k]), 1, ex(P10@[k]), pow(5, k as nat), 1, k),
{
    assert(p10_ok_below(23)) by (compute_only);
    lemma_p10_below(23, k);
    let b = P10@[k];
    let s = (k - ex(b)) as nat;
    lemma_cpow(5, k as nat);
    lemma_cpow(2, s);
    lemma_pow2(s);
    lemma_pow_positive(5, k as nat);
    lemma_pow2_pos(s);
    assert(sig(b) > 0) by (nonlinear_arith)
        requires sig(b) == pow(5, k as nat) * pow2(s), pow(5, k as nat) > 0, pow2(s) > 0;
    lemma_eq_scaled(sig(b), pow(5, k as nat), s, k);
}

} // verus!

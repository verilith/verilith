//! Signed-integer and bit-count primitives.
//!
//! The signed operations work on the two's-complement bit patterns with
//! unsigned operators only, so Verus checks them against the definitions
//! in [`crate::num`]. rustc compiles the comparison, the arithmetic shift
//! and the sign extensions to the same instructions as the signed Rust
//! operators (`setl`, `sar`, `movsx`); division and remainder take the
//! magnitudes, divide unsigned and fix the sign. `clz`/`ctz` are proven
//! from vstd's specifications of `leading_zeros`/`trailing_zeros`.
//!
//! `popcnt32`/`popcnt64` are the only trusted functions left here (vstd has
//! no specification of `count_ones`). `tests/sint.rs` checks every
//! function against an independent `i128` evaluation of the definitions.
use vstd::prelude::*;
use crate::num::*;

verus! {

// ---------------------------------------------------------------------------
// Two's complement on u32
// ---------------------------------------------------------------------------

/// `|s32(a)|` (which fits: `|s32(0x8000_0000)| = 2^31`).
#[inline(always)]
fn mag32(a: u32) -> (r: u32)
    ensures r as int == if s32(a) < 0 { -s32(a) } else { s32(a) },
{
    if a < 0x8000_0000 {
        a
    } else {
        assert(!a == (0xffff_ffffu32 - a) as u32) by (bit_vector);
        (!a) + 1
    }
}

/// `m32(-x)` for `0 <= x <= 2^32`.
#[inline(always)]
fn neg32(x: u32) -> (r: u32)
    ensures r == m32(-(x as int)),
{
    let r = 0u32.wrapping_sub(x);
    assert(r as int == if x == 0 { 0 } else { 0x1_0000_0000 - x as int });
    r
}

proof fn lemma_flip32(a: u32)
    ensures
        (a ^ 0x8000_0000u32) as int == s32(a) + 0x8000_0000,
{
    assert(a ^ 0x8000_0000u32 == if a < 0x8000_0000u32 { (a + 0x8000_0000u32) as u32 } else {
        (a - 0x8000_0000u32) as u32
    }) by (bit_vector);
}

/// The truncated quotient and remainder of signed values, from the
/// unsigned ones of their magnitudes.
proof fn lemma_tdiv_trem(x: int, y: int, q: int, r: int)
    requires
        y != 0,
        q == (if x < 0 { -x } else { x }) / (if y < 0 { -y } else { y }),
        r == (if x < 0 { -x } else { x }) % (if y < 0 { -y } else { y }),
    ensures
        tdiv(x, y) == if (x < 0) != (y < 0) { -q } else { q },
        trem(x, y) == if x < 0 { -r } else { r },
{
    let ax = if x < 0 { -x } else { x };
    let ay = if y < 0 { -y } else { y };
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ax, ay);
    assert(ax == ay * q + r);
    if x < 0 {
        if y < 0 {
            assert(x - y * q == -r) by (nonlinear_arith) requires ax == -x, ay == -y, ax == ay * q + r;
        } else {
            assert(x - y * (-q) == -r) by (nonlinear_arith) requires ax == -x, ay == y, ax == ay * q + r;
        }
    } else {
        if y < 0 {
            assert(x - y * (-q) == r) by (nonlinear_arith) requires ax == x, ay == -y, ax == ay * q + r;
        } else {
            assert(x - y * q == r) by (nonlinear_arith) requires ax == x, ay == y, ax == ay * q + r;
        }
    }
}

#[inline(always)]
pub fn div_s32(a: u32, b: u32) -> (r: u32)
    requires b != 0, !(a == 0x8000_0000 && b == 0xffff_ffff),
    ensures r == m32(tdiv(s32(a), s32(b))),
{
    let (x, y) = (mag32(a), mag32(b));
    let q = x / y;
    proof { lemma_tdiv_trem(s32(a), s32(b), q as int, (x % y) as int); }
    if (a < 0x8000_0000) != (b < 0x8000_0000) { neg32(q) } else { q }
}

#[inline(always)]
pub fn rem_s32(a: u32, b: u32) -> (r: u32)
    requires b != 0,
    ensures r == m32(trem(s32(a), s32(b))),
{
    let (x, y) = (mag32(a), mag32(b));
    let m = x % y;
    proof { lemma_tdiv_trem(s32(a), s32(b), (x / y) as int, m as int); }
    if a < 0x8000_0000 { m } else { neg32(m) }
}

/// The arithmetic shift: `a >> k`, or for a negative `a`, the complement
/// of the logical shift of its complement.
#[inline(always)]
pub fn shr_s32(a: u32, k: u32) -> (r: u32)
    requires k < 32,
    ensures r == m32(s32(a) / pow2(k as nat)),
{
    proof { lemma_pow2_pos(k as nat); }
    if a < 0x8000_0000 {
        proof { lemma_shr32(a, k); }
        a >> k
    } else {
        let n = !a;
        assert(n == (0xffff_ffffu32 - a) as u32) by (bit_vector) requires n == !a;
        proof { lemma_shr32(n, k); }
        let s = n >> k;
        let r = !s;
        assert(r == (0xffff_ffffu32 - s) as u32) by (bit_vector) requires r == !s;
        let ghost p = pow2(k as nat);
        // s32(a) = -(n + 1), and floor(-(n + 1) / p) = -(floor(n / p) + 1).
        assert((-(n as int) - 1) / p == -((n as int) / p) - 1) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, p);
            let q = (n as int) / p;
            let m = (n as int) % p;
            assert(-(n as int) - 1 == p * (-q - 1) + (p - 1 - m)) by (nonlinear_arith)
                requires n as int == p * q + m;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(-(n as int) - 1, p, -q - 1, p - 1 - m);
        }
        r
    }
}

#[inline(always)]
pub fn lt_s32(a: u32, b: u32) -> (r: bool)
    ensures r == (s32(a) < s32(b)),
{
    proof { lemma_flip32(a); lemma_flip32(b); }
    (a ^ 0x8000_0000) < (b ^ 0x8000_0000)
}

/// Sign-extends the low `n` bits of `a` to 32 bits (n = 8 or 16).
#[inline(always)]
pub fn sext32(a: u32, n: u32) -> (r: u32)
    requires n == 8 || n == 16,
    ensures r == m32(sext(a as nat, n as nat)),
{
    proof { lemma_pow2_values(); }
    if n == 8 {
        let x = a & 0xff;
        assert(x == a % 256) by (bit_vector) requires x == a & 0xff;
        let r = (x ^ 0x80).wrapping_sub(0x80);
        assert(r == if x < 0x80 { x } else { (x + 0xffff_ff00u32) as u32 }) by (bit_vector)
            requires x < 256, r == (x ^ 0x80).wrapping_sub(0x80);
        r
    } else {
        let x = a & 0xffff;
        assert(x == a % 65536) by (bit_vector) requires x == a & 0xffff;
        let r = (x ^ 0x8000).wrapping_sub(0x8000);
        assert(r == if x < 0x8000 { x } else { (x + 0xffff_0000u32) as u32 }) by (bit_vector)
            requires x < 65536, r == (x ^ 0x8000).wrapping_sub(0x8000);
        r
    }
}

// ---------------------------------------------------------------------------
// Two's complement on u64
// ---------------------------------------------------------------------------

#[inline(always)]
fn mag64(a: u64) -> (r: u64)
    ensures r as int == if s64(a) < 0 { -s64(a) } else { s64(a) },
{
    if a < 0x8000_0000_0000_0000 {
        a
    } else {
        assert(!a == (0xffff_ffff_ffff_ffffu64 - a) as u64) by (bit_vector);
        (!a) + 1
    }
}

#[inline(always)]
fn neg64(x: u64) -> (r: u64)
    ensures r == m64(-(x as int)),
{
    let r = 0u64.wrapping_sub(x);
    assert(r as int == if x == 0 { 0 } else { 0x1_0000_0000_0000_0000 - x as int });
    r
}

proof fn lemma_flip64(a: u64)
    ensures
        (a ^ 0x8000_0000_0000_0000u64) as int == s64(a) + 0x8000_0000_0000_0000,
{
    assert(a ^ 0x8000_0000_0000_0000u64 == if a < 0x8000_0000_0000_0000u64 {
        (a + 0x8000_0000_0000_0000u64) as u64
    } else {
        (a - 0x8000_0000_0000_0000u64) as u64
    }) by (bit_vector);
}

#[inline(always)]
pub fn div_s64(a: u64, b: u64) -> (r: u64)
    requires b != 0, !(a == 0x8000_0000_0000_0000 && b == 0xffff_ffff_ffff_ffff),
    ensures r == m64(tdiv(s64(a), s64(b))),
{
    let (x, y) = (mag64(a), mag64(b));
    let q = x / y;
    proof { lemma_tdiv_trem(s64(a), s64(b), q as int, (x % y) as int); }
    if (a < 0x8000_0000_0000_0000) != (b < 0x8000_0000_0000_0000) { neg64(q) } else { q }
}

#[inline(always)]
pub fn rem_s64(a: u64, b: u64) -> (r: u64)
    requires b != 0,
    ensures r == m64(trem(s64(a), s64(b))),
{
    let (x, y) = (mag64(a), mag64(b));
    let m = x % y;
    proof { lemma_tdiv_trem(s64(a), s64(b), (x / y) as int, m as int); }
    if a < 0x8000_0000_0000_0000 { m } else { neg64(m) }
}

#[inline(always)]
pub fn shr_s64(a: u64, k: u64) -> (r: u64)
    requires k < 64,
    ensures r == m64(s64(a) / pow2(k as nat)),
{
    proof { lemma_pow2_pos(k as nat); }
    if a < 0x8000_0000_0000_0000 {
        proof { lemma_shr64(a, k); }
        a >> k
    } else {
        let n = !a;
        assert(n == (0xffff_ffff_ffff_ffffu64 - a) as u64) by (bit_vector) requires n == !a;
        proof { lemma_shr64(n, k); }
        let s = n >> k;
        let r = !s;
        assert(r == (0xffff_ffff_ffff_ffffu64 - s) as u64) by (bit_vector) requires r == !s;
        let ghost p = pow2(k as nat);
        assert((-(n as int) - 1) / p == -((n as int) / p) - 1) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, p);
            let q = (n as int) / p;
            let m = (n as int) % p;
            assert(-(n as int) - 1 == p * (-q - 1) + (p - 1 - m)) by (nonlinear_arith)
                requires n as int == p * q + m;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(-(n as int) - 1, p, -q - 1, p - 1 - m);
        }
        r
    }
}

#[inline(always)]
pub fn lt_s64(a: u64, b: u64) -> (r: bool)
    ensures r == (s64(a) < s64(b)),
{
    proof { lemma_flip64(a); lemma_flip64(b); }
    (a ^ 0x8000_0000_0000_0000) < (b ^ 0x8000_0000_0000_0000)
}

/// Sign-extends the low `n` bits of `a` to 64 bits (n = 8, 16 or 32).
#[inline(always)]
pub fn sext64(a: u64, n: u32) -> (r: u64)
    requires n == 8 || n == 16 || n == 32,
    ensures r == m64(sext(a as nat, n as nat)),
{
    proof { lemma_pow2_values(); }
    if n == 8 {
        let x = a & 0xff;
        assert(x == a % 256) by (bit_vector) requires x == a & 0xff;
        let r = (x ^ 0x80).wrapping_sub(0x80);
        assert(r == if x < 0x80 { x } else { (x + 0xffff_ffff_ffff_ff00u64) as u64 }) by (bit_vector)
            requires x < 256, r == (x ^ 0x80).wrapping_sub(0x80);
        r
    } else if n == 16 {
        let x = a & 0xffff;
        assert(x == a % 65536) by (bit_vector) requires x == a & 0xffff;
        let r = (x ^ 0x8000).wrapping_sub(0x8000);
        assert(r == if x < 0x8000 { x } else { (x + 0xffff_ffff_ffff_0000u64) as u64 }) by (bit_vector)
            requires x < 65536, r == (x ^ 0x8000).wrapping_sub(0x8000);
        r
    } else {
        let x = a & 0xffff_ffff;
        assert(x == a % 0x1_0000_0000) by (bit_vector) requires x == a & 0xffff_ffff;
        let r = (x ^ 0x8000_0000).wrapping_sub(0x8000_0000);
        assert(r == if x < 0x8000_0000 { x } else { (x + 0xffff_ffff_0000_0000u64) as u64 }) by (bit_vector)
            requires x < 0x1_0000_0000, r == (x ^ 0x8000_0000).wrapping_sub(0x8000_0000);
        r
    }
}

// ---------------------------------------------------------------------------
// Bit counts
// ---------------------------------------------------------------------------

proof fn lemma_pow2_mono(a: nat, b: nat)
    requires a <= b,
    ensures pow2(a) <= pow2(b),
{
    lemma_pow2_add(a, (b - a) as nat);
    lemma_pow2_pos(a);
    lemma_pow2_pos((b - a) as nat);
    assert(pow2(a) * pow2((b - a) as nat) >= pow2(a) * 1) by (nonlinear_arith)
        requires pow2((b - a) as nat) >= 1, pow2(a) > 0;
}

/// `clz(a, n)` is `n - m` when `a` has exactly `m` significant bits.
proof fn lemma_clz(a: nat, n: nat, m: nat)
    requires
        m <= n,
        a < pow2(m),
        m == 0 || a >= pow2((m - 1) as nat),
    ensures
        clz(a, n) == n - m,
    decreases n,
{
    if n > 0 && m < n {
        lemma_pow2_mono(m, (n - 1) as nat);
        lemma_clz(a, (n - 1) as nat, m);
    }
}

/// `ctz(a, n)` is `t` when bit `t < n` is the lowest set bit of `a`.
proof fn lemma_ctz(a: int, n: nat, t: nat)
    requires
        a >= 0,
        t < n,
        a % pow2(t) == 0,
        (a / pow2(t)) % 2 == 1,
    ensures
        ctz(a as nat, n) == t,
    decreases t,
{
    if t > 0 {
        let t1 = (t - 1) as nat;
        lemma_pow2_pos(t1);
        let p = pow2(t1);
        assert(pow2(t) == 2 * p);
        // 2 divides 2^t, which divides a.
        assert(a % 2 == 0) by {
            vstd::arithmetic::div_mod::lemma_mod_mod(a, 2, p);
        }
        assert((a / 2) % p == 0 && (a / 2) / p == a / pow2(t)) by {
            vstd::arithmetic::div_mod::lemma_div_denominator(a, 2, p);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, 2 * p);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, 2);
            let k = a / (2 * p);
            assert(a == 2 * p * k);
            assert(a / 2 == p * k) by {
                assert(a == 2 * (p * k)) by (nonlinear_arith) requires a == 2 * p * k;
                vstd::arithmetic::div_mod::lemma_div_multiples_vanish(p * k, 2);
            }
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(k, p);
            assert(p * k == k * p) by (nonlinear_arith);
        }
        lemma_ctz(a / 2, (n - 1) as nat, t1);
    } else {
        assert(pow2(0) == 1);
    }
}

proof fn lemma_ctz_zero(n: nat)
    ensures ctz(0, n) == n,
    decreases n,
{
    if n > 0 {
        lemma_ctz_zero((n - 1) as nat);
    }
}

#[inline(always)]
pub fn clz32(a: u32) -> (r: u32)
    ensures r == clz(a as nat, 32),
{
    let r = a.leading_zeros();
    proof {
        broadcast use vstd::std_specs::bits::axiom_u32_leading_zeros;
        let m = (32 - r) as nat;
        if r == 0 {
            lemma_pow2_values();
        } else {
            lemma_shr32(a, (32 - r) as u32);
            lemma_pow2_pos(m);
            assert(a >> ((32 - r) as u32) == 0);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, pow2(m));
        }
        if r < 32 {
            let j = (31 - r) as u32;
            lemma_shr32(a, j);
            let s = a >> j;
            assert(s & 1 != 0 ==> s >= 1) by (bit_vector);
            lemma_pow2_pos(j as nat);
            assert(a as int >= pow2(j as nat)) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, pow2(j as nat));
                assert(a as int / pow2(j as nat) >= 1);
                assert(pow2(j as nat) * (a as int / pow2(j as nat)) >= pow2(j as nat)) by (nonlinear_arith)
                    requires a as int / pow2(j as nat) >= 1, pow2(j as nat) > 0;
            }
        }
        lemma_clz(a as nat, 32, m);
    }
    r
}

#[inline(always)]
pub fn ctz32(a: u32) -> (r: u32)
    ensures r == ctz(a as nat, 32),
{
    let r = a.trailing_zeros();
    proof {
        broadcast use vstd::std_specs::bits::axiom_u32_trailing_zeros;
        if a == 0 {
            lemma_ctz_zero(32);
        } else {
            let t = r as nat;
            lemma_shr32(a, r);
            let s = a >> r;
            assert(s & 1 == 1 ==> s % 2 == 1) by (bit_vector);
            lemma_pow2_pos(t);
            // The bits below `t` are zero: `a << (32 - t)` wraps to 0.
            if r > 0 {
                lemma_shl32(a, (32 - r) as u32);
                lemma_pow2_add(t, (32 - t) as nat);
                lemma_pow2_values();
                lemma_pow2_pos((32 - t) as nat);
                let p = pow2(t);
                let w = pow2((32 - t) as nat);
                assert(p * w == 0x1_0000_0000);
                assert((a as int * w) % 0x1_0000_0000 == 0);
                assert(a as int % p == 0) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, p);
                    let q = a as int / p;
                    let m = a as int % p;
                    assert(a as int * w == q * (p * w) + m * w) by (nonlinear_arith)
                        requires a as int == p * q + m;
                    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, m * w, p * w);
                    assert(0 <= m * w < p * w) by (nonlinear_arith) requires 0 <= m < p, w > 0;
                    vstd::arithmetic::div_mod::lemma_small_mod((m * w) as nat, (p * w) as nat);
                    assert(m * w == 0);
                    assert(m == 0) by (nonlinear_arith) requires m * w == 0, w > 0;
                }
            } else {
                assert(pow2(0) == 1);
            }
            lemma_ctz(a as int, 32, t);
        }
    }
    r
}

#[verifier::external_body]
#[inline(always)]
pub fn popcnt32(a: u32) -> (r: u32)
    ensures r == popcnt(a as nat),
{
    a.count_ones()
}

#[inline(always)]
pub fn clz64(a: u64) -> (r: u64)
    ensures r == clz(a as nat, 64),
{
    let r = a.leading_zeros();
    proof {
        broadcast use vstd::std_specs::bits::axiom_u64_leading_zeros;
        reveal(vstd::std_specs::bits::u64_leading_zeros);
        let m = (64 - r) as nat;
        if r == 0 {
            lemma_pow2_values();
        } else {
            lemma_shr64(a, (64 - r) as u64);
            lemma_pow2_pos(m);
            assert(a >> ((64 - r) as u64) == 0);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, pow2(m));
        }
        if r < 64 {
            let j = (63 - r) as u64;
            lemma_shr64(a, j);
            let s = a >> j;
            assert(s & 1 != 0 ==> s >= 1) by (bit_vector);
            lemma_pow2_pos(j as nat);
            assert(a as int >= pow2(j as nat)) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, pow2(j as nat));
                assert(a as int / pow2(j as nat) >= 1);
                assert(pow2(j as nat) * (a as int / pow2(j as nat)) >= pow2(j as nat)) by (nonlinear_arith)
                    requires a as int / pow2(j as nat) >= 1, pow2(j as nat) > 0;
            }
        }
        lemma_clz(a as nat, 64, m);
    }
    r as u64
}

#[inline(always)]
pub fn ctz64(a: u64) -> (r: u64)
    ensures r == ctz(a as nat, 64),
{
    let r = a.trailing_zeros();
    proof {
        broadcast use vstd::std_specs::bits::axiom_u64_trailing_zeros;
        if a == 0 {
            lemma_ctz_zero(64);
        } else {
            let t = r as nat;
            lemma_shr64(a, r as u64);
            let s = a >> (r as u64);
            assert(s & 1 == 1 ==> s % 2 == 1) by (bit_vector);
            lemma_pow2_pos(t);
            if r > 0 {
                lemma_shl64(a, (64 - r) as u64);
                lemma_pow2_add(t, (64 - t) as nat);
                lemma_pow2_values();
                lemma_pow2_pos((64 - t) as nat);
                let p = pow2(t);
                let w = pow2((64 - t) as nat);
                assert(p * w == 0x1_0000_0000_0000_0000);
                assert((a as int * w) % 0x1_0000_0000_0000_0000 == 0);
                assert(a as int % p == 0) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, p);
                    let q = a as int / p;
                    let m = a as int % p;
                    assert(a as int * w == q * (p * w) + m * w) by (nonlinear_arith)
                        requires a as int == p * q + m;
                    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, m * w, p * w);
                    assert(0 <= m * w < p * w) by (nonlinear_arith) requires 0 <= m < p, w > 0;
                    vstd::arithmetic::div_mod::lemma_small_mod((m * w) as nat, (p * w) as nat);
                    assert(m * w == 0);
                    assert(m == 0) by (nonlinear_arith) requires m * w == 0, w > 0;
                }
            } else {
                assert(pow2(0) == 1);
            }
            lemma_ctz(a as int, 64, t);
        }
    }
    r as u64
}

#[verifier::external_body]
#[inline(always)]
pub fn popcnt64(a: u64) -> (r: u64)
    ensures r == popcnt(a as nat),
{
    a.count_ones() as u64
}

} // verus!

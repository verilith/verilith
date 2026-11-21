//! Integer numerics (§4.3.2) as functions on bit patterns, and their exec
//! implementations.
//!
//! Values live in untyped 64-bit slots: an `i32` is the low 32 bits of its
//! slot (operations read `lo32` and write zero-extended results), an `i64`
//! is the whole slot. Signed operations are defined through `s32`/`s64`,
//! the two's-complement reading of a bit pattern, exactly as the spec's
//! `signed_N` function.
use vstd::prelude::*;
use crate::sint;

verus! {

pub open spec fn lo32(a: u64) -> u32 {
    (a % 0x1_0000_0000) as u32
}

/// `i mod 2^32`: the spec's wrap-around for N = 32.
pub open spec fn m32(i: int) -> u32 {
    (i % 0x1_0000_0000) as u32
}

pub open spec fn m64(i: int) -> u64 {
    (i % 0x1_0000_0000_0000_0000) as u64
}

/// `signed_32`.
pub open spec fn s32(a: u32) -> int {
    if a < 0x8000_0000 { a as int } else { a as int - 0x1_0000_0000 }
}

/// `signed_64`.
pub open spec fn s64(a: u64) -> int {
    if a < 0x8000_0000_0000_0000 { a as int } else { a as int - 0x1_0000_0000_0000_0000 }
}

/// Division truncating toward zero.
pub open spec fn tdiv(x: int, y: int) -> int {
    let q = (if x < 0 { -x } else { x }) / (if y < 0 { -y } else { y });
    if (x < 0) != (y < 0) { -q } else { q }
}

/// The remainder of `tdiv`, with the sign of the dividend.
pub open spec fn trem(x: int, y: int) -> int {
    x - y * tdiv(x, y)
}

pub open spec fn pow2(k: nat) -> int
    decreases k,
{
    if k == 0 { 1 } else { 2 * pow2((k - 1) as nat) }
}

pub open spec fn popcnt(a: nat) -> nat
    decreases a,
{
    if a == 0 { 0 } else { a % 2 + popcnt(a / 2) }
}

pub open spec fn b2u(b: bool) -> u64 {
    if b { 1 } else { 0 }
}

// ---------------------------------------------------------------------------
// i32 (operands and results as u32)
// ---------------------------------------------------------------------------

pub open spec fn i32_shl(a: u32, b: u32) -> u32 {
    m32(a as int * pow2((b % 32) as nat))
}

pub open spec fn i32_shr_u(a: u32, b: u32) -> u32 {
    (a as int / pow2((b % 32) as nat)) as u32
}

pub open spec fn i32_shr_s(a: u32, b: u32) -> u32 {
    m32(s32(a) / pow2((b % 32) as nat))
}

pub open spec fn i32_rotl(a: u32, b: u32) -> u32 {
    let k = (b % 32) as nat;
    m32(a as int * pow2(k) + a as int / pow2((32 - k) as nat))
}

pub open spec fn i32_rotr(a: u32, b: u32) -> u32 {
    let k = (b % 32) as nat;
    m32(a as int / pow2(k) + a as int * pow2((32 - k) as nat))
}

/// Number of leading zero bits.
pub open spec fn clz(a: nat, n: nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else if a >= pow2((n - 1) as nat) { 0 } else { 1 + clz(a, (n - 1) as nat) }
}

/// Number of trailing zero bits.
pub open spec fn ctz(a: nat, n: nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else if a % 2 == 1 { 0 } else { 1 + ctz(a / 2, (n - 1) as nat) }
}

/// Sign-extend the low `n` bits of `a` (n = 8, 16, 32).
pub open spec fn sext(a: nat, n: nat) -> int {
    let x = a as int % pow2(n);
    if x < pow2((n - 1) as nat) { x } else { x - pow2(n) }
}

// ---------------------------------------------------------------------------
// i64 (operands and results as u64)
// ---------------------------------------------------------------------------

pub open spec fn i64_shl(a: u64, b: u64) -> u64 {
    m64(a as int * pow2((b % 64) as nat))
}

pub open spec fn i64_shr_u(a: u64, b: u64) -> u64 {
    (a as int / pow2((b % 64) as nat)) as u64
}

pub open spec fn i64_shr_s(a: u64, b: u64) -> u64 {
    m64(s64(a) / pow2((b % 64) as nat))
}

pub open spec fn i64_rotl(a: u64, b: u64) -> u64 {
    let k = (b % 64) as nat;
    m64(a as int * pow2(k) + a as int / pow2((64 - k) as nat))
}

pub open spec fn i64_rotr(a: u64, b: u64) -> u64 {
    let k = (b % 64) as nat;
    m64(a as int / pow2(k) + a as int * pow2((64 - k) as nat))
}

// ---------------------------------------------------------------------------
// Lemmas linking the bit-level exec code to the definitions above
// ---------------------------------------------------------------------------

pub proof fn lemma_pow2_values()
    ensures
        pow2(0) == 1, pow2(1) == 2, pow2(2) == 4, pow2(3) == 8, pow2(4) == 16, pow2(5) == 32,
        pow2(6) == 64, pow2(7) == 128, pow2(8) == 256, pow2(15) == 0x8000, pow2(16) == 0x10000,
        pow2(31) == 0x8000_0000, pow2(32) == 0x1_0000_0000,
        pow2(63) == 0x8000_0000_0000_0000, pow2(64) == 0x1_0000_0000_0000_0000,
{
    reveal_with_fuel(pow2, 65);
}

pub proof fn lemma_pow2_pos(k: nat)
    ensures pow2(k) > 0,
    decreases k,
{
    if k > 0 { lemma_pow2_pos((k - 1) as nat); }
}

pub proof fn lemma_pow2_add(a: nat, b: nat)
    ensures pow2(a + b) == pow2(a) * pow2(b),
    decreases a,
{
    if a > 0 {
        lemma_pow2_add((a - 1) as nat, b);
        assert(pow2(a + b) == 2 * pow2((a - 1 + b) as nat));
        vstd::arithmetic::mul::lemma_mul_is_associative(2, pow2((a - 1) as nat), pow2(b));
    }
}

/// `lo32` is the truncating cast.
pub proof fn lemma_lo32(a: u64)
    ensures lo32(a) == a as u32, lo32(a) as u64 == a & 0xffff_ffff,
{
    assert(a as u32 == a % 0x1_0000_0000 && a & 0xffff_ffff == a % 0x1_0000_0000) by (bit_vector);
}

/// `x << k` on N-bit words is `x * 2^k mod 2^N`.
pub proof fn lemma_shl32(a: u32, k: u32)
    requires k < 32,
    ensures (a << k) == m32(a as int * pow2(k as nat)),
    decreases k,
{
    lemma_pow2_pos(k as nat);
    if k == 0 {
        assert(a << 0u32 == a) by (bit_vector);
    } else {
        let j = (k - 1) as u32;
        lemma_shl32(a, j);
        assert((a << k) == (((a << j) as u64 * 2) % 0x1_0000_0000) as u32) by (bit_vector)
            requires k < 32, j == k - 1, k >= 1;
        let p = pow2(j as nat);
        assert(pow2(k as nat) == 2 * p);
        let x = a as int * p;
        assert(x >= 0) by (nonlinear_arith) requires p > 0, x == a as int * p;
        assert(((x % 0x1_0000_0000) * 2) % 0x1_0000_0000 == (x * 2) % 0x1_0000_0000) by {
            vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(x, 2, 0x1_0000_0000);
        }
        assert(a as int * (2 * p) == x * 2) by (nonlinear_arith) requires x == a as int * p;
    }
}

pub proof fn lemma_shl64(a: u64, k: u64)
    requires k < 64,
    ensures (a << k) == m64(a as int * pow2(k as nat)),
    decreases k,
{
    lemma_pow2_pos(k as nat);
    if k == 0 {
        assert(a << 0u64 == a) by (bit_vector);
    } else {
        let j = (k - 1) as u64;
        lemma_shl64(a, j);
        assert((a << k) == (((a << j) as u128 * 2) % 0x1_0000_0000_0000_0000) as u64) by (bit_vector)
            requires k < 64, j == k - 1, k >= 1;
        let p = pow2(j as nat);
        assert(pow2(k as nat) == 2 * p);
        let x = a as int * p;
        assert(x >= 0) by (nonlinear_arith) requires p > 0, x == a as int * p;
        assert(((x % 0x1_0000_0000_0000_0000) * 2) % 0x1_0000_0000_0000_0000
            == (x * 2) % 0x1_0000_0000_0000_0000) by {
            vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(x, 2, 0x1_0000_0000_0000_0000);
        }
        assert(a as int * (2 * p) == x * 2) by (nonlinear_arith) requires x == a as int * p;
    }
}

/// `x >> k` is `x / 2^k`.
pub proof fn lemma_shr32(a: u32, k: u32)
    requires k < 32,
    ensures (a >> k) as int == a as int / pow2(k as nat),
    decreases k,
{
    if k == 0 {
        assert(a >> 0u32 == a) by (bit_vector);
    } else {
        let j = (k - 1) as u32;
        lemma_shr32(a, j);
        assert((a >> k) == (a >> j) / 2) by (bit_vector) requires k < 32, j == k - 1, k >= 1;
        lemma_pow2_pos(j as nat);
        vstd::arithmetic::div_mod::lemma_div_denominator(a as int, pow2(j as nat), 2);
        assert(pow2(k as nat) == pow2(j as nat) * 2);
    }
}

pub proof fn lemma_shr64(a: u64, k: u64)
    requires k < 64,
    ensures (a >> k) as int == a as int / pow2(k as nat),
    decreases k,
{
    if k == 0 {
        assert(a >> 0u64 == a) by (bit_vector);
    } else {
        let j = (k - 1) as u64;
        lemma_shr64(a, j);
        assert((a >> k) == (a >> j) / 2) by (bit_vector) requires k < 64, j == k - 1, k >= 1;
        lemma_pow2_pos(j as nat);
        vstd::arithmetic::div_mod::lemma_div_denominator(a as int, pow2(j as nat), 2);
        assert(pow2(k as nat) == pow2(j as nat) * 2);
    }
}

// ---------------------------------------------------------------------------
// Exec
// ---------------------------------------------------------------------------

#[inline(always)]
pub fn lo(a: u64) -> (r: u32)
    ensures r == lo32(a),
{
    proof { lemma_lo32(a); }
    a as u32
}

#[inline(always)]
pub fn add32(a: u32, b: u32) -> (r: u32)
    ensures r == m32(a + b),
{
    a.wrapping_add(b)
}

#[inline(always)]
pub fn sub32(a: u32, b: u32) -> (r: u32)
    ensures r == m32(a - b),
{
    a.wrapping_sub(b)
}

#[inline(always)]
pub fn mul32(a: u32, b: u32) -> (r: u32)
    ensures r == m32(a * b),
{
    a.wrapping_mul(b)
}

#[inline(always)]
pub fn add64(a: u64, b: u64) -> (r: u64)
    ensures r == m64(a + b),
{
    a.wrapping_add(b)
}

#[inline(always)]
pub fn sub64(a: u64, b: u64) -> (r: u64)
    ensures r == m64(a - b),
{
    a.wrapping_sub(b)
}

#[inline(always)]
pub fn mul64(a: u64, b: u64) -> (r: u64)
    ensures r == m64(a * b),
{
    a.wrapping_mul(b)
}

#[inline(always)]
pub fn shl32(a: u32, b: u32) -> (r: u32)
    ensures r == i32_shl(a, b),
{
    let k = b & 31;
    assert(k == b % 32) by (bit_vector) requires k == b & 31;
    proof { lemma_shl32(a, k); }
    a << k
}

#[inline(always)]
pub fn shr_u32(a: u32, b: u32) -> (r: u32)
    ensures r == i32_shr_u(a, b),
{
    let k = b & 31;
    assert(k == b % 32) by (bit_vector) requires k == b & 31;
    proof { lemma_shr32(a, k); }
    a >> k
}

#[inline(always)]
pub fn shr_s32(a: u32, b: u32) -> (r: u32)
    ensures r == i32_shr_s(a, b),
{
    let k = b & 31;
    assert(k == b % 32) by (bit_vector) requires k == b & 31;
    sint::shr_s32(a, k)
}

#[inline(always)]
pub fn shl64(a: u64, b: u64) -> (r: u64)
    ensures r == i64_shl(a, b),
{
    let k = b & 63;
    assert(k == b % 64) by (bit_vector) requires k == b & 63;
    proof { lemma_shl64(a, k); }
    a << k
}

#[inline(always)]
pub fn shr_u64(a: u64, b: u64) -> (r: u64)
    ensures r == i64_shr_u(a, b),
{
    let k = b & 63;
    assert(k == b % 64) by (bit_vector) requires k == b & 63;
    proof { lemma_shr64(a, k); }
    a >> k
}

#[inline(always)]
pub fn shr_s64(a: u64, b: u64) -> (r: u64)
    ensures r == i64_shr_s(a, b),
{
    let k = b & 63;
    assert(k == b % 64) by (bit_vector) requires k == b & 63;
    sint::shr_s64(a, k)
}

#[inline(always)]
pub fn rotl32(a: u32, b: u32) -> (r: u32)
    ensures r == i32_rotl(a, b),
{
    let k = b & 31;
    assert(k == b % 32) by (bit_vector) requires k == b & 31;
    if k == 0 {
        proof {
            lemma_pow2_values();
            assert(a as int / 0x1_0000_0000 == 0);
            assert(m32(a as int) == a);
        }
        a
    } else {
        let j = 32 - k;
        let x = a << k;
        let y = a >> j;
        proof {
            lemma_shl32(a, k);
            lemma_shr32(a, j);
            lemma_pow2_pos(k as nat);
            lemma_pow2_pos(j as nat);
            // The two halves occupy disjoint bits, so | is +.
            assert(x & y == 0) by (bit_vector) requires x == a << k, y == a >> j, j == 32 - k, 0 < k < 32;
            assert(x | y == x + y) by (bit_vector) requires x & y == 0;
            // x < 2^32 - y: the shifted-in low bits of x are zero.
            assert(x as int + y as int <= 0xffff_ffff) by (bit_vector) requires x == a << k, y == a >> j, j == 32 - k, 0 < k < 32;
            let p = a as int * pow2(k as nat);
            let q = a as int / pow2(j as nat);
            assert(p >= 0) by (nonlinear_arith) requires pow2(k as nat) > 0, p == a as int * pow2(k as nat);
            assert(q >= 0) by (nonlinear_arith) requires pow2(j as nat) > 0, q == a as int / pow2(j as nat), a >= 0;
            vstd::arithmetic::div_mod::lemma_add_mod_noop(p, q, 0x1_0000_0000);
            vstd::arithmetic::div_mod::lemma_small_mod(q as nat, 0x1_0000_0000);
            vstd::arithmetic::div_mod::lemma_small_mod((x + y) as nat, 0x1_0000_0000);
        }
        x | y
    }
}

#[inline(always)]
pub fn rotr32(a: u32, b: u32) -> (r: u32)
    ensures r == i32_rotr(a, b),
{
    let k = b & 31;
    assert(k == b % 32) by (bit_vector) requires k == b & 31;
    if k == 0 {
        proof {
            lemma_pow2_values();
            assert(a as int * 0x1_0000_0000 % 0x1_0000_0000 == 0) by {
                vstd::arithmetic::div_mod::lemma_mod_multiples_basic(a as int, 0x1_0000_0000);
            }
            vstd::arithmetic::div_mod::lemma_add_mod_noop(a as int, a as int * 0x1_0000_0000, 0x1_0000_0000);
            vstd::arithmetic::div_mod::lemma_small_mod(a as nat, 0x1_0000_0000);
        }
        a
    } else {
        let j = 32 - k;
        let r = rotl32(a, j);
        proof {
            assert(j % 32 == j);
            assert((32 - j) as nat == k as nat);
        }
        r
    }
}

#[inline(always)]
pub fn rotl64(a: u64, b: u64) -> (r: u64)
    ensures r == i64_rotl(a, b),
{
    let k = b & 63;
    assert(k == b % 64) by (bit_vector) requires k == b & 63;
    if k == 0 {
        proof {
            lemma_pow2_values();
            assert(a as int / 0x1_0000_0000_0000_0000 == 0);
            assert(m64(a as int) == a);
        }
        a
    } else {
        let j = 64 - k;
        let x = a << k;
        let y = a >> j;
        proof {
            lemma_shl64(a, k);
            lemma_shr64(a, j);
            lemma_pow2_pos(k as nat);
            lemma_pow2_pos(j as nat);
            assert(x & y == 0) by (bit_vector) requires x == a << k, y == a >> j, j == 64 - k, 0 < k < 64;
            assert(x | y == x + y) by (bit_vector) requires x & y == 0;
            assert(x as int + y as int <= 0xffff_ffff_ffff_ffff) by (bit_vector) requires x == a << k, y == a >> j, j == 64 - k, 0 < k < 64;
            let p = a as int * pow2(k as nat);
            let q = a as int / pow2(j as nat);
            assert(p >= 0) by (nonlinear_arith) requires pow2(k as nat) > 0, p == a as int * pow2(k as nat);
            assert(q >= 0) by (nonlinear_arith) requires pow2(j as nat) > 0, q == a as int / pow2(j as nat), a >= 0;
            vstd::arithmetic::div_mod::lemma_add_mod_noop(p, q, 0x1_0000_0000_0000_0000);
            vstd::arithmetic::div_mod::lemma_small_mod(q as nat, 0x1_0000_0000_0000_0000);
            vstd::arithmetic::div_mod::lemma_small_mod((x + y) as nat, 0x1_0000_0000_0000_0000);
        }
        x | y
    }
}

#[inline(always)]
pub fn rotr64(a: u64, b: u64) -> (r: u64)
    ensures r == i64_rotr(a, b),
{
    let k = b & 63;
    assert(k == b % 64) by (bit_vector) requires k == b & 63;
    if k == 0 {
        proof {
            lemma_pow2_values();
            assert(a as int * 0x1_0000_0000_0000_0000 % 0x1_0000_0000_0000_0000 == 0) by {
                vstd::arithmetic::div_mod::lemma_mod_multiples_basic(a as int, 0x1_0000_0000_0000_0000);
            }
            vstd::arithmetic::div_mod::lemma_add_mod_noop(a as int, a as int * 0x1_0000_0000_0000_0000, 0x1_0000_0000_0000_0000);
            vstd::arithmetic::div_mod::lemma_small_mod(a as nat, 0x1_0000_0000_0000_0000);
        }
        a
    } else {
        let j = 64 - k;
        let r = rotl64(a, j);
        proof {
            assert(j % 64 == j);
            assert((64 - j) as nat == k as nat);
        }
        r
    }
}

} // verus!

//! Small facts about machine arithmetic.
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

/// Rust's conversion to `i16` is the reduction of the specification.
pub proof fn lemma_wrap16(x: i64)
    ensures
        (x as i16) as int == wrap16(x as int),
{
    let m = x & 0xffff;
    let q = x >> 16;
    assert(0 <= m < 0x1_0000 && x == q * 0x1_0000 + m && (x as i16) as i64 == if m >= 0x8000 {
        m - 0x1_0000
    } else {
        m as int
    }) by (bit_vector)
        requires
            m == x & 0xffff,
            q == x >> 16,
    ;
    lemma_fundamental_div_mod_converse(x as int, 0x1_0000, q as int, m as int);
}

/// Rust's conversion to `i32` is the reduction of the specification.
pub proof fn lemma_wrap32(x: i64)
    ensures
        (x as i32) as int == wrap32(x as int),
{
    let m = x & 0xffff_ffff;
    let q = x >> 32;
    assert(0 <= m < 0x1_0000_0000 && x == q * 0x1_0000_0000 + m && (x as i32) as i64 == if m >= 0x8000_0000 {
        m - 0x1_0000_0000
    } else {
        m as int
    }) by (bit_vector)
        requires
            m == x & 0xffff_ffff,
            q == x >> 32,
    ;
    lemma_fundamental_div_mod_converse(x as int, 0x1_0000_0000, q as int, m as int);
}

/// An arithmetic shift right is a division rounding down.
pub proof fn lemma_shr(v: i64, n: u32)
    requires
        n == 10 || n == 11 || n == 16 || n == 18,
    ensures
        n == 10 ==> (v >> 10) == (v as int) / 1024 && (v & 1023) == (v as int) % 1024,
        n == 11 ==> (v >> 11) == (v as int) / 2048,
        n == 16 ==> (v >> 16) == (v as int) / 65536,
        n == 18 ==> (v >> 18) == (v as int) / 262144,
{
    if n == 10 {
        let m = v & 1023;
        let q = v >> 10;
        assert(0 <= m < 1024 && v == q * 1024 + m) by (bit_vector)
            requires
                m == v & 1023,
                q == v >> 10,
        ;
        lemma_fundamental_div_mod_converse(v as int, 1024, q as int, m as int);
    } else if n == 11 {
        let m = v & 2047;
        let q = v >> 11;
        assert(0 <= m < 2048 && v == q * 2048 + m) by (bit_vector)
            requires
                m == v & 2047,
                q == v >> 11,
        ;
        lemma_fundamental_div_mod_converse(v as int, 2048, q as int, m as int);
    } else if n == 16 {
        let m = v & 65535;
        let q = v >> 16;
        assert(0 <= m < 65536 && v == q * 65536 + m) by (bit_vector)
            requires
                m == v & 65535,
                q == v >> 16,
        ;
        lemma_fundamental_div_mod_converse(v as int, 65536, q as int, m as int);
    } else {
        let m = v & 262143;
        let q = v >> 18;
        assert(0 <= m < 262144 && v == q * 262144 + m) by (bit_vector)
            requires
                m == v & 262143,
                q == v >> 18,
        ;
        lemma_fundamental_div_mod_converse(v as int, 262144, q as int, m as int);
    }
}

/// `v >> 16` on 32 bits is a division rounding down.
pub proof fn lemma_shr5(v: i64)
    ensures
        (v >> 5) == (v as int) / 32,
{
    let m = v & 31;
    let q = v >> 5;
    assert(0 <= m < 32 && v == q * 32 + m) by (bit_vector)
        requires
            m == v & 31,
            q == v >> 5,
    ;
    lemma_fundamental_div_mod_converse(v as int, 32, q as int, m as int);
}

/// Congruence modulo 2^32: what 32-bit wrapping arithmetic preserves.
pub open spec fn cong(a: int, b: int) -> bool {
    (a - b) % 0x1_0000_0000 == 0
}

/// Two numbers a multiple of 2^32 apart are congruent.
pub proof fn lemma_cong_k(v: int, t: int, k: int)
    requires
        v == t + 0x1_0000_0000 * k,
    ensures
        cong(v, t),
{
    lemma_mod_multiples_basic(k, 0x1_0000_0000);
    assert(v - t == k * 0x1_0000_0000);
}

/// Wrapping addition.
#[inline(always)]
pub fn wadd(a: i32, b: i32) -> (r: i32)
    ensures
        r == a + b - 0x1_0000_0000 * wq(a + b),
{
    reveal(wq);
    a.wrapping_add(b)
}

/// Wrapping subtraction.
#[inline(always)]
pub fn wsub(a: i32, b: i32) -> (r: i32)
    ensures
        r == a - b - 0x1_0000_0000 * wq(a - b),
{
    reveal(wq);
    a.wrapping_sub(b)
}

/// Wrapping multiplication: the product less a multiple of 2^32.
#[inline(always)]
pub fn wmul(a: i32, b: i32) -> (r: i32)
    ensures
        r == a * b - 0x1_0000_0000 * wq(a * b),
{
    proof {
        reveal(wq);
        let x = a * b;
        lemma_fundamental_div_mod(x, 0x1_0000_0000);
        lemma_mod_bound(x, 0x1_0000_0000);
        let q = x / 0x1_0000_0000;
        let m = x % 0x1_0000_0000;
        if m >= 0x8000_0000 {
            lemma_fundamental_div_mod_converse(x + 0x8000_0000, 0x1_0000_0000, q + 1, m - 0x8000_0000);
        } else {
            lemma_fundamental_div_mod_converse(x + 0x8000_0000, 0x1_0000_0000, q, m + 0x8000_0000);
        }
    }
    a.wrapping_mul(b)
}

/// How many times 2^32 comes off `x` when it wraps to 32 bits.
#[verifier::opaque]
pub open spec fn wq(x: int) -> int {
    (x + 0x8000_0000) / 0x1_0000_0000
}

/// The ten bits from bit 18 up of two numbers that agree modulo 2^32 are
/// the same.
pub proof fn lemma_cong_bits(x: int, y: int, k: int)
    requires
        x == y + 0x1_0000_0000 * k,
    ensures
        (x / 262144) % 1024 == (y / 262144) % 1024,
{
    lemma_fundamental_div_mod(y, 262144);
    lemma_mod_bound(y, 262144);
    let q = y / 262144;
    lemma_fundamental_div_mod_converse(x, 262144, q + 16384 * k, y % 262144);
    lemma_fundamental_div_mod(q, 1024);
    lemma_mod_bound(q, 1024);
    lemma_fundamental_div_mod_converse(q + 16384 * k, 1024, q / 1024 + 16 * k, q % 1024);
}

/// Bits 18 to 27 of a 32-bit value.
pub proof fn lemma_bits18(v: i32)
    ensures
        ((v >> 18) & 1023) == ((v as int) / 262144) % 1024,
        0 <= ((v >> 18) & 1023) < 1024,
{
    let q = v >> 18;
    let m = v & 262143;
    assert(0 <= m < 262144 && v == q * 262144 + m) by (bit_vector)
        requires
            m == v & 262143,
            q == v >> 18,
    ;
    lemma_fundamental_div_mod_converse(v as int, 262144, q as int, m as int);
    let lo = q & 1023;
    let hi = q >> 10;
    assert(0 <= lo < 1024 && q == hi * 1024 + lo) by (bit_vector)
        requires
            lo == q & 1023,
            hi == q >> 10,
    ;
    lemma_fundamental_div_mod_converse(q as int, 1024, hi as int, lo as int);
}

pub proof fn lemma_shr11(v: i32)
    ensures
        (v >> 11) == (v as int) / 2048,
{
    let m = v & 2047;
    let q = v >> 11;
    assert(0 <= m < 2048 && v == q * 2048 + m) by (bit_vector)
        requires
            m == v & 2047,
            q == v >> 11,
    ;
    lemma_fundamental_div_mod_converse(v as int, 2048, q as int, m as int);
}

pub proof fn lemma_shr16(v: i32)
    ensures
        (v >> 16) == (v as int) / 65536,
{
    let m = v & 65535;
    let q = v >> 16;
    assert(0 <= m < 65536 && v == q * 65536 + m) by (bit_vector)
        requires
            m == v & 65535,
            q == v >> 16,
    ;
    lemma_fundamental_div_mod_converse(v as int, 65536, q as int, m as int);
}

/// A 16-bit value read as signed.
pub proof fn lemma_sx16(q: u16)
    ensures
        (q as i16) as int == sx16(q as int),
{
    assert((q as i16) as int == if q >= 0x8000 {
        q - 0x1_0000
    } else {
        q as int
    }) by (bit_vector);
}

/// The zigzag table, read.
#[inline(always)]
pub fn zzx(k: usize) -> (r: usize)
    requires
        k < 80,
    ensures
        r == zz(k as int),
        r <= 63,
{
    ZZ[k] as usize
}

} // verus!

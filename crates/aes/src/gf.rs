//! GF(2^128) as the kernels compute it: SP 800-38D's bit-serial product
//! (`spec::gf_mul`) is a carry-less product of the two blocks followed
//! by a reduction, and from that, the algebra the kernels rely on:
//! commutativity, associativity, distributivity over XOR, and GHASH over
//! many blocks as one sum of products with powers of H (aggregated
//! reduction).
//!
//! Blocks are `spec::be128` integers: bit i of the block, the
//! coefficient of t^i, is integer bit 127 - i. The carry-less product of
//! two such integers has the coefficient of t^k of the product at bit
//! 254 - k (it is bit-reversed); `red` shifts it left by one and reduces
//! it modulo t^128 + t^7 + t^2 + t + 1 by shifts and XORs.
#![allow(unused_imports)]
use crate::spec::*;
#[cfg(verus_only)]
pub use verilith_simd::clmul::{clmul, clmul_n, hi64, lo64};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The 64 x 64 -> 128-bit carry-less product (PCLMULQDQ, PMULL)
// ---------------------------------------------------------------------------

// `clmul_n`, `clmul`, `lo64` and `hi64` are verilith-simd's (`clmul`),
// re-exported above: the instructions' specifications use them.

pub proof fn lemma_clmul_n_xor_l(a: u64, c: u64, b: u64, n: nat)
    ensures
        clmul_n(a ^ c, b, n) == clmul_n(a, b, n) ^ clmul_n(c, b, n),
    decreases n,
{
    if n == 0 {
        assert(0u128 ^ 0u128 == 0u128) by (bit_vector);
    } else {
        lemma_clmul_n_xor_l(a, c, b, (n - 1) as nat);
        let i = (n - 1) as u64;
        let p = clmul_n(a, b, (n - 1) as nat);
        let q = clmul_n(c, b, (n - 1) as nat);
        let t = (b as u128) << (n - 1) as u128;
        let ba = (a >> i) & 1 == 1;
        let bc = (c >> i) & 1 == 1;
        assert(((a ^ c) >> i) & 1 == 1 <==> (ba != bc)) by (bit_vector)
            requires
                ba == ((a >> i) & 1 == 1),
                bc == ((c >> i) & 1 == 1),
        ;
        assert((p ^ q) ^ (if ba != bc {
            t
        } else {
            0
        }) == (p ^ (if ba {
            t
        } else {
            0
        })) ^ (q ^ (if bc {
            t
        } else {
            0
        }))) by (bit_vector);
    }
}

pub proof fn lemma_clmul_n_xor_r(a: u64, b: u64, c: u64, n: nat)
    ensures
        clmul_n(a, b ^ c, n) == clmul_n(a, b, n) ^ clmul_n(a, c, n),
    decreases n,
{
    if n == 0 {
        assert(0u128 ^ 0u128 == 0u128) by (bit_vector);
    } else {
        lemma_clmul_n_xor_r(a, b, c, (n - 1) as nat);
        let s = (n - 1) as u128;
        let p = clmul_n(a, b, (n - 1) as nat);
        let q = clmul_n(a, c, (n - 1) as nat);
        let on = (a >> (n - 1) as u64) & 1 == 1;
        assert(((b ^ c) as u128) << s == ((b as u128) << s) ^ ((c as u128) << s)) by (bit_vector);
        assert((p ^ q) ^ (if on {
            ((b as u128) << s) ^ ((c as u128) << s)
        } else {
            0
        }) == (p ^ (if on {
            (b as u128) << s
        } else {
            0
        })) ^ (q ^ (if on {
            (c as u128) << s
        } else {
            0
        }))) by (bit_vector);
    }
}

pub proof fn lemma_clmul_xor_l(a: u64, c: u64, b: u64)
    ensures
        clmul(a ^ c, b) == clmul(a, b) ^ clmul(c, b),
{
    lemma_clmul_n_xor_l(a, c, b, 64);
}

pub proof fn lemma_clmul_xor_r(a: u64, b: u64, c: u64)
    ensures
        clmul(a, b ^ c) == clmul(a, b) ^ clmul(a, c),
{
    lemma_clmul_n_xor_r(a, b, c, 64);
}

pub proof fn lemma_clmul_n_zero(b: u64, n: nat)
    ensures
        clmul_n(0, b, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_clmul_n_zero(b, (n - 1) as nat);
        let i = (n - 1) as u64;
        assert((0u64 >> i) & 1 == 0) by (bit_vector);
        assert(0u128 ^ 0u128 == 0) by (bit_vector);
    }
}

/// One set bit: `clmul(1 << j, b)` is `b << j`.
pub proof fn lemma_clmul_n_bit(j: u64, b: u64, n: nat)
    requires
        j < 64,
        n <= 64,
    ensures
        clmul_n(1u64 << j, b, n) == if (j as nat) < n {
            (b as u128) << (j as u128)
        } else {
            0
        },
    decreases n,
{
    if n > 0 {
        lemma_clmul_n_bit(j, b, (n - 1) as nat);
        let i = (n - 1) as u64;
        assert(((1u64 << j) >> i) & 1 == 1 <==> i == j) by (bit_vector)
            requires
                j < 64,
                i < 64,
        ;
        let t = (b as u128) << (j as u128);
        assert(0u128 ^ t == t && t ^ 0u128 == t && 0u128 ^ 0u128 == 0) by (bit_vector);
    }
}

/// The low `n` bits of `a`.
pub open spec fn low_bits(a: u64, n: nat) -> u64 {
    if n >= 64 {
        a
    } else {
        a & ((1u64 << n as u64) - 1) as u64
    }
}

pub proof fn lemma_clmul_n_comm(a: u64, b: u64, n: nat)
    requires
        n <= 64,
    ensures
        clmul_n(a, b, n) == clmul(b, low_bits(a, n)),
    decreases n,
{
    if n == 0 {
        assert(a & ((1u64 << 0u64) - 1) as u64 == 0) by (bit_vector);
        lemma_clmul_n_zero(b, 64);
        lemma_clmul_n_comm_zero(b);
    } else {
        lemma_clmul_n_comm(a, b, (n - 1) as nat);
        let i = (n - 1) as u64;
        let l0 = low_bits(a, (n - 1) as nat);
        let l1 = low_bits(a, n);
        let on = (a >> i) & 1 == 1;
        assert(l1 == l0 ^ (if on {
            1u64 << i
        } else {
            0u64
        })) by {
            if n < 64 {
                assert(a & ((1u64 << (i + 1)) - 1) as u64 == (a & ((1u64 << i) - 1) as u64) ^ (if (a >> i) & 1 == 1 {
                    1u64 << i
                } else {
                    0u64
                })) by (bit_vector)
                    requires
                        i < 63,
                ;
            } else {
                assert(a == (a & ((1u64 << 63u64) - 1) as u64) ^ (if (a >> 63u64) & 1 == 1 {
                    1u64 << 63u64
                } else {
                    0u64
                })) by (bit_vector);
            }
        };
        lemma_clmul_xor_r(b, l0, if on {
            1u64 << i
        } else {
            0u64
        });
        if on {
            lemma_clmul_n_bit_r(b, i, 64);
        } else {
            lemma_clmul_n_comm_zero(b);
        }
    }
}

proof fn lemma_clmul_n_comm_zero(b: u64)
    ensures
        clmul(b, 0) == 0,
{
    lemma_clmul_n_zero_r(b, 64);
}

proof fn lemma_clmul_n_zero_r(b: u64, n: nat)
    ensures
        clmul_n(b, 0, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_clmul_n_zero_r(b, (n - 1) as nat);
        let s = (n - 1) as u128;
        assert((0u64 as u128) << s == 0 && 0u128 ^ 0u128 == 0) by (bit_vector);
    }
}

/// `clmul(b, 1 << j)` is `b << j` too.
proof fn lemma_clmul_n_bit_r(b: u64, j: u64, n: nat)
    requires
        j < 64,
        n <= 64,
    ensures
        clmul_n(b, 1u64 << j, n) == ((low_bits(b, n) as u128) << (j as u128)),
    decreases n,
{
    if n == 0 {
        assert(((b & ((1u64 << 0u64) - 1) as u64) as u128) << (j as u128) == 0) by (bit_vector);
    } else {
        lemma_clmul_n_bit_r(b, j, (n - 1) as nat);
        let i = (n - 1) as u64;
        if n < 64 {
            assert(((b & ((1u64 << (i + 1)) - 1) as u64) as u128) << (j as u128) == (((b & ((1u64 << i) - 1) as u64) as u128)
                << (j as u128)) ^ (if (b >> i) & 1 == 1 {
                ((1u64 << j) as u128) << (i as u128)
            } else {
                0
            })) by (bit_vector)
                requires
                    i < 63,
                    j < 64,
            ;
        } else {
            assert((b as u128) << (j as u128) == (((b & ((1u64 << 63u64) - 1) as u64) as u128) << (j as u128)) ^ (if (b
                >> 63u64) & 1 == 1 {
                ((1u64 << j) as u128) << (63u128)
            } else {
                0
            })) by (bit_vector)
                requires
                    j < 64,
            ;
        }
    }
}

/// Carry-less multiplication commutes.
pub proof fn lemma_clmul_comm(a: u64, b: u64)
    ensures
        clmul(a, b) == clmul(b, a),
{
    lemma_clmul_n_comm(a, b, 64);
}

// ---------------------------------------------------------------------------
// The 128 x 128 -> 256-bit product, as (low, high) halves
// ---------------------------------------------------------------------------

/// XOR of two 256-bit values.
pub open spec fn pxor(a: (u128, u128), b: (u128, u128)) -> (u128, u128) {
    (a.0 ^ b.0, a.1 ^ b.1)
}

/// The middle term of the product: x0 y1 + x1 y0.
pub open spec fn mid(x: u128, y: u128) -> u128 {
    clmul(lo64(x), hi64(y)) ^ clmul(hi64(x), lo64(y))
}

/// The halves of a product from its three parts: low, middle, high.
pub open spec fn join(l: u128, m: u128, h: u128) -> (u128, u128) {
    (l ^ (m << 64u128), h ^ (m >> 64u128))
}

/// The carry-less product of two 128-bit integers, schoolbook.
pub open spec fn prod(x: u128, y: u128) -> (u128, u128) {
    join(clmul(lo64(x), lo64(y)), mid(x, y), clmul(hi64(x), hi64(y)))
}

pub proof fn lemma_join_xor(l1: u128, m1: u128, h1: u128, l2: u128, m2: u128, h2: u128)
    ensures
        pxor(join(l1, m1, h1), join(l2, m2, h2)) == join(l1 ^ l2, m1 ^ m2, h1 ^ h2),
{
    assert((l1 ^ (m1 << 64u128)) ^ (l2 ^ (m2 << 64u128)) == (l1 ^ l2) ^ ((m1 ^ m2) << 64u128)) by (bit_vector);
    assert((h1 ^ (m1 >> 64u128)) ^ (h2 ^ (m2 >> 64u128)) == (h1 ^ h2) ^ ((m1 ^ m2) >> 64u128)) by (bit_vector);
}

pub proof fn lemma_halves_xor(a: u128, b: u128)
    ensures
        lo64(a ^ b) == lo64(a) ^ lo64(b),
        hi64(a ^ b) == hi64(a) ^ hi64(b),
{
    assert((a ^ b) as u64 == (a as u64) ^ (b as u64)) by (bit_vector);
    assert(((a ^ b) >> 64u128) as u64 == ((a >> 64u128) as u64) ^ ((b >> 64u128) as u64)) by (bit_vector);
}

pub proof fn lemma_prod_xor(x1: u128, x2: u128, y: u128)
    ensures
        prod(x1 ^ x2, y) == pxor(prod(x1, y), prod(x2, y)),
{
    lemma_halves_xor(x1, x2);
    lemma_clmul_xor_l(lo64(x1), lo64(x2), lo64(y));
    lemma_clmul_xor_l(lo64(x1), lo64(x2), hi64(y));
    lemma_clmul_xor_l(hi64(x1), hi64(x2), lo64(y));
    lemma_clmul_xor_l(hi64(x1), hi64(x2), hi64(y));
    let a = clmul(lo64(x1), hi64(y));
    let b = clmul(hi64(x1), lo64(y));
    let c = clmul(lo64(x2), hi64(y));
    let d = clmul(hi64(x2), lo64(y));
    assert((a ^ c) ^ (b ^ d) == (a ^ b) ^ (c ^ d)) by (bit_vector);
    lemma_join_xor(
        clmul(lo64(x1), lo64(y)),
        mid(x1, y),
        clmul(hi64(x1), hi64(y)),
        clmul(lo64(x2), lo64(y)),
        mid(x2, y),
        clmul(hi64(x2), hi64(y)),
    );
}

pub proof fn lemma_prod_comm(x: u128, y: u128)
    ensures
        prod(x, y) == prod(y, x),
{
    lemma_clmul_comm(lo64(x), lo64(y));
    lemma_clmul_comm(hi64(x), hi64(y));
    lemma_clmul_comm(lo64(x), hi64(y));
    lemma_clmul_comm(hi64(x), lo64(y));
    let a = clmul(lo64(y), hi64(x));
    let b = clmul(hi64(y), lo64(x));
    assert(a ^ b == b ^ a) by (bit_vector);
}

pub proof fn lemma_prod_zero(y: u128)
    ensures
        prod(0, y) == (0u128, 0u128),
{
    assert(0u128 as u64 == 0 && (0u128 >> 64u128) as u64 == 0) by (bit_vector);
    lemma_clmul_n_zero(lo64(y), 64);
    lemma_clmul_n_zero(hi64(y), 64);
    assert(0u128 ^ 0u128 == 0 && 0u128 ^ (0u128 << 64u128) == 0 && 0u128 ^ (0u128 >> 64u128) == 0) by (bit_vector);
}

/// The 256-bit integer `y << k`, k < 128, as halves.
pub open spec fn shl(y: u128, k: u128) -> (u128, u128) {
    (y << k, if k == 0 {
        0
    } else {
        y >> (128 - k) as u128
    })
}

/// One set bit: the product with `1 << k` is `y << k`.
pub proof fn lemma_prod_bit(k: u128, y: u128)
    requires
        k < 128,
    ensures
        prod(1u128 << k, y) == shl(y, k),
{
    let y0 = lo64(y);
    let y1 = hi64(y);
    lemma_clmul_n_zero(y0, 64);
    lemma_clmul_n_zero(y1, 64);
    if k < 64 {
        let j = k as u64;
        assert((1u128 << k) as u64 == 1u64 << j && ((1u128 << k) >> 64u128) as u64 == 0) by (bit_vector)
            requires
                k < 64,
                j == k as u64,
        ;
        lemma_clmul_n_bit(j, y0, 64);
        lemma_clmul_n_bit(j, y1, 64);
        assert(((y0 as u128) << k) ^ ((((y1 as u128) << k) ^ 0u128) << 64u128) == y << k) by (bit_vector)
            requires
                k < 64,
                y0 == y as u64,
                y1 == (y >> 64u128) as u64,
        ;
        assert(0u128 ^ ((((y1 as u128) << k) ^ 0u128) >> 64u128) == if k == 0 {
            0
        } else {
            y >> (128 - k) as u128
        }) by (bit_vector)
            requires
                k < 64,
                y1 == (y >> 64u128) as u64,
        ;
    } else {
        let j = (k - 64) as u64;
        assert((1u128 << k) as u64 == 0 && ((1u128 << k) >> 64u128) as u64 == 1u64 << j) by (bit_vector)
            requires
                64 <= k < 128,
                j == (k - 64) as u64,
        ;
        lemma_clmul_n_bit(j, y0, 64);
        lemma_clmul_n_bit(j, y1, 64);
        assert(0u128 ^ ((0u128 ^ ((y0 as u128) << (j as u128))) << 64u128) == y << k) by (bit_vector)
            requires
                64 <= k < 128,
                j == (k - 64) as u64,
                y0 == y as u64,
        ;
        assert(((y1 as u128) << (j as u128)) ^ ((0u128 ^ ((y0 as u128) << (j as u128))) >> 64u128) == y >> (128 - k) as u128)
            by (bit_vector)
            requires
                64 <= k < 128,
                j == (k - 64) as u64,
                y0 == y as u64,
                y1 == (y >> 64u128) as u64,
        ;
    }
}

// ---------------------------------------------------------------------------
// The reduction
// ---------------------------------------------------------------------------

/// The field element a 256-bit carry-less product of two blocks stands
/// for. Shifted left by one, the product's high half is the low 128
/// coefficients D_L and its low half the high ones D_H, both as blocks;
/// t^128 = t^7 + t^2 + t + 1 folds D_H in, and the at most 6 coefficients
/// that this pushes past t^127 (the left shifts) are folded in again.
pub open spec fn red(w: (u128, u128)) -> u128 {
    let hi = (w.1 << 1u128) | (w.0 >> 127u128);
    let h = w.0 << 1u128;
    let f = h ^ (h << 127u128) ^ (h << 126u128) ^ (h << 121u128);
    hi ^ f ^ (f >> 1u128) ^ (f >> 2u128) ^ (f >> 7u128)
}

pub proof fn lemma_red_xor(a: (u128, u128), b: (u128, u128))
    ensures
        red(pxor(a, b)) == red(a) ^ red(b),
{
    let (a0, a1) = a;
    let (b0, b1) = b;
    assert({
        let hi = ((a1 ^ b1) << 1u128) | ((a0 ^ b0) >> 127u128);
        let h = (a0 ^ b0) << 1u128;
        let f = h ^ (h << 127u128) ^ (h << 126u128) ^ (h << 121u128);
        hi ^ f ^ (f >> 1u128) ^ (f >> 2u128) ^ (f >> 7u128)
    } == {
        let hi = (a1 << 1u128) | (a0 >> 127u128);
        let h = a0 << 1u128;
        let f = h ^ (h << 127u128) ^ (h << 126u128) ^ (h << 121u128);
        hi ^ f ^ (f >> 1u128) ^ (f >> 2u128) ^ (f >> 7u128)
    } ^ {
        let hi = (b1 << 1u128) | (b0 >> 127u128);
        let h = b0 << 1u128;
        let f = h ^ (h << 127u128) ^ (h << 126u128) ^ (h << 121u128);
        hi ^ f ^ (f >> 1u128) ^ (f >> 2u128) ^ (f >> 7u128)
    }) by (bit_vector);
}

pub proof fn lemma_red_zero()
    ensures
        red((0u128, 0u128)) == 0,
{
    assert({
        let hi = (0u128 << 1u128) | (0u128 >> 127u128);
        let h = 0u128 << 1u128;
        let f = h ^ (h << 127u128) ^ (h << 126u128) ^ (h << 121u128);
        hi ^ f ^ (f >> 1u128) ^ (f >> 2u128) ^ (f >> 7u128)
    } == 0) by (bit_vector);
}

/// Halving the product is multiplying by t: `red(w >> 1)` is
/// `gf_shift(red(w))`, if nothing is shifted out.
pub proof fn lemma_red_shift(lo: u128, hi: u128)
    requires
        lo & 1 == 0,
        hi >> 127u128 == 0,
    ensures
        red(((lo >> 1u128) | (hi << 127u128), hi >> 1u128)) == gf_shift(red((lo, hi))),
{
    let a = red(((lo >> 1u128) | (hi << 127u128), hi >> 1u128));
    let b = red((lo, hi));
    assert(a == {
        let w0 = (lo >> 1u128) | (hi << 127u128);
        let w1 = hi >> 1u128;
        let hh = (w1 << 1u128) | (w0 >> 127u128);
        let h = w0 << 1u128;
        let f = h ^ (h << 127u128) ^ (h << 126u128) ^ (h << 121u128);
        hh ^ f ^ (f >> 1u128) ^ (f >> 2u128) ^ (f >> 7u128)
    });
    assert(b == {
        let hh = (hi << 1u128) | (lo >> 127u128);
        let h = lo << 1u128;
        let f = h ^ (h << 127u128) ^ (h << 126u128) ^ (h << 121u128);
        hh ^ f ^ (f >> 1u128) ^ (f >> 2u128) ^ (f >> 7u128)
    });
    assert(a == if b & 1 == 0 {
        b >> 1u128
    } else {
        (b >> 1u128) ^ (0xe1u128 << 120u128)
    }) by (bit_vector)
        requires
            lo & 1 == 0,
            hi >> 127u128 == 0,
            a == {
                let w0 = (lo >> 1u128) | (hi << 127u128);
                let w1 = hi >> 1u128;
                let hh = (w1 << 1u128) | (w0 >> 127u128);
                let h = w0 << 1u128;
                let f = h ^ (h << 127u128) ^ (h << 126u128) ^ (h << 121u128);
                hh ^ f ^ (f >> 1u128) ^ (f >> 2u128) ^ (f >> 7u128)
            },
            b == {
                let hh = (hi << 1u128) | (lo >> 127u128);
                let h = lo << 1u128;
                let f = h ^ (h << 127u128) ^ (h << 126u128) ^ (h << 121u128);
                hh ^ f ^ (f >> 1u128) ^ (f >> 2u128) ^ (f >> 7u128)
            },
    ;
}

/// V_i of Algorithm 1 is the reduced `y << (127 - i)`.
pub proof fn lemma_v(y: u128, n: nat)
    requires
        n <= 127,
    ensures
        gf_steps(y, y, n).1 == gf_steps(0, y, n).1,
        gf_steps(0, y, n).1 == red(shl(y, (127 - n) as u128)),
    decreases n,
{
    lemma_v_any(y, y, n);
    lemma_v_any(0, y, n);
    if n == 0 {
        assert(red(shl(y, 127)) == y) by {
            assert({
                let w0 = y << 127u128;
                let w1 = y >> 1u128;
                let hh = (w1 << 1u128) | (w0 >> 127u128);
                let h = w0 << 1u128;
                let f = h ^ (h << 127u128) ^ (h << 126u128) ^ (h << 121u128);
                hh ^ f ^ (f >> 1u128) ^ (f >> 2u128) ^ (f >> 7u128)
            } == y) by (bit_vector);
        };
    } else {
        lemma_v(y, (n - 1) as nat);
        let k = (128 - n) as u128;
        let (lo, hi) = shl(y, k);
        assert(lo & 1 == 0 && hi >> 127u128 == 0) by (bit_vector)
            requires
                1 <= k < 128,
                lo == y << k,
                hi == y >> (128 - k) as u128,
        ;
        lemma_red_shift(lo, hi);
        assert(((lo >> 1u128) | (hi << 127u128), hi >> 1u128) == shl(y, (k - 1) as u128)) by {
            assert((y << k) >> 1u128 | ((y >> (128 - k) as u128) << 127u128) == y << (k - 1) as u128) by (bit_vector)
                requires
                    1 <= k < 128,
            ;
            assert((y >> (128 - k) as u128) >> 1u128 == if k - 1 == 0 {
                0
            } else {
                y >> (128 - (k - 1)) as u128
            }) by (bit_vector)
                requires
                    1 <= k < 128,
            ;
        };
    }
}

/// V_n does not depend on X.
pub proof fn lemma_v_any(x: u128, y: u128, n: nat)
    ensures
        gf_steps(x, y, n).1 == gf_steps(0, y, n).1,
    decreases n,
{
    if n > 0 {
        lemma_v_any(x, y, (n - 1) as nat);
    }
}

/// The bits of `x` from 128 - n up: x_0 .. x_{n-1}.
pub open spec fn top(x: u128, n: nat) -> u128 {
    if n == 0 {
        0
    } else if n >= 128 {
        x
    } else {
        (x >> (128 - n) as u128) << (128 - n) as u128
    }
}

/// Algorithm 1 computes the reduced carry-less product.
pub proof fn lemma_steps_prod(x: u128, y: u128, n: nat)
    requires
        n <= 128,
    ensures
        gf_steps(x, y, n).0 == red(prod(top(x, n), y)),
    decreases n,
{
    if n == 0 {
        lemma_prod_zero(y);
        lemma_red_zero();
    } else {
        lemma_steps_prod(x, y, (n - 1) as nat);
        let i = (n - 1) as u128;
        let k = (127 - i) as u128;
        let on = (x >> k) & 1 == 1;
        let e = if on {
            1u128 << k
        } else {
            0u128
        };
        assert(top(x, n) == top(x, (n - 1) as nat) ^ e) by {
            if n == 1 {
                assert((x >> 127u128) << 127u128 == 0u128 ^ (if (x >> 127u128) & 1 == 1 {
                    1u128 << 127u128
                } else {
                    0u128
                })) by (bit_vector);
            } else if n < 128 {
                assert((x >> k) << k == ((x >> (k + 1) as u128) << (k + 1) as u128) ^ (if (x >> k) & 1 == 1 {
                    1u128 << k
                } else {
                    0u128
                })) by (bit_vector)
                    requires
                        1 <= k < 127,
                ;
            } else {
                assert(x == ((x >> 1u128) << 1u128) ^ (if (x >> 0u128) & 1 == 1 {
                    1u128 << 0u128
                } else {
                    0u128
                })) by (bit_vector);
            }
        };
        lemma_prod_xor(top(x, (n - 1) as nat), e, y);
        lemma_red_xor(prod(top(x, (n - 1) as nat), y), prod(e, y));
        lemma_v(y, (n - 1) as nat);
        lemma_v_any(x, y, (n - 1) as nat);
        let z = gf_steps(x, y, (n - 1) as nat).0;
        if on {
            lemma_prod_bit(k, y);
            assert((x >> (127 - i) as u128) & 1 != 0);
        } else {
            lemma_prod_zero(y);
            lemma_red_zero();
            assert(z ^ 0u128 == z) by (bit_vector);
            assert((x >> (127 - i) as u128) & 1 == 0) by (bit_vector)
                requires
                    !((x >> k) & 1 == 1),
                    k == (127 - i) as u128,
            ;
        }
    }
}

/// X • Y is the reduced carry-less product.
pub proof fn lemma_gf_mul_prod(x: u128, y: u128)
    ensures
        gf_mul(x, y) == red(prod(x, y)),
{
    lemma_steps_prod(x, y, 128);
}

// ---------------------------------------------------------------------------
// The algebra
// ---------------------------------------------------------------------------

pub proof fn lemma_gf_comm(x: u128, y: u128)
    ensures
        gf_mul(x, y) == gf_mul(y, x),
{
    lemma_gf_mul_prod(x, y);
    lemma_gf_mul_prod(y, x);
    lemma_prod_comm(x, y);
}

pub proof fn lemma_gf_xor_l(a: u128, b: u128, y: u128)
    ensures
        gf_mul(a ^ b, y) == gf_mul(a, y) ^ gf_mul(b, y),
{
    lemma_gf_mul_prod(a ^ b, y);
    lemma_gf_mul_prod(a, y);
    lemma_gf_mul_prod(b, y);
    lemma_prod_xor(a, b, y);
    lemma_red_xor(prod(a, y), prod(b, y));
}

pub proof fn lemma_gf_xor_r(x: u128, a: u128, b: u128)
    ensures
        gf_mul(x, a ^ b) == gf_mul(x, a) ^ gf_mul(x, b),
{
    lemma_gf_comm(x, a ^ b);
    lemma_gf_comm(x, a);
    lemma_gf_comm(x, b);
    lemma_gf_xor_l(a, b, x);
}

pub proof fn lemma_gf_zero(y: u128)
    ensures
        gf_mul(0, y) == 0,
        gf_mul(y, 0) == 0,
{
    lemma_gf_mul_prod(0, y);
    lemma_prod_zero(y);
    lemma_red_zero();
    lemma_gf_comm(0, y);
}

proof fn lemma_shift_xor(a: u128, b: u128)
    ensures
        gf_shift(a ^ b) == gf_shift(a) ^ gf_shift(b),
        gf_shift(0) == 0,
{
    assert((if (a ^ b) & 1 == 0 {
        (a ^ b) >> 1u128
    } else {
        ((a ^ b) >> 1u128) ^ (0xe1u128 << 120u128)
    }) == (if a & 1 == 0 {
        a >> 1u128
    } else {
        (a >> 1u128) ^ (0xe1u128 << 120u128)
    }) ^ (if b & 1 == 0 {
        b >> 1u128
    } else {
        (b >> 1u128) ^ (0xe1u128 << 120u128)
    })) by (bit_vector);
    assert(0u128 & 1 == 0 && 0u128 >> 1u128 == 0) by (bit_vector);
}

proof fn lemma_steps_shift(x: u128, y: u128, n: nat)
    ensures
        gf_steps(x, gf_shift(y), n).0 == gf_shift(gf_steps(x, y, n).0),
        gf_steps(x, gf_shift(y), n).1 == gf_shift(gf_steps(x, y, n).1),
    decreases n,
{
    lemma_shift_xor(0, 0);
    if n > 0 {
        lemma_steps_shift(x, y, (n - 1) as nat);
        let (z, v) = gf_steps(x, y, (n - 1) as nat);
        lemma_shift_xor(z, v);
    }
}

/// X • (Y t) = (X • Y) t.
pub proof fn lemma_gf_shift_r(x: u128, y: u128)
    ensures
        gf_mul(x, gf_shift(y)) == gf_shift(gf_mul(x, y)),
{
    lemma_steps_shift(x, y, 128);
}

/// (X t) • Y = (X • Y) t.
pub proof fn lemma_gf_shift_l(x: u128, y: u128)
    ensures
        gf_mul(gf_shift(x), y) == gf_shift(gf_mul(x, y)),
{
    lemma_gf_comm(gf_shift(x), y);
    lemma_gf_shift_r(y, x);
    lemma_gf_comm(x, y);
}

proof fn lemma_steps_assoc(a: u128, b: u128, c: u128, n: nat)
    ensures
        gf_steps(a, gf_mul(b, c), n).0 == gf_mul(gf_steps(a, b, n).0, c),
        gf_steps(a, gf_mul(b, c), n).1 == gf_mul(gf_steps(a, b, n).1, c),
    decreases n,
{
    if n == 0 {
        lemma_gf_zero(c);
    } else {
        lemma_steps_assoc(a, b, c, (n - 1) as nat);
        let (z, v) = gf_steps(a, b, (n - 1) as nat);
        lemma_gf_shift_l(v, c);
        lemma_gf_xor_l(z, v, c);
    }
}

/// (A • B) • C = A • (B • C).
pub proof fn lemma_gf_assoc(a: u128, b: u128, c: u128)
    ensures
        gf_mul(gf_mul(a, b), c) == gf_mul(a, gf_mul(b, c)),
{
    lemma_steps_assoc(a, b, c, 128);
}

// ---------------------------------------------------------------------------
// GHASH over many blocks
// ---------------------------------------------------------------------------

/// H^n, n >= 1.
pub open spec fn pow(h: u128, n: nat) -> u128
    decreases n,
{
    if n <= 1 {
        h
    } else {
        gf_mul(pow(h, (n - 1) as nat), h)
    }
}

/// The sum of `xs[i] • H^(k - i)`.
pub open spec fn dsum(h: u128, xs: Seq<u128>, k: nat) -> u128
    decreases xs.len(),
{
    if xs.len() == 0 {
        0
    } else {
        dsum(h, xs.drop_last(), k) ^ gf_mul(xs.last(), pow(h, (k - (xs.len() - 1)) as nat))
    }
}

pub proof fn lemma_ghash_append(h: u128, y: u128, xs: Seq<u128>, ys: Seq<u128>)
    ensures
        ghash_from(h, y, xs + ys) == ghash_from(h, ghash_from(h, y, xs), ys),
    decreases xs.len(),
{
    if xs.len() > 0 {
        assert((xs + ys).drop_first() == xs.drop_first() + ys);
        lemma_ghash_append(h, gf_mul(y ^ xs[0], h), xs.drop_first(), ys);
    } else {
        assert(xs + ys == ys);
    }
}

proof fn lemma_dsum_mul(h: u128, xs: Seq<u128>, k: nat)
    requires
        xs.len() <= k,
    ensures
        gf_mul(dsum(h, xs, k), h) == dsum(h, xs, k + 1),
    decreases xs.len(),
{
    if xs.len() == 0 {
        lemma_gf_zero(h);
    } else {
        lemma_dsum_mul(h, xs.drop_last(), k);
        let m = (k - (xs.len() - 1)) as nat;
        lemma_gf_xor_l(dsum(h, xs.drop_last(), k), gf_mul(xs.last(), pow(h, m)), h);
        lemma_gf_assoc(xs.last(), pow(h, m), h);
        assert((k + 1 - (xs.len() - 1)) as nat == m + 1);
    }
}

/// GHASH is the sum of the blocks times powers of H:
/// GHASH(X_1..X_k) = X_1 H^k + ... + X_k H.
pub proof fn lemma_ghash_dsum(h: u128, xs: Seq<u128>)
    ensures
        ghash(h, xs) == dsum(h, xs, xs.len()),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let n = (xs.len() - 1) as nat;
        let p = xs.drop_last();
        lemma_ghash_dsum(h, p);
        assert(xs == p + seq![xs.last()]);
        let x = xs.last();
        lemma_ghash_append(h, 0, p, seq![x]);
        assert(seq![x].drop_first() =~= Seq::<u128>::empty());
        assert(ghash_from(h, ghash(h, p), seq![x]) == ghash_from(h, gf_mul(ghash(h, p) ^ x, h), Seq::<u128>::empty()));
        assert(ghash(h, xs) == gf_mul(ghash(h, p) ^ x, h));
        lemma_dsum_mul(h, p, n);
        lemma_gf_xor_l(dsum(h, p, n), x, h);
        assert(pow(h, 1) == h);
        assert(dsum(h, xs, xs.len()) == dsum(h, p, n + 1) ^ gf_mul(x, pow(h, 1)));
    }
}

/// Starting from `y` is XORing it into the first block.
pub proof fn lemma_ghash_from_first(h: u128, y: u128, xs: Seq<u128>)
    requires
        xs.len() > 0,
    ensures
        ghash_from(h, y, xs) == ghash(h, xs.update(0, y ^ xs[0])),
{
    let ys = xs.update(0, y ^ xs[0]);
    let x0 = xs[0];
    assert(0u128 ^ (y ^ x0) == y ^ x0) by (bit_vector);
    assert(ys.drop_first() == xs.drop_first());
}

} // verus!

verus! {

/// The XOR of a sequence, left to right.
pub open spec fn xsum(s: Seq<u128>) -> u128
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        xsum(s.drop_last()) ^ s.last()
    }
}

/// Reducing a sum of products is summing the reduced products.
pub proof fn lemma_red_join_sum(ls: Seq<u128>, ms: Seq<u128>, hs: Seq<u128>)
    requires
        ls.len() == ms.len(),
        ms.len() == hs.len(),
    ensures
        red(join(xsum(ls), xsum(ms), xsum(hs))) == xsum(Seq::new(ls.len(), |b: int| red(join(ls[b], ms[b], hs[b])))),
    decreases ls.len(),
{
    let n = ls.len();
    let f = Seq::new(n, |b: int| red(join(ls[b], ms[b], hs[b])));
    if n == 0 {
        assert(0u128 ^ (0u128 << 64u128) == 0 && 0u128 ^ (0u128 >> 64u128) == 0) by (bit_vector);
        lemma_red_zero();
    } else {
        let (l1, m1, h1) = (ls.drop_last(), ms.drop_last(), hs.drop_last());
        lemma_red_join_sum(l1, m1, h1);
        assert(f.drop_last() =~= Seq::new(l1.len(), |b: int| red(join(l1[b], m1[b], h1[b]))));
        lemma_join_xor(xsum(l1), xsum(m1), xsum(h1), ls.last(), ms.last(), hs.last());
        lemma_red_xor(join(xsum(l1), xsum(m1), xsum(h1)), join(ls.last(), ms.last(), hs.last()));
    }
}

/// `dsum` is the XOR of the products.
pub proof fn lemma_dsum_xsum(h: u128, ys: Seq<u128>, k: nat)
    ensures
        dsum(h, ys, k) == xsum(Seq::new(ys.len(), |b: int| gf_mul(ys[b], pow(h, (k - b) as nat)))),
    decreases ys.len(),
{
    let f = Seq::new(ys.len(), |b: int| gf_mul(ys[b], pow(h, (k - b) as nat)));
    if ys.len() > 0 {
        let p = ys.drop_last();
        lemma_dsum_xsum(h, p, k);
        assert(f.drop_last() =~= Seq::new(p.len(), |b: int| gf_mul(p[b], pow(h, (k - b) as nat))));
    }
}

} // verus!

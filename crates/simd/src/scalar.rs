//! Scalar bit instructions, proven from vstd's specification of
//! `count_ones`.
use crate::ops::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2_unfold, pow2};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::std_specs::bits::nat_count_ones;

verus! {

/// One step of `nat_count_ones`, also below 2.
proof fn lemma_count_step(n: nat)
    ensures
        nat_count_ones(n) == n % 2 + nat_count_ones(n / 2),
{
    if n < 2 {
        assert(n / 2 == 0);
        assert(nat_count_ones(0) == 0);
    }
}

/// Adding a top bit `b` above `x < 2^k` adds `b` to the count.
proof fn lemma_count_top(x: nat, b: nat, k: nat)
    requires
        x < pow2(k),
        b <= 1,
    ensures
        nat_count_ones(x + b * pow2(k)) == nat_count_ones(x) + b,
    decreases k,
{
    if k == 0 {
        lemma2_to64();
        assert(x == 0);
        assert(nat_count_ones(0) == 0);
        assert(nat_count_ones(b) == b);
    } else {
        lemma_pow2_unfold(k);
        let p = pow2((k - 1) as nat);
        let y = x + b * pow2(k);
        assert(b * pow2(k) == 2 * (b * p)) by (nonlinear_arith)
            requires
                pow2(k) == 2 * p,
        ;
        assert(y % 2 == x % 2 && y / 2 == x / 2 + b * p) by (nonlinear_arith)
            requires
                y == x + 2 * (b * p),
        ;
        assert(x / 2 < p) by (nonlinear_arith)
            requires
                x < 2 * p,
        ;
        lemma_count_top(x / 2, b, (k - 1) as nat);
        lemma_count_step(y);
        lemma_count_step(x);
    }
}

/// The set bits of `m` below `n` are as many as the ones of `m mod 2^n`.
proof fn lemma_set_bits_count(m: u64, n: nat)
    requires
        n <= 64,
    ensures
        set_bits(m, n).len() == nat_count_ones((m as nat) % pow2(n)),
    decreases n,
{
    lemma2_to64();
    if n > 0 {
        lemma_set_bits_count(m, (n - 1) as nat);
        let k = (n - 1) as nat;
        lemma_pow2_unfold(n);
        let p = pow2(k);
        vstd::arithmetic::power2::lemma_pow2_pos(k);
        let x = (m as nat) % p;
        let b = ((m as nat) / p) % 2;
        vstd::bits::lemma_u64_shr_is_div(m, k as u64);
        let sh = m >> (k as u64);
        assert(sh & 1u64 == sh % 2) by (bit_vector);
        assert((m as nat) % pow2(n) == x + b * p) by {
            vstd::arithmetic::div_mod::lemma_mod_breakdown(m as int, p as int, 2);
            assert(pow2(n) == p * 2);
        }
        assert(x < p) by {
            vstd::arithmetic::div_mod::lemma_mod_bound(m as int, p as int);
        }
        lemma_count_top(x, b, k);
    }
}

proof fn lemma_set_bits_le(m: u64, n: nat)
    ensures
        set_bits(m, n).len() <= n,
    decreases n,
{
    if n > 0 {
        lemma_set_bits_le(m, (n - 1) as nat);
    }
}

/// `popcnt`: the number of set bits. (`u64::count_ones` is the `popcnt`
/// instruction where the CPU has it and a software count elsewhere, so
/// this needs no CPU feature.) Proven from vstd's specification of
/// `count_ones`; `tests/ext.rs` still checks it against
/// `refs::ref_popcount64`.
#[inline(always)]
pub fn popcnt64(m: u64) -> (r: u32)
    ensures
        r == popcount64(m),
        r <= 64,
{
    let r = m.count_ones();
    proof {
        lemma_set_bits_count(m, 64);
        lemma2_to64();
        assert(pow2(64) == 0x1_0000_0000_0000_0000);
        assert((m as nat) % pow2(64) == m as nat);
        broadcast use vstd::std_specs::bits::axiom_u64_count_ones;
        lemma_set_bits_le(m, 64);
    }
    r
}

} // verus!

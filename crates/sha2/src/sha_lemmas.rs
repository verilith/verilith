//! Lemmas shared by the SHA instruction kernels ([`crate::shani`],
//! [`crate::armv8`]): sums modulo 2^32 and 2^64 in other orders, and the
//! rounds and schedule of FIPS 180-4 unfolded a step.
use crate::spec::{self, Vars};
use crate::spec512;
use vstd::prelude::*;

verus! {

pub spec const M32: int = 0x1_0000_0000int;

pub proof fn lemma_mod_add(x: int, y: int)
    requires
        0 <= x,
        0 <= y,
    ensures
        ((x % M32) + y) % M32 == (x + y) % M32,
        (x + (y % M32)) % M32 == (x + y) % M32,
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop(x, y, M32);
    vstd::arithmetic::div_mod::lemma_mod_twice(x, M32);
    vstd::arithmetic::div_mod::lemma_mod_twice(y, M32);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(x % M32, y, M32);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(x, y % M32, M32);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(x, M32);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(y, M32);
}

/// The pseudocode's `+` ([`crate::isa::add32`]) is FIPS 180-4's.
pub proof fn lemma_add32_eq(x: u32, y: u32)
    ensures
        crate::isa::add32(x, y) == spec::add(x, y),
{
}

/// A round moves a, b, c to b, c, d and e, f, g to f, g, h.
pub proof fn lemma_round_shift(v: Vars, k: u32, w: u32)
    ensures
        spec::round(v, k, w).b == v.a,
        spec::round(v, k, w).c == v.b,
        spec::round(v, k, w).d == v.c,
        spec::round(v, k, w).f == v.e,
        spec::round(v, k, w).g == v.f,
        spec::round(v, k, w).h == v.g,
{
    hide(spec::add);
    hide(spec::ch);
    hide(spec::maj);
    hide(spec::big_sigma0);
    hide(spec::big_sigma1);
}

/// W_t to W_{t+3} of `m`.
pub open spec fn sched4(m: Seq<u32>, t: int) -> Seq<u32> {
    seq![spec::schedule(m, t), spec::schedule(m, t + 1), spec::schedule(m, t + 2), spec::schedule(m, t + 3)]
}

/// W_{t+16} to W_{t+19} by their definition.
pub proof fn lemma_sched_unfold(m: Seq<u32>, t: int)
    requires
        0 <= t,
    ensures
        spec::schedule(m, t + 16) == spec::add(spec::add(spec::add(spec::small_sigma1(spec::schedule(m, t + 14)), spec::schedule(m, t + 9)), spec::small_sigma0(spec::schedule(m, t + 1))), spec::schedule(m, t)),
        spec::schedule(m, t + 17) == spec::add(spec::add(spec::add(spec::small_sigma1(spec::schedule(m, t + 15)), spec::schedule(m, t + 10)), spec::small_sigma0(spec::schedule(m, t + 2))), spec::schedule(m, t + 1)),
        spec::schedule(m, t + 18) == spec::add(spec::add(spec::add(spec::small_sigma1(spec::schedule(m, t + 16)), spec::schedule(m, t + 11)), spec::small_sigma0(spec::schedule(m, t + 3))), spec::schedule(m, t + 2)),
        spec::schedule(m, t + 19) == spec::add(spec::add(spec::add(spec::small_sigma1(spec::schedule(m, t + 17)), spec::schedule(m, t + 12)), spec::small_sigma0(spec::schedule(m, t + 4))), spec::schedule(m, t + 3)),
{
    hide(spec::add);
    hide(spec::small_sigma0);
    hide(spec::small_sigma1);
}

} // verus!

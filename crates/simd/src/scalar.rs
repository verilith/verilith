//! Scalar bit instructions (TRUSTED).
use crate::ops::*;
use vstd::prelude::*;

verus! {

/// `popcnt`: the number of set bits. (`u64::count_ones` is the `popcnt`
/// instruction where the CPU has it and a software count elsewhere, so
/// this needs no CPU feature.) `tests/ext.rs` checks it against
/// `refs::ref_popcount64`.
#[verifier::external_body]
#[inline(always)]
pub fn popcnt64(m: u64) -> (r: u32)
    ensures
        r == popcount64(m),
        r <= 64,
{
    m.count_ones()
}

} // verus!

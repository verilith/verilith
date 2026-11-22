//! The spec's little-endian numbers and verilith-core's.
#[cfg(verus_only)]
use crate::spec::le;
#[cfg(verus_only)]
use verilith_core::prims::le_bytes;
use vstd::prelude::*;

verus! {

/// The spec's `le` is verilith-core's `le_bytes`, the value its loads are
/// specified with.
pub proof fn lemma_le_is(b: Seq<u8>, i: int, n: nat)
    ensures
        le(b, i, n) == le_bytes(b, i, n),
    decreases n,
{
    if n > 0 {
        lemma_le_is(b, i + 1, (n - 1) as nat);
    }
}

} // verus!

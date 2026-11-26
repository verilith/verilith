//! What the byte dot-product instructions compute (`vpdpbusd`,
//! `vpmaddubsw`/`vpmaddwd`, `udot`), as spec functions on every target.
//! The wrappers are in `vdot` (x86-64) and `vudot` (AArch64).
use vstd::prelude::*;

verus! {

/// The dot product of lane `j`'s four bytes of `x` and `w`.
pub open spec fn dot4(x: Seq<u8>, w: Seq<u8>, j: int) -> nat {
    (x[4 * j] as nat) * (w[4 * j] as nat) + (x[4 * j + 1] as nat) * (w[4 * j + 1] as nat) + (x[4 * j
        + 2] as nat) * (w[4 * j + 2] as nat) + (x[4 * j + 3] as nat) * (w[4 * j + 3] as nat)
}

/// `a + b` in a 32-bit lane, wrapping (what the vector adds compute).
pub open spec fn add32(a: int, b: int) -> u32 {
    ((a + b) % 0x1_0000_0000) as u32
}

} // verus!

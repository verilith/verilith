//! The decoder's step counter, for the work bound (`top::decode_counted`).
use vstd::prelude::*;

verus! {

/// Steps taken so far: ghost state, erased at compile time. Each loop turn
/// adds at least one, and a copy, fill or zeroed allocation of `n` bytes
/// adds `n`.
pub tracked struct Meter {
    /// The count.
    pub ghost n: nat,
}

} // verus!

//! The decoder's step counter, for the work bound (`decode::decode_counted`).
use vstd::prelude::*;

verus! {

/// Steps taken so far: ghost state, erased at compile time. Each loop turn
/// adds at least one, and a copy, fill or zeroed allocation of `n` bytes
/// adds `n`.
pub tracked struct Meter {
    /// The count.
    pub ghost n: nat,
}

/// The unit of the work done reading the IFD of a file of `len` bytes: a
/// walk over its entries, or over the values of one field, costs at most
/// this.
pub open spec fn unit(len: nat) -> nat {
    len + 4
}

} // verus!

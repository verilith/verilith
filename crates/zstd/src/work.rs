//! The step meter for the decoder's work bounds.
//!
//! A step is one turn of a loop, or one byte moved by a library copy
//! (`extend_from_slice`, `resize`, a `Tail` append, a trusted copy in
//! `prims`), or one byte fed to the checksum. Every loop of the one-shot
//! decoder (with or without a dictionary) ticks the meter once per turn,
//! however small its bound; the streaming decoder is not metered. The
//! meter is ghost state: it is erased at compile time and costs nothing.
use vstd::prelude::*;

verus! {

/// A ghost count of the steps taken so far.
pub tracked struct Meter {
    pub ghost n: nat,
}

} // verus!

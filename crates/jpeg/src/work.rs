//! The decoder's step counter, for the work bound (`decode::decode_counted`).
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// Steps taken so far: ghost state, erased at compile time. Each turn of a
/// loop whose length depends on the input adds at least one, and a zeroed
/// allocation of `n` elements adds `n`. Loops with a bound fixed by the
/// format (the 64 coefficients of a block, the 16 code lengths of a
/// Huffman table, the eight rows of an inverse DCT) count as part of the
/// turn of the loop that runs them.
pub tracked struct Meter {
    /// The count.
    pub ghost n: nat,
}

/// The 8x8 blocks a frame's coefficients are stored in: whole MCUs of
/// each component.
pub open spec fn fblk(f: Frame) -> int {
    if f.nc == 1 {
        cw(f, 0) * ch(f, 0)
    } else {
        cw(f, 0) * ch(f, 0) + cw(f, 1) * ch(f, 1) + cw(f, 2) * ch(f, 2)
    }
}

/// The blocks component `c` of a frame is stored in (hidden, so that the
/// product stays out of the solver's way where it is not needed).
#[verifier::opaque]
pub open spec fn cblk(f: Frame, c: int) -> int {
    cw(f, c) * ch(f, c)
}

/// The pixels of a frame.
pub open spec fn npx(f: Frame) -> int {
    f.w * f.h
}

/// The most work rendering a frame does.
pub open spec fn render_cost(f: Frame) -> int {
    66 * fblk(f) + 110 * npx(f) + 8
}

/// The most work one scan of a frame of `b` blocks does beyond four steps
/// per byte of the file, its first allocation included.
pub open spec fn scan_cost(b: int) -> int {
    300 * b + 10
}

} // verus!

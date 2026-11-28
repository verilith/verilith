//! The specification of smart gravity's choice, as libvips's
//! `vips_smartcrop` makes it from its attention map: the first pixel, in
//! reading order, with the highest value (`vips_max`, which keeps the
//! first of equal maxima), and the crop centred on that point and kept
//! inside the image (`VIPS_CLIP(0, x - width / 2, in->Xsize - width)`).
//! Part of the trusted base with `spec.rs`.
//!
//! The map is single-precision floats, given by their bits; `fkey` orders
//! the bits as the floats are ordered (the map has no NaNs; minus zero
//! is zero).
use vstd::prelude::*;

verus! {

/// The bits of a float as an integer in the float's order.
pub open spec fn fkey(b: u32) -> int {
    if b == 0x8000_0000 {
        0x8000_0000
    } else if b > 0x8000_0000 {
        0xFFFF_FFFF - b
    } else {
        b + 0x8000_0000
    }
}

/// The first of the first `n` values with the highest key.
pub open spec fn first_max(v: Seq<u32>, n: int) -> int
    decreases n,
{
    if n <= 1 {
        0
    } else {
        let b = first_max(v, n - 1);
        if fkey(v[n - 1]) > fkey(v[b]) {
            n - 1
        } else {
            b
        }
    }
}

/// Where a crop `c` long starts on a side `s` long, centred on `a`.
pub open spec fn centred(a: int, s: int, c: int) -> int {
    let t = a - c / 2;
    let hi = s - c;
    if t > hi {
        if hi < 0 {
            0
        } else {
            hi
        }
    } else if t < 0 {
        0
    } else {
        t
    }
}

} // verus!

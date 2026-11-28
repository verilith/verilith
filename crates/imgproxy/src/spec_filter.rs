//! The specification of `blur` and `sharpen`: a separable convolution with
//! a table of non-negative weights (a sampled Gaussian), rows then
//! columns, edges repeated, normalized by the weights' sum, 8 bits of
//! fraction kept between the passes (as `spec_lanczos`'s resampler, whose
//! `kc`, `kdiv` and `kunit` it reuses); and an unsharp mask. Part of the
//! trusted base with `spec.rs`.
//!
//! The table `g` has an odd length `2r + 1`: `g[r + k]` weighs the sample
//! `k` away. Which table (which sigma) is the caller's choice; the
//! values decide only how the image looks.
use crate::spec::*;
use crate::spec_lanczos::*;
use vstd::prelude::*;

verus! {

/// The table's radius.
pub open spec fn gr(g: Seq<int>) -> int {
    (g.len() - 1) / 2
}

/// `sum(g[k] * v(kc(x + k - r)))` over the first `t` entries.
pub open spec fn gsum(v: spec_fn(int) -> int, g: Seq<int>, x: int, s: int, t: int) -> int
    decreases t,
{
    if t <= 0 {
        0
    } else {
        gsum(v, g, x, s, t - 1) + g[t - 1] * v(kc(x + (t - 1) - gr(g), s))
    }
}

/// The sum of the weights.
pub open spec fn gtot(g: Seq<int>) -> int {
    gsum(kunit(), g, 0, 1, g.len() as int)
}

/// The row pass: channel `c` of pixel `(x, y)` of `src` (`w` wide)
/// convolved along the row, times 256.
pub open spec fn ghpx(g: Seq<int>, src: Seq<u8>, w: int, y: int, x: int, c: int) -> int {
    kdiv(gsum(src_line(src, w, y, c), g, x, w, g.len() as int), gtot(g), 256)
}

/// Column `x`, channel `c` of the row pass, as a function of y.
pub open spec fn gmid_line(g: Seq<int>, src: Seq<u8>, w: int, x: int, c: int) -> spec_fn(int) -> int {
    |j: int| ghpx(g, src, w, j, x, c)
}

/// Channel `c` of pixel `(x, y)` blurred.
pub open spec fn gopx(g: Seq<int>, src: Seq<u8>, w: int, h: int, y: int, x: int, c: int) -> u8 {
    kdiv(gsum(gmid_line(g, src, w, x, c), g, y, h, g.len() as int), 256 * gtot(g), 1) as u8
}

/// `src` (`w` by `h` RGBA pixels) blurred with `g`, every channel.
pub open spec fn blur(g: Seq<int>, src: Seq<u8>, w: int, h: int) -> Seq<u8> {
    Seq::new((w * h * NC) as nat, |k: int| gopx(g, src, w, h, (k / NC) / w, (k / NC) % w, k % NC))
}

/// An unsharp mask: each colour channel moved away from its blurred value
/// by as much again (`2 * v - blurred`, clamped); alpha is kept.
pub open spec fn sharpen(g: Seq<int>, src: Seq<u8>, w: int, h: int) -> Seq<u8> {
    let b = blur(g, src, w, h);
    Seq::new(
        (w * h * NC) as nat,
        |k: int|
            if k % NC == 3 {
                src[k]
            } else {
                let v = 2 * src[k] - b[k];
                (if v < 0 {
                    0
                } else if v > 255 {
                    255
                } else {
                    v
                }) as u8
            },
    )
}

} // verus!

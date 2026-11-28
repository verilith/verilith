//! The specification: what a resize, a crop and the size computation
//! return, as total functions over `Seq<u8>` and integers. Together with
//! `verilith_png::spec` (for the encoder's theorem) and the decoders' own
//! specifications, this file is the trusted base of the image pipeline:
//! review it, not the code.
//!
//! Images are 8-bit RGBA, row by row, 4 bytes per pixel: pixel `(x, y)`'s
//! channel `c` of a `w`-pixel-wide image is byte `(y * w + x) * 4 + c`.
use vstd::prelude::*;

verus! {

/// Channels per pixel.
pub spec const NC: int = 4;

/// The largest width or height the pipeline handles (also JPEG's and
/// WebP's limit).
pub spec const MAX_DIM: int = 65535;

// ---------------------------------------------------------------------------
// Area-average resampling, one dimension
// ---------------------------------------------------------------------------
//
// Resampling `s` source samples to `d` output samples lays both on one line
// of length `s * d`: source sample `i` covers `[i * d, (i + 1) * d)` and
// output sample `x` covers `[x * s, (x + 1) * s)`. The output is the
// average of the source over its cell, each source sample weighted by how
// much of the cell it covers. This is a box (area) filter: exact for
// downscaling, pixel replication with blended edges for upscaling.

/// How much of output cell `x` source cell `i` covers.
pub open spec fn ov(x: int, i: int, s: int, d: int) -> int {
    let a = if x * s > i * d { x * s } else { i * d };
    let b = if (x + 1) * s < (i + 1) * d { (x + 1) * s } else { (i + 1) * d };
    if b > a { b - a } else { 0 }
}

/// The first source sample output cell `x` overlaps.
pub open spec fn lo(x: int, s: int, d: int) -> int {
    x * s / d
}

/// One past the last source sample output cell `x` overlaps.
pub open spec fn hi(x: int, s: int, d: int) -> int {
    ((x + 1) * s + d - 1) / d
}

/// `sum(ov(x, i) * v(i))` over source samples `lo(x)` to `k - 1`.
pub open spec fn acc(v: spec_fn(int) -> int, x: int, s: int, d: int, k: int) -> int
    decreases k - lo(x, s, d),
{
    if k <= lo(x, s, d) {
        0
    } else {
        acc(v, x, s, d, k - 1) + ov(x, k - 1, s, d) * v(k - 1)
    }
}

// ---------------------------------------------------------------------------
// Two-dimensional resize
// ---------------------------------------------------------------------------
//
// Rows first, then columns. The row pass keeps 8 bits of fraction (a
// value of at most 255 * 256); the column pass rounds to 8 bits. Both
// round to nearest.

/// Channel `c` of row `y` of a `sw`-wide image, as a function of x.
pub open spec fn src_line(src: Seq<u8>, sw: int, y: int, c: int) -> spec_fn(int) -> int {
    |i: int| src[(y * sw + i) * NC + c] as int
}

/// The row pass: channel `c` of pixel `(x, y)` of the image `src`
/// (`sw` wide) resampled to `dw` wide, times 256.
pub open spec fn hpx(src: Seq<u8>, sw: int, dw: int, y: int, x: int, c: int) -> int {
    (acc(src_line(src, sw, y, c), x, sw, dw, hi(x, sw, dw)) * 256 + sw / 2) / sw
}

/// Column `x`, channel `c` of the row pass's result, as a function of y.
pub open spec fn mid_line(src: Seq<u8>, sw: int, dw: int, x: int, c: int) -> spec_fn(int) -> int {
    |j: int| hpx(src, sw, dw, j, x, c)
}

/// Channel `c` of pixel `(x, y)` of `src` (`sw` by `sh`) resized to `dw`
/// by `dh`.
pub open spec fn opx(src: Seq<u8>, sw: int, sh: int, dw: int, dh: int, y: int, x: int, c: int) -> u8 {
    ((acc(mid_line(src, sw, dw, x, c), y, sh, dh, hi(y, sh, dh)) + 128 * sh) / (256 * sh)) as u8
}

/// `src` (`sw` by `sh` pixels) resized to `dw` by `dh`.
pub open spec fn resize(src: Seq<u8>, sw: int, sh: int, dw: int, dh: int) -> Seq<u8> {
    Seq::new(
        (dw * dh * NC) as nat,
        |k: int| opx(src, sw, sh, dw, dh, (k / NC) / dw, (k / NC) % dw, k % NC),
    )
}

// ---------------------------------------------------------------------------
// Crop
// ---------------------------------------------------------------------------

/// The `cw` by `ch` rectangle of `src` (`sw` wide) whose top left pixel is
/// `(x0, y0)`.
pub open spec fn crop(src: Seq<u8>, sw: int, x0: int, y0: int, cw: int, ch: int) -> Seq<u8> {
    Seq::new(
        (cw * ch * NC) as nat,
        |k: int| src[((y0 + (k / NC) / cw) * sw + x0 + (k / NC) % cw) * NC + k % NC],
    )
}

} // verus!

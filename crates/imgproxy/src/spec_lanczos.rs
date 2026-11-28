//! The specification of kernel resampling (Lanczos 3 by default, as
//! imgproxy and libvips resize with), as total functions over `Seq<u8>`
//! and integers. Part of the trusted base with `spec.rs`, whose image
//! layout, row lines (`src_line`) and area-average `resize` it reuses.
//!
//! The kernel is a table `kt` of fixed-point weights (`KONE` is 1.0):
//! `kt[j]` is the kernel at distance `j / 256` from the centre, for
//! distances below `kt.len() / 256`, and the kernel is 0 beyond. The
//! proofs hold for every table; which table is used (a Lanczos window, a
//! cubic, a triangle) is the caller's choice, and the values only decide
//! the image's look, not the code's correctness.
//!
//! Resampling `s` samples to `d` puts source sample `i`'s centre at
//! `(i + 1/2) / s` and output sample `x`'s at `(x + 1/2) / d` of the
//! line. Output `x` is the weighted average of the source samples near
//! it, each weighted by the kernel at its distance, measured in source
//! samples when upscaling and in output samples when downscaling (the
//! kernel is stretched by `s / d` then, so that it averages enough
//! samples). Samples past the edge repeat the edge sample. The weights
//! are normalized by their sum, as libvips does.
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// Table entries per unit of distance.
pub spec const KSTEP: int = 256;

/// The fixed-point 1.0 of the table's weights.
pub spec const KONE: int = 16384;

/// The kernel's support, in units: the table's length over 256, rounded up.
pub open spec fn ka(kt: Seq<int>) -> int {
    (kt.len() as int + 255) / 256
}

/// Twice the longer of the two lengths: `knum / kd` is a distance in
/// samples of the shorter line (see `kw`).
pub open spec fn kd(s: int, d: int) -> int {
    2 * if s > d { s } else { d }
}

/// `2 * s * d` times the signed distance between source sample `i`'s
/// centre and output sample `x`'s, as fractions of the line.
pub open spec fn knum(x: int, i: int, s: int, d: int) -> int {
    (2 * i + 1) * d - (2 * x + 1) * s
}

/// The weight of source sample `i` in output sample `x`: the table at the
/// distance `|knum| / kd` (in source samples when upscaling, in output
/// samples when downscaling), rounded to the nearest 1/256.
pub open spec fn kw(kt: Seq<int>, x: int, i: int, s: int, d: int) -> int {
    let n = knum(x, i, s, d);
    let a = if n < 0 { -n } else { n };
    let j = (a * KSTEP + kd(s, d) / 2) / kd(s, d);
    if j < kt.len() {
        kt[j]
    } else {
        0
    }
}

/// The first source sample output `x` could weigh: the sample whose centre
/// is `ka` units before `x`'s, rounded down.
pub open spec fn klo(kt: Seq<int>, x: int, s: int, d: int) -> int {
    ((2 * x + 1) * s - ka(kt) * kd(s, d)) / (2 * d)
}

/// How many source samples, from `klo` on, every output sample is summed
/// over (more than its support can reach; `lemma_kw_outside` in
/// `lanczos.rs` proves the samples outside them weigh 0).
pub open spec fn ktaps(kt: Seq<int>, s: int, d: int) -> int {
    ka(kt) * kd(s, d) / d + 2
}

/// Source sample `i`, repeating the edge samples past the edges.
pub open spec fn kc(i: int, s: int) -> int {
    if i < 0 {
        0
    } else if i >= s {
        s - 1
    } else {
        i
    }
}

/// `sum(kw(x, i) * v(kc(i)))` over the first `t` samples from `klo(x)`.
pub open spec fn ksum(v: spec_fn(int) -> int, kt: Seq<int>, x: int, s: int, d: int, t: int) -> int
    decreases t,
{
    if t <= 0 {
        0
    } else {
        let i = klo(kt, x, s, d) + t - 1;
        ksum(v, kt, x, s, d, t - 1) + kw(kt, x, i, s, d) * v(kc(i, s))
    }
}

/// 1 everywhere.
pub open spec fn kunit() -> spec_fn(int) -> int {
    |i: int| 1int
}

/// The sum of output `x`'s weights.
pub open spec fn kwsum(kt: Seq<int>, x: int, s: int, d: int) -> int {
    ksum(kunit(), kt, x, s, d, ktaps(kt, s, d))
}

/// `scale * n / w` rounded to nearest (halves up), clamped to
/// `[0, 255 * scale]`; 0 if the weights do not add up to more than 0.
pub open spec fn kdiv(n: int, w: int, scale: int) -> int {
    if w <= 0 {
        0
    } else {
        let q = (2 * scale * n + w) / (2 * w);
        if q < 0 {
            0
        } else if q > 255 * scale {
            255 * scale
        } else {
            q
        }
    }
}

// ---------------------------------------------------------------------------
// Two-dimensional kernel resize: rows first, then columns. The row pass
// keeps 8 bits of fraction (at most 255 * 256), the column pass rounds to
// 8 bits; each clamps (a Lanczos kernel overshoots near edges).
// ---------------------------------------------------------------------------

/// The row pass: channel `c` of pixel `(x, y)` of `src` (`sw` wide)
/// resampled to `dw` wide, times 256.
pub open spec fn khpx(kt: Seq<int>, src: Seq<u8>, sw: int, dw: int, y: int, x: int, c: int) -> int {
    kdiv(ksum(src_line(src, sw, y, c), kt, x, sw, dw, ktaps(kt, sw, dw)), kwsum(kt, x, sw, dw), 256)
}

/// Column `x`, channel `c` of the row pass's result, as a function of y.
pub open spec fn kmid_line(kt: Seq<int>, src: Seq<u8>, sw: int, dw: int, x: int, c: int) -> spec_fn(int) -> int {
    |j: int| khpx(kt, src, sw, dw, j, x, c)
}

/// Channel `c` of pixel `(x, y)` of `src` (`sw` by `sh`) resampled to `dw`
/// by `dh`.
pub open spec fn kopx(kt: Seq<int>, src: Seq<u8>, sw: int, sh: int, dw: int, dh: int, y: int, x: int, c: int) -> u8 {
    kdiv(ksum(kmid_line(kt, src, sw, dw, x, c), kt, y, sh, dh, ktaps(kt, sh, dh)), 256 * kwsum(kt, y, sh, dh), 1) as u8
}

/// `src` (`sw` by `sh` pixels) resampled with the kernel `kt` to `dw` by `dh`.
pub open spec fn kresize(kt: Seq<int>, src: Seq<u8>, sw: int, sh: int, dw: int, dh: int) -> Seq<u8> {
    Seq::new(
        (dw * dh * NC) as nat,
        |k: int| kopx(kt, src, sw, sh, dw, dh, (k / NC) / dw, (k / NC) % dw, k % NC),
    )
}

// ---------------------------------------------------------------------------
// The thumbnailer: libvips's `vips_resize` shrinks by a whole factor with a
// box filter first, so that the kernel works on at most about four source
// samples per output sample, then resamples with the kernel.
// ---------------------------------------------------------------------------

/// The whole factor `s` is box-shrunk by before resampling to `d`: half
/// the ratio, rounded down, and at least 1.
pub open spec fn kshrink(s: int, d: int) -> int {
    if s >= 4 * d {
        s / (2 * d)
    } else {
        1
    }
}

/// The length after the box shrink.
pub open spec fn kpre(s: int, d: int) -> int {
    (s + kshrink(s, d) - 1) / kshrink(s, d)
}

/// `src` (`sw` by `sh`) thumbnailed to `dw` by `dh`: area-averaged to
/// `kpre` of each length (when that is smaller), then resampled with `kt`.
pub open spec fn thumb(kt: Seq<int>, src: Seq<u8>, sw: int, sh: int, dw: int, dh: int) -> Seq<u8> {
    let mw = kpre(sw, dw);
    let mh = kpre(sh, dh);
    if mw == sw && mh == sh {
        kresize(kt, src, sw, sh, dw, dh)
    } else {
        kresize(kt, resize(src, sw, sh, mw, mh), mw, mh, dw, dh)
    }
}

} // verus!

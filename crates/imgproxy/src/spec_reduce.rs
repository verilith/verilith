//! The specification of libvips's `vips_resize` reduction on 8-bit RGBA
//! (`resample/reducev.cpp`, `reduceh.cpp`, `shrinkv.c`, `shrinkh.c`):
//! each pass is a box pre-shrink by a whole factor (`vips_shrinkv` /
//! `vips_shrinkh` with `ceil`: the edge copied out to whole blocks, each
//! block averaged as libvips rounds it), then a reduction where output
//! sample `o` is `sum(m[t[o] * n + i] * v(st[o] + i))` over `n` taps,
//! edges repeated (`VIPS_EXTEND_COPY`), rounded as libvips's fixed point
//! (`(sum + 2048) >> 12`, clipped to 8 bits). Where each output sample
//! starts (`st`), which of the 65 sub-pixel masks it takes (`t`) and the
//! masks themselves (`m`, `short`s scaled by 4096) are the caller's
//! choice, made as libvips makes them. Part of the trusted base with
//! `spec.rs`.
use crate::spec::*;
use crate::spec_filter::*;
use crate::spec_lanczos::*;
use vstd::prelude::*;

verus! {

/// `sum(m[b + i] * v(kc(st + i)))` over the first `n` taps.
pub open spec fn tsum(v: spec_fn(int) -> int, m: Seq<i16>, b: int, st: int, s: int, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        tsum(v, m, b, st, s, n - 1) + m[b + n - 1] as int * v(kc(st + n - 1, s))
    }
}

/// libvips's rounding of a fixed-point sum to 8 bits
/// (`unsigned_fixed_round`, then `VIPS_CLIP(0, sum, 255)`).
pub open spec fn fround(sum: int) -> int {
    let q = (sum + 2048) / 4096;
    if q < 0 {
        0
    } else if q > 255 {
        255
    } else {
        q
    }
}

/// Column `x`, channel `c` of `src` (`w` wide), as a function of y.
pub open spec fn col_line(src: Seq<u8>, w: int, x: int, c: int) -> spec_fn(int) -> int {
    |j: int| src[(j * w + x) * NC + c] as int
}

/// `vips_reducev`'s reduction: `src` (`w` by `h`) to `oh` rows.
pub open spec fn reducev(src: Seq<u8>, w: int, h: int, n: int, m: Seq<i16>, st: Seq<i64>, t: Seq<u8>, oh: int) -> Seq<u8> {
    Seq::new(
        (w * oh * NC) as nat,
        |k: int|
            {
                let o = (k / NC) / w;
                fround(tsum(col_line(src, w, (k / NC) % w, k % NC), m, t[o] as int * n, st[o] as int, h, n)) as u8
            },
    )
}

/// `vips_reduceh`'s reduction: `src` (`w` by `h`) to `ow` columns.
pub open spec fn reduceh(src: Seq<u8>, w: int, h: int, n: int, m: Seq<i16>, st: Seq<i64>, t: Seq<u8>, ow: int) -> Seq<u8> {
    Seq::new(
        (ow * h * NC) as nat,
        |k: int|
            {
                let o = (k / NC) % ow;
                fround(tsum(src_line(src, w, (k / NC) / ow, k % NC), m, t[o] as int * n, st[o] as int, w, n)) as u8
            },
    )
}

/// `sum(v(kc(st + i)))` over the first `n` samples.
pub open spec fn bsum(v: spec_fn(int) -> int, st: int, s: int, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        bsum(v, st, s, n - 1) + v(kc(st + n - 1, s))
    }
}

/// libvips's 8-bit box average of `n` samples summing to `sum`: the fixed
/// point of 8.17 and later, or (`exact`) the rounded division before.
pub open spec fn bavg(sum: int, n: int, exact: bool) -> int {
    if exact {
        (sum + n / 2) / n
    } else {
        fixavg(sum, n)
    }
}

/// `ceil(s / k)`.
pub open spec fn cdiv(s: int, k: int) -> int {
    (s + k - 1) / k
}

/// `vips_shrinkv(k, ceil)` of `src` (`w` by `h`).
pub open spec fn shrinkv(src: Seq<u8>, w: int, h: int, k: int, exact: bool) -> Seq<u8> {
    Seq::new(
        (w * cdiv(h, k) * NC) as nat,
        |j: int| bavg(bsum(col_line(src, w, (j / NC) % w, j % NC), ((j / NC) / w) * k, h, k), k, exact) as u8,
    )
}

/// `vips_shrinkh(k, ceil)` of `src` (`w` by `h`).
pub open spec fn shrinkh(src: Seq<u8>, w: int, h: int, k: int, exact: bool) -> Seq<u8> {
    let ow = cdiv(w, k);
    Seq::new(
        (ow * h * NC) as nat,
        |j: int| bavg(bsum(src_line(src, w, (j / NC) / ow, j % NC), ((j / NC) % ow) * k, w, k), k, exact) as u8,
    )
}

/// `vips_subsample(kx, ky)` of `src` (`w` by `h`): every `kx`-th pixel
/// of every `ky`-th row, from the first.
pub open spec fn subsample(src: Seq<u8>, w: int, h: int, kx: int, ky: int) -> Seq<u8> {
    let ow = w / kx;
    Seq::new(
        (ow * (h / ky) * NC) as nat,
        |j: int| src[((((j / NC) / ow) * ky) * w + ((j / NC) % ow) * kx) * NC + j % NC],
    )
}

} // verus!

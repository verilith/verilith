//! The specification of imgproxy's filters as libvips computes them
//! (`vips_gaussblur`, `vips_sharpen`'s step on the lightness,
//! `vips_premultiply` and `vips_unpremultiply`, and
//! imgproxy's pixelate: `vips_embed` with mirroring, `vips_shrink`,
//! `vips_zoom`), on 8-bit RGBA. Part of the trusted base with `spec.rs`.
//!
//! A blur is libvips's `vips_convsep` at integer precision: a row pass
//! then a column pass, each rounding to 8 bits, edges repeated
//! (`VIPS_EXTEND_COPY`). Each pass is `(sum(g[k] * v) + d / 2) / d`,
//! clamped to `0..=255`: the table `g` and divisor `d` are the mask's
//! integer weights and their sum on libvips's C path
//! (`convi.c`, `CONV_INT`), or its 8-bit mantissas and `2^exp` on its
//! vector path (`convi_hwy.cpp`), which rounds the same way. Which table
//! (which sigma, which path) is the caller's choice, built as
//! `vips_gaussmat` and `vips_convi_intize` build it.
//!
//! The table `g` has an odd length `2r + 1`: `g[r + k]` weighs the sample
//! `k` away.
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

/// The row pass: channel `c` of pixel `(x, y)` of `src` (`w` wide)
/// convolved along the row, rounded to 8 bits.
pub open spec fn ghpx(g: Seq<int>, d: int, src: Seq<u8>, w: int, y: int, x: int, c: int) -> int {
    kdiv(gsum(src_line(src, w, y, c), g, x, w, g.len() as int), d, 1)
}

/// Column `x`, channel `c` of the row pass, as a function of y.
pub open spec fn gmid_line(g: Seq<int>, d: int, src: Seq<u8>, w: int, x: int, c: int) -> spec_fn(int) -> int {
    |j: int| ghpx(g, d, src, w, j, x, c)
}

/// Channel `c` of pixel `(x, y)` blurred.
pub open spec fn gopx(g: Seq<int>, d: int, src: Seq<u8>, w: int, h: int, y: int, x: int, c: int) -> u8 {
    kdiv(gsum(gmid_line(g, d, src, w, x, c), g, y, h, g.len() as int), d, 1) as u8
}

/// `src` (`w` by `h` RGBA pixels) blurred with `g` and `d`, every channel.
pub open spec fn blur(g: Seq<int>, d: int, src: Seq<u8>, w: int, h: int) -> Seq<u8> {
    Seq::new((w * h * NC) as nat, |k: int| gopx(g, d, src, w, h, (k / NC) / w, (k / NC) % w, k % NC))
}

// ---------------------------------------------------------------------------
// sharpen
// ---------------------------------------------------------------------------

/// Row `y` of the one-channel image `l` (`w` wide), as a function of x.
pub open spec fn l_line(l: Seq<u16>, w: int, y: int) -> spec_fn(int) -> int {
    |i: int| l[y * w + i] as int
}

/// libvips's integer convolution of a 16-bit image (`convi.c`'s C path,
/// which `vips_sharpen` takes): `(sum + d / 2) / d`, kept within
/// `0..=32767`. With the mask's own sum as `d` the result never leaves
/// that range, so this is libvips's clip to a short, and `vips_sharpen`'s
/// `& 0x7fff` leaves it as it is.
pub open spec fn sdiv(n: int, d: int) -> int {
    let q = (n + d / 2) / d;
    if q < 0 {
        0
    } else if q > 32767 {
        32767
    } else {
        q
    }
}

/// The row pass of the blur of `l`.
pub open spec fn lhpx(g: Seq<int>, d: int, l: Seq<u16>, w: int, y: int, x: int) -> int {
    sdiv(gsum(l_line(l, w, y), g, x, w, g.len() as int), d)
}

/// Column `x` of the row pass, as a function of y.
pub open spec fn lmid_line(g: Seq<int>, d: int, l: Seq<u16>, w: int, x: int) -> spec_fn(int) -> int {
    |j: int| lhpx(g, d, l, w, j, x)
}

/// Pixel `(x, y)` of `l` blurred.
pub open spec fn lopx(g: Seq<int>, d: int, l: Seq<u16>, w: int, h: int, y: int, x: int) -> int {
    sdiv(gsum(lmid_line(g, d, l, w, x), g, y, h, g.len() as int), d)
}

/// `vips_sharpen`'s step on the lightness `l` (`w` by `h`, LabS: 0 to
/// 32767): each value moved by `lut` of how far it is from its blurred
/// value, `v + lut[v - blurred + 32768]`, kept within `0..=32767`. The
/// table is the caller's (`vips_sharpen` builds it from its curve).
pub open spec fn sharpen_l(g: Seq<int>, d: int, lut: Seq<int>, l: Seq<u16>, w: int, h: int) -> Seq<u16> {
    Seq::new(
        (w * h) as nat,
        |k: int|
            {
                let v1 = l[k] as int;
                let o = v1 + lut[v1 - lopx(g, d, l, w, h, k / w, k % w) + 32768];
                (if o < 0 {
                    0
                } else if o > 32767 {
                    32767
                } else {
                    o
                }) as u16
            },
    )
}

// ---------------------------------------------------------------------------
// premultiplied alpha
// ---------------------------------------------------------------------------

/// `vips_premultiply` then `vips_cast` to 8 bits: `v * (a / 255)` in
/// single precision, truncated. For 8-bit `v` and `a` that is exactly
/// `v * a / 255` rounded down (all 65536 cases checked in IEEE single
/// precision by `tests/filter.rs`).
pub open spec fn pm(v: int, a: int) -> int {
    v * a / 255
}

/// Where single precision rounds `v * (255 / a)` below the whole number
/// it equals: those values come out one less (found by running all 65536
/// cases in IEEE single precision as `unpremultiply.c` computes them;
/// `tests/filter.rs` checks the list).
pub open spec fn up_low(v: int, a: int) -> bool {
    (v == a && (a == 7 || a == 14 || a == 28 || a == 41 || a == 56 || a == 63 || a == 82 || a == 91 || a == 101
        || a == 112 || a == 113 || a == 119 || a == 123 || a == 126 || a == 163 || a == 164 || a == 182 || a == 191
        || a == 197 || a == 202 || a == 207 || a == 209 || a == 223 || a == 224 || a == 226 || a == 229 || a == 233
        || a == 237 || a == 238 || a == 239 || a == 246 || a == 252)) || (a == 237 && (v == 79 || v == 158))
}

/// `vips_unpremultiply` then `vips_cast` to 8 bits: `v * (255 / a)` in
/// single precision, truncated and clipped to 255; 0 where `a` is 0.
pub open spec fn up(v: int, a: int) -> int {
    if a <= 0 {
        0
    } else {
        let e = v * 255 / a - (if up_low(v, a) { 1int } else { 0 });
        if e > 255 {
            255
        } else {
            e
        }
    }
}

/// `src` (RGBA) premultiplied: colour channels scaled by alpha.
pub open spec fn premultiply(src: Seq<u8>) -> Seq<u8> {
    Seq::new(src.len(), |k: int| if k % NC == 3 { src[k] } else { pm(src[k] as int, src[k - k % NC + 3] as int) as u8 })
}

/// `src` (RGBA) unpremultiplied.
pub open spec fn unpremultiply(src: Seq<u8>) -> Seq<u8> {
    Seq::new(src.len(), |k: int| if k % NC == 3 { src[k] } else { up(src[k] as int, src[k - k % NC + 3] as int) as u8 })
}

// ---------------------------------------------------------------------------
// pixelate
// ---------------------------------------------------------------------------

/// `VIPS_EXTEND_MIRROR`: the source of coordinate `i >= 0` of a line `s`
/// long extended by mirroring (the edge repeated: `s` maps to `s - 1`),
/// as `embed.c` tiles the image with its flipped copies.
pub open spec fn mir(i: int, s: int) -> int {
    let m = i % (2 * s);
    if m < s {
        m
    } else {
        2 * s - 1 - m
    }
}

/// libvips's 8-bit box average of `n` values summing to `sum`
/// (`shrinkv.c` and `shrinkh.c`, and their vector versions):
/// `((sum + n / 2) * floor(2^24 / n)) >> 24`.
pub open spec fn fixavg(sum: int, n: int) -> int {
    ((sum + n / 2) * (0x100_0000int / n)) / 0x100_0000int
}

/// Channel `c` of the mirrored image's column `xx`, summed over `n` rows
/// from `y0`.
pub open spec fn vsum(src: Seq<u8>, w: int, h: int, c: int, xx: int, y0: int, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        vsum(src, w, h, c, xx, y0, n - 1) + src[(mir(y0 + n - 1, h) * w + mir(xx, w)) * NC + c]
    }
}

/// `vips_shrinkv` by `p`: channel `c` of column `xx`, block row `by`.
pub open spec fn vshr(src: Seq<u8>, w: int, h: int, p: int, c: int, xx: int, by: int) -> int {
    fixavg(vsum(src, w, h, c, xx, by * p, p), p)
}

/// `n` of `vshr`'s values along block row `by` from column `bx * p`.
pub open spec fn hsum(src: Seq<u8>, w: int, h: int, p: int, c: int, bx: int, by: int, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        hsum(src, w, h, p, c, bx, by, n - 1) + vshr(src, w, h, p, c, bx * p + n - 1, by)
    }
}

/// Then `vips_shrinkh` by `p`: block `(bx, by)`'s channel `c`.
pub open spec fn pval(src: Seq<u8>, w: int, h: int, p: int, c: int, bx: int, by: int) -> int {
    fixavg(hsum(src, w, h, p, c, bx, by, p), p)
}

/// The block size imgproxy uses: at most the longer side.
pub open spec fn pclamp(p: int, w: int, h: int) -> int {
    let m = if w > h { w } else { h };
    if p > m {
        m
    } else {
        p
    }
}

/// imgproxy's `pixelate`: `src` (`w` by `h`) mirrored out to whole
/// `p`-pixel blocks, shrunk by `p` (`vips_shrink`: rows, then columns),
/// zoomed back by `p` (each pixel repeated) and cropped to `w` by `h`.
/// Nothing changes for `p` up to 1.
pub open spec fn pixelate(src: Seq<u8>, w: int, h: int, p0: int) -> Seq<u8> {
    let p = pclamp(p0, w, h);
    if p <= 1 {
        src
    } else {
        Seq::new(
            (w * h * NC) as nat,
            |k: int| pval(src, w, h, p, k % NC, ((k / NC) % w) / p, ((k / NC) / w) / p) as u8,
        )
    }
}

} // verus!

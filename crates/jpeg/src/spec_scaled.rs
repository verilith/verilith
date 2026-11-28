//! The specification of decoding at a reduced size: 1/2, 1/4 and 1/8 of
//! the image's width and height, as libjpeg-turbo 3.2.1 decodes with
//! `scale_num / scale_denom` set to 4/8, 2/8 and 1/8 (TurboJPEG's
//! `tj3SetScalingFactor`). Part of the trusted base with `spec.rs`, whose
//! coefficients (`jpeg_coded`), range limit, upsampling filters and colour
//! conversion it reuses.
//!
//! libjpeg decodes each 8x8 block of coefficients straight to an `n` by
//! `n` block of samples with a reduced inverse DCT (`jidctred.c`), where
//! `m / 8` is the scale and `n` is `m`, or larger for a subsampled chroma
//! component: `jdmaster.c` doubles `n` while that leaves the component
//! still evenly divisible into the output, so that, say, 4:2:0 chroma at
//! 1/8 comes out of a 2x2 inverse DCT at the luma's resolution instead of
//! being upsampled. What is left is upsampled as at full size, except that
//! at 1/8 nothing uses the "fancy" triangle filters (`jdsample.c`:
//! `do_fancy` needs `min_DCT_scaled_size > 1`).
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The reduced inverse DCTs (`jidctred.c`), on dequantized coefficients `c`
// (row-major, as `dequant` gives them).
// ---------------------------------------------------------------------------
/// 1x1: the DC coefficient divided by 8, rounded (`jpeg_idct_1x1`).
pub open spec fn idct1(c: Seq<int>) -> u8 {
    range_limit(descale(c[0], 3))
}

/// The first pass of `jpeg_idct_2x2`, down column `x` (0, 1, 3, 5 or 7):
/// row `y` (0 or 1) of the workspace, in 32 bits.
pub open spec fn idct2_col(c: Seq<int>, x: int, y: int) -> int {
    let t10 = c[x] * 32768;
    let t0 = c[56 + x] * (-5906) + c[40 + x] * 6967 + c[24 + x] * (-10426) + c[8 + x] * 29692;
    wrap32(descale(if y == 0 { t10 + t0 } else { t10 - t0 }, 13))
}

/// Sample (`y`, `x`) of `jpeg_idct_2x2`.
pub open spec fn idct2(c: Seq<int>, y: int, x: int) -> u8 {
    let t10 = idct2_col(c, 0, y) * 32768;
    let t0 = idct2_col(c, 7, y) * (-5906) + idct2_col(c, 5, y) * 6967 + idct2_col(c, 3, y) * (-10426) + idct2_col(c, 1, y)
        * 29692;
    range_limit(descale(if x == 0 { t10 + t0 } else { t10 - t0 }, 20))
}

/// The four outputs of `jpeg_idct_4x4`'s one-dimensional transform of the
/// eight values `v` (of which `v[4]` is not used), before the final shift.
pub open spec fn idct4_1d(v: Seq<int>) -> Seq<int> {
    let t0 = v[0] * 16384;
    let t2 = v[2] * 15137 + v[6] * (-6270);
    let t10 = t0 + t2;
    let t12 = t0 - t2;
    let o0 = v[7] * (-1730) + v[5] * 11893 + v[3] * (-17799) + v[1] * 8697;
    let o2 = v[7] * (-4176) + v[5] * (-4926) + v[3] * 7373 + v[1] * 20995;
    seq![t10 + o2, t12 + o0, t12 - o0, t10 - o2]
}

/// The first pass of `jpeg_idct_4x4`, down column `x` (any but 4): row
/// `y` (0 to 3) of the workspace, in 32 bits.
pub open spec fn idct4_col(c: Seq<int>, x: int, y: int) -> int {
    wrap32(descale(idct4_1d(Seq::new(8, |i: int| c[8 * i + x]))[y], 12))
}

/// Sample (`y`, `x`) of `jpeg_idct_4x4`.
pub open spec fn idct4(c: Seq<int>, y: int, x: int) -> u8 {
    range_limit(descale(idct4_1d(Seq::new(8, |j: int| if j == 4 { 0 } else { idct4_col(c, j, y) }))[x], 19))
}

/// Sample (`y`, `x`) of an `n` by `n` inverse DCT.
pub open spec fn idct_n(c: Seq<int>, n: int, y: int, x: int) -> u8 {
    if n == 1 {
        idct1(c)
    } else if n == 2 {
        idct2(c, y, x)
    } else if n == 4 {
        idct4(c, y, x)
    } else {
        idct(c, y, x)
    }
}

// ---------------------------------------------------------------------------
// Component sizes at scale `m / 8` (m is 1, 2 or 4)
// ---------------------------------------------------------------------------
/// `jdmaster.c`'s choice of inverse DCT size for component `c`, from `s` on.
pub open spec fn ssize_from(f: Frame, c: int, m: int, s: int) -> int
    decreases 16 - s,
{
    if s <= 0 || s >= 8 {
        s
    } else if (maxh(f) * m) % (f.comps[c].h as int * s * 2) == 0 && (maxv(f) * m) % (f.comps[c].v as int * s * 2) == 0 {
        ssize_from(f, c, m, 2 * s)
    } else {
        s
    }
}

/// The inverse DCT size component `c` is decoded with at scale `m / 8`.
pub open spec fn ssize(f: Frame, c: int, m: int) -> int {
    ssize_from(f, c, m, m)
}

/// The width and height of component `c` at scale `m / 8`
/// (`downsampled_width` and `downsampled_height`).
pub open spec fn sdw(f: Frame, c: int, m: int) -> int {
    cdiv(f.w * f.comps[c].h as int * ssize(f, c, m), 8 * maxh(f))
}

pub open spec fn sdh(f: Frame, c: int, m: int) -> int {
    cdiv(f.h * f.comps[c].v as int * ssize(f, c, m), 8 * maxv(f))
}

/// Sample (`r`, `x`) of component `c` at scale `m / 8`.
pub open spec fn ssample(k: Coded, c: int, m: int, r: int, x: int) -> int {
    let n = ssize(k.f, c, m);
    idct_n(dequant(k.a[c], 64 * ((r / n) * cw(k.f, c) + x / n), k.ql[c]), n, r % n, x % n) as int
}

// ---------------------------------------------------------------------------
// Upsampling and pixels
// ---------------------------------------------------------------------------
/// The samples of component `c` across one output group (`h_in_group`,
/// `v_in_group` in `jdsample.c`); an output group is `maxh` by `maxv`.
pub open spec fn hin(f: Frame, c: int, m: int) -> int {
    f.comps[c].h as int * ssize(f, c, m) / m
}

pub open spec fn vin(f: Frame, c: int, m: int) -> int {
    f.comps[c].v as int * ssize(f, c, m) / m
}

/// The sample row a vertical 2:1 upsampler blends with row `y / 2`.
pub open spec fn sfar_row(k: Coded, c: int, m: int, y: int) -> int {
    if y % 2 == 0 {
        clamp(y / 2 - 1, 0, sdh(k.f, c, m) - 1)
    } else {
        clamp(y / 2 + 1, 0, sdh(k.f, c, m) - 1)
    }
}

/// `3 * near + far` for the two rows `h2v2_fancy_upsample` blends.
pub open spec fn scolsum(k: Coded, c: int, m: int, y: int, x: int) -> int {
    3 * ssample(k, c, m, y / 2, x) + ssample(k, c, m, sfar_row(k, c, m, y), x)
}

/// Component `c` at output pixel (`y`, `x`) at scale `m / 8`: as `spec::upsampled`, with the
/// triangle filters only when `m > 1`, and replication by
/// `maxh / hin` and `maxv / vin` otherwise.
pub open spec fn supsampled(k: Coded, c: int, m: int, y: int, x: int) -> int {
    let hi = hin(k.f, c, m);
    let vi = vin(k.f, c, m);
    let ho = maxh(k.f);
    let vo = maxv(k.f);
    let fancy = m > 1;
    let w = sdw(k.f, c, m);
    let i = x / 2;
    if hi == ho && vi == vo {
        ssample(k, c, m, y, x)
    } else if hi * 2 == ho && vi == vo && fancy && w > 2 {
        let s = ssample(k, c, m, y, i);
        if x % 2 == 0 {
            if i == 0 {
                s
            } else {
                (3 * s + ssample(k, c, m, y, i - 1) + 1) / 4
            }
        } else if i == w - 1 {
            s
        } else {
            (3 * s + ssample(k, c, m, y, i + 1) + 2) / 4
        }
    } else if hi == ho && vi * 2 == vo && fancy {
        (scolsum(k, c, m, y, x) + 1 + y % 2) / 4
    } else if hi * 2 == ho && vi * 2 == vo && fancy && w > 2 {
        let s = scolsum(k, c, m, y, i);
        if x % 2 == 0 {
            if i == 0 {
                (4 * s + 8) / 16
            } else {
                (3 * s + scolsum(k, c, m, y, i - 1) + 8) / 16
            }
        } else if i == w - 1 {
            (4 * s + 7) / 16
        } else {
            (3 * s + scolsum(k, c, m, y, i + 1) + 7) / 16
        }
    } else {
        ssample(k, c, m, y / (vo / vi), x / (ho / hi))
    }
}

/// Channel `ch` of output pixel (`y`, `x`) at scale `m / 8`.
pub open spec fn spixel(k: Coded, m: int, y: int, x: int, ch: int) -> int {
    match k.color {
        Color::Gray => supsampled(k, 0, m, y, x),
        Color::Rgb => supsampled(k, ch, m, y, x),
        Color::YCbCr => {
            let l = supsampled(k, 0, m, y, x);
            let cb = supsampled(k, 1, m, y, x);
            let cr = supsampled(k, 2, m, y, x);
            if ch == 0 {
                ycc_r(l, cr)
            } else if ch == 1 {
                ycc_g(l, cb, cr)
            } else {
                ycc_b(l, cb)
            }
        },
    }
}

/// The image at scale `m / 8`: `ceil(w * m / 8)` by `ceil(h * m / 8)`.
pub open spec fn render_scaled(k: Coded, m: int) -> Image {
    let nc = k.f.nc as int;
    let w = cdiv(k.f.w * m, 8);
    let h = cdiv(k.f.h * m, 8);
    Image { w, h, nc, px: Seq::new((w * h * nc) as nat, |j: int| spixel(k, m, j / (w * nc), (j / nc) % w, j % nc) as u8) }
}

/// The image a file decodes to at scale `m / 8`, for `m` 1, 2 or 4.
pub open spec fn jpeg_decode_scaled(d: Seq<u8>, m: int) -> Option<Image> {
    match jpeg_coded(d) {
        None => None,
        Some(k) => Some(render_scaled(k, m)),
    }
}

} // verus!

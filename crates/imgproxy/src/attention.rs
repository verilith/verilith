//! libvips's "attention" map for smart gravity (`conversion/smartcrop.c`,
//! `vips_smartcrop_attention`), in floating point as libvips computes it:
//! the image premultiplied if it has alpha, reduced to about 32 by 32
//! with `vips_resize`'s Lanczos 3 (`resample/resize.c`, `reducev.cpp`,
//! `reduceh.cpp`, `templates.h`, `shrinkv.c`, `shrinkh.c`), turned to XYZ;
//! edges (a Laplacian of Y, times 5, made positive), skin (100 less 100
//! times the distance of the normalised XYZ from the skin vector
//! -0.78, -0.57, -0.44) and saturation (Lab's a), the last two where Y is
//! above 5; their sum blurred with a sigma of a tenth of the crop's
//! diagonal at that scale (at least 1). Not verified: the proxy's
//! verified `smart::smart_x` picks the first highest value of this map
//! and places the crop on it, as `vips_max` and `smartcrop.c` do, and its
//! proofs hold for every map, so a wrong value moves the crop, never
//! what the code may do. Checked against libvips itself
//! (`tests/libvips.rs`).

/// `VIPS_TRANSFORM_SCALE` and `VIPS_INTERPOLATE_SHIFT` (`interpolate.h`).
const TSCALE: i32 = 64;
const ISHIFT: i32 = 12;

/// One band-interleaved image: 8-bit values (held exactly in `f32`) or
/// floats, as libvips's uchar and float paths.
#[derive(Clone)]
struct Img {
    w: usize,
    h: usize,
    nb: usize,
    uchar: bool,
    px: Vec<f32>,
}

impl Img {
    fn at(&self, x: usize, y: usize, b: usize) -> f32 {
        self.px[(y * self.w + x) * self.nb + b]
    }
}

/// `VIPS_ROUND_UINT`.
fn round_uint(v: f64) -> usize {
    (v + 0.5) as usize
}

fn sinc(x: f64) -> f64 {
    if x == 0.0 {
        1.0
    } else {
        (x * std::f64::consts::PI).sin() / (x * std::f64::consts::PI)
    }
}

fn lanczos3(x: f64) -> f64 {
    if (-3.0..=3.0).contains(&x) {
        sinc(x) * sinc(x / 3.0)
    } else {
        0.0
    }
}

/// `vips_reduce_make_mask` for Lanczos 3 (`calculate_coefficients`).
fn make_mask(n: usize, shrink: f64, x: f64) -> Vec<f64> {
    let half = x + n as f64 / 2.0 - 1.0;
    let scale = 1.0 / shrink;
    let mut c: Vec<f64> = (0..n).map(|i| lanczos3((i as f64 - half) * scale)).collect();
    let sum: f64 = c.iter().sum();
    for v in &mut c {
        *v /= sum;
    }
    c
}

/// The 65 masks for a residual shrink, as doubles and as libvips's
/// `short`s (`(short) (c * VIPS_INTERPOLATE_SCALE)`, truncated).
fn masks(n: usize, shrink: f64) -> (Vec<Vec<f64>>, Vec<Vec<i32>>) {
    let f: Vec<Vec<f64>> = (0..=TSCALE).map(|x| make_mask(n, shrink, (x as f32 / TSCALE as f32) as f64)).collect();
    let s = f.iter().map(|m| m.iter().map(|&v| (v * (1 << ISHIFT) as f64) as i16 as i32).collect()).collect();
    (f, s)
}

/// `vips_shrinkv` (`ceil`: the bottom extended by copying to a whole
/// number of blocks); along columns when `vert`, else `vips_shrinkh`.
/// 8-bit averages are libvips 8.17's fixed point, or (`exact`) the exact
/// rounded division of earlier versions.
fn shrink(img: &Img, k: usize, vert: bool, exact: bool) -> Img {
    let (len, other) = if vert { (img.h, img.w) } else { (img.w, img.h) };
    let out = len.div_ceil(k);
    let mult = ((1u64 << 32) / (256 * k as u64)) as u64;
    let mut px = vec![0f32; out * other * img.nb];
    let (ow, oh) = if vert { (img.w, out) } else { (out, img.h) };
    for o in 0..out {
        for j in 0..other {
            for b in 0..img.nb {
                let get = |i: usize| {
                    let i = i.min(len - 1);
                    if vert { img.at(j, i, b) } else { img.at(i, j, b) }
                };
                let v = if img.uchar {
                    let s: u64 = (0..k).map(|i| get(o * k + i) as u64).sum();
                    if exact {
                        ((s + k as u64 / 2) / k as u64) as f32
                    } else {
                        (((s + k as u64 / 2) * mult) >> 24) as f32
                    }
                } else {
                    let s: f64 = (0..k).map(|i| get(o * k + i) as f64).sum();
                    (s * (1.0 / k as f64)) as f32
                };
                let (x, y) = if vert { (j, o) } else { (o, j) };
                px[(y * ow + x) * img.nb + b] = v;
            }
        }
    }
    Img { w: ow, h: oh, nb: img.nb, uchar: img.uchar, px }
}

/// `vips_reducev` (`vert`) or `vips_reduceh` by `factor`, Lanczos 3, gap 2.
fn reduce(img: &Img, factor: f64, vert: bool, exact: bool) -> Img {
    let len = if vert { img.h } else { img.w };
    let out = round_uint(len as f64 / factor).max(1);
    let mut extra = out as f64 * factor - len as f64;
    let ishr = ((len as f64 / out as f64 / 2.0).floor() as usize).max(1);
    let mut resid = factor;
    let src = if ishr > 1 {
        resid /= ishr as f64;
        extra /= ishr as f64;
        shrink(img, ishr, vert, exact)
    } else {
        img.clone()
    };
    if resid == 1.0 {
        return src;
    }
    let slen = if vert { src.h } else { src.w };
    let other = if vert { src.w } else { src.h };
    let n = (2.0 * (3.0 * resid).round_ties_even() + 1.0) as usize;
    let off = (1.0 + extra) / 2.0 - 1.0;
    let (mf, ms) = masks(n, resid);
    let pad = (n as f64 / 2.0).ceil() as i64 - 1;
    let (ow, oh) = if vert { (src.w, out) } else { (out, src.h) };
    let mut px = vec![0f32; ow * oh * src.nb];
    for o in 0..out {
        let p = (o as f64 + 0.5) * resid - 0.5 - off;
        let ip = p as i32 as i64;
        let sp = (p * TSCALE as f64 * 2.0) as i32;
        let t = (((sp & (TSCALE * 2 - 1)) + 1) >> 1) as usize;
        for j in 0..other {
            for b in 0..src.nb {
                let get = |i: i64| {
                    let i = (ip + i - pad).clamp(0, slen as i64 - 1) as usize;
                    if vert { src.at(j, i, b) } else { src.at(i, j, b) }
                };
                let v = if src.uchar {
                    let s: i32 = (0..n).map(|i| ms[t][i] * get(i as i64) as i32).sum();
                    ((s + (1 << (ISHIFT - 1))) >> ISHIFT).clamp(0, 255) as f32
                } else {
                    let s: f64 = (0..n).map(|i| mf[t][i] * get(i as i64) as f64).sum();
                    s as f32
                };
                let (x, y) = if vert { (j, o) } else { (o, j) };
                px[(y * ow + x) * src.nb + b] = v;
            }
        }
    }
    Img { w: ow, h: oh, nb: src.nb, uchar: src.uchar, px }
}

/// `vips_resize(hscale, vscale)` for scales below 1: rows, then columns.
/// Scales of 1 and more are left as they are (libvips enlarges with
/// bicubic interpolation there; see `attention`).
fn resize(img: &Img, hscale: f64, vscale: f64, exact: bool) -> Img {
    let hscale = hscale.max(1.0 / img.w as f64);
    let vscale = vscale.max(1.0 / img.h as f64);
    let mut img = img.clone();
    if vscale < 1.0 {
        img = reduce(&img, 1.0 / vscale, true, exact);
    }
    if hscale < 1.0 {
        img = reduce(&img, 1.0 / hscale, false, exact);
    }
    img
}

/// A one-band float plane, `w` by `h`.
struct Plane {
    w: usize,
    h: usize,
    v: Vec<f32>,
}

/// `vips_conv` at integer precision on a float plane (`convi.c`'s C path:
/// `double` sums over the non-zero entries in order, divided by the
/// scale), edges repeated; `m` is `mw` by `mh`.
fn conv(p: &Plane, m: &[f64], mw: usize, mh: usize, scale: f64) -> Plane {
    let (rx, ry) = ((mw / 2) as i64, (mh / 2) as i64);
    let mut v = vec![0f32; p.w * p.h];
    for y in 0..p.h {
        for x in 0..p.w {
            let mut s = 0f64;
            for j in 0..mh {
                for i in 0..mw {
                    let c = m[j * mw + i];
                    if c == 0.0 {
                        continue;
                    }
                    let xx = (x as i64 + i as i64 - rx).clamp(0, p.w as i64 - 1) as usize;
                    let yy = (y as i64 + j as i64 - ry).clamp(0, p.h as i64 - 1) as usize;
                    s += c * p.v[yy * p.w + xx] as f64;
                }
            }
            v[y * p.w + x] = (s / scale) as f32;
        }
    }
    Plane { w: p.w, h: p.h, v }
}

/// libvips's attention map of `px` (`w` by `h` RGBA; `alpha`: whether the
/// image has an alpha band in libvips) for a crop of `cw` by `ch`, its
/// size, and the scales it was computed at; `exact_shrink` for libvips
/// before 8.17 (see `shrink`).
pub fn attention(
    px: &[u8],
    w: usize,
    h: usize,
    alpha: bool,
    cw: usize,
    ch: usize,
    exact_shrink: bool,
) -> (Vec<f32>, usize, usize, f64, f64) {
    // `vips_premultiply` (float) when there is alpha, else the 8-bit image.
    let img = if alpha {
        let v = px
            .chunks_exact(4)
            .flat_map(|p| {
                let na = (p[3] as f64 / 255.0) as f32;
                [p[0] as f32 * na, p[1] as f32 * na, p[2] as f32 * na, p[3] as f32]
            })
            .collect();
        Img { w, h, nb: 4, uchar: false, px: v }
    } else {
        Img { w, h, nb: 4, uchar: true, px: px.iter().map(|&v| v as f32).collect() }
    };
    let hscale = 32.0 / w as f64;
    let vscale = 32.0 / h as f64;
    let sigma = ((cw as f64 * hscale).hypot(ch as f64 * vscale) / 10.0).max(1.0);
    let s = resize(&img, hscale, vscale, exact_shrink);
    let (sw, sh) = (s.w, s.h);
    let n = sw * sh;
    // XYZ (an image in float is cast to 8 bits first, as sRGB2scRGB takes
    // only 8 bits), then Lab of it.
    let to8 = |v: f32| v.clamp(0.0, 255.0) as u8;
    let xyz: Vec<(f32, f32, f32)> =
        (0..n).map(|k| crate::colour::srgb_to_xyz(to8(s.px[k * 4]), to8(s.px[k * 4 + 1]), to8(s.px[k * 4 + 2]))).collect();
    let yp = Plane { w: sw, h: sh, v: xyz.iter().map(|t| t.1).collect() };
    let lap = [0.0, -1.0, 0.0, -1.0, 4.0, -1.0, 0.0, -1.0, 0.0];
    let edge = conv(&yp, &lap, 3, 3, 1.0);
    let pyth = |a: f32, b: f32, c: f32| -> f32 {
        let s = a * a + b * b + c * c;
        (s as f64).powf(0.5) as f32
    };
    let skin_vector = [-0.78f64, -0.57, -0.44];
    let mut sum = Vec::with_capacity(n);
    for k in 0..n {
        let (x, y, z) = xyz[k];
        let e = (5.0f32 * edge.v[k] + 0.0f32).abs();
        let mag = pyth(x, y, z);
        let d = |v: f32| if mag == 0.0 { 0.0 } else { v / mag };
        let o = |v: f32, i: usize| (1.0 * v as f64 + skin_vector[i]) as f32;
        let dist = pyth(o(d(x), 0), o(d(y), 1), o(d(z), 2));
        let skin = -100.0f32 * dist + 100.0f32;
        let bright = y as f64 > 5.0;
        let sat = crate::colour::xyz_to_lab(x, y, z).1;
        let (skin, sat) = if bright { (skin, sat) } else { (0.0, 0.0) };
        sum.push(e + skin + sat);
    }
    // `vips_gaussblur(sigma)`: gaussmat's integer mask, rows then columns.
    let (m, scale) = crate::mask::gaussmat(sigma, 0.2).unwrap_or((vec![1], 1));
    let m: Vec<f64> = m.iter().map(|&v| v as f64).collect();
    let p = Plane { w: sw, h: sh, v: sum };
    let p = conv(&p, &m, m.len(), 1, scale as f64);
    let p = conv(&p, &m, 1, m.len(), scale as f64);
    (p.v, sw, sh, hscale, vscale)
}

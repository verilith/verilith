//! Which masks and positions libvips's `vips_resize` takes
//! (`resample/resize.c`, `reducev.cpp`, `reduceh.cpp`, `templates.h`),
//! for the verified passes in `reduce` to apply. Not verified: these
//! numbers decide how the result looks, and `reduce`'s proofs hold for
//! every choice of them. Checked byte for byte against libvips itself
//! (`tests/libvips.rs`).
//!
//! Every constant here is libvips's: 65 sub-pixel masks
//! (`VIPS_TRANSFORM_SCALE` 64, plus one), entries scaled by 4096
//! (`VIPS_INTERPOLATE_SCALE`) and truncated to `short`, a reducing gap of
//! 2.0 (`vips_resize`'s default), kernels and their widths
//! (`vips_reduce_get_points`). Output positions step by the reduction
//! factor in floating point from the start of each region libvips
//! computes: a whole row across, and 16 rows down (the strips its sinks
//! ask for), so a position can land a rounding step away from where a
//! direct multiplication would put it, as in libvips.
use crate::reduce;

/// libvips's `VipsKernel`s (as imgproxy's `resizing_algorithm`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kernel {
    Nearest,
    Linear,
    Cubic,
    Mitchell,
    Lanczos2,
    Lanczos3,
}

/// Which libvips: before 8.17, `vips_shrink` divides 8-bit sums exactly
/// and `calculate_coefficients` divides by the shrink (`old`); from 8.17
/// a fixed-point average and a multiplication by its reciprocal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Vips {
    pub old: bool,
}

pub const CURRENT: Vips = Vips { old: false };

const TSCALE: usize = 64;
const ISCALE: f64 = 4096.0;
const GAP: f64 = 2.0;
/// The rows of the strips libvips's sinks compute at a time.
const STRIP: usize = 16;

fn sinc(x: f64) -> f64 {
    if x == 0.0 {
        1.0
    } else {
        let x = x * std::f64::consts::PI;
        x.sin() / x
    }
}

fn cubic(x: f64, b: f64, c: f64) -> f64 {
    let ax = x.abs();
    let ax2 = ax * ax;
    let ax3 = ax2 * ax;
    if ax <= 1.0 {
        ((12.0 - 9.0 * b - 6.0 * c) * ax3 + (-18.0 + 12.0 * b + 6.0 * c) * ax2 + (6.0 - 2.0 * b)) / 6.0
    } else if ax <= 2.0 {
        ((-b - 6.0 * c) * ax3 + (6.0 * b + 30.0 * c) * ax2 + (-12.0 * b - 48.0 * c) * ax + (8.0 * b + 24.0 * c)) / 6.0
    } else {
        0.0
    }
}

fn filter(k: Kernel, x: f64) -> f64 {
    match k {
        Kernel::Nearest => 1.0,
        Kernel::Linear => {
            let x = x.abs();
            if x < 1.0 {
                1.0 - x
            } else {
                0.0
            }
        }
        Kernel::Cubic => cubic(x, 0.0, 0.5),
        Kernel::Mitchell => cubic(x, 1.0 / 3.0, 1.0 / 3.0),
        Kernel::Lanczos2 => {
            if (-2.0..=2.0).contains(&x) {
                sinc(x) * sinc(x / 2.0)
            } else {
                0.0
            }
        }
        Kernel::Lanczos3 => {
            if (-3.0..=3.0).contains(&x) {
                sinc(x) * sinc(x / 3.0)
            } else {
                0.0
            }
        }
    }
}

/// `vips_reduce_get_points`.
fn points(k: Kernel, shrink: f64) -> usize {
    let r = |v: f64| v.round_ties_even() as usize;
    match k {
        Kernel::Nearest => 1,
        Kernel::Linear => 2 * r(shrink) + 1,
        Kernel::Cubic | Kernel::Mitchell | Kernel::Lanczos2 => 2 * r(2.0 * shrink) + 1,
        Kernel::Lanczos3 => 2 * r(3.0 * shrink) + 1,
    }
}

/// `vips_reduce_make_mask`.
pub fn make_mask(k: Kernel, n: usize, shrink: f64, x: f64, v: Vips) -> Vec<f64> {
    if k == Kernel::Nearest {
        return vec![1.0];
    }
    let half = x + n as f64 / 2.0 - 1.0;
    let scale = 1.0 / shrink;
    let mut c: Vec<f64> = (0..n)
        .map(|i| {
            let xp = if v.old { (i as f64 - half) / shrink } else { (i as f64 - half) * scale };
            filter(k, xp)
        })
        .collect();
    let mut sum = 0.0;
    for &l in &c {
        sum += l;
    }
    for l in &mut c {
        *l /= sum;
    }
    c
}

/// `VIPS_ROUND_UINT`.
fn round_uint(v: f64) -> usize {
    (v + 0.5) as usize
}

/// One `vips_reducev` or `vips_reduceh` by `factor` along a `len` long
/// axis: the box shrink before it (1 for none), and the reduction after
/// (`None` when the shrink was all of it).
pub struct Pass {
    pub shrink: usize,
    pub red: Option<Red>,
}

/// A reduction: `n` taps; the 65 masks as doubles (for libvips's float
/// path) and as libvips's `short`s; each output sample's first tap and
/// mask; the output length.
pub struct Red {
    pub n: usize,
    pub mf: Vec<Vec<f64>>,
    pub ms: Vec<i16>,
    pub st: Vec<i64>,
    pub t: Vec<u8>,
    pub out: usize,
}

/// The plan of one pass; `strip` is how many outputs libvips computes
/// from one starting position.
pub fn pass(len: usize, factor: f64, k: Kernel, v: Vips, strip: usize) -> Pass {
    let out = round_uint(len as f64 / factor);
    let mut extra = out as f64 * factor - len as f64;
    let mut shrink = 1;
    let mut resid = factor;
    if k != Kernel::Nearest {
        let i = ((len as f64 / out as f64 / GAP).floor() as usize).max(1);
        if i > 1 {
            shrink = i;
            resid /= i as f64;
            extra /= i as f64;
        }
    }
    if resid == 1.0 {
        return Pass { shrink, red: None };
    }
    let n = points(k, resid);
    let off = (1.0 + extra) / 2.0 - 1.0;
    let mf: Vec<Vec<f64>> = (0..=TSCALE).map(|y| make_mask(k, n, resid, (y as f32 / TSCALE as f32) as f64, v)).collect();
    let ms = mf.iter().flat_map(|m| m.iter().map(|&c| (c * ISCALE) as i16)).collect();
    let pad = (n as f64 / 2.0).ceil() as i64 - 1;
    let mut st = Vec::with_capacity(out);
    let mut t = Vec::with_capacity(out);
    let mut p = 0.0;
    for o in 0..out {
        if o % strip == 0 {
            p = (o as f64 + 0.5) * resid - 0.5 - off;
        } else {
            p += resid;
        }
        let sp = (p * TSCALE as f64 * 2.0) as i32;
        st.push(p as i32 as i64 - pad);
        t.push((((sp & (TSCALE as i32 * 2 - 1)) + 1) >> 1) as u8);
    }
    Pass { shrink, red: Some(Red { n, mf, ms, st, t, out }) }
}

/// The vertical and horizontal passes of `vips_resize(hscale, "vscale",
/// vscale)` on a `w` by `h` image, for scales of at most 1, and the
/// `vips_subsample` before them (`kx`, `ky`) that `Nearest` takes.
pub struct Plan {
    pub kx: usize,
    pub ky: usize,
    pub v: Option<Pass>,
    pub h: Option<Pass>,
}

pub fn plan(w: usize, h: usize, hscale: f64, vscale: f64, k: Kernel, v: Vips) -> Plan {
    let (mut hs, mut vs) = (hscale, vscale);
    let (mut w, mut h) = (w, h);
    let (mut kx, mut ky) = (1, 1);
    if k == Kernel::Nearest {
        let tw = round_uint(w as f64 * hs);
        let th = round_uint(h as f64 * vs);
        kx = ((w as f64 / tw as f64 / GAP).floor() as usize).max(1);
        ky = ((h as f64 / th as f64 / GAP).floor() as usize).max(1);
        if kx > 1 || ky > 1 {
            w /= kx;
            h /= ky;
            hs *= kx as f64;
            vs *= ky as f64;
        }
    }
    hs = hs.max(1.0 / w as f64);
    vs = vs.max(1.0 / h as f64);
    let vp = (vs < 1.0).then(|| pass(h, 1.0 / vs, k, v, STRIP));
    let hp = (hs < 1.0).then(|| pass(w, 1.0 / hs, k, v, usize::MAX));
    Plan { kx, ky, v: vp, h: hp }
}

/// `vips_resize` of 8-bit RGBA `px` (`w` by `h`) by scales of at most 1,
/// through the verified passes; the result and its size.
pub fn resize_rgba(px: &[u8], w: usize, h: usize, hscale: f64, vscale: f64, k: Kernel, v: Vips) -> (Vec<u8>, usize, usize) {
    let p = plan(w, h, hscale, vscale, k, v);
    let (mut px, mut w, mut h) = (std::borrow::Cow::Borrowed(px), w, h);
    // pre: the passes' (sizes in 1..=MAX_DIM; plan_ok: at most 1000 taps,
    // which libvips's own widths after the gap's shrink are far below).
    if p.kx > 1 || p.ky > 1 {
        px = reduce::subsample_x(&px, w, h, p.kx, p.ky).into();
        w /= p.kx;
        h /= p.ky;
    }
    let exact = v.old;
    if let Some(vp) = &p.v {
        if vp.shrink > 1 {
            px = reduce::shrinkv_x(&px, w, h, vp.shrink, exact).into();
            h = h.div_ceil(vp.shrink);
        }
        if let Some(r) = &vp.red {
            px = reduce::reducev_x(&px, w, h, r.n, &r.ms, &r.st, &r.t, r.out).into();
            h = r.out;
        }
    }
    if let Some(hp) = &p.h {
        if hp.shrink > 1 {
            px = reduce::shrinkh_x(&px, w, h, hp.shrink, exact).into();
            w = w.div_ceil(hp.shrink);
        }
        if let Some(r) = &hp.red {
            px = reduce::reduceh_x(&px, w, h, r.n, &r.ms, &r.st, &r.t, r.out).into();
            w = r.out;
        }
    }
    (px.into_owned(), w, h)
}

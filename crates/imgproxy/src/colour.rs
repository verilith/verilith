//! libvips's colour conversions between 8-bit sRGB and LabS, and
//! `vips_sharpen`, in floating point as libvips computes them: the
//! formulas, constants and order of operations of `colour/LabQ2sRGB.c`
//! (the sRGB tables, `vips_col_scRGB2XYZ`, `vips_col_XYZ2scRGB`,
//! `vips_col_scRGB2sRGB_8`), `XYZ2Lab.c` (its cube-root table),
//! `Lab2LabS.c`, `LabS2Lab.c`, `Lab2XYZ.c` and `convolution/sharpen.c`,
//! with `f32` for `float`, `f64` for `double`, `round_ties_even` for
//! `rint` and `as` casts for C's truncating conversions. Not verified:
//! the step on the lightness between the conversions is
//! (`filter::sharpen_l_x`), and its proofs hold for every table and image,
//! so a wrong value here changes how the image looks, never what the code
//! may do. Checked against libvips itself (`tests/libvips.rs`).
use std::sync::OnceLock;

/// D65, `include/vips/colour.h`.
const X0: f64 = 95.0470;
const Y0: f64 = 100.0;
const Z0: f64 = 108.8827;
/// `QUANT_ELEMENTS` in `XYZ2Lab.c`.
const QUANT: usize = 100000;

struct Tables {
    /// `vips_v2Y_8`: 8-bit sRGB to linear.
    v2y: [f32; 256],
    /// `vips_Y2v_8`: linear to 8-bit sRGB, one extra for interpolation.
    y2v: [i32; 257],
    /// `XYZ2Lab.c`'s `cbrt_table`.
    cbrt: Vec<f32>,
    /// `vips_sharpen`'s table, for its default curve.
    lut: Vec<i16>,
}

fn tables() -> &'static Tables {
    static T: OnceLock<Tables> = OnceLock::new();
    T.get_or_init(|| {
        let mut v2y = [0f32; 256];
        let mut y2v = [0i32; 257];
        for i in 0..256 {
            let f = i as f32 / 255.0;
            let v = if (f as f64) <= 0.0031308 { 12.92f32 * f } else { (1.0f32 + 0.055f32) * f.powf(1.0f32 / 2.4f32) - 0.055f32 };
            y2v[i] = (255.0f32 * v).round_ties_even() as i32;
            v2y[i] = if (f as f64) <= 0.04045 { f / 12.92f32 } else { ((f + 0.055f32) / (1.0f32 + 0.055f32)).powf(2.4f32) };
        }
        y2v[256] = y2v[255];
        let cbrt = (0..QUANT)
            .map(|i| {
                let y = i as f32 / QUANT as f32;
                if (y as f64) < 0.008856 { 7.787f32 * y + (16.0f32 / 116.0f32) } else { y.cbrt() }
            })
            .collect();
        Tables { v2y, y2v, cbrt, lut: sharpen_lut(2.0, 10.0, 20.0, 0.0, 3.0) }
    })
}

/// `vips_sharpen`'s table (`sharpen.c`): how far to move a lightness that
/// is `i - 32768` (LabS units) from its blurred value.
pub fn sharpen_lut(x1: f64, y2: f64, y3: f64, m1: f64, m2: f64) -> Vec<i16> {
    (0..65536)
        .map(|i| {
            let v = (i as f64 - 32767.0) / 327.67;
            let mut y = if v < -x1 {
                (v + x1) * m2 + (-x1) * m1
            } else if v < x1 {
                v * m1
            } else {
                (v - x1) * m2 + x1 * m1
            };
            if y < -y3 {
                y = -y3;
            }
            if y > y2 {
                y = y2;
            }
            (y * 327.67).round_ties_even() as i16
        })
        .collect()
}

fn cbr(t: &Tables, n: f32) -> f32 {
    if !(0.0..=1.0).contains(&n) {
        return n.cbrt();
    }
    let v = n * QUANT as f32;
    let i = (v as i32).clamp(0, QUANT as i32 - 2) as usize;
    let f = v - i as f32;
    t.cbrt[i] + f * (t.cbrt[i + 1] - t.cbrt[i])
}

/// 8-bit sRGB to LabS (`vips_colourspace`'s route: sRGB2scRGB, scRGB2XYZ,
/// XYZ2Lab, Lab2LabS).
pub fn srgb_to_labs(r: u8, g: u8, b: u8) -> (u16, i16, i16) {
    let t = tables();
    let s = |v: u8| (t.v2y[v as usize] as f64 * Y0) as f32;
    let (r, g, b) = (s(r), s(g), s(b));
    let x = 0.4124f32 * r + 0.3576f32 * g + 0.1805f32 * b;
    let y = 0.2126f32 * r + 0.7152f32 * g + 0.0722f32 * b;
    let z = 0.0193f32 * r + 0.1192f32 * g + 0.9505f32 * b;
    let cx = cbr(t, (x as f64 / X0) as f32);
    let cy = cbr(t, (y as f64 / Y0) as f32);
    let cz = cbr(t, (z as f64 / Z0) as f32);
    let l = 116.0f32 * cy - 16.0f32;
    let a = 500.0f32 * (cx - cy);
    let bb = 200.0f32 * (cy - cz);
    let l = (l as f64 * (32767.0 / 100.0)).clamp(0.0, 32767.0) as u16;
    let a = (a as f64 * (32768.0 / 128.0)).clamp(-32768.0, 32767.0) as i16;
    let bb = (bb as f64 * (32768.0 / 128.0)).clamp(-32768.0, 32767.0) as i16;
    (l, a, bb)
}

/// LabS to 8-bit sRGB (LabS2Lab, Lab2XYZ, XYZ2scRGB, scRGB2sRGB).
pub fn labs_to_srgb(l: u16, a: i16, b: i16) -> (u8, u8, u8) {
    let t = tables();
    let l = (l as f64 / (32767.0 / 100.0)) as f32 as f64;
    let a = (a as f64 / (32768.0 / 128.0)) as f32 as f64;
    let b = (b as f64 / (32768.0 / 128.0)) as f32 as f64;
    let (y, cby) = if l < 8.0 {
        let y = (l * Y0) / 903.3;
        (y, 7.787 * (y / Y0) + 16.0 / 116.0)
    } else {
        let cby = (l + 16.0) / 116.0;
        (Y0 * cby * cby * cby, cby)
    };
    let side = |tmp: f64, w: f64| if tmp < 0.2069 { w * (tmp - 0.13793) / 7.787 } else { w * tmp * tmp * tmp };
    let x = side(a / 500.0 + cby, X0) as f32;
    let z = side(cby - b / 200.0, Z0) as f32;
    let y = y as f32;
    let (x, y, z) = ((x as f64 / Y0) as f32, (y as f64 / Y0) as f32, (z as f64 / Y0) as f32);
    let r = 3.240625f32 * x + -1.537208f32 * y + -0.498629f32 * z;
    let g = -0.968931f32 * x + 1.875756f32 * y + 0.041518f32 * z;
    let bl = 0.055710f32 * x + -0.204021f32 * y + 1.056996f32 * z;
    let to8 = |v: f32| -> u8 {
        if v.is_nan() {
            return 0;
        }
        let yf = (v * 255.0f32).clamp(0.0, 255.0);
        let yi = yf as usize;
        let lo = t.y2v[yi];
        let hi = t.y2v[yi + 1];
        (lo as f32 + (hi - lo) as f32 * (yf - yi as f32)).round_ties_even() as u8
    };
    (to8(r), to8(g), to8(bl))
}

/// `vips_sharpen(sigma)` with its default curve, on 8-bit RGBA (`w` by
/// `h`; alpha is kept): `None` for a sigma outside libvips's range for it
/// (0.000001 to 10).
pub fn sharpen_rgba(px: &[u8], w: usize, h: usize, sigma: f64) -> Option<Vec<u8>> {
    if !(0.000001..=10.0).contains(&sigma) {
        return None;
    }
    let (m, scale) = crate::mask::gaussmat(sigma, 0.1)?;
    let n = w * h;
    let mut l = Vec::with_capacity(n);
    let mut ab = Vec::with_capacity(n);
    for p in px.chunks_exact(4) {
        let (lv, a, b) = srgb_to_labs(p[0], p[1], p[2]);
        l.push(lv);
        ab.push((a, b));
    }
    // pre: sharpen_l_x (gaussmat's masks are 1 to 9999 entries of at most
    // 20, odd; the scale is their sum, at least 1; LabS lightness is at
    // most 32767; sizes in 1..=MAX_DIM).
    let s = crate::filter::sharpen_l_x(&m, scale.max(1) as i64, &tables().lut, &l, w, h);
    let mut out = Vec::with_capacity(px.len());
    for (k, p) in px.chunks_exact(4).enumerate() {
        let (r, g, b) = labs_to_srgb(s[k], ab[k].0, ab[k].1);
        out.extend_from_slice(&[r, g, b, p[3]]);
    }
    Some(out)
}

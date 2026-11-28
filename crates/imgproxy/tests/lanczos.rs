//! The kernel resampler against a direct floating-point computation of
//! Lanczos 3 (and the other filters), with the exact kernel instead of the
//! table, and no rounding between the passes (each pass clamps to 0..=255, as the
//! code and libvips do).
use verilith_imgproxy::lanczos::{kresize_rgba, thumb_rgba};
use verilith_imgproxy::proxy::{kernel, Filter};

fn sinc(x: f64) -> f64 {
    if x == 0.0 { 1.0 } else { (std::f64::consts::PI * x).sin() / (std::f64::consts::PI * x) }
}

fn lanczos3(x: f64) -> f64 {
    if x < 3.0 { sinc(x) * sinc(x / 3.0) } else { 0.0 }
}

/// One dimension: `n` lines of `s` samples each (sample `i` of line `l`
/// at `l * ls + i * is`) to `d` samples.
fn pass(v: &[f64], s: usize, d: usize, at: impl Fn(usize, usize) -> usize, lines: usize, k: fn(f64) -> f64, a: f64) -> Vec<Vec<f64>> {
    let scale = if s > d { s as f64 / d as f64 } else { 1.0 };
    (0..lines)
        .map(|l| {
            (0..d)
                .map(|x| {
                    let c = (x as f64 + 0.5) * s as f64 / d as f64;
                    let (mut sum, mut ws) = (0.0, 0.0);
                    let lo = (c - a * scale).floor() as i64 - 1;
                    let hi = (c + a * scale).ceil() as i64 + 1;
                    for i in lo..=hi {
                        let w = k(((i as f64 + 0.5) - c).abs() / scale);
                        let ci = i.clamp(0, s as i64 - 1) as usize;
                        sum += w * v[at(l, ci)];
                        ws += w;
                    }
                    sum / ws
                })
                .collect()
        })
        .collect()
}

fn reference(src: &[u8], sw: usize, sh: usize, dw: usize, dh: usize) -> Vec<f64> {
    let v: Vec<f64> = src.iter().map(|&b| b as f64).collect();
    let mut out = vec![0.0; dw * dh * 4];
    for c in 0..4 {
        let rows = pass(&v, sw, dw, |y, i| (y * sw + i) * 4 + c, sh, lanczos3, 3.0);
        let mid: Vec<f64> = (0..sh * dw).map(|j| rows[j / dw][j % dw].clamp(0.0, 255.0)).collect();
        let cols = pass(&mid, sh, dh, |x, j| j * dw + x, dw, lanczos3, 3.0);
        for x in 0..dw {
            for y in 0..dh {
                out[(y * dw + x) * 4 + c] = cols[x][y].clamp(0.0, 255.0);
            }
        }
    }
    out
}

fn image(w: usize, h: usize, seed: u64) -> Vec<u8> {
    let mut s = seed | 1;
    let mut v = Vec::with_capacity(w * h * 4);
    for y in 0..h {
        for x in 0..w {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            let n = (s % 48) as usize;
            v.push(((x * 255 / w) ^ n) as u8);
            v.push(((y * 255 / h) + n / 2) as u8);
            v.push(if (x / 7 + y / 5) % 2 == 0 { 30 } else { 220 });
            v.push(255 - (n as u8));
        }
    }
    v
}

#[test]
fn matches_float_lanczos3() {
    let kt = kernel(Filter::Lanczos3).unwrap();
    for &(sw, sh, dw, dh) in &[(64, 48, 23, 17), (40, 40, 40, 40), (30, 20, 71, 45), (97, 13, 50, 7), (5, 5, 1, 1), (1, 9, 4, 3)] {
        let src = image(sw, sh, (sw * 31 + dh) as u64);
        let got = kresize_rgba(kt, &src, sw, sh, dw, dh);
        let want = reference(&src, sw, sh, dw, dh);
        let (mut max, mut sum) = (0f64, 0f64);
        for (g, w) in got.iter().zip(&want) {
            let e = (*g as f64 - w).abs();
            max = max.max(e);
            sum += e;
        }
        let mean = sum / got.len() as f64;
        assert!(max <= 2.0 && mean < 0.6, "{sw}x{sh} -> {dw}x{dh}: max {max}, mean {mean}");
    }
}

#[test]
fn same_size_is_the_identity_and_flat_stays_flat() {
    for f in [Filter::Lanczos3, Filter::Lanczos2, Filter::Cubic, Filter::Linear, Filter::Nearest] {
        let kt = kernel(f).unwrap();
        let src = image(33, 21, 7);
        assert_eq!(kresize_rgba(kt, &src, 33, 21, 33, 21), src, "{f:?}");
        let flat: Vec<u8> = [10u8, 200, 77, 255].repeat(50 * 40);
        for (dw, dh) in [(7, 9), (50, 40), (120, 13)] {
            let out = thumb_rgba(kt, &flat, 50, 40, dw, dh);
            assert!(out.chunks(4).all(|p| p == [10, 200, 77, 255]), "{f:?} {dw}x{dh}");
        }
    }
}

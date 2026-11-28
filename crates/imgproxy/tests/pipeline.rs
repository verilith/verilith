//! The verified pieces against independent code: the PNG encoder's output
//! read back by the `png` crate, the resizer against a direct float
//! computation of the area average, and the whole pipeline on JPEG and
//! PNG input made by the `image` crate.
use verilith_imgproxy::fit::Mode;
use verilith_imgproxy::proxy::{process, Limits, Options};

fn rng(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn image(w: usize, h: usize, seed: u64) -> Vec<u8> {
    let mut s = seed | 1;
    let mut v = Vec::with_capacity(w * h * 4);
    for y in 0..h {
        for x in 0..w {
            // Smooth gradients with noise, so every filter gets chosen.
            let n = (rng(&mut s) % 32) as usize;
            v.push(((x * 255 / w.max(1)) ^ n) as u8);
            v.push(((y * 255 / h.max(1)) + n) as u8);
            v.push(((x + y) * 7 % 256) as u8);
            v.push(if (x / 3 + y / 5) % 4 == 0 { 0 } else { 255 - n as u8 });
        }
    }
    v
}

fn png_read(b: &[u8]) -> (u32, u32, Vec<u8>) {
    let dec = png::Decoder::new(b);
    let mut r = dec.read_info().unwrap();
    let mut buf = vec![0; r.output_buffer_size()];
    let info = r.next_frame(&mut buf).unwrap();
    assert_eq!(info.color_type, png::ColorType::Rgba);
    assert_eq!(info.bit_depth, png::BitDepth::Eight);
    buf.truncate(info.buffer_size());
    (info.width, info.height, buf)
}

#[test]
fn png_round_trip() {
    for (i, &(w, h)) in [(1, 1), (2, 3), (17, 9), (64, 64), (301, 7), (5, 400)].iter().enumerate() {
        let px = image(w, h, i as u64 + 7);
        for level in [0, 1, 6, 9] {
            let b = verilith_imgproxy::pngenc::encode_rgba(&px, w as u32, h as u32, level).unwrap();
            assert_eq!(png_read(&b), (w as u32, h as u32, px.clone()), "{w}x{h} level {level}");
            let (hd, back) = verilith_png::top::decode(&b, verilith_png::top::PixelFormat::Rgba8, 1 << 30).unwrap();
            assert_eq!((hd.width, hd.height), (w as u32, h as u32));
            assert_eq!(back, px);
        }
    }
}

/// The area average, computed directly in floating point.
fn reference(src: &[u8], sw: usize, sh: usize, dw: usize, dh: usize) -> Vec<f64> {
    let ov = |x: usize, i: usize, s: usize, d: usize| -> f64 {
        let a = (x * s).max(i * d);
        let b = ((x + 1) * s).min((i + 1) * d);
        if b > a { (b - a) as f64 } else { 0.0 }
    };
    let mut out = vec![0.0; dw * dh * 4];
    for y in 0..dh {
        for x in 0..dw {
            for c in 0..4 {
                let mut t = 0.0;
                for j in 0..sh {
                    for i in 0..sw {
                        t += ov(y, j, sh, dh) * ov(x, i, sw, dw) * src[(j * sw + i) * 4 + c] as f64;
                    }
                }
                out[(y * dw + x) * 4 + c] = t / (sw * sh) as f64;
            }
        }
    }
    out
}

#[test]
fn resize_matches_area_average() {
    let mut seed = 99;
    for _ in 0..40 {
        let sw = 1 + (rng(&mut seed) % 40) as usize;
        let sh = 1 + (rng(&mut seed) % 40) as usize;
        let dw = 1 + (rng(&mut seed) % 50) as usize;
        let dh = 1 + (rng(&mut seed) % 50) as usize;
        let src = image(sw, sh, rng(&mut seed));
        let got = verilith_imgproxy::resize::resize_rgba(&src, sw, sh, dw, dh);
        let want = reference(&src, sw, sh, dw, dh);
        assert_eq!(got.len(), want.len());
        for (k, (&g, &w)) in got.iter().zip(&want).enumerate() {
            // Two roundings: at most a unit off.
            assert!((g as f64 - w).abs() <= 1.0, "{sw}x{sh} -> {dw}x{dh} at {k}: {g} vs {w}");
        }
    }
    // Same size: the identity.
    let src = image(13, 11, 5);
    assert_eq!(verilith_imgproxy::resize::resize_rgba(&src, 13, 11, 13, 11), src);
}

#[test]
fn pipeline_on_jpeg_and_png() {
    let (w, h) = (640u32, 427u32);
    let rgb: Vec<u8> = image(w as usize, h as usize, 3).chunks(4).flat_map(|p| [p[0], p[1], p[2]]).collect();
    let img = image::RgbImage::from_raw(w, h, rgb).unwrap();
    let mut jpg = Vec::new();
    img.write_to(&mut std::io::Cursor::new(&mut jpg), image::ImageFormat::Jpeg).unwrap();
    let mut pngb = Vec::new();
    img.write_to(&mut std::io::Cursor::new(&mut pngb), image::ImageFormat::Png).unwrap();
    let lim = Limits::default();
    for src in [&jpg, &pngb] {
        let fit = Options { mode: Mode::Fit, w: 300, h: 300, ..Default::default() };
        let (ow, oh, _) = png_read(&process(src, &fit, &lim).unwrap());
        assert_eq!((ow, oh), (300, 200));
        let fill = Options { mode: Mode::Fill, w: 100, h: 100, ..Default::default() };
        let (ow, oh, _) = png_read(&process(src, &fill, &lim).unwrap());
        assert_eq!((ow, oh), (100, 100));
        let force = Options { mode: Mode::Force, w: 50, h: 70, ..Default::default() };
        let (ow, oh, px) = png_read(&process(src, &force, &lim).unwrap());
        assert_eq!((ow, oh), (50, 70));
        assert!(px.chunks(4).all(|p| p[3] == 255));
        // No enlarging by default.
        let big = Options { mode: Mode::Fit, w: 2000, h: 2000, ..Default::default() };
        assert_eq!(png_read(&process(src, &big, &lim).unwrap()).0, 640);
        let big = Options { enlarge: true, ..big };
        assert_eq!(png_read(&process(src, &big, &lim).unwrap()).0, 2000);
    }
    // Limits are checked before decoding.
    let tiny = Limits { max_src_px: 1000, ..Limits::default() };
    assert!(process(&jpg, &Options::default(), &tiny).is_err());
    assert!(process(b"not an image", &Options::default(), &lim).is_err());
}

#[test]
fn shrink_on_load_matches_full_decode() {
    // A smooth image (gradients and a few blobs): the thumbnail made from a
    // JPEG decoded at 1/8, 1/4 and 1/2 is the one made from the full-size
    // decode, but for rounding.
    let (w, h) = (1600u32, 1200u32);
    let mut rgb = Vec::with_capacity((w * h * 3) as usize);
    for y in 0..h {
        for x in 0..w {
            let (fx, fy) = (x as f64 / w as f64, y as f64 / h as f64);
            let b = ((fx * 9.0).sin() * (fy * 7.0).cos() * 60.0 + 128.0) as u8;
            rgb.extend_from_slice(&[(fx * 255.0) as u8, (fy * 255.0) as u8, b]);
        }
    }
    let img = image::RgbImage::from_raw(w, h, rgb).unwrap();
    let mut jpg = Vec::new();
    img.write_to(&mut std::io::Cursor::new(&mut jpg), image::ImageFormat::Jpeg).unwrap();
    let full = verilith_imgproxy::proxy::decode(&jpg, 1 << 30).unwrap();
    let (tw, th) = (100usize, 75usize);
    let want = verilith_imgproxy::resize::resize_rgba(&full.px, w as usize, h as usize, tw, th);
    for shrink in [2u32, 4, 8] {
        let s = verilith_imgproxy::proxy::decode_shrunk(&jpg, 1 << 30, shrink).unwrap();
        assert_eq!((s.w, s.h), (w.div_ceil(shrink), h.div_ceil(shrink)));
        let got = verilith_imgproxy::resize::resize_rgba(&s.px, s.w as usize, s.h as usize, tw, th);
        let diff: f64 = got.iter().zip(&want).map(|(a, b)| (*a as f64 - *b as f64).abs()).sum::<f64>() / got.len() as f64;
        assert!(diff < 1.5, "shrink {shrink}: mean difference {diff}");
    }
}

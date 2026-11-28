//! Watermarks: the blend against a direct computation of Porter-Duff
//! "over", and placement, tiling and scaling through the pipeline.
use verilith_imgproxy::geom::watermark_rgba;
use verilith_imgproxy::proxy::{parse, process_with, Limits, Rgba};

fn rng(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn noise(n: usize, seed: u64) -> Vec<u8> {
    let mut s = seed | 1;
    (0..n * 4).map(|_| rng(&mut s) as u8).collect()
}

/// "over", in floating point, rounded.
fn over(d: &[u8], s: &[u8], op: f64) -> [u8; 4] {
    let a = ((s[3] as f64 * op * 10000.0).round() / 10000.0).round();
    let a = a.min(255.0);
    let da = d[3] as f64;
    let oa = a * 255.0 + da * (255.0 - a);
    if oa == 0.0 {
        return [0; 4];
    }
    let c = |i: usize| ((s[i] as f64 * a * 255.0 + d[i] as f64 * da * (255.0 - a)) / oa).round() as u8;
    [c(0), c(1), c(2), (oa / 255.0).round() as u8]
}

#[test]
fn blend_matches_over() {
    let (w, h, ww, wh) = (13, 9, 4, 3);
    let dst = noise(w * h, 1);
    let wm = noise(ww * wh, 2);
    for (op, tile, x, y, pw, ph) in [(10000, false, 2, 3, 1, 1), (5000, false, 9, 6, 1, 1), (2500, true, 0, 0, 6, 5), (10000, true, 0, 0, 4, 3)] {
        let out = watermark_rgba(&dst, w, h, &wm, ww, wh, x, y, tile, pw, ph, op);
        for py in 0..h {
            for px in 0..w {
                let k = (py * w + px) * 4;
                let (sx, sy) = if tile { (px % pw, py % ph) } else { (px.wrapping_sub(x), py.wrapping_sub(y)) };
                let want = if sx < ww && sy < wh {
                    over(&dst[k..k + 4], &wm[(sy * ww + sx) * 4..][..4], op as f64 / 10000.0)
                } else {
                    dst[k..k + 4].try_into().unwrap()
                };
                for c in 0..4 {
                    // Rounding halves can differ by one from floating point.
                    assert!((out[k + c] as i32 - want[c] as i32).abs() <= 1, "op {op} tile {tile} at ({px}, {py})");
                }
            }
        }
    }
}

fn solid(w: usize, h: usize, p: [u8; 4]) -> Vec<u8> {
    p.repeat(w * h)
}

fn read(b: &[u8]) -> (usize, usize, Vec<u8>) {
    let mut r = png::Decoder::new(std::io::Cursor::new(b)).read_info().unwrap();
    let mut buf = vec![0; r.output_buffer_size()];
    let info = r.next_frame(&mut buf).unwrap();
    buf.truncate(info.buffer_size());
    (info.width as usize, info.height as usize, buf)
}

#[test]
fn placed_tiled_and_scaled() {
    let (w, h) = (20, 10);
    let white = [255, 255, 255, 255];
    let red = [255, 0, 0, 255];
    let data = verilith_imgproxy::pngenc::encode_rgba(&solid(w, h, white), w as u32, h as u32, 1).unwrap();
    let wm = Rgba { w: 4, h: 2, px: solid(4, 2, red) };
    let run = |opts: &str| {
        let url = format!("/x/{opts}/plain/local:///a.png");
        let o = parse(url.as_bytes()).unwrap().opts;
        read(&process_with(&data, &o, &Limits::default(), Some(&wm)).unwrap())
    };
    let at = |v: &[u8], x: usize, y: usize| -> [u8; 4] { v[(y * w + x) * 4..][..4].try_into().unwrap() };
    let reds = |v: &[u8]| v.chunks(4).filter(|p| p == &red).count();
    // Top left, with an offset.
    let (_, _, out) = run("wm:1:nowe:1:2");
    assert_eq!(reds(&out), 8);
    assert_eq!(at(&out, 1, 2), red);
    assert_eq!(at(&out, 4, 3), red);
    assert_eq!(at(&out, 0, 0), white);
    // Bottom right; centre.
    let (_, _, out) = run("watermark:1:soea");
    assert_eq!((at(&out, 19, 9), at(&out, 16, 8), at(&out, 15, 9)), (red, red, white));
    let (_, _, out) = run("wm:1:ce");
    assert_eq!((at(&out, 8, 4), at(&out, 11, 5), at(&out, 7, 4)), (red, red, white));
    // Half opacity: halfway between.
    let (_, _, out) = run("wm:0.5:nowe");
    assert_eq!(at(&out, 0, 0), [255, 127, 127, 255]);
    // Tiled every 4 + 1 across, 2 + 2 down.
    let (_, _, out) = run("wm:1:re:1:2");
    assert_eq!(reds(&out), 4 * 3 * 8);
    assert_eq!((at(&out, 4, 0), at(&out, 5, 0), at(&out, 0, 2), at(&out, 0, 4)), (white, red, white, red));
    // Scaled to half the width: 10 by 5.
    let (_, _, out) = run("wm:1:nowe:0:0:0.5");
    assert_eq!(reds(&out), 50);
    // No watermark without the option, or at opacity 0.
    assert_eq!(reds(&run("w:20").2), 0);
    assert_eq!(reds(&run("wm:0").2), 0);
    // A watermark larger than the image is shrunk to fit.
    let big = Rgba { w: 40, h: 40, px: solid(40, 40, red) };
    let o = parse(b"/x/wm:1/plain/local:///a.png").unwrap().opts;
    let (_, _, out) = read(&process_with(&data, &o, &Limits::default(), Some(&big)).unwrap());
    assert_eq!(reds(&out), 100);
    for bad in ["wm:2", "wm:1:up", "wm:x", "wm:1:re:a"] {
        assert!(parse(format!("/x/{bad}/plain/local:///a.png").as_bytes()).is_err(), "{bad}");
    }
}

//! Smart gravity: the scores against a direct computation of their
//! specification, and the crop landing on the interesting part.
use verilith_imgproxy::proxy::{parse, process, Limits};
use verilith_imgproxy::smart::{scores_rgba, smart_x};

fn rng(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn reference_scores(s: &[u8], w: usize, h: usize) -> Vec<u8> {
    let lum = |k: usize| (2126 * s[k] as i32 + 7152 * s[k + 1] as i32 + 722 * s[k + 2] as i32 + 5000) / 10000;
    let at = |x: i64, y: i64| lum(((y.clamp(0, h as i64 - 1) as usize) * w + x.clamp(0, w as i64 - 1) as usize) * 4);
    let mut out = Vec::new();
    for y in 0..h as i64 {
        for x in 0..w as i64 {
            let l = 4 * at(x, y) - at(x - 1, y) - at(x + 1, y) - at(x, y - 1) - at(x, y + 1);
            let e = l.abs().min(255);
            let k = (y as usize * w + x as usize) * 4;
            let (r, g, b, a) = (s[k] as i32, s[k + 1] as i32, s[k + 2] as i32, s[k + 3] as i32);
            let skin = r > 95 && g > 40 && b > 20 && r > g && r > b && r - g.min(b) > 15 && r - g > 15;
            let sat = if lum(k) > 32 { r.max(g).max(b) - r.min(g).min(b) } else { 0 };
            let v = (e + if skin { 128 } else { 0 } + sat / 2).min(255);
            out.extend_from_slice(&[(v * a / 255) as u8; 4]);
        }
    }
    out
}

#[test]
fn scores_match_specification() {
    let mut seed = 7u64;
    for &(w, h) in &[(1, 1), (5, 3), (31, 17)] {
        let s: Vec<u8> = (0..w * h * 4).map(|_| rng(&mut seed) as u8).collect();
        assert_eq!(scores_rgba(&s, w, h), reference_scores(&s, w, h));
    }
}

/// Flat grey, with a noisy patch at `(px, py)`.
fn scene(w: usize, h: usize, px: usize, py: usize) -> Vec<u8> {
    let mut seed = 11u64;
    let mut v = Vec::with_capacity(w * h * 4);
    for y in 0..h {
        for x in 0..w {
            if (px..px + 12).contains(&x) && (py..py + 12).contains(&y) {
                let n = rng(&mut seed) as u8;
                v.extend_from_slice(&[n, n / 2, 255 - n, 255]);
            } else {
                v.extend_from_slice(&[128, 128, 128, 255]);
            }
        }
    }
    v
}

#[test]
fn point_is_on_the_patch() {
    let s = scene(64, 40, 44, 5);
    let (x, y) = smart_x(&[1], &s, 64, 40);
    assert!((44..56).contains(&x) && (5..17).contains(&y), "({x}, {y})");
    // A flat image: the first pixel.
    assert_eq!(smart_x(&[1, 2, 1], &[9u8; 4 * 6], 3, 2), (0, 0));
}

fn read(b: &[u8]) -> (usize, usize, Vec<u8>) {
    let mut r = png::Decoder::new(std::io::Cursor::new(b)).read_info().unwrap();
    let mut buf = vec![0; r.output_buffer_size()];
    let info = r.next_frame(&mut buf).unwrap();
    buf.truncate(info.buffer_size());
    (info.width as usize, info.height as usize, buf)
}

#[test]
fn crop_keeps_the_patch() {
    let (w, h) = (300, 100);
    let src = scene(w, h, 250, 40);
    let data = verilith_imgproxy::pngenc::encode_rgba(&src, w as u32, h as u32, 1).unwrap();
    let run = |opts: &str| {
        let url = format!("/x/{opts}/plain/local:///a.png");
        read(&process(&data, &parse(url.as_bytes()).unwrap().opts, &Limits::default()).unwrap())
    };
    let grey = |v: &[u8]| v.chunks(4).all(|p| p == [128, 128, 128, 255]);
    // Centred, the crop misses the patch; smart, it keeps it.
    let (cw, ch, centre) = run("rs:fill:100:100");
    assert_eq!((cw, ch), (100, 100));
    assert!(grey(&centre));
    let (_, _, smart) = run("rs:fill:100:100/g:sm");
    assert!(!grey(&smart));
    // The crop option's own smart gravity too.
    let (_, _, c) = run("c:100:100:sm");
    assert!(!grey(&c));
    // On a JPEG shrunk on load as well.
    let rgb: Vec<u8> = src.chunks(4).flat_map(|p| [p[0], p[1], p[2], 255]).collect();
    let j = verilith_jpeg::encode::encode_rgb(&rgb, w, h, 4, 95, false).unwrap();
    let o = parse(b"/x/rs:fill:25:25/g:sm/plain/local:///a.jpg").unwrap().opts;
    let (_, _, out) = read(&process(&j, &o, &Limits::default()).unwrap());
    let spread = out.chunks(4).map(|p| (p[0] as i32 - 128).abs() + (p[2] as i32 - 128).abs()).max().unwrap();
    assert!(spread > 20, "{spread}");
}

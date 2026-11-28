//! `blur` and `sharpen` against a direct computation of their
//! specification, and their properties through the whole proxy.
use verilith_imgproxy::filter::{blur_rgba, sharpen_rgba};
use verilith_imgproxy::proxy::{gauss, parse, process, Limits};

fn rng(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn noise(w: usize, h: usize, seed: u64) -> Vec<u8> {
    let mut s = seed | 1;
    (0..w * h * 4).map(|_| rng(&mut s) as u8).collect()
}

/// `kdiv`: `scale * n / d` rounded half up, clamped.
fn div(n: i64, d: i64, scale: i64) -> i64 {
    if d <= 0 {
        return 0;
    }
    ((2 * scale * n + d) / (2 * d)).clamp(0, 255 * scale)
}

/// The specification, written out directly.
fn reference(g: &[u32], src: &[u8], w: usize, h: usize) -> Vec<u8> {
    let r = (g.len() as i64 - 1) / 2;
    let tot: i64 = g.iter().map(|&v| v as i64).sum();
    let at = |i: i64, s: usize| i.clamp(0, s as i64 - 1) as usize;
    let mut mid = vec![0i64; w * h * 4];
    for y in 0..h {
        for x in 0..w {
            for c in 0..4 {
                let n: i64 = (0..g.len()).map(|t| g[t] as i64 * src[(y * w + at(x as i64 + t as i64 - r, w)) * 4 + c] as i64).sum();
                mid[(y * w + x) * 4 + c] = div(n, tot, 256);
            }
        }
    }
    let mut out = vec![0u8; w * h * 4];
    for y in 0..h {
        for x in 0..w {
            for c in 0..4 {
                let n: i64 = (0..g.len()).map(|t| g[t] as i64 * mid[(at(y as i64 + t as i64 - r, h) * w + x) * 4 + c]).sum();
                out[(y * w + x) * 4 + c] = div(n, 256 * tot, 1) as u8;
            }
        }
    }
    out
}

#[test]
fn blur_matches_specification() {
    for (i, &(w, h, sigma)) in [(1, 1, 10000), (7, 3, 5000), (17, 9, 20000), (40, 31, 33000), (3, 50, 80000)].iter().enumerate() {
        let src = noise(w, h, i as u64 + 3);
        let g = gauss(sigma).unwrap();
        let b = blur_rgba(&g, &src, w, h);
        assert_eq!(b, reference(&g, &src, w, h), "{w}x{h} sigma {sigma}");
        let s = sharpen_rgba(&g, &src, w, h);
        for k in 0..src.len() {
            let want = if k % 4 == 3 { src[k] } else { (2 * src[k] as i32 - b[k] as i32).clamp(0, 255) as u8 };
            assert_eq!(s[k], want);
        }
    }
    // Any table, not only Gaussians.
    let src = noise(9, 8, 99);
    let g = [3, 0, 65536, 17, 9];
    assert_eq!(blur_rgba(&g, &src, 9, 8), reference(&g, &src, 9, 8));
}

#[test]
fn flat_stays_flat_and_tiny_sigma_is_none() {
    let flat: Vec<u8> = [12u8, 200, 99, 255].repeat(20 * 10);
    let g = gauss(40000).unwrap();
    assert_eq!(blur_rgba(&g, &flat, 20, 10), flat);
    assert_eq!(sharpen_rgba(&g, &flat, 20, 10), flat);
    assert!(gauss(0).is_none());
    assert!(gauss(400).is_none());
    // The table stays within what the proofs cover.
    let big = gauss(655_359_999).unwrap();
    assert_eq!(big.len(), 2049);
    assert!(big.iter().all(|&v| v <= 65536));
}

fn png(w: usize, h: usize, px: &[u8]) -> Vec<u8> {
    verilith_imgproxy::pngenc::encode_rgba(px, w as u32, h as u32, 1).unwrap()
}

fn read(b: &[u8]) -> Vec<u8> {
    let mut r = png::Decoder::new(std::io::Cursor::new(b)).read_info().unwrap();
    let mut buf = vec![0; r.output_buffer_size()];
    let info = r.next_frame(&mut buf).unwrap();
    buf.truncate(info.buffer_size());
    buf
}

#[test]
fn through_the_proxy() {
    let src = noise(24, 16, 5);
    let data = png(24, 16, &src);
    let run = |opts: &str| {
        let url = format!("/x/{opts}/plain/local:///a.png");
        read(&process(&data, &parse(url.as_bytes()).unwrap().opts, &Limits::default()).unwrap())
    };
    let g = gauss(15000).unwrap();
    assert_eq!(run("blur:1.5"), blur_rgba(&g, &src, 24, 16));
    assert_eq!(run("bl:1.5/sh:1.5"), sharpen_rgba(&g, &blur_rgba(&g, &src, 24, 16), 24, 16));
    assert_eq!(run("sharpen:0"), src);
    // Blurring lowers the spread of the noise.
    let spread = |v: &[u8]| v.iter().step_by(4).map(|&c| (c as f64 - 127.5).powi(2)).sum::<f64>();
    assert!(spread(&run("bl:2")) < spread(&src) / 4.0);
    // After the crop, before padding: the padding stays transparent.
    let out = read(&process(&data, &parse(b"/x/bl:1/pd:2/plain/local:///a.png").unwrap().opts, &Limits::default()).unwrap());
    assert_eq!(&out[..4], &[0, 0, 0, 0]);
    assert!(parse(b"/x/bl:x/plain/local:///a.png").is_err());
}

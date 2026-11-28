//! The filters against a direct computation of their specification, and
//! their properties through the whole proxy.
use verilith_imgproxy::filter::{blur_rgba, pixelate_rgba, premul_rgba, sharpen_rgba, unpremul_rgba};
use verilith_imgproxy::mask;
use verilith_imgproxy::proxy::{parse, process, Limits};

/// `vips_gaussblur`'s weights and divisor.
fn gauss(sigma: f64) -> (Vec<u32>, i64) {
    mask::gaussblur(sigma).unwrap().unwrap()
}

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
fn reference(g: &[u32], d: i64, src: &[u8], w: usize, h: usize) -> Vec<u8> {
    let r = (g.len() as i64 - 1) / 2;
    let at = |i: i64, s: usize| i.clamp(0, s as i64 - 1) as usize;
    let mut mid = vec![0i64; w * h * 4];
    for y in 0..h {
        for x in 0..w {
            for c in 0..4 {
                let n: i64 = (0..g.len()).map(|t| g[t] as i64 * src[(y * w + at(x as i64 + t as i64 - r, w)) * 4 + c] as i64).sum();
                mid[(y * w + x) * 4 + c] = div(n, d, 1);
            }
        }
    }
    let mut out = vec![0u8; w * h * 4];
    for y in 0..h {
        for x in 0..w {
            for c in 0..4 {
                let n: i64 = (0..g.len()).map(|t| g[t] as i64 * mid[(at(y as i64 + t as i64 - r, h) * w + x) * 4 + c]).sum();
                out[(y * w + x) * 4 + c] = div(n, d, 1) as u8;
            }
        }
    }
    out
}

#[test]
fn blur_matches_specification() {
    for (i, &(w, h, sigma)) in [(1, 1, 1.0), (7, 3, 0.5), (17, 9, 2.0), (40, 31, 3.3), (3, 50, 8.0), (30, 20, 40.0)].iter().enumerate() {
        let src = noise(w, h, i as u64 + 3);
        let (g, d) = gauss(sigma);
        let b = blur_rgba(&g, d, &src, w, h);
        assert_eq!(b, reference(&g, d, &src, w, h), "{w}x{h} sigma {sigma}");
        let s = sharpen_rgba(&g, d, &src, w, h);
        for k in 0..src.len() {
            let want = if k % 4 == 3 { src[k] } else { (2 * src[k] as i32 - b[k] as i32).clamp(0, 255) as u8 };
            assert_eq!(s[k], want);
        }
    }
    // Any table and divisor, not only libvips's.
    let src = noise(9, 8, 99);
    let g = [3, 0, 65536, 17, 9];
    for d in [1, 7, 65625, 1 << 31] {
        assert_eq!(blur_rgba(&g, d, &src, 9, 8), reference(&g, d, &src, 9, 8));
    }
}

#[test]
fn masks_as_libvips_builds_them() {
    // gaussmat.c: rint(20 * exp(-x^2 / 2 sigma^2)) out to where it falls
    // below 0.2 of the peak.
    assert_eq!(mask::gaussmat(1.0, 0.2), Some((vec![12, 20, 12], 44)));
    assert_eq!(mask::gaussmat(0.5, 0.1), Some((vec![3, 20, 3], 26)));
    assert_eq!(mask::gaussmat(0.2, 0.2), Some((vec![20], 20)));
    // The vector path's mantissas: 128 * w / sum, shifted.
    let (g, d) = gauss(1.0);
    assert_eq!(d, 1 << 7);
    assert_eq!(g, vec![35, 58, 35]);
    // Too large for libvips: an error, as there.
    assert!(mask::gaussblur(3000.0).is_err());
    assert_eq!(mask::gaussblur(0.1), Ok(None));
    // Within what the proofs cover.
    let (g, d) = mask::gaussblur(2700.0).unwrap().unwrap();
    assert!(g.len() <= 10001 && g.len() % 2 == 1 && g.iter().all(|&v| v <= 65536) && (1..=1 << 31).contains(&d));
}

#[test]
fn flat_stays_flat() {
    let flat: Vec<u8> = [12u8, 200, 99, 255].repeat(20 * 10);
    let (g, d) = mask::gaussmat(4.0, 0.2).map(|(m, s)| (m, s as i64)).unwrap();
    assert_eq!(blur_rgba(&g, d, &flat, 20, 10), flat);
    assert_eq!(sharpen_rgba(&g, d, &flat, 20, 10), flat);
    // Pixelate's fixed point can lower a flat value by one, as libvips's
    // does: ((3 v + 1) * floor(2^24 / 3)) >> 24, twice.
    let f = |s: u64| (((s + 1) * ((1 << 24) / 3)) >> 24) as u8;
    let want: Vec<u8> = flat.iter().map(|&v| f(3 * f(3 * v as u64) as u64)).collect();
    assert_eq!(pixelate_rgba(flat.clone(), 20, 10, 3), want);
}

/// IEEE single precision, as libvips's premultiply.c and unpremultiply.c
/// compute (`float` factors, `double` max_alpha), then cast's truncation.
#[test]
fn premultiply_matches_single_precision() {
    for a in 0..=255u8 {
        for v in 0..=255u8 {
            let px = [v, v, v, a];
            let na = (a as f64 / 255.0) as f32;
            let want = (v as f32 * na) as f64;
            assert_eq!(premul_rgba(&px), [want as u8, want as u8, want as u8, a]);
            let f = if a == 0 { 0.0f32 } else { (255.0 / a as f64) as f32 };
            let want = ((v as f32 * f) as f64).clamp(0.0, 255.0) as u8;
            assert_eq!(unpremul_rgba(&px), [want, want, want, a], "v {v} a {a}");
        }
    }
}

/// imgproxy's pixelate, written out directly.
fn pix_ref(src: &[u8], w: usize, h: usize, p: usize) -> Vec<u8> {
    let p = p.min(w.max(h));
    if p <= 1 {
        return src.to_vec();
    }
    let mir = |i: usize, s: usize| {
        let m = i % (2 * s);
        if m < s { m } else { 2 * s - 1 - m }
    };
    let f = |s: u64, n: u64| (((s + n / 2) * ((1 << 24) / n as u64)) >> 24) as u64;
    let (nbx, nby) = (w.div_ceil(p), h.div_ceil(p));
    let mut out = vec![0u8; w * h * 4];
    for y in 0..h {
        for x in 0..w {
            for c in 0..4 {
                let (bx, by) = (x / p, y / p);
                assert!(bx < nbx && by < nby);
                let v: u64 = (0..p)
                    .map(|i| {
                        let xx = mir(bx * p + i, w);
                        f((0..p).map(|j| src[(mir(by * p + j, h) * w + xx) * 4 + c] as u64).sum(), p as u64)
                    })
                    .sum();
                out[(y * w + x) * 4 + c] = f(v, p as u64) as u8;
            }
        }
    }
    out
}

#[test]
fn pixelate_matches_specification() {
    for (i, &(w, h, p)) in [(1, 1, 5), (5, 3, 2), (5, 3, 4), (17, 9, 3), (40, 31, 7), (3, 50, 64), (12, 12, 4), (9, 2, 1)].iter().enumerate() {
        let src = noise(w, h, i as u64 + 11);
        assert_eq!(pixelate_rgba(src.clone(), w, h, p), pix_ref(&src, w, h, p), "{w}x{h} p {p}");
    }
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
    let mut src = noise(24, 16, 5);
    for k in (3..src.len()).step_by(4) {
        src[k] = 255;
    }
    let data = png(24, 16, &src);
    let run = |opts: &str| {
        let url = format!("/x/{opts}/plain/local:///a.png");
        read(&process(&data, &parse(url.as_bytes()).unwrap().opts, &Limits::default()).unwrap())
    };
    let (g, d) = gauss(1.5);
    // Opaque: premultiplying changes nothing.
    assert_eq!(run("blur:1.5"), blur_rgba(&g, d, &src, 24, 16));
    assert_eq!(run("bl:1.5/sh:1.5"), sharpen_rgba(&g, d, &blur_rgba(&g, d, &src, 24, 16), 24, 16));
    assert_eq!(run("sharpen:0"), src);
    assert_eq!(run("pix:4"), pixelate_rgba(src.clone(), 24, 16, 4));
    assert_eq!(run("pixelate:1"), src);
    // Blurring lowers the spread of the noise.
    let spread = |v: &[u8]| v.iter().step_by(4).map(|&c| (c as f64 - 127.5).powi(2)).sum::<f64>();
    assert!(spread(&run("bl:2")) < spread(&src) / 4.0);
    // After the crop, before padding: the padding stays transparent.
    let out = read(&process(&data, &parse(b"/x/bl:1/pd:2/plain/local:///a.png").unwrap().opts, &Limits::default()).unwrap());
    assert_eq!(&out[..4], &[0, 0, 0, 0]);
    assert!(parse(b"/x/bl:x/plain/local:///a.png").is_err());
    assert!(parse(b"/x/pix:1.5/plain/local:///a.png").is_err());
    // With alpha: blur premultiplied, then back.
    let mut asrc = noise(24, 16, 77);
    for k in (3..asrc.len()).step_by(37) {
        asrc[k] = 0;
    }
    let adata = png(24, 16, &asrc);
    let out = read(&process(&adata, &parse(b"/x/bl:1.5/plain/local:///a.png").unwrap().opts, &Limits::default()).unwrap());
    assert_eq!(out, unpremul_rgba(&blur_rgba(&g, d, &premul_rgba(&asrc), 24, 16)));
}

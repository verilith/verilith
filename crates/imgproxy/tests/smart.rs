//! Smart gravity: the verified choice against direct computations, and
//! crops through the whole proxy.
use verilith_imgproxy::proxy::{parse, process, smart_crop, Limits};
use verilith_imgproxy::smart::{centred_x, first_max_x, fkey_x};

fn rng(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

#[test]
fn keys_order_as_floats() {
    let mut seed = 5u64;
    let mut vals: Vec<f32> = vec![0.0, -0.0, 1.0, -1.0, f32::MIN, f32::MAX, f32::INFINITY, f32::NEG_INFINITY, 1e-40, -1e-40];
    for _ in 0..2000 {
        vals.push(f32::from_bits(rng(&mut seed) as u32));
    }
    vals.retain(|v| !v.is_nan());
    for &a in &vals {
        for &b in vals.iter().take(200) {
            assert_eq!(a.partial_cmp(&b).unwrap(), fkey_x(a.to_bits()).cmp(&fkey_x(b.to_bits())), "{a} {b}");
        }
    }
}

#[test]
fn first_max_and_centring() {
    let v: Vec<u32> = [1.0f32, 3.0, -2.0, 3.0, 0.5].iter().map(|v| v.to_bits()).collect();
    assert_eq!(first_max_x(&v), 1);
    assert_eq!(first_max_x(&[0.0f32.to_bits(), (-0.0f32).to_bits()]), 0);
    assert_eq!(first_max_x(&[(-0.0f32).to_bits(), 0.0f32.to_bits()]), 0);
    // VIPS_CLIP(0, a - c / 2, s - c).
    assert_eq!(centred_x(50, 100, 30), 35);
    assert_eq!(centred_x(5, 100, 30), 0);
    assert_eq!(centred_x(99, 100, 31), 69);
    assert_eq!(centred_x(7, 10, 10), 0);
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
fn crop_is_on_the_patch() {
    let s = scene(200, 120, 150, 20);
    let (x, y) = smart_crop(&s, 200, 120, false, 40, 40);
    assert!(x <= 150 && x + 40 >= 162 && y <= 20 && y + 40 >= 32, "({x}, {y})");
    // A flat image: the first pixel, as libvips.
    assert_eq!(smart_crop(&[9u8; 4 * 64 * 48], 64, 48, false, 10, 10), (0, 0));
    // Nothing to choose.
    assert_eq!(smart_crop(&s, 200, 120, false, 200, 120), (0, 0));
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

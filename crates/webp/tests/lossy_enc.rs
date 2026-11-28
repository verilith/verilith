//! The lossy encoder's files decode, and look like what went in.
use verilith_webp::enc_vp8::encode_lossy;

fn rng(s: &mut u64) -> u32 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    (*s >> 16) as u32
}

fn psnr(a: &[u32], b: &[u32]) -> f64 {
    let mut se = 0f64;
    for (x, y) in a.iter().zip(b) {
        for s in [0, 8, 16] {
            let d = ((x >> s) & 0xff) as f64 - ((y >> s) & 0xff) as f64;
            se += d * d;
        }
    }
    let mse = se / (3.0 * a.len() as f64);
    if mse == 0.0 { 99.0 } else { 10.0 * (255.0 * 255.0 / mse).log10() }
}

fn smooth(w: u32, h: u32, seed: u64) -> Vec<u32> {
    let mut s = seed;
    let (a, b, c) = (rng(&mut s) % 7 + 1, rng(&mut s) % 5 + 1, rng(&mut s) % 3 + 1);
    (0..w * h)
        .map(|i| {
            let x = i % w;
            let y = i / w;
            let r = ((x * a + y) / 2) & 0xff;
            let g = ((y * b + 2 * x) / 3) & 0xff;
            let bl = (((x ^ y) * c) / 4 + (rng(&mut s) % 6)) & 0xff;
            0xff00_0000 | (r << 16) | (g << 8) | bl
        })
        .collect()
}

#[test]
fn lossy_decodes() {
    let mut s = 0x9e37_79b9_7f4a_7c15u64;
    for &(w, h) in &[(1, 1), (3, 5), (16, 16), (17, 33), (64, 48), (100, 37), (257, 3), (320, 240)] {
        for q in [0, 30, 75, 95, 100] {
            for kind in 0..3 {
                let n = (w * h) as usize;
                let px: Vec<u32> = match kind {
                    0 => vec![0xff20_4060; n],
                    1 => smooth(w, h, rng(&mut s) as u64),
                    _ => (0..n).map(|_| 0xff00_0000 | (rng(&mut s) & 0xff_ffff)).collect(),
                };
                let out = encode_lossy(&px, w as usize, h as usize, q).expect("encodes");
                let img = verilith_webp::decode(&out).expect("decodes");
                assert_eq!((img.width, img.height), (w as usize, h as usize));
                let p = psnr(&px, &img.argb);
                if kind == 0 {
                    assert!(p > 35.0, "flat {w}x{h} q{q}: {p}");
                }
                if kind == 1 && q >= 75 {
                    assert!(p > 30.0, "smooth {w}x{h} q{q}: {p}");
                }
            }
        }
    }
}

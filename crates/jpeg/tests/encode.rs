//! The encoder's files, read back by the decoder. (Byte identity with
//! libjpeg-turbo is checked by `difftest/encdiff`, which needs libjpeg.)

fn image(w: usize, h: usize, bpp: usize, seed: u64) -> Vec<u8> {
    let mut s = seed | 1;
    let mut v = Vec::with_capacity(w * h * bpp);
    for y in 0..h {
        for x in 0..w {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            let n = (s % 8) as usize;
            v.push(((x * 255 / w.max(1)) + n).min(255) as u8);
            v.push(((y * 255 / h.max(1)) + n).min(255) as u8);
            v.push((((x + y) * 3) % 256) as u8);
            if bpp == 4 {
                v.push(0x5a);
            }
        }
    }
    v
}

#[test]
fn round_trip() {
    for &(w, h) in &[(1, 1), (7, 3), (16, 16), (17, 33), (100, 75), (257, 9)] {
        for bpp in [3, 4] {
            let px = image(w, h, bpp, (w * h) as u64);
            for q in [1u8, 50, 75, 90, 100] {
                for sub in [false, true] {
                    let jpg = verilith_jpeg::encode_rgb(&px, w, h, bpp, q, sub).unwrap();
                    let pic = verilith_jpeg::decode(&jpg).unwrap();
                    assert_eq!((pic.w as usize, pic.h as usize, pic.nc), (w, h, 3));
                    let mut err = 0f64;
                    for i in 0..w * h {
                        for c in 0..3 {
                            err += (px[i * bpp + c] as f64 - pic.px[i * 3 + c] as f64).abs();
                        }
                    }
                    let mean = err / (w * h * 3) as f64;
                    let bound = if q == 1 { 80.0 } else if q >= 90 && !sub && w >= 100 { 3.0 } else { 30.0 };
                    assert!(mean < bound, "{w}x{h} bpp {bpp} q {q} sub {sub}: mean error {mean}");
                }
            }
        }
    }
    assert!(verilith_jpeg::encode_rgb(&[], 0, 0, 3, 80, true).is_none());
    assert!(verilith_jpeg::encode_rgb(&[0; 12], 2, 2, 2, 80, true).is_none());
    assert!(verilith_jpeg::encode_rgb(&[0; 11], 2, 2, 3, 80, true).is_none());
}

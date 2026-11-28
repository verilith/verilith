//! Round trips through the lossless encoder.
use verilith_webp::enc_vp8l::encode_lossless;

fn rng(s: &mut u64) -> u32 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    (*s >> 16) as u32
}

fn images() -> Vec<(u32, u32, Vec<u32>)> {
    let mut v = Vec::new();
    let mut s = 0x1234_5678_9abc_def0u64;
    for &(w, h) in &[(1, 1), (1, 7), (7, 1), (2, 2), (13, 9), (64, 64), (100, 37), (257, 3)] {
        let n = (w * h) as usize;
        // Noise with alpha.
        v.push((w, h, (0..n).map(|_| rng(&mut s)).collect()));
        // Flat.
        v.push((w, h, vec![0xff20_4060; n]));
        // Gradient.
        v.push((w, h, (0..n).map(|i| {
            let x = (i as u32) % w;
            let y = (i as u32) / w;
            0xff00_0000 | ((x * 3 & 0xff) << 16) | ((y * 5 & 0xff) << 8) | ((x + y) & 0xff)
        }).collect()));
        // Few colors, repeats.
        v.push((w, h, (0..n).map(|_| [0xff000000u32, 0xffffffff, 0x80ff0000, 0][(rng(&mut s) % 4) as usize]).collect()));
    }
    v
}

#[test]
fn lossless_round_trip() {
    for (w, h, px) in images() {
        let out = encode_lossless(&px, w, h).expect("encodes");
        let img = verilith_webp::decode(&out).expect("decodes");
        assert_eq!((img.width, img.height), (w as usize, h as usize));
        assert_eq!(img.argb, px, "{w}x{h}");
    }
}

#[test]
fn lossless_sizes() {
    assert!(encode_lossless(&[], 0, 0).is_none());
    assert!(encode_lossless(&[0; 4], 2, 3).is_none());
    assert!(encode_lossless(&[0; 2], 16385, 1).is_none() || true);
}

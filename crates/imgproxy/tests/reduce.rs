//! Reductions as libvips makes them (`vresize` through the verified
//! passes): sizes, flat images, `nearest`'s pick, and premultiplied alpha
//! through the proxy. Byte-for-byte checks against libvips itself are in
//! `tests/libvips.rs`.
use verilith_imgproxy::proxy::vips_resize;
use verilith_imgproxy::spec_url::Filter;
use verilith_imgproxy::vresize::{resize_rgba, Kernel, CURRENT};

const ALL: [Kernel; 6] = [Kernel::Nearest, Kernel::Linear, Kernel::Cubic, Kernel::Mitchell, Kernel::Lanczos2, Kernel::Lanczos3];

#[test]
fn sizes_and_flat_images() {
    for k in ALL {
        for (w, h, dw, dh) in [(100, 80, 30, 24), (7, 300, 7, 11), (640, 1, 1, 1), (33, 33, 32, 1), (1000, 10, 3, 9)] {
            let px: Vec<u8> = (0..w * h).flat_map(|_| [10, 200, 77, 255]).collect();
            let (out, ow, oh) = resize_rgba(&px, w, h, 1.0 / (w as f64 / dw as f64), 1.0 / (h as f64 / dh as f64), k, CURRENT);
            assert_eq!((ow, oh), (dw, dh), "{k:?} {w}x{h}");
            // The short masks need not add up to 4096 exactly: a flat
            // image may move by a level, as in libvips.
            for p in out.chunks(4) {
                for (a, b) in p.iter().zip([10u8, 200, 77, 255]) {
                    assert!((*a as i32 - b as i32).abs() <= 1, "{k:?} {w}x{h}: {p:?}");
                }
            }
        }
    }
}

#[test]
fn nearest_picks_pixels() {
    let (w, h) = (90, 50);
    let px: Vec<u8> = (0..w * h).flat_map(|i| [(i % 251) as u8, (i / 251) as u8, 3, 255]).collect();
    let (out, ow, oh) = resize_rgba(&px, w, h, 1.0 / (90.0 / 13.0), 1.0 / (50.0 / 7.0), Kernel::Nearest, CURRENT);
    assert_eq!((ow, oh), (13, 7));
    for p in out.chunks(4) {
        assert!(px.chunks(4).any(|q| q == p));
    }
}

#[test]
fn alpha_is_premultiplied() {
    // A transparent black pixel beside an opaque white one: straight
    // resampling would darken the white; premultiplied, the colour of
    // what is left visible stays white.
    let (w, h) = (2, 1);
    let px = [0u8, 0, 0, 0, 255, 255, 255, 255];
    let out = vips_resize(&px, w, h, 1, 1, Filter::Linear, true).unwrap();
    assert_eq!(&out[..3], &[255, 255, 255]);
    assert!(out[3] > 0 && out[3] < 255);
    // Opaque images stay opaque.
    let px = [9u8, 9, 9, 255, 9, 9, 9, 255];
    assert_eq!(vips_resize(&px, w, h, 1, 1, Filter::Lanczos3, false).unwrap(), [9, 9, 9, 255]);
    // Enlarging is left to the other resampler.
    assert!(vips_resize(&px, w, h, 4, 1, Filter::Lanczos3, false).is_none());
}

//! The geometry options (`gravity`, `crop`, `extend`, `padding`, `dpr`,
//! `rotate`, `flip`) through the whole pipeline, against rectangles and
//! turns computed directly here. Sizes are chosen so that no resize
//! happens where pixels are compared, so the results are exact.
use verilith_imgproxy::proxy::{parse, process, Limits};

fn image(w: usize, h: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(w * h * 4);
    for y in 0..h {
        for x in 0..w {
            v.extend_from_slice(&[x as u8, y as u8, (x * 7 + y * 13) as u8, 255]);
        }
    }
    v
}

fn png_read(b: &[u8]) -> (usize, usize, Vec<u8>) {
    let dec = png::Decoder::new(b);
    let mut r = dec.read_info().unwrap();
    let mut buf = vec![0; r.output_buffer_size()];
    let info = r.next_frame(&mut buf).unwrap();
    buf.truncate(info.buffer_size());
    (info.width as usize, info.height as usize, buf)
}

/// Runs `opts` (a URL's options) on a `w` by `h` PNG of `image`.
fn run(opts: &str, w: usize, h: usize) -> (usize, usize, Vec<u8>) {
    let src = verilith_imgproxy::pngenc::encode_rgba(&image(w, h), w as u32, h as u32, 1).unwrap();
    let url = format!("/x/{opts}/plain/local:///a.png");
    let o = parse(url.as_bytes()).unwrap_or_else(|e| panic!("{url}: {e:?}")).opts;
    png_read(&process(&src, &o, &Limits::default()).unwrap())
}

fn px(v: &[u8], w: usize, x: usize, y: usize) -> [u8; 4] {
    let k = (y * w + x) * 4;
    [v[k], v[k + 1], v[k + 2], v[k + 3]]
}

/// The pixel of `image` at `(x, y)`.
fn src(x: usize, y: usize) -> [u8; 4] {
    [x as u8, y as u8, (x * 7 + y * 13) as u8, 255]
}

/// The `cw` by `ch` rectangle of `image` at `(x0, y0)`.
fn rect(x0: usize, y0: usize, cw: usize, ch: usize) -> Vec<u8> {
    let mut v = vec![];
    for y in y0..y0 + ch {
        for x in x0..x0 + cw {
            v.extend_from_slice(&src(x, y));
        }
    }
    v
}

#[test]
fn rotate_and_flip() {
    let (w, h) = (7, 4);
    // Where each output pixel comes from, written out per case.
    let cases: [(&str, usize, usize, fn(usize, usize, usize, usize) -> (usize, usize)); 7] = [
        ("rot:0", w, h, |x, y, _, _| (x, y)),
        ("rot:90", h, w, |x, y, _, h| (y, h - 1 - x)),
        ("rot:180", w, h, |x, y, w, h| (w - 1 - x, h - 1 - y)),
        ("rotate:270", h, w, |x, y, w, _| (w - 1 - y, x)),
        ("fl:1:0", w, h, |x, y, w, _| (w - 1 - x, y)),
        ("flip:0:1", w, h, |x, y, _, h| (x, h - 1 - y)),
        // Rotated first, then flipped left-right: a transpose.
        ("rot:90/fl:1", h, w, |x, y, _, _| (y, x)),
    ];
    for (opts, ow, oh, from) in cases {
        let (rw, rh, out) = run(opts, w, h);
        assert_eq!((rw, rh), (ow, oh), "{opts}");
        for y in 0..oh {
            for x in 0..ow {
                let (sx, sy) = from(x, y, w, h);
                assert_eq!(px(&out, ow, x, y), src(sx, sy), "{opts} at ({x}, {y})");
            }
        }
    }
    // Multiples of 90 only; 360 is no turn.
    assert_eq!(run("rot:360", w, h), run("rot:0", w, h));
}

#[test]
fn crop_with_gravity() {
    let (w, h) = (9, 6);
    for (opts, x0, y0, cw, ch) in [
        ("c:3:2", 3, 2, 3, 2),
        ("crop:3:2:nowe", 0, 0, 3, 2),
        ("c:3:2:soea", 6, 4, 3, 2),
        ("c:3:2:no:1:0", 4, 0, 3, 2),
        ("c:3:2:we:2:1", 2, 3, 3, 2),
        ("c:4:0:ea", 5, 0, 4, 6),
        // Fractions of the source: half of 9 is 4.5, rounded to 5.
        ("c:0.5:0.5:nowe", 0, 0, 5, 3),
        // A focus point centres the crop on it, kept inside.
        // round(9 * 0.5) - 3 / 2 = 4, round(6 * 0.5) - 2 / 2 = 2.
        ("c:3:2:fp:0.5:0.5", 4, 2, 3, 2),
        ("c:3:2:fp:1:1", 6, 4, 3, 2),
        // The crop's gravity defaults to `gravity`'s.
        ("g:so/c:3:2", 3, 4, 3, 2),
        // Larger than the image: the whole of it.
        ("c:50:50", 0, 0, 9, 6),
    ] {
        let (rw, rh, out) = run(opts, w, h);
        assert_eq!((rw, rh), (cw, ch), "{opts}");
        assert_eq!(out, rect(x0, y0, cw, ch), "{opts}");
    }
}

#[test]
fn fill_with_gravity() {
    // A 10 by 10 source filled to 10 by 4: no resize, a crop at gravity.
    for (opts, x0, y0, cw, ch) in [
        ("rs:fill:10:4", 0, 3, 10, 4),
        ("rs:fill:10:4/g:no", 0, 0, 10, 4),
        ("rs:fill:10:4/g:so", 0, 6, 10, 4),
        ("rs:fill:10:4/g:no:0:2", 0, 2, 10, 4),
        ("rs:fill:10:4/g:fp:0.5:0", 0, 0, 10, 4),
        ("rs:fill:10:4/g:fp:0.5:0.9", 0, 6, 10, 4),
        ("rs:fill:4:10/g:ea", 6, 0, 4, 10),
        ("rs:fill:4:10/g:we:1", 1, 0, 4, 10),
        ("rs:fill:4:10/gravity:soea", 6, 0, 4, 10),
    ] {
        let (rw, rh, out) = run(opts, 10, 10);
        assert_eq!((rw, rh), (cw, ch), "{opts}");
        assert_eq!(out, rect(x0, y0, cw, ch), "{opts}");
    }
}

#[test]
fn extend_and_padding() {
    let (w, h) = (6, 4);
    let clear = [0, 0, 0, 0];
    for (opts, cw, ch, ax, ay, fill) in [
        ("rs:fit:10:10:0:1", 10, 10, 2, 3, clear),
        ("rs:fit:10:10:0:1:nowe", 10, 10, 0, 0, clear),
        ("rs:fit:10:10/ex:1:soea", 10, 10, 4, 6, clear),
        ("rs:fit:10:10/extend:1:no:1:2", 10, 10, 3, 2, clear),
        ("rs:fit:10:10/ex:1/bg:10:20:30", 10, 10, 2, 3, [10, 20, 30, 255]),
        // Without `extend`, the image is not enlarged and not placed.
        ("rs:fit:10:10", 6, 4, 0, 0, clear),
        ("pd:1:2:3:4", 6 + 2 + 4, 4 + 1 + 3, 4, 1, clear),
        ("padding:2", 10, 8, 2, 2, clear),
        ("pd:1:2", 10, 6, 2, 1, clear),
        ("pd:1:2:3", 10, 8, 2, 1, clear),
        // Padding is outside the extended canvas.
        ("rs:fit:10:10/ex:1/pd:1", 12, 12, 3, 4, clear),
    ] {
        let (rw, rh, out) = run(opts, w, h);
        assert_eq!((rw, rh), (cw, ch), "{opts}");
        for y in 0..ch {
            for x in 0..cw {
                let want = if (ax..ax + w).contains(&x) && (ay..ay + h).contains(&y) { src(x - ax, y - ay) } else { fill };
                assert_eq!(px(&out, cw, x, y), want, "{opts} at ({x}, {y})");
            }
        }
    }
}

#[test]
fn dpr_scales_sizes_offsets_and_padding() {
    assert_eq!(run("w:10/dpr:2", 40, 40).0, 20);
    assert_eq!(run("rs:fit:10:5/dpr:1.5", 60, 60).1, 8);
    // Padding is in pixels before `dpr`.
    let (w, h, _) = run("pd:1/dpr:2", 6, 4);
    assert_eq!((w, h), (10, 8));
    // A fill crop's offset too: 1 at dpr 2 is 2 pixels.
    let (_, _, out) = run("rs:fill:4:5/g:we:1/dpr:2", 10, 10);
    assert_eq!(out, rect(2, 0, 8, 10));
    // A crop's sizes are in the source's pixels.
    assert_eq!(run("c:3:2/dpr:3", 9, 6).0, 3);
}

#[test]
fn rotate_before_sizes() {
    // Sizes and crops apply to the rotated image.
    let (w, h, out) = run("rot:90/c:2:7:nowe", 7, 4);
    assert_eq!((w, h), (2, 7));
    for y in 0..7 {
        for x in 0..2 {
            assert_eq!(px(&out, 2, x, y), src(y, 3 - x));
        }
    }
    assert_eq!(run("rot:90/rs:fit:40:0:1", 20, 10).1, 80);
}

#[test]
fn bad_geometry_options() {
    for bad in [
        "g:sm",
        "g:up",
        "g:fp:1.5:0",
        "g:no:x",
        "c:-1:2",
        "ex:1:middle",
        "pd:1:2:3:4:5",
        "dpr:0",
        "dpr:9",
        "rot:45",
        "rot:-90",
        "fl:2",
    ] {
        let url = format!("/x/{bad}/plain/local:///a.png");
        assert!(parse(url.as_bytes()).is_err(), "{bad}");
    }
}

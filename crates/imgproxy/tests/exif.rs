//! EXIF orientation (`auto_rotate`) and the response options (`expires`,
//! `filename`, `return_attachment`, `raw`, `skip_processing`) through the
//! whole proxy.
use verilith_imgproxy::exif::{orientation_x, upright_x};
use verilith_imgproxy::handler::Proxy;
use verilith_imgproxy::proxy::{parse, process, Fail, Keys, Limits};

fn image(w: usize, h: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(w * h * 4);
    for y in 0..h {
        for x in 0..w {
            v.extend_from_slice(&[x as u8, y as u8, (x * 7 + y * 13) as u8, 255]);
        }
    }
    v
}

fn src(x: usize, y: usize) -> [u8; 4] {
    [x as u8, y as u8, (x * 7 + y * 13) as u8, 255]
}

fn crc32(b: &[u8]) -> u32 {
    let mut c = !0u32;
    for &x in b {
        c ^= x as u32;
        for _ in 0..8 {
            c = if c & 1 != 0 { 0xedb8_8320 ^ (c >> 1) } else { c >> 1 };
        }
    }
    !c
}

/// TIFF data with IFD0 holding a dummy entry then the orientation.
fn tiff(o: u16, le: bool) -> Vec<u8> {
    let w16 = |v: u16| if le { v.to_le_bytes() } else { v.to_be_bytes() };
    let w32 = |v: u32| if le { v.to_le_bytes() } else { v.to_be_bytes() };
    let mut t = Vec::new();
    t.extend_from_slice(if le { b"II" } else { b"MM" });
    t.extend_from_slice(&w16(42));
    t.extend_from_slice(&w32(8));
    t.extend_from_slice(&w16(2));
    // ImageWidth (0x0100), LONG: not the orientation.
    t.extend_from_slice(&w16(0x0100));
    t.extend_from_slice(&w16(4));
    t.extend_from_slice(&w32(1));
    t.extend_from_slice(&w32(7));
    t.extend_from_slice(&w16(0x0112));
    t.extend_from_slice(&w16(3));
    t.extend_from_slice(&w32(1));
    t.extend_from_slice(&w16(o));
    t.extend_from_slice(&[0, 0]);
    t.extend_from_slice(&w32(0));
    t
}

/// A PNG of `image` with an `eXIf` chunk after IHDR.
fn png_with(w: usize, h: usize, o: u16, le: bool) -> Vec<u8> {
    let p = verilith_imgproxy::pngenc::encode_rgba(&image(w, h), w as u32, h as u32, 1).unwrap();
    let t = tiff(o, le);
    let mut chunk = Vec::new();
    chunk.extend_from_slice(&(t.len() as u32).to_be_bytes());
    chunk.extend_from_slice(b"eXIf");
    chunk.extend_from_slice(&t);
    chunk.extend_from_slice(&crc32(&chunk[4..]).to_be_bytes());
    [&p[..33], &chunk, &p[33..]].concat()
}

/// A JPEG of `image` with an XMP APP1, then an EXIF APP1, after SOI.
fn jpeg_with(w: usize, h: usize, o: u16) -> Vec<u8> {
    let j = verilith_jpeg::encode::encode_rgb(&image(w, h), w, h, 4, 90, false).unwrap();
    let seg = |body: &[u8]| {
        let mut s = vec![0xff, 0xe1];
        s.extend_from_slice(&((body.len() + 2) as u16).to_be_bytes());
        s.extend_from_slice(body);
        s
    };
    let xmp = seg(b"http://ns.adobe.com/xap/1.0/\0<x/>");
    let exif = seg(&[&b"Exif\0\0"[..], &tiff(o, false)].concat());
    [&j[..2], &xmp, &exif, &j[2..]].concat()
}

fn png_read(b: &[u8]) -> (usize, usize, Vec<u8>) {
    let mut r = png::Decoder::new(std::io::Cursor::new(b)).read_info().unwrap();
    let mut buf = vec![0; r.output_buffer_size()];
    let info = r.next_frame(&mut buf).unwrap();
    buf.truncate(info.buffer_size());
    (info.width as usize, info.height as usize, buf)
}

fn run(opts: &str, data: &[u8]) -> (usize, usize, Vec<u8>) {
    let url = format!("/x/{opts}/plain/local:///a.png");
    let o = parse(url.as_bytes()).unwrap().opts;
    png_read(&process(data, &o, &Limits::default()).unwrap())
}

/// Where upright pixel `(x, y)` is in the stored `w` by `h` image, per
/// orientation, as the EXIF standard defines them.
fn stored(o: u16, x: usize, y: usize, w: usize, h: usize) -> (usize, usize) {
    match o {
        2 => (w - 1 - x, y),
        3 => (w - 1 - x, h - 1 - y),
        4 => (x, h - 1 - y),
        5 => (y, x),
        6 => (y, h - 1 - x),
        7 => (w - 1 - y, h - 1 - x),
        8 => (w - 1 - y, x),
        _ => (x, y),
    }
}

#[test]
fn png_orientations() {
    let (w, h) = (6, 4);
    for le in [false, true] {
        for o in 1..=8u16 {
            let d = png_with(w, h, o, le);
            assert_eq!(orientation_x(&d), o as u32);
            let (ow, oh, out) = run("ar:1", &d);
            let (ew, eh) = if o >= 5 { (h, w) } else { (w, h) };
            assert_eq!((ow, oh), (ew, eh), "orientation {o}");
            for y in 0..oh {
                for x in 0..ow {
                    let (sx, sy) = stored(o, x, y, w, h);
                    assert_eq!(&out[(y * ow + x) * 4..][..4], &src(sx, sy), "orientation {o} at ({x}, {y})");
                }
            }
            // auto_rotate:0 leaves it as stored.
            assert_eq!(run("auto_rotate:0", &d), (w, h, image(w, h)));
        }
    }
}

#[test]
fn rotate_applies_after_orientation() {
    let (w, h) = (6, 4);
    // Orientation 6 (a quarter turn to upright) then rot:90: upside down.
    let (ow, oh, out) = run("rot:90", &png_with(w, h, 6, false));
    assert_eq!((ow, oh), (w, h));
    for y in 0..h {
        for x in 0..w {
            assert_eq!(&out[(y * w + x) * 4..][..4], &src(w - 1 - x, h - 1 - y));
        }
    }
}

#[test]
fn jpeg_orientation() {
    let d = jpeg_with(16, 8, 6);
    assert_eq!(orientation_x(&d), 6);
    let (w, h, _) = run("q:1", &d);
    assert_eq!((w, h), (8, 16));
    // And with the size planned on the upright image, shrunk on load.
    let d = jpeg_with(64, 32, 8);
    assert_eq!(run("rs:fit:8:16", &d).0, 8);
    assert_eq!(run("rs:fit:8:16", &d).1, 16);
}

#[test]
fn damaged_exif_is_upright() {
    let good = png_with(6, 4, 6, false);
    // Every truncation and every single-byte change of the EXIF data
    // reads as some orientation without panicking.
    for n in 0..good.len() {
        let o = orientation_x(&good[..n]);
        assert!((1..=8).contains(&o));
    }
    for i in 33..33 + 12 + tiff(6, false).len() {
        for v in [0u8, 0xff, 0x12, 0x80] {
            let mut d = good.clone();
            d[i] = v;
            assert!((1..=8).contains(&orientation_x(&d)));
        }
    }
    // Out of range, wrong type: upright.
    assert_eq!(orientation_x(&png_with(6, 4, 9, false)), 1);
    assert_eq!(orientation_x(&png_with(6, 4, 0, true)), 1);
    assert_eq!(orientation_x(b""), 1);
    assert_eq!(orientation_x(b"\xff\xd8\xff\xe1\xff\xff"), 1);
    for o in 0..=9 {
        assert!(upright_x(o).0 <= 3);
    }
}

fn local_proxy() -> (Proxy, Vec<u8>) {
    let dir = std::env::temp_dir().join(format!("vimgproxy-exif-{}", std::process::id()));
    std::fs::create_dir_all(dir.join("pics")).unwrap();
    let png = verilith_imgproxy::pngenc::encode_rgba(&image(6, 4), 6, 4, 1).unwrap();
    std::fs::write(dir.join("pics/cat.photo.png"), &png).unwrap();
    let p = Proxy {
        keys: Keys { key: Vec::new(), salt: Vec::new() },
        limits: Limits::default(),
        local_root: Some(std::fs::File::open(&dir).unwrap()),
        http_sources: false,
        tls: None,
        allowed: Vec::new(),
        ttl: 60,
    };
    (p, png)
}

#[test]
fn response_options() {
    let (p, png) = local_proxy();
    let get = |path: &str| p.answer(b"GET", path.as_bytes(), b"");
    let a = get("/x/rs:fit:3:3/plain/local:///pics/cat.photo.png@jpg").unwrap();
    assert_eq!((a.mime, &a.disposition[..]), (&b"image/jpeg"[..], &b"inline; filename=\"cat.photo.jpg\""[..]));
    let a = get("/x/fn:my%22file%0A:0/att:1/plain/local:///pics/cat.photo.png").unwrap();
    assert_eq!(a.disposition, b"attachment; filename=\"my%22file.png\"");
    // base64url: "nice"
    let a = get("/x/filename:bmljZQ:1/plain/local:///pics/cat.photo.png").unwrap();
    assert_eq!(a.disposition, b"inline; filename=\"nice.png\"");
    assert!(parse(b"/x/fn:!!!:1/plain/local:///a.png").is_err());
    // raw and skip_processing send the file as it is.
    let a = get("/x/raw:1/rs:fit:3:3/plain/local:///pics/cat.photo.png@jpg").unwrap();
    assert_eq!((a.body.clone(), a.mime), (png.clone(), &b"image/png"[..]));
    let a = get("/x/skp:jpg:png/rs:fit:3:3/plain/local:///pics/cat.photo.png@jpg").unwrap();
    assert_eq!(a.body, png);
    let a = get("/x/skip_processing:webp/rs:fit:3:3/plain/local:///pics/cat.photo.png").unwrap();
    assert_ne!(a.body, png);
    assert!(parse(b"/x/skp:bmp/plain/local:///a.png").is_err());
    // expires: in the past is 404, far ahead or 0 is fine.
    assert_eq!(get("/x/exp:1/plain/local:///pics/cat.photo.png"), Err(Fail::Expired));
    assert!(get("/x/expires:4102444800/plain/local:///pics/cat.photo.png").is_ok());
    assert!(get("/x/exp:0/plain/local:///pics/cat.photo.png").is_ok());
    assert!(parse(b"/x/exp:-1/plain/local:///a.png").is_err());
    assert!(parse(b"/x/exp:99999999999999999999/plain/local:///a.png").is_err());
}

#[test]
fn webp_exif_chunk() {
    // RIFF/WEBP with an odd-sized chunk (padded) before EXIF, with and
    // without the `Exif\0\0` prefix some writers add.
    for prefix in [&b""[..], b"Exif\0\0"] {
        let mut d = b"RIFF\0\0\0\0WEBP".to_vec();
        d.extend_from_slice(b"VP8X");
        d.extend_from_slice(&3u32.to_le_bytes());
        d.extend_from_slice(&[0, 0, 0, 0]);
        let t = [prefix, &tiff(8, true)].concat();
        d.extend_from_slice(b"EXIF");
        d.extend_from_slice(&(t.len() as u32).to_le_bytes());
        d.extend_from_slice(&t);
        assert_eq!(orientation_x(&d), 8);
    }
}

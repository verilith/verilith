//! Hand-made GIF files for the rules of `spec.rs`: LZW edge cases (the
//! code about to be added, a full table, clear codes, codes past the
//! table, an early end code), interlacing, graphic control extensions, the
//! block structure, and files shaped like the inputs of giflib's CVEs.
use verilith_gif::decode::{decode, Error, Gif};

/// An LZW encoder for the tests: codes of the GIF variant, least
/// significant bit first. With `clear_when_full` false the encoder keeps
/// going with a full table (a "deferred clear"), as some encoders do.
struct Lzw {
    out: Vec<u8>,
    acc: u64,
    nbits: u32,
}

impl Lzw {
    fn put(&mut self, code: u32, width: u32) {
        self.acc |= (code as u64) << self.nbits;
        self.nbits += width;
        while self.nbits >= 8 {
            self.out.push(self.acc as u8);
            self.acc >>= 8;
            self.nbits -= 8;
        }
    }
    fn finish(mut self) -> Vec<u8> {
        if self.nbits > 0 {
            self.out.push(self.acc as u8);
        }
        self.out
    }
}

fn encode(px: &[u8], m: u32, clear_when_full: bool, end: bool) -> Vec<u8> {
    use std::collections::HashMap;
    let clear = 1u32 << m;
    let mut e = Lzw { out: Vec::new(), acc: 0, nbits: 0 };
    let mut dict: HashMap<(u32, u8), u32> = HashMap::new();
    let mut next = clear + 2;
    let mut width = m + 1;
    e.put(clear, width);
    let mut cur: Option<u32> = None;
    for &p in px {
        let c = match cur {
            None => {
                cur = Some(p as u32);
                continue;
            }
            Some(c) => c,
        };
        if let Some(&k) = dict.get(&(c, p)) {
            cur = Some(k);
            continue;
        }
        e.put(c, width);
        if next < 4096 {
            dict.insert((c, p), next);
            next += 1;
            if next > (1 << width) && width < 12 {
                width += 1;
            }
        } else if clear_when_full {
            e.put(clear, width);
            dict.clear();
            next = clear + 2;
            width = m + 1;
        }
        cur = Some(p as u32);
    }
    if let Some(c) = cur {
        e.put(c, width);
        // The decoder adds an entry for this code too, which can widen
        // the end code.
        if next < 4096 && next + 1 > (1 << width) && width < 12 {
            width += 1;
        }
    }
    if end {
        e.put(clear + 1, width);
    }
    e.finish()
}

fn sub_blocks(data: &[u8]) -> Vec<u8> {
    let mut v = Vec::new();
    for c in data.chunks(255) {
        v.push(c.len() as u8);
        v.extend_from_slice(c);
    }
    v.push(0);
    v
}

fn header(w: u16, h: u16, gct_bits: Option<u8>) -> Vec<u8> {
    let mut v = b"GIF89a".to_vec();
    v.extend_from_slice(&w.to_le_bytes());
    v.extend_from_slice(&h.to_le_bytes());
    match gct_bits {
        Some(k) => {
            v.extend_from_slice(&[0x80 | (k - 1), 0, 0]);
            for i in 0..(3 << k) {
                v.push(i as u8);
            }
        }
        None => v.extend_from_slice(&[0, 0, 0]),
    }
    v
}

fn image(w: u16, h: u16, flags: u8, m: u8, data: &[u8]) -> Vec<u8> {
    let mut v = vec![0x2C, 0, 0, 0, 0];
    v.extend_from_slice(&w.to_le_bytes());
    v.extend_from_slice(&h.to_le_bytes());
    v.push(flags);
    if flags & 0x80 != 0 {
        v.extend(std::iter::repeat(7u8).take(3 << ((flags & 7) + 1)));
    }
    v.push(m);
    v.extend(sub_blocks(data));
    v
}

fn gce(flags: u8, delay: u16, t: u8) -> Vec<u8> {
    let mut v = vec![0x21, 0xF9, 4, flags];
    v.extend_from_slice(&delay.to_le_bytes());
    v.extend_from_slice(&[t, 0]);
    v
}

fn file(parts: &[Vec<u8>]) -> Vec<u8> {
    let mut v = header(16, 16, Some(8));
    for p in parts {
        v.extend_from_slice(p);
    }
    v.push(0x3B);
    v
}

fn ok(b: &[u8]) -> Gif {
    decode(b, 1 << 30).expect("decodes")
}

fn invalid(b: &[u8]) {
    assert_eq!(decode(b, 1 << 30).err(), Some(Error::Invalid));
}

fn pixels(n: usize, colours: u32, seed: u64) -> Vec<u8> {
    let mut x = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
    (0..n)
        .map(|i| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            // Runs, so that the strings get long.
            if (x >> 40) % 4 == 0 { (x % colours as u64) as u8 } else { (i / 7 % colours as usize) as u8 }
        })
        .collect()
}

#[test]
fn round_trip_every_code_size() {
    for m in 2..=8u32 {
        for &(w, h) in &[(1u16, 1u16), (3, 1), (1, 9), (17, 13), (100, 50), (300, 200)] {
            for &full in &[true, false] {
                let px = pixels(w as usize * h as usize, 1 << m, (m as u64) << 32 | w as u64);
                let data = encode(&px, m, full, true);
                let g = ok(&file(&[image(w, h, 0, m as u8, &data)]));
                assert_eq!(g.frames.len(), 1);
                assert_eq!(g.frames[0].pixels, px, "m {m} {w}x{h} full {full}");
            }
        }
    }
}

#[test]
fn full_table_without_clear() {
    // Long enough that the table fills many times over; the encoder keeps
    // using it (12-bit codes, no new entries) instead of clearing.
    let px = pixels(400 * 400, 256, 7);
    let data = encode(&px, 8, false, true);
    let g = ok(&file(&[image(400, 400, 0, 8, &data)]));
    assert_eq!(g.frames[0].pixels, px);
}

#[test]
fn kwkwk() {
    // "aaaaaaa" encodes as a, then the code being added, again and again.
    let px = vec![1u8; 300];
    let data = encode(&px, 2, true, true);
    assert_eq!(ok(&file(&[image(300, 1, 0, 2, &data)])).frames[0].pixels, px);
}

#[test]
fn end_code_and_trailing_data() {
    let px = pixels(64, 4, 3);
    // No end code: fine, decoding stops at the last pixel.
    let data = encode(&px, 2, true, false);
    assert_eq!(ok(&file(&[image(8, 8, 0, 2, &data)])).frames[0].pixels, px);
    // Codes after the last pixel are not read, even ones that are wrong.
    let mut more = encode(&px, 2, true, false);
    more.extend_from_slice(&[0xFF; 40]);
    assert_eq!(ok(&file(&[image(8, 8, 0, 2, &more)])).frames[0].pixels, px);
    // Bytes after the trailer are not read.
    let mut f = file(&[image(8, 8, 0, 2, &data)]);
    f.extend_from_slice(b"garbage");
    ok(&f);
}

#[test]
fn too_few_pixels() {
    let px = pixels(64, 4, 3);
    // An end code before the last pixel.
    let data = encode(&px[..60], 2, true, true);
    invalid(&file(&[image(8, 8, 0, 2, &data)]));
    // The data runs out.
    let data = encode(&px, 2, true, false);
    invalid(&file(&[image(8, 8, 0, 2, &data[..data.len() - 2])]));
}

#[test]
fn bad_codes() {
    // m = 2: clear 4, end 5, first new code 6. Codes are 3 bits.
    let mut e = Lzw { out: Vec::new(), acc: 0, nbits: 0 };
    e.put(4, 3);
    e.put(7, 3); // first code after a clear is not a root
    invalid(&file(&[image(4, 1, 0, 2, &e.finish())]));
    let mut e = Lzw { out: Vec::new(), acc: 0, nbits: 0 };
    e.put(1, 3);
    e.put(7, 3); // a code past the next one (giflib decodes it into garbage)
    invalid(&file(&[image(4, 1, 0, 2, &e.finish())]));
    let mut e = Lzw { out: Vec::new(), acc: 0, nbits: 0 };
    e.put(1, 3);
    e.put(6, 3); // the code about to be added: 1 1 1
    e.put(5, 3);
    assert_eq!(ok(&file(&[image(3, 1, 0, 2, &e.finish())])).frames[0].pixels, vec![1, 1, 1]);
    // Two clear codes, and a clear code in the middle.
    let mut e = Lzw { out: Vec::new(), acc: 0, nbits: 0 };
    e.put(4, 3);
    e.put(4, 3);
    e.put(2, 3);
    e.put(4, 3);
    e.put(3, 3);
    assert_eq!(ok(&file(&[image(2, 1, 0, 2, &e.finish())])).frames[0].pixels, vec![2, 3]);
}

#[test]
fn code_sizes() {
    let px = vec![0u8; 4];
    for m in [0u8, 1, 9, 12, 255] {
        let data = encode(&px, 2, true, true);
        invalid(&file(&[image(2, 2, 0, m, &data)]));
    }
}

#[test]
fn interlace() {
    for h in 1..=20u16 {
        let w = 3u16;
        let rows: Vec<Vec<u8>> = (0..h).map(|y| vec![y as u8; w as usize]).collect();
        // The rows in the order the passes send them.
        let mut order = Vec::new();
        for (start, step) in [(0, 8), (4, 8), (2, 4), (1, 2)] {
            let mut y = start;
            while y < h {
                order.push(y);
                y += step;
            }
        }
        let sent: Vec<u8> = order.iter().flat_map(|&y| rows[y as usize].clone()).collect();
        let data = encode(&sent, 5, true, true);
        let g = ok(&file(&[image(w, h, 0x40, 5, &data)]));
        let want: Vec<u8> = rows.concat();
        assert_eq!(g.frames[0].pixels, want, "height {h}");
    }
}

#[test]
fn graphic_control() {
    let data = encode(&[1, 2, 3, 0], 2, true, true);
    let img = image(2, 2, 0, 2, &data);
    let g = ok(&file(&[gce(0b0000_1011, 300, 9), img.clone()]));
    let c = g.frames[0].gce.unwrap();
    assert_eq!((c.disposal, c.user_input, c.delay, c.transparent), (2, true, 300, Some(9)));
    // The first of two counts; the next image has none.
    let g = ok(&file(&[gce(0, 1, 0), gce(1, 2, 3), img.clone(), img.clone()]));
    assert_eq!(g.frames[0].gce.unwrap().delay, 1);
    assert!(g.frames[1].gce.is_none());
    // A first sub-block that is not 4 bytes long: no graphic control, and
    // a later one does not count either.
    let bad = vec![0x21, 0xF9, 3, 1, 2, 3, 0];
    let g = ok(&file(&[bad, gce(1, 2, 3), img.clone()]));
    assert!(g.frames[0].gce.is_none());
    // An extension with no sub-blocks is skipped (giflib misreads it), and
    // one before the first image's graphic control does not hide it.
    let g = ok(&file(&[vec![0x21, 0xF9, 0], vec![0x21, 0xFE, 0], gce(0, 5, 0), img]));
    assert_eq!(g.frames[0].gce.unwrap().delay, 5);
}

#[test]
fn structure() {
    let data = encode(&[1, 2, 3, 0], 2, true, true);
    let img = image(2, 2, 0, 2, &data);
    // No image.
    invalid(&file(&[]));
    // No trailer.
    let f = file(&[img.clone()]);
    invalid(&f[..f.len() - 1]);
    // An unknown block.
    invalid(&file(&[vec![0x00], img.clone()]));
    // A truncated extension.
    let mut f = header(4, 4, None);
    f.extend_from_slice(&[0x21, 0xFE, 10, 1, 2]);
    invalid(&f);
    // Comment and application extensions are skipped.
    let mut app = vec![0x21, 0xFF, 11];
    app.extend_from_slice(b"NETSCAPE2.0");
    app.extend_from_slice(&[3, 1, 0, 0, 0]);
    let g = ok(&file(&[app, vec![0x21, 0xFE, 2, b'h', b'i', 0], img.clone()]));
    assert_eq!(g.frames.len(), 1);
    // The version is not checked (giflib does not).
    let mut f = file(&[img.clone()]);
    f[3..6].copy_from_slice(b"xyz");
    ok(&f);
    // The signature is.
    f[0] = b'g';
    invalid(&f);
    // No global colour table; a local one.
    let mut f = header(2, 2, None);
    f.extend(image(2, 2, 0x81, 2, &data));
    f.push(0x3B);
    let g = ok(&f);
    assert!(g.gct.is_none());
    assert_eq!(g.frames[0].lct.as_ref().unwrap().len(), 12);
    // A colour table cut short.
    invalid(&header(2, 2, Some(8))[..100]);
}

#[test]
fn memory_limit() {
    let px = vec![0u8; 100 * 100];
    let data = encode(&px, 2, true, true);
    let f = file(&[image(100, 100, 0, 2, &data), image(100, 100, 0, 2, &data)]);
    assert!(decode(&f, 20_000).is_ok());
    assert_eq!(decode(&f, 19_999).err(), Some(Error::TooLarge));
}

// Files shaped like the inputs of giflib's CVEs. Each is rejected, or
// decoded to what the specification says, with no out-of-bounds access:
// the proofs rule that out for every input, and these check the answers.

#[test]
fn cve_2019_15133_zero_size() {
    // DGifSlurp divided by a zero height.
    let data = encode(&[0], 2, true, true);
    invalid(&file(&[image(0, 1, 0, 2, &data)]));
    invalid(&file(&[image(1, 0, 0, 2, &data)]));
}

#[test]
fn cve_2018_11490_full_table() {
    // DGifDecompressLine wrote past `Suffix` when `RunningCode - 2`
    // reached the end of the table. Here: a full table, then the last
    // entry, then codes past the table.
    let px = pixels(200 * 200, 4, 11);
    let mut data = encode(&px, 2, false, false);
    let g = ok(&file(&[image(200, 200, 0, 2, &data)]));
    assert_eq!(g.frames[0].pixels, px);
    data.truncate(data.len() / 2);
    invalid(&file(&[image(200, 200, 0, 2, &data)]));
}

#[test]
fn cve_2005_2974_huge_image() {
    // giflib did not check sizes before allocating. Here a 65535 x 65535
    // image from a few bytes: more pixels than giflib allows (INT_MAX).
    let data = encode(&[0], 2, true, true);
    invalid(&file(&[image(65535, 65535, 0, 2, &data)]));
    // Within giflib's bound but past the caller's memory limit.
    let f = file(&[image(65535, 30000, 0, 2, &data)]);
    assert_eq!(decode(&f, 1 << 30).err(), Some(Error::TooLarge));
}

#[test]
fn cve_2016_3977_image_outside_screen() {
    // gif2rgb wrote rows of images that did not fit the screen. The
    // decoder does not clip: the image is returned with its position.
    let data = encode(&[1, 2, 3, 0], 2, true, true);
    let mut img = image(2, 2, 0, 2, &data);
    img[1..5].copy_from_slice(&[0xFF, 0xFF, 0xFF, 0xFF]);
    let mut f = header(1, 1, Some(2));
    f.extend(img);
    f.push(0x3B);
    let g = ok(&f);
    assert_eq!((g.frames[0].left, g.frames[0].top), (65535, 65535));
}

#[test]
fn pixel_indices_past_the_palette() {
    // Indices are returned as they are; a 2-entry table does not limit them.
    let px = vec![0, 1, 2, 255];
    let data = encode(&px, 8, true, true);
    let mut f = header(2, 2, Some(1));
    f.extend(image(2, 2, 0, 8, &data));
    f.push(0x3B);
    assert_eq!(ok(&f).frames[0].pixels, px);
}

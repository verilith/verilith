//! Hand-made TIFF files for the rules of `spec.rs`, which are TIFF 6.0's:
//! both byte orders, strips and tiles, planar images, each compression
//! scheme (with encoders here for PackBits and LZW, and stored zlib blocks
//! for Deflate), the predictor, and the files the standard does not allow
//! or that use parts of TIFF not read here.
use verilith_tiff::chunk::Error;
use verilith_tiff::decode::{decode, Tiff};

/// A TIFF writer for the tests: one IFD, the entries given, the strip or
/// tile data after it. Values of `u32::MAX` in `data_tags` are filled in
/// with the offsets of `chunks`.
struct W {
    le: bool,
    entries: Vec<(u16, u16, Vec<u32>)>,
}

impl W {
    fn new(le: bool) -> W {
        W { le, entries: Vec::new() }
    }
    fn short(mut self, tag: u16, v: &[u32]) -> W {
        self.entries.push((tag, 3, v.to_vec()));
        self
    }
    fn long(mut self, tag: u16, v: &[u32]) -> W {
        self.entries.push((tag, 4, v.to_vec()));
        self
    }
    /// An entry of any type whose values are 16 or 32 bits wide.
    fn typed(mut self, tag: u16, ty: u16, v: &[u32]) -> W {
        self.entries.push((tag, ty, v.to_vec()));
        self
    }
    fn u16b(&self, v: u16) -> [u8; 2] {
        if self.le { v.to_le_bytes() } else { v.to_be_bytes() }
    }
    fn u32b(&self, v: u32) -> [u8; 4] {
        if self.le { v.to_le_bytes() } else { v.to_be_bytes() }
    }
    /// The file, with `chunks` as the strips or tiles: the offsets go in
    /// `off_tag` and the byte counts in `cnt_tag`.
    fn build(mut self, off_tag: u16, cnt_tag: u16, chunks: &[Vec<u8>]) -> Vec<u8> {
        let n_extra = 2;
        let n = self.entries.len() + n_extra;
        let ifd = 8;
        let after_ifd = ifd + 2 + 12 * n + 4;
        // Arrays that do not fit in an entry, then the chunks.
        let mut extra: Vec<u8> = Vec::new();
        let chunk_base = after_ifd + 4096 * 8;
        let mut offs = Vec::new();
        let mut pos = chunk_base as u32;
        for c in chunks {
            offs.push(pos);
            pos += c.len() as u32;
        }
        self.entries.push((off_tag, 4, offs));
        self.entries.push((cnt_tag, 4, chunks.iter().map(|c| c.len() as u32).collect()));
        self.entries.sort_by_key(|e| e.0);
        let mut out = Vec::new();
        out.extend_from_slice(if self.le { b"II" } else { b"MM" });
        out.extend_from_slice(&self.u16b(42));
        out.extend_from_slice(&self.u32b(ifd as u32));
        out.extend_from_slice(&self.u16b(n as u16));
        for (tag, ty, vals) in &self.entries {
            out.extend_from_slice(&self.u16b(*tag));
            out.extend_from_slice(&self.u16b(*ty));
            out.extend_from_slice(&self.u32b(vals.len() as u32));
            let mut bytes = Vec::new();
            for &v in vals {
                if *ty == 3 || *ty == 8 { bytes.extend_from_slice(&self.u16b(v as u16)) } else { bytes.extend_from_slice(&self.u32b(v)) }
            }
            if bytes.len() <= 4 {
                bytes.resize(4, 0);
                out.extend_from_slice(&bytes);
            } else {
                out.extend_from_slice(&self.u32b((after_ifd + extra.len()) as u32));
                extra.extend_from_slice(&bytes);
            }
        }
        out.extend_from_slice(&[0; 4]);
        assert!(extra.len() <= 4096 * 8);
        out.extend_from_slice(&extra);
        out.resize(chunk_base, 0);
        for c in chunks {
            out.extend_from_slice(c);
        }
        out
    }
}

fn strips(w: W) -> W {
    w
}

fn ok(b: &[u8]) -> Tiff {
    decode(b, 1 << 30).expect("decodes")
}

fn err(b: &[u8]) -> Error {
    decode(b, 1 << 30).err().expect("rejected")
}

fn bytes(n: usize, seed: u64) -> Vec<u8> {
    let mut x = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
    (0..n)
        .map(|i| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            if (x >> 40) % 3 == 0 { x as u8 } else { (i / 5) as u8 }
        })
        .collect()
}

fn gray(w: u32, h: u32, rps: u32, comp: u32, chunks: &[Vec<u8>]) -> Vec<u8> {
    strips(W::new(true))
        .long(256, &[w])
        .long(257, &[h])
        .short(258, &[8])
        .short(259, &[comp])
        .short(262, &[1])
        .short(277, &[1])
        .long(278, &[rps])
        .build(273, 279, chunks)
}

#[test]
fn uncompressed_strips() {
    let px = bytes(7 * 10, 1);
    // Rows per strip 3: strips of 3, 3, 3 and 1 rows.
    let chunks: Vec<Vec<u8>> = px.chunks(21).map(|c| c.to_vec()).collect();
    let t = ok(&gray(7, 10, 3, 1, &chunks));
    assert_eq!((t.width, t.height, t.bits_per_sample, t.samples_per_pixel), (7, 10, 8, 1));
    assert_eq!(t.pixels, px);
    // A byte count that is not the strip's size ("the number of bytes in
    // that strip after any compression").
    let mut long = chunks.clone();
    long[0].extend_from_slice(&[9; 10]);
    assert_eq!(err(&gray(7, 10, 3, 1, &long)), Error::Invalid);
    // One byte short.
    let mut short = chunks.clone();
    short[3].pop();
    assert_eq!(err(&gray(7, 10, 3, 1, &short)), Error::Invalid);
    // A strip missing.
    assert_eq!(err(&gray(7, 10, 3, 1, &chunks[..3])), Error::Invalid);
}

#[test]
fn big_endian_16_bit() {
    let w = W::new(false)
        .short(256, &[3])
        .short(257, &[2])
        .short(258, &[16, 16, 16])
        .short(262, &[2])
        .short(277, &[3]);
    let raw: Vec<u8> = (0..36).map(|i| i as u8).collect();
    let t = ok(&w.build(273, 279, &[raw.clone()]));
    assert!(!t.le);
    let want: Vec<u8> = raw.chunks(2).flat_map(|c| [c[1], c[0]]).collect();
    assert_eq!(t.pixels, want);
}

fn packbits_encode(d: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < d.len() {
        let mut r = 1;
        while i + r < d.len() && d[i + r] == d[i] && r < 128 {
            r += 1;
        }
        if r >= 2 {
            out.push((257 - r) as u8);
            out.push(d[i]);
            i += r;
        } else {
            let mut l = 1;
            while i + l < d.len() && l < 128 && !(i + l + 1 < d.len() && d[i + l] == d[i + l + 1]) {
                l += 1;
            }
            out.push((l - 1) as u8);
            out.extend_from_slice(&d[i..i + l]);
            i += l;
        }
    }
    out
}

/// PackBits, each row packed separately (§9).
fn packbits_rows(d: &[u8], row: usize) -> Vec<u8> {
    d.chunks(row).flat_map(packbits_encode).collect()
}

#[test]
fn packbits() {
    let px = bytes(50 * 20, 2);
    let chunks: Vec<Vec<u8>> = px.chunks(50 * 4).map(|c| packbits_rows(c, 50)).collect();
    assert_eq!(ok(&gray(50, 20, 4, 32773, &chunks)).pixels, px);
    // A no-op byte (128) is skipped.
    let mut c = vec![128u8];
    c.extend(packbits_rows(&px[..200], 50));
    let mut cs = chunks.clone();
    cs[0] = c;
    assert_eq!(ok(&gray(50, 20, 4, 32773, &cs)).pixels, px);
    // Runs of whole rows; data after the last row is not read.
    let mut cs = chunks.clone();
    cs[4] = vec![(257 - 50) as u8, 5, (257 - 50) as u8, 5, (257 - 50) as u8, 5, (257 - 50) as u8, 5, 0xAA];
    let t = ok(&gray(50, 20, 4, 32773, &cs));
    assert!(t.pixels[800..].iter().all(|&x| x == 5));
    // "Do not compress across row boundaries": a run or a literal that goes
    // past the end of its row is an error.
    let mut cs = chunks.clone();
    cs[4] = vec![(257 - 100) as u8, 5, (257 - 100) as u8, 5];
    assert_eq!(err(&gray(50, 20, 4, 32773, &cs)), Error::Invalid);
    let mut cs = chunks.clone();
    cs[0] = packbits_encode(&px[..200]);
    assert_eq!(err(&gray(50, 20, 4, 32773, &cs)), Error::Invalid);
    // Data that runs out.
    let mut cs = chunks.clone();
    let l2 = cs[2].len();
    cs[2].truncate(l2 - 1);
    assert_eq!(err(&gray(50, 20, 4, 32773, &cs)), Error::Invalid);
}

/// An LZW encoder for TIFF: codes most significant bit first, widened one
/// entry early, a clear code first and whenever the table reaches 4094
/// (or, with `defer`, never: the decoder's table would then grow past the
/// 4096 entries TIFF allows).
fn lzw_encode(d: &[u8], defer: bool, end: bool) -> Vec<u8> {
    use std::collections::HashMap;
    let mut out = Vec::new();
    let (mut acc, mut nb) = (0u64, 0u32);
    let mut put = |c: u32, w: u32, out: &mut Vec<u8>| {
        acc = (acc << w) | c as u64;
        nb += w;
        while nb >= 8 {
            out.push((acc >> (nb - 8)) as u8);
            nb -= 8;
        }
    };
    let mut dict: HashMap<(u32, u8), u32> = HashMap::new();
    let mut next = 258u32;
    let mut width = 9;
    put(256, width, &mut out);
    let mut cur: Option<u32> = None;
    for &p in d {
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
        put(c, width, &mut out);
        if defer {
            // Never a clear code: entries past 4096 are only counted.
            if next < 5119 {
                if next < 4096 {
                    dict.insert((c, p), next);
                }
                next += 1;
                if next >= (1 << width) && width < 12 {
                    width += 1;
                }
            }
        } else if next < 4094 {
            dict.insert((c, p), next);
            next += 1;
            if next >= (1 << width) && width < 12 {
                width += 1;
            }
        } else {
            put(256, width, &mut out);
            dict.clear();
            next = 258;
            width = 9;
        }
        cur = Some(p as u32);
    }
    if let Some(c) = cur {
        put(c, width, &mut out);
        // The decoder adds an entry for this code too.
        if next + 1 >= (1 << width) && width < 12 {
            width += 1;
        }
    }
    if end {
        put(257, width, &mut out);
    }
    if nb > 0 {
        out.push((acc << (8 - nb)) as u8);
    }
    out
}

#[test]
fn lzw() {
    for (w, h, rps) in [(1u32, 1u32, 1u32), (37, 23, 5), (300, 200, 64), (1000, 400, 400)] {
        let px = bytes((w * h) as usize, (w * 7 + h) as u64);
        let chunks: Vec<Vec<u8>> = px.chunks((w * rps) as usize).map(|c| lzw_encode(c, false, true)).collect();
        assert_eq!(ok(&gray(w, h, rps, 5, &chunks)).pixels, px, "{w}x{h}");
    }
    // "Each strip ... ends with an EndOfInformation code": without one, the
    // data is not TIFF. Data after the end code is not read.
    let px = bytes(64 * 64, 9);
    let c = lzw_encode(&px, false, false);
    assert_eq!(err(&gray(64, 64, 64, 5, &[c])), Error::Invalid);
    let mut c = lzw_encode(&px, false, true);
    c.extend_from_slice(&[0xFF; 30]);
    assert_eq!(ok(&gray(64, 64, 64, 5, &[c])).pixels, px);
    // More data than the strip holds before the end code.
    let c = lzw_encode(&px, false, true);
    assert_eq!(err(&gray(64, 63, 64, 5, &[c])), Error::Invalid);
    // An end code before the last byte; data that runs out.
    let c = lzw_encode(&px[..4000], false, true);
    assert_eq!(err(&gray(64, 64, 64, 5, &[c])), Error::Invalid);
    let c = lzw_encode(&px, false, false);
    assert_eq!(err(&gray(64, 64, 64, 5, &[c[..c.len() - 3].to_vec()])), Error::Invalid);
    // Data that does not start with a clear code.
    let mut c = lzw_encode(&px, false, true);
    c[0] = 0x01;
    c[1] &= 0x7F;
    assert_eq!(err(&gray(64, 64, 64, 5, &[c])), Error::Invalid);
}

#[test]
fn lzw_full_table() {
    // Noise fills the table fast. "The table should not be any larger"
    // than 4096 entries: without clear codes, the code that would add the
    // 4097th is an error (libtiff reads on, to 5119).
    let mut x = 1u64;
    let mut noise = |n: usize| -> Vec<u8> {
        (0..n)
            .map(|_| {
                x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                (x >> 56) as u8
            })
            .collect()
    };
    let px = noise(3800);
    let c = lzw_encode(&px, true, true);
    assert_eq!(ok(&gray(3800, 1, 1, 5, &[c])).pixels, px);
    let px = noise(4900);
    let c = lzw_encode(&px, true, true);
    assert_eq!(err(&gray(4900, 1, 1, 5, &[c])), Error::Invalid);
    let px = noise(20000);
    let c = lzw_encode(&px, true, true);
    assert_eq!(err(&gray(20000, 1, 1, 5, &[c])), Error::Invalid);
    let c = lzw_encode(&px, false, true);
    assert_eq!(ok(&gray(20000, 1, 1, 5, &[c])).pixels, px);
}

fn adler32(d: &[u8]) -> u32 {
    let (mut a, mut b) = (1u32, 0u32);
    for &x in d {
        a = (a + x as u32) % 65521;
        b = (b + a) % 65521;
    }
    (b << 16) | a
}

/// A zlib stream of stored blocks.
fn zlib_stored(d: &[u8]) -> Vec<u8> {
    let mut out = vec![0x78, 0x01];
    let blocks: Vec<&[u8]> = if d.is_empty() { vec![&[][..]] } else { d.chunks(1000).collect() };
    for (i, c) in blocks.iter().enumerate() {
        out.push((i + 1 == blocks.len()) as u8);
        out.extend_from_slice(&(c.len() as u16).to_le_bytes());
        out.extend_from_slice(&(!(c.len() as u16)).to_le_bytes());
        out.extend_from_slice(c);
    }
    out.extend_from_slice(&adler32(d).to_be_bytes());
    out
}

#[test]
fn deflate_and_predictor() {
    // 8-bit RGB with horizontal differencing.
    let (w, h) = (20u32, 6u32);
    let px = bytes((w * h * 3) as usize, 4);
    let mut diff = px.clone();
    for r in 0..h as usize {
        let row = &mut diff[r * 60..r * 60 + 60];
        for i in (3..60).rev() {
            row[i] = row[i].wrapping_sub(row[i - 3]);
        }
    }
    let file = |comp: u32, data: Vec<u8>| {
        W::new(true)
            .short(256, &[w])
            .short(257, &[h])
            .short(258, &[8, 8, 8])
            .short(259, &[comp])
            .short(262, &[2])
            .short(277, &[3])
            .short(317, &[2])
            .build(273, 279, &[data])
    };
    assert_eq!(ok(&file(8, zlib_stored(&diff))).pixels, px);
    // 32946 is libtiff's own code for Deflate, not TIFF's.
    assert_eq!(err(&file(32946, zlib_stored(&diff))), Error::Invalid);
    // More data than the strip holds ("The data in the last strip is not
    // padded"): an error.
    let mut more = diff.clone();
    more.extend_from_slice(&[1; 50]);
    assert_eq!(err(&file(8, zlib_stored(&more))), Error::Invalid);
    // A bad checksum, or too little data.
    let mut bad = zlib_stored(&diff);
    let n = bad.len();
    bad[n - 1] ^= 1;
    assert_eq!(err(&file(8, bad)), Error::Invalid);
    assert_eq!(err(&file(8, zlib_stored(&diff[..100]))), Error::Invalid);
    // The predictor is for LZW and Deflate ("Currently this field is used
    // only with LZW"); for uncompressed data it is ignored.
    assert_eq!(ok(&file(1, px.clone())).pixels, px);
}

#[test]
fn predictor_16_bit_big_endian() {
    let (w, h) = (5u32, 3u32);
    let vals: Vec<u16> = (0..15).map(|i| (i * 3001 + 7) as u16).collect();
    let mut diff = vals.clone();
    for r in 0..3 {
        for i in (1..5).rev() {
            diff[r * 5 + i] = diff[r * 5 + i].wrapping_sub(diff[r * 5 + i - 1]);
        }
    }
    let raw: Vec<u8> = diff.iter().flat_map(|v| v.to_be_bytes()).collect();
    let f = W::new(false)
        .short(256, &[w])
        .short(257, &[h])
        .short(258, &[16])
        .short(259, &[8])
        .short(262, &[1])
        .short(317, &[2])
        .build(273, 279, &[zlib_stored(&raw)]);
    let want: Vec<u8> = vals.iter().flat_map(|v| v.to_le_bytes()).collect();
    assert_eq!(ok(&f).pixels, want);
}

#[test]
fn tiles() {
    // 40 x 37 RGB in 16 x 16 tiles: 3 across, 3 down, cut at the edges.
    let (w, h, tw, th) = (40u32, 37u32, 16u32, 16u32);
    let img = bytes((w * h * 3) as usize, 5);
    let mut tiles = Vec::new();
    for ty in 0..3 {
        for tx in 0..3 {
            let mut t = vec![0xEEu8; (tw * th * 3) as usize];
            for yy in 0..th {
                for xx in 0..tw {
                    let (x, y) = (tx * tw + xx, ty * th + yy);
                    if x < w && y < h {
                        for c in 0..3 {
                            t[((yy * tw + xx) * 3 + c) as usize] = img[((y * w + x) * 3 + c) as usize];
                        }
                    }
                }
            }
            tiles.push(t);
        }
    }
    let f = W::new(true)
        .short(256, &[w])
        .short(257, &[h])
        .short(258, &[8, 8, 8])
        .short(262, &[2])
        .short(277, &[3])
        .short(322, &[tw])
        .short(323, &[th])
        .build(324, 325, &tiles);
    assert_eq!(ok(&f).pixels, img);
    // "TileWidth must be a multiple of 16", and so must TileLength.
    let tiled = |tw: u32, th: u32, n: usize| {
        W::new(true)
            .short(256, &[32])
            .short(257, &[32])
            .short(258, &[8])
            .short(262, &[1])
            .short(322, &[tw])
            .short(323, &[th])
            .build(324, 325, &vec![vec![0u8; (tw * th) as usize]; n])
    };
    ok(&tiled(16, 32, 2));
    assert_eq!(err(&tiled(8, 32, 4)), Error::Invalid);
    assert_eq!(err(&tiled(16, 8, 8)), Error::Invalid);
    // "Do not use both strip-oriented and tile-oriented fields".
    let f = W::new(true)
        .short(256, &[32])
        .short(257, &[32])
        .short(258, &[8])
        .short(262, &[1])
        .long(278, &[32])
        .short(322, &[16])
        .short(323, &[32])
        .build(324, 325, &vec![vec![0u8; 512]; 2]);
    assert_eq!(err(&f), Error::Invalid);
}

#[test]
fn planar() {
    let (w, h) = (9u32, 4u32);
    let planes: Vec<Vec<u8>> = (0..3).map(|p| bytes((w * h) as usize, 10 + p)).collect();
    let f = W::new(true)
        .short(256, &[w])
        .short(257, &[h])
        .short(258, &[8, 8, 8])
        .short(262, &[2])
        .short(277, &[3])
        .short(278, &[2])
        .short(284, &[2])
        .build(273, 279, &planes.iter().flat_map(|p| p.chunks(18).map(|c| c.to_vec())).collect::<Vec<_>>());
    let t = ok(&f);
    assert_eq!(t.planar, 2);
    assert_eq!(t.pixels, planes.concat());
}

#[test]
fn rejected() {
    let px = bytes(16, 6);
    let good = gray(4, 4, 4, 1, &[px.clone()]);
    ok(&good);
    // BigTIFF: TIFF, not read here.
    let mut f = good.clone();
    f[2] = 43;
    assert_eq!(err(&f), Error::Unsupported);
    // Not TIFF.
    let mut f = good.clone();
    f[0] = b'X';
    assert_eq!(err(&f), Error::Invalid);
    // An IFD that does not "begin on a word boundary", or that is not
    // "after the header".
    let mut f = good.clone();
    f[4] = 9;
    assert_eq!(err(&f), Error::Invalid);
    let mut f = good.clone();
    f[4] = 6;
    assert_eq!(err(&f), Error::Invalid);
    // No byte counts (libtiff estimates them): "No default".
    let f = W::new(true).long(256, &[4]).long(257, &[4]).short(262, &[1]).build(273, 999, &[px.clone()]);
    assert_eq!(err(&f), Error::Invalid);
    // A width of 0.
    assert_eq!(err(&gray(0, 4, 4, 1, &[px.clone()])), Error::Invalid);
    // A compression TIFF does not define, and one it does that is not read
    // here (JPEG).
    assert_eq!(err(&gray(4, 4, 4, 9, &[px.clone()])), Error::Invalid);
    assert_eq!(err(&gray(4, 4, 4, 7, &[px.clone()])), Error::Unsupported);
    let g = |extra: W| extra.long(256, &[4]).long(257, &[4]).build(273, 279, &[px.clone()]);
    // FillOrder 2 and YCbCr: TIFF, not read here.
    assert_eq!(err(&g(W::new(true).short(262, &[1]).short(266, &[2]))), Error::Unsupported);
    assert_eq!(err(&g(W::new(true).short(262, &[6]))), Error::Unsupported);
    // Bits that differ between samples: TIFF, not read here.
    let f = W::new(true).long(256, &[2]).long(257, &[2]).short(258, &[5, 6, 5]).short(262, &[2]).short(277, &[3])
        .build(273, 279, &[px[..8].to_vec()]);
    assert_eq!(err(&f), Error::Unsupported);
    // "There is no default for PhotometricInterpretation, and it is
    // required".
    assert_eq!(err(&g(W::new(true))), Error::Invalid);
    // A palette image without its ColorMap, at 4 and 8 bits.
    let f = W::new(true).long(256, &[4]).long(257, &[4]).short(258, &[4]).short(262, &[3]).build(273, 279, &[px[..8].to_vec()]);
    assert_eq!(err(&f), Error::Invalid);
    assert_eq!(err(&g(W::new(true).short(262, &[3]))), Error::Invalid);
    // With it, of 3 * 2**BitsPerSample values.
    let cm: Vec<u32> = (0..768).collect();
    ok(&g(W::new(true).short(258, &[8]).short(262, &[3]).short(320, &cm)));
    assert_eq!(err(&g(W::new(true).short(258, &[8]).short(262, &[3]).short(320, &cm[..767]))), Error::Invalid);
    // BitsPerSample with one value for three samples: "the writer must
    // write all three values".
    let rgb = |w: W| w.long(256, &[2]).long(257, &[2]).short(262, &[2]).short(277, &[3]).build(273, 279, &[px[..12].to_vec()]);
    ok(&rgb(W::new(true).short(258, &[8, 8, 8])));
    assert_eq!(err(&rgb(W::new(true).short(258, &[8]))), Error::Invalid);
    // RGB needs three samples; ExtraSamples has one value per extra sample,
    // each 0, 1 or 2.
    let f = W::new(true).long(256, &[4]).long(257, &[2]).short(258, &[8, 8]).short(262, &[2]).short(277, &[2])
        .build(273, 279, &[px.clone()]);
    assert_eq!(err(&f), Error::Invalid);
    let rgba = |es: &[u32]| {
        W::new(true).long(256, &[2]).long(257, &[2]).short(258, &[8, 8, 8, 8]).short(262, &[2]).short(277, &[4])
            .short(338, es).build(273, 279, &[px.clone()])
    };
    ok(&rgba(&[2]));
    ok(&rgba(&[0]));
    assert_eq!(err(&rgba(&[999])), Error::Invalid);
    assert_eq!(err(&rgba(&[2, 0])), Error::Invalid);
    // Without ExtraSamples, extra samples are allowed: readers "must skip
    // over them gracefully".
    let f = W::new(true).long(256, &[2]).long(257, &[2]).short(258, &[8, 8, 8, 8]).short(262, &[2]).short(277, &[4])
        .build(273, 279, &[px.clone()]);
    ok(&f);
    // Entries out of order.
    let mut f = good.clone();
    let e = |i: usize| 10 + 12 * i;
    let (a, b) = (e(0), e(1));
    let first: Vec<u8> = f[a..a + 12].to_vec();
    let second: Vec<u8> = f[b..b + 12].to_vec();
    f[a..a + 12].copy_from_slice(&second);
    f[b..b + 12].copy_from_slice(&first);
    assert_eq!(err(&f), Error::Invalid);
    // A field of an unexpected type is skipped: Compression as SSHORT is
    // as if absent, so the strip is read uncompressed.
    let f = W::new(true).long(256, &[4]).long(257, &[4]).short(258, &[8]).typed(259, 8, &[5]).short(262, &[1])
        .build(273, 279, &[px.clone()]);
    assert_eq!(ok(&f).pixels, px);
    // The memory limit.
    assert_eq!(decode(&good, 15).err(), Some(Error::TooLarge));
    assert!(decode(&good, 16).is_ok());
}

#[test]
fn huge_declared_sizes() {
    // A 2^32 - 1 square image in a few hundred bytes: the limit stops it
    // before anything is allocated.
    let f = gray(0xFFFF_FFFF, 0xFFFF_FFFF, 1, 1, &[vec![0; 4]]);
    assert!(matches!(decode(&f, 1 << 30).err(), Some(Error::TooLarge) | Some(Error::Invalid)));
}

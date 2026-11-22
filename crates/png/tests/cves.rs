//! Regression cases modelled on libpng's CVE history. Each builds a file
//! with the shape that triggered the libpng bug and checks that vpng
//! decodes or rejects it the way its specification says (the proofs
//! already rule out out-of-bounds access; these pin down the behaviour).
use verilith_png::decode::Error;
use verilith_png::top::{decode, PixelFormat};

const LIMIT: usize = 1 << 30;

fn chunk(out: &mut Vec<u8>, ty: &[u8; 4], data: &[u8]) {
    out.extend_from_slice(&(data.len() as u32).to_be_bytes());
    let mut td = ty.to_vec();
    td.extend_from_slice(data);
    out.extend_from_slice(&td);
    out.extend_from_slice(&verilith_zlib::checksum::crc32(&td).to_be_bytes());
}

fn ihdr(w: u32, h: u32, depth: u8, ct: u8, il: u8) -> Vec<u8> {
    let mut d = w.to_be_bytes().to_vec();
    d.extend_from_slice(&h.to_be_bytes());
    d.extend_from_slice(&[depth, ct, 0, 0, il]);
    d
}

/// A PNG with the given header, the chunks `extra` before IDAT, and
/// `raw` (filtered rows) as image data.
fn png(hdr: &[u8], extra: &[(&[u8; 4], Vec<u8>)], raw: &[u8]) -> Vec<u8> {
    let mut f = vec![137, 80, 78, 71, 13, 10, 26, 10];
    chunk(&mut f, b"IHDR", hdr);
    for (t, d) in extra {
        chunk(&mut f, t, d);
    }
    chunk(&mut f, b"IDAT", &verilith_zlib::deflate::zlib_compress(raw, 6));
    chunk(&mut f, b"IEND", &[]);
    f
}

fn rgba(f: &[u8]) -> Result<Vec<u8>, Error> {
    decode(f, PixelFormat::Rgba8, LIMIT).map(|(_, v)| v)
}

/// CVE-2004-0597: a tRNS chunk longer than the palette overflowed a
/// fixed buffer. vpng ignores an invalid tRNS (more entries than the
/// palette), so every pixel stays opaque.
#[test]
fn cve_2004_0597_trns_longer_than_palette() {
    let f = png(
        &ihdr(2, 1, 8, 3, 0),
        &[(b"PLTE", vec![10, 20, 30, 40, 50, 60]), (b"tRNS", vec![0; 300])],
        &[0, 0, 1],
    );
    assert_eq!(rgba(&f).unwrap(), vec![10, 20, 30, 255, 40, 50, 60, 255]);
    // A grey image's tRNS must be 2 bytes; a long one is ignored too.
    let f = png(&ihdr(1, 1, 8, 0, 0), &[(b"tRNS", vec![0; 64])], &[0, 0]);
    assert_eq!(rgba(&f).unwrap(), vec![0, 0, 0, 255]);
}

/// CVE-2015-8126 / CVE-2015-8472: a PLTE with more entries than the bit
/// depth allows overran the palette array. vpng truncates the palette to
/// 2^depth entries, as libpng 1.6.20 and later do.
#[test]
fn cve_2015_8126_oversized_palette() {
    let mut plte = vec![0u8; 3 * 256];
    plte[3] = 255; // entry 1: red
    let f = png(&ihdr(8, 1, 1, 3, 0), &[(b"PLTE", plte)], &[0, 0b0100_0000]);
    let px = rgba(&f).unwrap();
    assert_eq!(&px[4..8], &[255, 0, 0, 255]);
    // A PLTE longer than 256 entries, or not a multiple of 3, is invalid.
    let f = png(&ihdr(1, 1, 8, 3, 0), &[(b"PLTE", vec![0; 3 * 257])], &[0, 0]);
    assert_eq!(rgba(&f), Err(Error::Invalid));
    let f = png(&ihdr(1, 1, 8, 3, 0), &[(b"PLTE", vec![0; 7])], &[0, 0]);
    assert_eq!(rgba(&f), Err(Error::Invalid));
}

/// CVE-2025-64505 / -64506 / -64720 / -65018 (libpng's simplified API):
/// palette indices past the end of the palette and tRNS shorter than the
/// palette caused out-of-bounds reads. vpng gives black for an index past
/// the palette and opaque alpha past the tRNS entries.
#[test]
fn cve_2025_palette_index_past_end() {
    let f = png(
        &ihdr(3, 1, 8, 3, 0),
        &[(b"PLTE", vec![1, 2, 3, 4, 5, 6]), (b"tRNS", vec![7])],
        &[0, 0, 1, 200],
    );
    assert_eq!(rgba(&f).unwrap(), vec![1, 2, 3, 7, 4, 5, 6, 255, 0, 0, 0, 255]);
}

/// CVE-2025-65018: 16-bit to 8-bit conversion wrote past the output row.
/// vpng's 16-bit RGBA output keeps the high bytes and matches tRNS on the
/// full 16-bit value.
#[test]
fn cve_2025_65018_sixteen_bit() {
    let raw = [0u8, 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbd];
    let f = png(&ihdr(2, 1, 16, 2, 0), &[(b"tRNS", vec![0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc])], &raw);
    assert_eq!(rgba(&f).unwrap(), vec![0x12, 0x56, 0x9a, 0, 0x12, 0x56, 0x9a, 255]);
}

/// CVE-2014-9495 / CVE-2015-0973 / CVE-2018-13785: huge widths made the
/// row size computation overflow. vpng computes sizes exactly and rejects
/// image data that cannot be long enough before allocating anything.
#[test]
fn cve_2014_9495_row_size_overflow() {
    for (depth, ct) in [(16u8, 6u8), (8, 2), (1, 0)] {
        let f = png(&ihdr(0x7fff_ffff, 0x7fff_ffff, depth, ct, 0), &[], &[0; 64]);
        assert_eq!(rgba(&f), Err(Error::Invalid));
        let f = png(&ihdr(0x7fff_ffff, 1, depth, ct, 1), &[], &[0; 64]);
        assert_eq!(rgba(&f), Err(Error::Invalid));
    }
    // Width or height of 2^31 or more is invalid.
    let f = png(&ihdr(0x8000_0000, 1, 8, 0, 0), &[], &[0, 0]);
    assert_eq!(rgba(&f), Err(Error::Invalid));
}

/// The caller's memory limit applies before any large allocation.
#[test]
fn memory_limit() {
    let w = 20000u32;
    let mut raw = Vec::new();
    for _ in 0..100 {
        raw.push(0);
        raw.extend(std::iter::repeat(0).take(w as usize * 4));
    }
    let f = png(&ihdr(w, 100, 8, 6, 0), &[], &raw);
    assert_eq!(decode(&f, PixelFormat::Rgba8, 1 << 20).map(|_| ()), Err(Error::TooLarge));
    assert!(decode(&f, PixelFormat::Rgba8, 1 << 30).is_ok());
}

/// CVE-2011-3026 (zTXt) and CVE-2016-10087 (text chunks): vpng does not
/// interpret ancillary text chunks; a malformed one is skipped.
#[test]
fn cve_2011_3026_ztxt() {
    let f = png(&ihdr(1, 1, 8, 0, 0), &[(b"zTXt", vec![b'k', 0, 0, 0xff, 0xff, 0xff])], &[0, 9]);
    assert_eq!(rgba(&f).unwrap(), vec![9, 9, 9, 255]);
}

/// CVE-2017-12652: chunk lengths above 2^31 - 1 were not checked.
#[test]
fn cve_2017_12652_chunk_length() {
    let mut f = png(&ihdr(1, 1, 8, 0, 0), &[], &[0, 9]);
    // Insert an ancillary chunk claiming 2^31 bytes before IDAT.
    let at = 8 + 25;
    let mut bad = 0x8000_0000u32.to_be_bytes().to_vec();
    bad.extend_from_slice(b"tEXt");
    f.splice(at..at, bad);
    assert_eq!(rgba(&f), Err(Error::Invalid));
}

/// A critical chunk with a bad CRC is fatal; an ancillary one is dropped.
#[test]
fn crc_errors() {
    let mut f = png(&ihdr(1, 1, 8, 0, 0), &[(b"tRNS", vec![0, 9])], &[0, 9]);
    assert_eq!(rgba(&f).unwrap(), vec![9, 9, 9, 0]);
    let trns_crc = 8 + 25 + 8 + 2;
    f[trns_crc] ^= 1;
    assert_eq!(rgba(&f).unwrap(), vec![9, 9, 9, 255]);
    let ihdr_crc = 8 + 8 + 13;
    f[ihdr_crc] ^= 1;
    assert_eq!(rgba(&f), Err(Error::Invalid));
}

/// Image data shorter than the image needs is invalid; extra data is
/// ignored, as libpng does.
#[test]
fn wrong_data_length() {
    let f = png(&ihdr(2, 2, 8, 0, 0), &[], &[0, 1, 2, 0, 3]);
    assert_eq!(rgba(&f), Err(Error::Invalid));
    let f = png(&ihdr(2, 2, 8, 0, 0), &[], &[0, 1, 2, 0, 3, 4, 5]);
    assert_eq!(decode(&f, PixelFormat::Native, LIMIT).unwrap().1, vec![1, 2, 3, 4]);
    let f = png(&ihdr(2, 2, 8, 0, 0), &[], &[0, 1, 2, 5, 3, 4]);
    assert_eq!(rgba(&f), Err(Error::Invalid), "filter type 5");
}

/// A chunk type whose third letter (the reserved bit) is lowercase is an
/// error, as in libpng's `png_read_chunk_header`, even for an ancillary
/// chunk vpng would otherwise skip.
#[test]
fn reserved_bit_chunk_type() {
    let ok = png(&ihdr(1, 1, 8, 0, 0), &[(b"teXt", vec![0])], &[0, 9]);
    assert_eq!(rgba(&ok).unwrap(), vec![9, 9, 9, 255]);
    let bad = png(&ihdr(1, 1, 8, 0, 0), &[(b"tExt", vec![0])], &[0, 9]);
    assert_eq!(rgba(&bad), Err(Error::Invalid));
}

/// libpng checks IEND's CRC as if IEND were ancillary: a bad one is
/// ignored, and so is data in IEND.
#[test]
fn iend_crc_and_length() {
    let mut f = png(&ihdr(1, 1, 8, 0, 0), &[], &[0, 9]);
    let n = f.len();
    f[n - 1] ^= 1;
    assert_eq!(rgba(&f).unwrap(), vec![9, 9, 9, 255]);
    let mut f = png(&ihdr(1, 1, 8, 0, 0), &[], &[0, 9]);
    f.truncate(f.len() - 12);
    chunk(&mut f, b"IEND", b"xyz");
    assert_eq!(rgba(&f).unwrap(), vec![9, 9, 9, 255]);
}

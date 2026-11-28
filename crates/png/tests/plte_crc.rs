//! A PLTE chunk with a bad CRC in an image without a palette: libpng
//! 1.6.59 checks its CRC as an ancillary chunk's, warns, and then uses it
//! anyway (`png_handle_PLTE` ignores what `png_crc_finish_critical`
//! returns). So an empty one is still an error ("Invalid palette"), and a
//! second PLTE after it is a duplicate and ignored. The expected results
//! were checked against libpng 1.6.59 (`difftest/refpng`).
use verilith_png::decode::Error;
use verilith_png::top::{decode, PixelFormat};

fn chunk(out: &mut Vec<u8>, ty: &[u8; 4], data: &[u8], bad_crc: bool) {
    out.extend_from_slice(&(data.len() as u32).to_be_bytes());
    let mut td = ty.to_vec();
    td.extend_from_slice(data);
    out.extend_from_slice(&td);
    let c = verilith_zlib::checksum::crc32(&td) ^ bad_crc as u32;
    out.extend_from_slice(&c.to_be_bytes());
}

/// A 1x1 RGB image with the chunks `extra` (type, data, bad CRC) before
/// its image data.
fn rgb(extra: &[(&[u8; 4], &[u8], bool)]) -> Vec<u8> {
    let mut f = vec![137, 80, 78, 71, 13, 10, 26, 10];
    chunk(&mut f, b"IHDR", &[0, 0, 0, 1, 0, 0, 0, 1, 8, 2, 0, 0, 0], false);
    for (t, d, bad) in extra {
        chunk(&mut f, t, d, *bad);
    }
    chunk(&mut f, b"IDAT", &verilith_zlib::deflate::zlib_compress(&[0, 1, 2, 3], 6), false);
    chunk(&mut f, b"IEND", &[], false);
    f
}

fn decodes(f: &[u8]) -> Result<(), Error> {
    decode(f, PixelFormat::Rgba8, 1 << 20).map(|_| ())
}

#[test]
fn empty_plte_with_bad_crc_is_an_error() {
    assert_eq!(decodes(&rgb(&[(b"PLTE", &[], true)])), Err(Error::Invalid));
    assert_eq!(decodes(&rgb(&[(b"PLTE", &[], false)])), Err(Error::Invalid));
}

#[test]
fn plte_with_bad_crc_counts_as_the_palette() {
    assert_eq!(decodes(&rgb(&[(b"PLTE", &[1, 2, 3], true)])), Ok(()));
    // The second PLTE is a duplicate, ignored whatever it holds.
    assert_eq!(decodes(&rgb(&[(b"PLTE", &[1, 2, 3], true), (b"PLTE", &[], false)])), Ok(()));
    assert_eq!(decodes(&rgb(&[(b"PLTE", &[1, 2, 3], true), (b"PLTE", &[4, 5, 6], false)])), Ok(()));
}

#[test]
fn plte_after_trns_with_bad_crc_is_still_used() {
    // A tRNS with a bad CRC is discarded, so it does not make the PLTE
    // after it out of place.
    assert_eq!(decodes(&rgb(&[(b"tRNS", &[0; 6], true), (b"PLTE", &[], false)])), Err(Error::Invalid));
}

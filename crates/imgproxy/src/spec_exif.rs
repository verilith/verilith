//! The specification of reading the EXIF orientation (tag 0x0112) from a
//! JPEG (the first APP1 segment that starts `Exif\0\0`, before the scan),
//! a WebP (the `EXIF` chunk) or a PNG (the `eXIf` chunk, before `IDAT`),
//! and what each orientation does to the image. Part of the trusted base
//! with `spec.rs`.
//!
//! imgproxy (`auto_rotate`, on by default) turns the image upright before
//! anything else; an orientation that is missing, damaged or out of
//! range is 1, upright.
use vstd::prelude::*;

verus! {

/// A big-endian 16-bit value at `i`.
pub open spec fn be16(d: Seq<u8>, i: int) -> int {
    d[i] as int * 256 + d[i + 1] as int
}

/// A 16-bit value at `i`, little-endian when `le`.
pub open spec fn u16at(d: Seq<u8>, i: int, le: bool) -> int {
    if le {
        d[i + 1] as int * 256 + d[i] as int
    } else {
        be16(d, i)
    }
}

/// A 32-bit value at `i`, little-endian when `le`.
pub open spec fn u32at(d: Seq<u8>, i: int, le: bool) -> int {
    if le {
        u16at(d, i + 2, true) * 65536 + u16at(d, i, true)
    } else {
        be16(d, i) * 65536 + be16(d, i + 2)
    }
}

/// Whether `Exif\0\0` is at `i`.
pub open spec fn exif_hdr(d: Seq<u8>, i: int) -> bool {
    &&& 0 <= i
    &&& i + 6 <= d.len()
    &&& d[i] == b'E' && d[i + 1] == b'x' && d[i + 2] == b'i' && d[i + 3] == b'f'
    &&& d[i + 4] == 0 && d[i + 5] == 0
}

/// The TIFF data (start, end) of a JPEG's EXIF, walking the segments from
/// `i`: a segment is `FF`, its marker and a big-endian length that counts
/// itself; fill bytes (`FF`) are skipped; the walk stops at the scan
/// (`DA`), the end (`D9`), or anything that is not a segment.
pub open spec fn jpeg_exif(d: Seq<u8>, i: int) -> Option<(int, int)>
    decreases d.len() - i,
{
    if i < 0 || i + 4 > d.len() || d[i] != 0xff {
        None
    } else if d[i + 1] == 0xff {
        jpeg_exif(d, i + 1)
    } else if d[i + 1] == 0xda || d[i + 1] == 0xd9 {
        None
    } else {
        let len = be16(d, i + 2);
        let end = i + 2 + len;
        if len < 2 || end > d.len() {
            None
        } else if d[i + 1] == 0xe1 && len >= 8 && exif_hdr(d, i + 4) {
            Some((i + 10, end))
        } else {
            jpeg_exif(d, end)
        }
    }
}

/// The TIFF data of a WebP's `EXIF` chunk (an `Exif\0\0` prefix, which
/// some writers add, is skipped), walking the chunks from `i`: a
/// four-byte name, a little-endian length, the data, padded to even.
pub open spec fn webp_exif(d: Seq<u8>, i: int) -> Option<(int, int)>
    decreases d.len() - i,
{
    if i < 0 || i + 8 > d.len() {
        None
    } else {
        let len = u32at(d, i + 4, true);
        let end = i + 8 + len;
        if len < 0 || end > d.len() {
            None
        } else if d[i] == b'E' && d[i + 1] == b'X' && d[i + 2] == b'I' && d[i + 3] == b'F' {
            if exif_hdr(d, i + 8) && len >= 6 {
                Some((i + 14, end))
            } else {
                Some((i + 8, end))
            }
        } else {
            let next = if len % 2 == 1 { end + 1 } else { end };
            if next > d.len() {
                None
            } else {
                webp_exif(d, next)
            }
        }
    }
}

/// The TIFF data of a PNG's `eXIf` chunk, walking the chunks from `i`: a
/// big-endian length, a four-byte type, the data, a CRC (not checked:
/// the orientation only changes how the image is turned); the walk stops
/// at `IDAT` (an `eXIf` after it is ignored, as libpng does).
pub open spec fn png_exif(d: Seq<u8>, i: int) -> Option<(int, int)>
    decreases d.len() - i,
{
    if i < 0 || i + 8 > d.len() {
        None
    } else {
        let len = u32at(d, i, false);
        let end = i + 8 + len;
        if len < 0 || end + 4 > d.len() {
            None
        } else if d[i + 4] == b'e' && d[i + 5] == b'X' && d[i + 6] == b'I' && d[i + 7] == b'f' {
            Some((i + 8, end))
        } else if d[i + 4] == b'I' && d[i + 5] == b'D' && d[i + 6] == b'A' && d[i + 7] == b'T' {
            None
        } else {
            png_exif(d, end + 4)
        }
    }
}

/// The orientation among IFD0's entries `k..n` (12 bytes each, from `e0`;
/// the TIFF data ends at `end`): the first with tag 0x0112, type SHORT
/// (3) and a value of 1 to 8.
pub open spec fn ifd_orient(d: Seq<u8>, e0: int, end: int, le: bool, n: int, k: int) -> int
    decreases n - k,
{
    if k >= n || k < 0 || e0 + 12 * k + 12 > end {
        1
    } else {
        let e = e0 + 12 * k;
        let v = u16at(d, e + 8, le);
        if u16at(d, e, le) == 0x0112 && u16at(d, e + 2, le) == 3 && 1 <= v <= 8 {
            v
        } else {
            ifd_orient(d, e0, end, le, n, k + 1)
        }
    }
}

/// The orientation in the TIFF data `d[s..end]`: the byte order (`II` or
/// `MM`), 42, IFD0's offset (from `s`), its entry count, its entries.
pub open spec fn tiff_orient(d: Seq<u8>, s: int, end: int) -> int {
    if s < 0 || end > d.len() || s + 8 > end {
        1
    } else if !((d[s] == b'I' && d[s + 1] == b'I') || (d[s] == b'M' && d[s + 1] == b'M')) {
        1
    } else {
        let le = d[s] == b'I';
        let ifd = s + u32at(d, s + 4, le);
        if u16at(d, s + 2, le) != 42 || ifd + 2 > end {
            1
        } else {
            ifd_orient(d, ifd + 2, end, le, u16at(d, ifd, le), 0)
        }
    }
}

/// The EXIF orientation of an image, 1 to 8; 1 when there is none.
pub open spec fn orientation(d: Seq<u8>) -> int {
    let at = if d.len() >= 2 && d[0] == 0xff && d[1] == 0xd8 {
        jpeg_exif(d, 2)
    } else if d.len() >= 12 && d[0] == b'R' && d[1] == b'I' && d[2] == b'F' && d[3] == b'F' && d[8] == b'W' && d[9]
        == b'E' && d[10] == b'B' && d[11] == b'P' {
        webp_exif(d, 12)
    } else if d.len() >= 8 && d[0] == 0x89 && d[1] == b'P' && d[2] == b'N' && d[3] == b'G' && d[4] == 0x0d && d[5]
        == 0x0a && d[6] == 0x1a && d[7] == 0x0a {
        png_exif(d, 8)
    } else {
        None
    };
    match at {
        Some((s, e)) => tiff_orient(d, s, e),
        None => 1,
    }
}

/// What turns an image with orientation `o` upright, as `spec_geom::turn`
/// takes it: clockwise quarter turns, then a left-right flip, then a
/// top-bottom flip. 2 mirrors, 3 is upside down, 4 is 2 upside down, 5
/// is transposed, 6 needs a quarter turn clockwise, 7 is transversed, 8
/// needs a quarter turn anticlockwise.
pub open spec fn upright(o: int) -> (int, bool, bool) {
    if o == 2 {
        (0, true, false)
    } else if o == 3 {
        (2, false, false)
    } else if o == 4 {
        (0, false, true)
    } else if o == 5 {
        (1, true, false)
    } else if o == 6 {
        (1, false, false)
    } else if o == 7 {
        (3, true, false)
    } else if o == 8 {
        (3, false, false)
    } else {
        (0, false, false)
    }
}

} // verus!

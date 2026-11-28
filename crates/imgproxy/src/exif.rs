//! The EXIF orientation, proven to compute `spec_exif::orientation`: the
//! walks over the segments, chunks and IFD entries are loops (a file of
//! many small segments cannot exhaust the stack), every read is in
//! bounds, and no sum overflows, for any input.
use crate::spec_exif::*;
use vstd::prelude::*;

verus! {

fn be16_x(d: &[u8], i: usize) -> (r: usize)
    requires
        i + 2 <= d@.len(),
    ensures
        r as int == be16(d@, i as int),
        r <= 65535,
{
    let _n = d.len();
    d[i] as usize * 256 + d[i + 1] as usize
}

fn u16at_x(d: &[u8], i: usize, le: bool) -> (r: usize)
    requires
        i + 2 <= d@.len(),
    ensures
        r as int == u16at(d@, i as int, le),
        r <= 65535,
{
    let _n = d.len();
    if le {
        d[i + 1] as usize * 256 + d[i] as usize
    } else {
        be16_x(d, i)
    }
}

fn u32at_x(d: &[u8], i: usize, le: bool) -> (r: usize)
    requires
        i + 4 <= d@.len(),
    ensures
        r as int == u32at(d@, i as int, le),
        r <= 0xffff_ffff,
{
    let _n = d.len();
    if le {
        u16at_x(d, i + 2, true) * 65536 + u16at_x(d, i, true)
    } else {
        be16_x(d, i) * 65536 + be16_x(d, i + 2)
    }
}

fn exif_hdr_x(d: &[u8], i: usize) -> (r: bool)
    ensures
        r == exif_hdr(d@, i as int),
{
    i <= d.len() && d.len() - i >= 6 && d[i] == b'E' && d[i + 1] == b'x' && d[i + 2] == b'i' && d[i + 3] == b'f'
        && d[i + 4] == 0 && d[i + 5] == 0
}

pub open spec fn as_int(r: Option<(usize, usize)>) -> Option<(int, int)> {
    match r {
        Some((s, e)) => Some((s as int, e as int)),
        None => None,
    }
}

/// `jpeg_exif(d, 2)`.
pub fn jpeg_exif_x(d: &[u8]) -> (r: Option<(usize, usize)>)
    requires
        d@.len() >= 2,
    ensures
        as_int(r) == jpeg_exif(d@, 2),
        r matches Some((s, e)) ==> s <= e <= d@.len(),
{
    let mut i: usize = 2;
    loop
        invariant
            2 <= i <= d@.len(),
            jpeg_exif(d@, i as int) == jpeg_exif(d@, 2),
        decreases d@.len() - i,
    {
        if d.len() - i < 4 || d[i] != 0xff {
            return None;
        }
        if d[i + 1] == 0xff {
            i = i + 1;
        } else if d[i + 1] == 0xda || d[i + 1] == 0xd9 {
            return None;
        } else {
            let len = be16_x(d, i + 2);
            if len < 2 || len > d.len() - (i + 2) {
                return None;
            }
            let end = i + 2 + len;
            if d[i + 1] == 0xe1 && len >= 8 && exif_hdr_x(d, i + 4) {
                return Some((i + 10, end));
            }
            i = end;
        }
    }
}

/// `webp_exif(d, 12)`.
pub fn webp_exif_x(d: &[u8]) -> (r: Option<(usize, usize)>)
    requires
        d@.len() >= 12,
    ensures
        as_int(r) == webp_exif(d@, 12),
        r matches Some((s, e)) ==> s <= e <= d@.len(),
{
    let mut i: usize = 12;
    loop
        invariant
            12 <= i <= d@.len(),
            webp_exif(d@, i as int) == webp_exif(d@, 12),
        decreases d@.len() - i,
    {
        if d.len() - i < 8 {
            return None;
        }
        let len = u32at_x(d, i + 4, true);
        if len > d.len() - (i + 8) {
            return None;
        }
        let end = i + 8 + len;
        if d[i] == b'E' && d[i + 1] == b'X' && d[i + 2] == b'I' && d[i + 3] == b'F' {
            if exif_hdr_x(d, i + 8) && len >= 6 {
                return Some((i + 14, end));
            } else {
                return Some((i + 8, end));
            }
        }
        if len % 2 == 1 && end == d.len() {
            // The next chunk would start past the end.
            proof {
                assert(webp_exif(d@, end + 1) is None);
            }
            return None;
        }
        i = if len % 2 == 1 { end + 1 } else { end };
    }
}

/// `png_exif(d, 8)`.
pub fn png_exif_x(d: &[u8]) -> (r: Option<(usize, usize)>)
    requires
        d@.len() >= 8,
    ensures
        as_int(r) == png_exif(d@, 8),
        r matches Some((s, e)) ==> s <= e <= d@.len(),
{
    let mut i: usize = 8;
    loop
        invariant
            8 <= i <= d@.len(),
            png_exif(d@, i as int) == png_exif(d@, 8),
        decreases d@.len() - i,
    {
        if d.len() - i < 8 {
            return None;
        }
        let len = u32at_x(d, i, false);
        if d.len() - (i + 8) < 4 || len > d.len() - (i + 8) - 4 {
            return None;
        }
        let end = i + 8 + len;
        if d[i + 4] == b'e' && d[i + 5] == b'X' && d[i + 6] == b'I' && d[i + 7] == b'f' {
            return Some((i + 8, end));
        }
        if d[i + 4] == b'I' && d[i + 5] == b'D' && d[i + 6] == b'A' && d[i + 7] == b'T' {
            return None;
        }
        i = end + 4;
    }
}

/// `ifd_orient(d, e0, end, le, n, 0)`.
fn ifd_orient_x(d: &[u8], e0: usize, end: usize, le: bool, n: usize) -> (r: u32)
    requires
        e0 <= end <= d@.len(),
        n <= 65535,
    ensures
        r as int == ifd_orient(d@, e0 as int, end as int, le, n as int, 0),
{
    let mut k: usize = 0;
    while k < n
        invariant
            e0 <= end <= d@.len(),
            n <= 65535,
            k <= n,
            ifd_orient(d@, e0 as int, end as int, le, n as int, k as int) == ifd_orient(
                d@,
                e0 as int,
                end as int,
                le,
                n as int,
                0,
            ),
        decreases n - k,
    {
        if 12 * k + 12 > end - e0 {
            return 1;
        }
        let e = e0 + 12 * k;
        let v = u16at_x(d, e + 8, le);
        if u16at_x(d, e, le) == 0x0112 && u16at_x(d, e + 2, le) == 3 && 1 <= v && v <= 8 {
            return v as u32;
        }
        k = k + 1;
    }
    1
}

/// `tiff_orient(d, s, end)`.
fn tiff_orient_x(d: &[u8], s: usize, end: usize) -> (r: u32)
    requires
        s <= end <= d@.len(),
    ensures
        r as int == tiff_orient(d@, s as int, end as int),
{
    if end - s < 8 {
        return 1;
    }
    if !((d[s] == b'I' && d[s + 1] == b'I') || (d[s] == b'M' && d[s + 1] == b'M')) {
        return 1;
    }
    let le = d[s] == b'I';
    let off = u32at_x(d, s + 4, le);
    if u16at_x(d, s + 2, le) != 42 || off > end - s || end - (s + off) < 2 {
        return 1;
    }
    let ifd = s + off;
    let n = u16at_x(d, ifd, le);
    ifd_orient_x(d, ifd + 2, end, le, n)
}

/// `orientation`.
pub fn orientation_x(d: &[u8]) -> (r: u32)
    ensures
        r as int == orientation(d@),
        1 <= r <= 8,
{
    let at = if d.len() >= 2 && d[0] == 0xff && d[1] == 0xd8 {
        jpeg_exif_x(d)
    } else if d.len() >= 12 && d[0] == b'R' && d[1] == b'I' && d[2] == b'F' && d[3] == b'F' && d[8] == b'W' && d[9]
        == b'E' && d[10] == b'B' && d[11] == b'P' {
        webp_exif_x(d)
    } else if d.len() >= 8 && d[0] == 0x89 && d[1] == b'P' && d[2] == b'N' && d[3] == b'G' && d[4] == 0x0d && d[5]
        == 0x0a && d[6] == 0x1a && d[7] == 0x0a {
        png_exif_x(d)
    } else {
        None
    };
    let r = match at {
        Some((s, e)) => tiff_orient_x(d, s, e),
        None => 1,
    };
    proof {
        lemma_orient_range(d@);
    }
    r
}

pub proof fn lemma_ifd_range(d: Seq<u8>, e0: int, end: int, le: bool, n: int, k: int)
    ensures
        1 <= ifd_orient(d, e0, end, le, n, k) <= 8,
    decreases n - k,
{
    if !(k >= n || k < 0 || e0 + 12 * k + 12 > end) {
        lemma_ifd_range(d, e0, end, le, n, k + 1);
    }
}

pub proof fn lemma_orient_range(d: Seq<u8>)
    ensures
        1 <= orientation(d) <= 8,
{
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
    if let Some((s, e)) = at {
        let s = s;
        if !(s < 0 || e > d.len() || s + 8 > e) && ((d[s] == b'I' && d[s + 1] == b'I') || (d[s] == b'M' && d[s + 1]
            == b'M')) {
            let le = d[s] == b'I';
            let ifd = s + u32at(d, s + 4, le);
            if !(u16at(d, s + 2, le) != 42 || ifd + 2 > e) {
                lemma_ifd_range(d, ifd + 2, e, le, u16at(d, ifd, le), 0);
            }
        }
    }
}

/// `upright`.
pub fn upright_x(o: u32) -> (r: (u32, bool, bool))
    ensures
        (r.0 as int, r.1, r.2) == upright(o as int),
        r.0 <= 3,
{
    match o {
        2 => (0, true, false),
        3 => (2, false, false),
        4 => (0, false, true),
        5 => (1, true, false),
        6 => (1, false, false),
        7 => (3, true, false),
        8 => (3, false, false),
        _ => (0, false, false),
    }
}

} // verus!

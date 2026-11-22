//! The trusted specification, part 1: what an archive *is*.
//!
//! The zip half follows PKWARE's APPNOTE.TXT (6.3.10), including zip64. The
//! tar half follows POSIX.1-2017 `pax` ("ustar Interchange Format" and "pax
//! Extended Header") and the GNU tar manual's description of its `L`/`K`
//! long-name records and base-256 numbers. Each function names the section
//! it transcribes.
//!
//! Everything here is a pure function of the archive bytes. The parsers in
//! `zip.rs` and `tar.rs` are proven to compute exactly these functions.
use vstd::prelude::*;

verus! {

/// What an archive member is.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Kind {
    File,
    Dir,
    Symlink,
    Hardlink,
    /// Devices, FIFOs and anything else: listed, never extracted.
    Other,
}

/// One archive member, as the format documents describe it.
pub ghost struct SEntry {
    /// The path, as stored.
    pub name: Seq<u8>,
    pub kind: Kind,
    /// The link target of a tar symlink or hard link. (A zip symlink keeps
    /// its target in the member's data.)
    pub link: Seq<u8>,
    /// The compression method: 0 stored, 8 DEFLATE, 93 Zstandard.
    pub method: int,
    pub encrypted: bool,
    /// The CRC-32 the archive declares for the data, when `has_crc`.
    pub crc: int,
    pub has_crc: bool,
    /// Where the member's own header starts in the archive.
    pub hdr_off: int,
    /// Where its (compressed) data starts.
    pub data_off: int,
    /// The length of its (compressed) data in the archive.
    pub csize: int,
    /// The declared length of its data once decompressed.
    pub size: int,
    /// Permission bits.
    pub mode: int,
    /// zip: MS-DOS date * 65536 + time. tar: seconds since the epoch.
    pub mtime: int,
}

impl SEntry {
    /// One past the last archive byte this member owns.
    pub open spec fn end(self) -> int {
        self.data_off + self.csize
    }
}

/// No two members share an archive byte: each owns the bytes from its
/// header to the end of its data.
pub open spec fn disjoint(es: Seq<SEntry>) -> bool {
    forall|i: int, j: int|
        0 <= i < es.len() && 0 <= j < es.len() && i != j ==> #[trigger] es[i].end() <= (
        #[trigger] es[j]).hdr_off || es[j].end() <= es[i].hdr_off
}

/// Every member's header and data lie inside the archive, in that order.
pub open spec fn in_bounds(es: Seq<SEntry>, len: int) -> bool {
    forall|i: int|
        0 <= i < es.len() ==> 0 <= (#[trigger] es[i]).hdr_off < es[i].data_off && es[i].csize >= 0
            && es[i].end() <= len
}

// ---------------------------------------------------------------------
// Little-endian fields (APPNOTE 4.4: "All values MUST be stored in
// little-endian byte order").
// ---------------------------------------------------------------------
pub open spec fn le16(b: Seq<u8>, i: int) -> int {
    b[i] as int + 256 * (b[i + 1] as int)
}

pub open spec fn le32(b: Seq<u8>, i: int) -> int {
    le16(b, i) + 0x1_0000 * le16(b, i + 2)
}

pub open spec fn le64(b: Seq<u8>, i: int) -> int {
    le32(b, i) + 0x1_0000_0000 * le32(b, i + 4)
}

// ---------------------------------------------------------------------
// zip: the end of central directory record (APPNOTE 4.3.16) and its zip64
// forms (4.3.14, 4.3.15).
// ---------------------------------------------------------------------
/// An end of central directory record starts at `p`: its signature is
/// there, and its comment runs exactly to the end of the file.
pub open spec fn eocd_at(b: Seq<u8>, p: int) -> bool {
    0 <= p && p + 22 <= b.len() && le32(b, p) == 0x06054b50 && p + 22 + le16(b, p + 20) == b.len()
}

/// The last position at or below `p`, and at or above `lo`, where an end
/// record starts.
pub open spec fn eocd_scan(b: Seq<u8>, p: int, lo: int) -> Option<int>
    decreases p - lo + 1,
{
    if p < lo {
        None
    } else if eocd_at(b, p) {
        Some(p)
    } else {
        eocd_scan(b, p - 1, lo)
    }
}

/// Where the end record is. The comment is at most 65535 bytes, so the
/// record starts in the last 22 + 65535 bytes.
pub open spec fn eocd_pos(b: Seq<u8>) -> Option<int> {
    let lo = if b.len() >= 22 + 65535 {
        b.len() - 22 - 65535
    } else {
        0
    };
    eocd_scan(b, b.len() - 22, lo)
}

/// What the end record says about the central directory.
pub ghost struct End {
    /// The number of members.
    pub n: int,
    pub cd_off: int,
    pub cd_size: int,
    /// Where the end records start: the central directory ends by here.
    pub end: int,
}

/// A classic field `c` of width `max` agrees with the zip64 value `v`:
/// it either holds the value or is saturated (APPNOTE 4.4.1.4).
pub open spec fn agrees(c: int, v: int, max: int) -> bool {
    c == v || c == max
}

/// The end record of a zip64 archive whose classic end record is at `p`:
/// the locator (4.3.15) is the 20 bytes before `p`, and it points at the
/// zip64 end record (4.3.14).
#[verifier::opaque]
pub open spec fn zip64_end(b: Seq<u8>, p: int) -> Option<End> {
    let l = p - 20;
    let q = le64(b, l + 8);
    if le32(b, l + 4) != 0 || le32(b, l + 16) > 1 || q + 56 > l || le32(b, q) != 0x06064b50 {
        None
    } else if le32(b, q + 16) != 0 || le32(b, q + 20) != 0 || le64(b, q + 24) != le64(b, q + 32) {
        // Multi-disk archives are not supported.
        None
    } else {
        let n = le64(b, q + 32);
        let cd_size = le64(b, q + 40);
        let cd_off = le64(b, q + 48);
        if agrees(le16(b, p + 4), 0, 0xffff) && agrees(le16(b, p + 6), 0, 0xffff) && agrees(
            le16(b, p + 8),
            n,
            0xffff,
        ) && agrees(le16(b, p + 10), n, 0xffff) && agrees(le32(b, p + 12), cd_size, 0xffff_ffff)
            && agrees(le32(b, p + 16), cd_off, 0xffff_ffff) {
            Some(End { n, cd_off, cd_size, end: q })
        } else {
            None
        }
    }
}

/// The end record of the archive: the zip64 one when a zip64 locator sits
/// right before the classic record, the classic one otherwise. The central
/// directory must end before the end records start.
pub open spec fn zip_end(b: Seq<u8>) -> Option<End> {
    match eocd_pos(b) {
        None => None,
        Some(p) => {
            let e = if p >= 20 && le32(b, p - 20) == 0x07064b50 {
                zip64_end(b, p)
            } else if le16(b, p + 4) != 0 || le16(b, p + 6) != 0 || le16(b, p + 8) != le16(
                b,
                p + 10,
            ) {
                None
            } else {
                Some(
                    End {
                        n: le16(b, p + 10),
                        cd_off: le32(b, p + 16),
                        cd_size: le32(b, p + 12),
                        end: p,
                    },
                )
            };
            match e {
                None => None,
                Some(e) => if e.cd_off + e.cd_size <= e.end {
                    Some(e)
                } else {
                    None
                },
            }
        },
    }
}

// ---------------------------------------------------------------------
// zip: extra fields (APPNOTE 4.5) and the zip64 one (4.5.3).
// ---------------------------------------------------------------------
/// The data (offset and length within `x`) of the first extra field with
/// header ID `id`, walking the records from `i`.
pub open spec fn find_extra(x: Seq<u8>, i: int, id: int) -> Option<(int, int)>
    decreases x.len() - i,
{
    if i < 0 || i + 4 > x.len() {
        None
    } else {
        let l = le16(x, i + 2);
        if i + 4 + l > x.len() {
            None
        } else if le16(x, i) == id {
            Some((i + 4, l))
        } else {
            find_extra(x, i + 4 + l, id)
        }
    }
}

/// The 64-bit values of the saturated fields of a central header, read
/// from its zip64 extra field `z` in the fixed order of 4.5.3: original
/// size, compressed size, local header offset, disk number. Each is present
/// only if its 32-bit (16-bit) field is saturated. Returns (size, csize,
/// offset, disk).
#[verifier::opaque]
pub open spec fn zip64_fields(x: Seq<u8>, usize32: int, csize32: int, lho32: int, disk16: int) -> Option<
    (int, int, int, int),
> {
    let nu = usize32 == 0xffff_ffff;
    let nc = csize32 == 0xffff_ffff;
    let nl = lho32 == 0xffff_ffff;
    let nd = disk16 == 0xffff;
    if !nu && !nc && !nl && !nd {
        Some((usize32, csize32, lho32, disk16))
    } else {
        match find_extra(x, 0, 1) {
            None => None,
            Some((o, l)) => {
                let o1 = o + if nu { 8int } else { 0 };
                let o2 = o1 + if nc { 8int } else { 0 };
                let o3 = o2 + if nl { 8int } else { 0 };
                let o4 = o3 + if nd { 4int } else { 0 };
                if o4 - o > l {
                    None
                } else {
                    Some(
                        (
                            if nu { le64(x, o) } else { usize32 },
                            if nc { le64(x, o1) } else { csize32 },
                            if nl { le64(x, o2) } else { lho32 },
                            if nd { le32(x, o3) } else { disk16 },
                        ),
                    )
                }
            },
        }
    }
}

// ---------------------------------------------------------------------
// zip: central directory headers (APPNOTE 4.3.12) and local headers
// (4.3.7).
// ---------------------------------------------------------------------
/// A member is a directory if its name ends in `/` (4.3.6), a symlink if a
/// Unix system made it and its mode says so (the external attributes' high
/// 16 bits are `st_mode` when "version made by" names Unix, 4.4.2), and a
/// file otherwise.
pub open spec fn zip_kind(name: Seq<u8>, made: int, xattr: int) -> Kind {
    if name.len() > 0 && name.last() == 0x2f {
        Kind::Dir
    } else if made / 256 == 3 && (xattr / 0x1_0000) / 4096 == 10 {
        Kind::Symlink
    } else {
        Kind::File
    }
}

pub open spec fn zip_mode(made: int, xattr: int) -> int {
    if made / 256 == 3 {
        (xattr / 0x1_0000) % 4096
    } else {
        0
    }
}

/// The member whose central header starts at `p`, and where the next
/// central header starts. The central directory is `[eo.cd_off, eo.cd_off +
/// eo.cd_size)`; the member's local header and data must lie before it.
///
/// The central header is authoritative for sizes and CRC. The local header
/// must be there, with the same name, method and encryption flag: a reader
/// that trusted the local header instead would see the same member.
#[verifier::opaque]
pub open spec fn zip_entry(b: Seq<u8>, p: int, eo: End) -> Option<(SEntry, int)> {
    let cd_end = eo.cd_off + eo.cd_size;
    if p < 0 || p + 46 > cd_end || le32(b, p) != 0x02014b50 {
        None
    } else {
        let made = le16(b, p + 4);
        let flags = le16(b, p + 8);
        let method = le16(b, p + 10);
        let nlen = le16(b, p + 28);
        let xlen = le16(b, p + 30);
        let clen = le16(b, p + 32);
        let next = p + 46 + nlen + xlen + clen;
        if next > cd_end {
            None
        } else {
            let name = b.subrange(p + 46, p + 46 + nlen);
            let x = b.subrange(p + 46 + nlen, p + 46 + nlen + xlen);
            match zip64_fields(x, le32(b, p + 24), le32(b, p + 20), le32(b, p + 42), le16(b, p + 34)) {
                None => None,
                Some((size, csize, lho, disk)) => {
                    // The local header.
                    let ln = le16(b, lho + 26);
                    let lx = le16(b, lho + 28);
                    let data = lho + 30 + ln + lx;
                    if disk != 0 || lho + 30 > eo.cd_off || le32(b, lho) != 0x04034b50 {
                        None
                    } else if data + csize > eo.cd_off || ln != nlen || b.subrange(
                        lho + 30,
                        lho + 30 + ln,
                    ) != name || le16(b, lho + 8) != method || le16(b, lho + 6) % 2 != flags % 2 {
                        None
                    } else {
                        let xattr = le32(b, p + 38);
                        Some(
                            (
                                SEntry {
                                    name,
                                    kind: zip_kind(name, made, xattr),
                                    link: Seq::empty(),
                                    method,
                                    encrypted: flags % 2 == 1,
                                    crc: le32(b, p + 16),
                                    has_crc: true,
                                    hdr_off: lho,
                                    data_off: data,
                                    csize,
                                    size,
                                    mode: zip_mode(made, xattr),
                                    mtime: le16(b, p + 14) * 0x1_0000 + le16(b, p + 12),
                                },
                                next,
                            ),
                        )
                    }
                },
            }
        }
    }
}

/// The `n` members whose central headers start at `p`. The headers must
/// fill the central directory exactly.
pub open spec fn zip_entries(b: Seq<u8>, p: int, n: nat, eo: End) -> Option<Seq<SEntry>>
    decreases n,
{
    if n == 0 {
        if p == eo.cd_off + eo.cd_size {
            Some(Seq::empty())
        } else {
            None
        }
    } else {
        match zip_entry(b, p, eo) {
            None => None,
            Some((e, next)) => match zip_entries(b, next, (n - 1) as nat, eo) {
                None => None,
                Some(r) => Some(seq![e] + r),
            },
        }
    }
}

/// The members the central directory lists, in its order.
pub open spec fn zip_listed(b: Seq<u8>) -> Option<Seq<SEntry>> {
    match zip_end(b) {
        None => None,
        Some(eo) => zip_entries(b, eo.cd_off, eo.n as nat, eo),
    }
}

/// **A zip archive.** Its members are those the central directory lists,
/// and no two of them may share a byte of the file: an archive whose
/// members overlap (the construction behind "zip bombs" that reuse one
/// compressed stream for many members) is not an archive.
pub open spec fn zip(b: Seq<u8>) -> Option<Seq<SEntry>> {
    match zip_listed(b) {
        None => None,
        Some(es) => if disjoint(es) {
            Some(es)
        } else {
            None
        },
    }
}

// ---------------------------------------------------------------------
// tar: numbers (POSIX pax, "ustar Interchange Format": "octal numbers
// using digits from the ISO/IEC 646:1991 standard IRV ... terminated by one
// or more <space> or NUL characters"; GNU tar manual, "Extensions to the
// tar format": a leading 0x80 byte marks a big-endian binary number).
// ---------------------------------------------------------------------
/// The first index at or after `i` holding a NUL, or the length.
pub open spec fn nul_from(f: Seq<u8>, i: int) -> int
    decreases f.len() - i,
{
    if i >= f.len() || f[i] == 0 {
        i
    } else {
        nul_from(f, i + 1)
    }
}

/// A NUL-terminated (or field-filling) string.
pub open spec fn cstr(f: Seq<u8>) -> Seq<u8> {
    f.subrange(0, nul_from(f, 0))
}

pub open spec fn skip_sp(f: Seq<u8>, i: int) -> int
    decreases f.len() - i,
{
    if 0 <= i < f.len() && f[i] == 0x20 {
        skip_sp(f, i + 1)
    } else {
        i
    }
}

/// Octal digits from `i` up to a space, a NUL or the end of the field.
/// Values of 2^63 or more are not numbers.
pub open spec fn oct_from(f: Seq<u8>, i: int, acc: int) -> Option<int>
    decreases f.len() - i,
{
    if i < 0 || i >= f.len() {
        Some(acc)
    } else if 0x30 <= f[i] <= 0x37 {
        if acc >= 0x1000_0000_0000_0000 {
            None
        } else {
            oct_from(f, i + 1, acc * 8 + (f[i] - 0x30))
        }
    } else if f[i] == 0x20 || f[i] == 0 {
        Some(acc)
    } else {
        None
    }
}

pub open spec fn octal(f: Seq<u8>) -> Option<int> {
    oct_from(f, skip_sp(f, 0), 0)
}

/// Big-endian bytes from `i` to the end of the field.
pub open spec fn be_from(f: Seq<u8>, i: int, acc: int) -> Option<int>
    decreases f.len() - i,
{
    if i < 0 || i >= f.len() {
        Some(acc)
    } else if acc >= 0x80_0000_0000_0000 {
        None
    } else {
        be_from(f, i + 1, acc * 256 + f[i])
    }
}

/// A numeric header field: octal, or GNU base-256 when the first byte is
/// 0x80. (A first byte above 0x80 would be a negative or oversized number.)
pub open spec fn tar_num(f: Seq<u8>) -> Option<int> {
    if f.len() > 0 && f[0] >= 0x80 {
        if f[0] == 0x80 {
            be_from(f, 1, 0)
        } else {
            None
        }
    } else {
        octal(f)
    }
}

// ---------------------------------------------------------------------
// tar: the header block (POSIX pax, "ustar Interchange Format", the table
// of field offsets).
// ---------------------------------------------------------------------
pub open spec fn sum_to(h: Seq<u8>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        sum_to(h, n - 1) + h[n - 1]
    }
}

/// "The chksum field shall be ... the simple sum of all octets in the
/// header logical record ... [with] each octet in the chksum field treated
/// as a <space>".
pub open spec fn tar_checksum(h: Seq<u8>) -> int {
    sum_to(h, 148) + 8 * 0x20 + (sum_to(h, 512) - sum_to(h, 156))
}

pub ghost struct THeader {
    pub name: Seq<u8>,
    pub mode: int,
    pub size: int,
    pub mtime: int,
    pub typeflag: u8,
    pub linkname: Seq<u8>,
}

/// `magic` is "ustar" and a NUL: the POSIX format, whose `prefix` field
/// holds the leading part of a long name. (GNU's older "ustar  " format
/// uses those bytes for other things.)
pub open spec fn is_ustar(h: Seq<u8>) -> bool {
    h[257] == 0x75 && h[258] == 0x73 && h[259] == 0x74 && h[260] == 0x61 && h[261] == 0x72 && h[262] == 0
}

/// The 512-byte header block `h`. Its checksum must match and its size
/// must be a number; an unreadable mode or mtime counts as 0.
#[verifier::opaque]
pub open spec fn tar_header(h: Seq<u8>) -> Option<THeader> {
    match octal(h.subrange(148, 156)) {
        None => None,
        Some(c) => if c != tar_checksum(h) {
            None
        } else {
            match tar_num(h.subrange(124, 136)) {
                None => None,
                Some(size) => {
                    let nm = cstr(h.subrange(0, 100));
                    let pf = cstr(h.subrange(345, 500));
                    Some(
                        THeader {
                            name: if is_ustar(h) && pf.len() > 0 {
                                pf + seq![0x2fu8] + nm
                            } else {
                                nm
                            },
                            mode: match octal(h.subrange(100, 108)) {
                                Some(m) => m % 4096,
                                None => 0,
                            },
                            size,
                            mtime: match tar_num(h.subrange(136, 148)) {
                                Some(t) => t,
                                None => 0,
                            },
                            typeflag: h[156],
                            linkname: cstr(h.subrange(157, 257)),
                        },
                    )
                },
            }
        },
    }
}

// ---------------------------------------------------------------------
// tar: pax extended header records (POSIX pax, "pax Extended Header":
// `"%d %s=%s\n", <length>, <keyword>, <value>`).
// ---------------------------------------------------------------------
/// What extended headers have said about the next member.
pub ghost struct Pend {
    pub path: Option<Seq<u8>>,
    pub link: Option<Seq<u8>>,
    pub size: Option<int>,
}

/// Decimal digits from `i`: their value and the index after them. Values
/// of 2^63 or more are not numbers.
pub open spec fn dec_from(d: Seq<u8>, i: int, acc: int) -> Option<(int, int)>
    decreases d.len() - i,
{
    if 0 <= i < d.len() && 0x30 <= d[i] <= 0x39 {
        if acc >= 0x800_0000_0000_0000 {
            None
        } else {
            dec_from(d, i + 1, acc * 10 + (d[i] - 0x30))
        }
    } else {
        Some((acc, i))
    }
}

/// The first index in `[i, end)` holding `c`, or `end`.
pub open spec fn find_byte(d: Seq<u8>, i: int, end: int, c: u8) -> int
    decreases end - i,
{
    if i >= end || d[i] == c {
        i
    } else {
        find_byte(d, i + 1, end, c)
    }
}

/// The record starting at `i`: its keyword, its value, and where the next
/// record starts.
pub open spec fn pax_record(d: Seq<u8>, i: int) -> Option<(Seq<u8>, Seq<u8>, int)> {
    match dec_from(d, i, 0) {
        None => None,
        Some((l, j)) => {
            let end = i + l - 1;
            if j == i || j >= d.len() || d[j] != 0x20 || i + l > d.len() || l < (j - i) + 3 || d[end] != 0x0a {
                None
            } else {
                let eq = find_byte(d, j + 1, end, 0x3d);
                if eq == end {
                    None
                } else {
                    Some((d.subrange(j + 1, eq), d.subrange(eq + 1, end), i + l))
                }
            }
        },
    }
}

pub open spec fn key_path(k: Seq<u8>) -> bool {
    k.len() == 4 && k[0] == 0x70 && k[1] == 0x61 && k[2] == 0x74 && k[3] == 0x68
}

pub open spec fn key_linkpath(k: Seq<u8>) -> bool {
    k.len() == 8 && k[0] == 0x6c && k[1] == 0x69 && k[2] == 0x6e && k[3] == 0x6b && key_path(k.subrange(4, 8))
}

pub open spec fn key_size(k: Seq<u8>) -> bool {
    k.len() == 4 && k[0] == 0x73 && k[1] == 0x69 && k[2] == 0x7a && k[3] == 0x65
}

/// The keywords that change where a member goes or how long it is: `path`,
/// `linkpath` and `size`. All others are ignored.
pub open spec fn pax_apply(p: Pend, k: Seq<u8>, v: Seq<u8>) -> Option<Pend> {
    if key_path(k) {
        Some(Pend { path: Some(v), ..p })
    } else if key_linkpath(k) {
        Some(Pend { link: Some(v), ..p })
    } else if key_size(k) {
        match dec_from(v, 0, 0) {
            Some((s, j)) => if j == v.len() && j > 0 {
                Some(Pend { size: Some(s), ..p })
            } else {
                None
            },
            None => None,
        }
    } else {
        Some(p)
    }
}

pub open spec fn pax_from(d: Seq<u8>, i: int, p: Pend) -> Option<Pend>
    decreases d.len() - i,
{
    if i >= d.len() {
        Some(p)
    } else {
        match pax_record(d, i) {
            None => None,
            Some((k, v, next)) => if next <= i {
                None
            } else {
                match pax_apply(p, k, v) {
                    None => None,
                    Some(p2) => pax_from(d, next, p2),
                }
            },
        }
    }
}

// ---------------------------------------------------------------------
// tar: the archive (POSIX pax, "ustar Interchange Format": typeflag
// values; GNU tar manual: `L` and `K` long names).
// ---------------------------------------------------------------------
pub open spec fn all_zero(h: Seq<u8>) -> bool {
    forall|k: int| 0 <= k < h.len() ==> h[k] == 0
}

/// Links, directories, devices and FIFOs have no data, whatever their
/// size field says.
pub open spec fn tar_has_data(t: u8) -> bool {
    !(0x31 <= t <= 0x36)
}

pub open spec fn tar_kind(t: u8, name: Seq<u8>) -> Kind {
    if t == 0x30 || t == 0 || t == 0x37 {
        if name.len() > 0 && name.last() == 0x2f {
            Kind::Dir
        } else {
            Kind::File
        }
    } else if t == 0x31 {
        Kind::Hardlink
    } else if t == 0x32 {
        Kind::Symlink
    } else if t == 0x35 {
        Kind::Dir
    } else {
        Kind::Other
    }
}

/// What the header block at `pos` contributes.
pub ghost enum Step {
    /// The archive ends here.
    End,
    /// The bytes here are not a tar archive.
    Bad,
    /// A header about the next member: what is now known about it, and
    /// where the next header block is.
    Meta(Pend, int),
    /// A member, and where the next header block is.
    Member(SEntry, int),
}

/// The header block at `pos`, given what extended headers before it said.
/// The archive ends at a block of zeros or at the end of the bytes.
#[verifier::opaque]
pub open spec fn tar_step(b: Seq<u8>, pos: int, pend: Pend) -> Step {
    if pos < 0 {
        Step::Bad
    } else if pos == b.len() {
        Step::End
    } else if pos + 512 > b.len() {
        Step::Bad
    } else {
        let h = b.subrange(pos, pos + 512);
        if all_zero(h) {
            Step::End
        } else {
            match tar_header(h) {
                None => Step::Bad,
                Some(hd) => {
                    let t = hd.typeflag;
                    let meta = t == 0x78 || t == 0x67 || t == 0x4c || t == 0x4b || t == 0x56;
                    let size = if !tar_has_data(t) || hd.size < 0 {
                        0
                    } else if meta {
                        hd.size
                    } else {
                        match pend.size {
                            Some(s) => if s < 0 { 0 } else { s },
                            None => hd.size,
                        }
                    };
                    let data = pos + 512;
                    // Data is padded to a whole number of 512-byte blocks.
                    let next = data + ((size + 511) / 512) * 512;
                    if next > b.len() {
                        Step::Bad
                    } else if t == 0x78 {
                        // 'x': a pax extended header for the next member.
                        match pax_from(b.subrange(data, data + size), 0, pend) {
                            None => Step::Bad,
                            Some(p) => Step::Meta(p, next),
                        }
                    } else if t == 0x67 || t == 0x56 {
                        // 'g': pax global header; 'V': GNU volume label.
                        Step::Meta(pend, next)
                    } else if t == 0x4c {
                        // 'L': the next member's name.
                        Step::Meta(Pend { path: Some(cstr(b.subrange(data, data + size))), ..pend }, next)
                    } else if t == 0x4b {
                        // 'K': the next member's link target.
                        Step::Meta(Pend { link: Some(cstr(b.subrange(data, data + size))), ..pend }, next)
                    } else if t == 0x53 || t == 0x4d {
                        // GNU sparse files and multi-volume continuations
                        // lay their data out differently: not supported.
                        Step::Bad
                    } else {
                        let name = match pend.path {
                            Some(p) => p,
                            None => hd.name,
                        };
                        Step::Member(
                            SEntry {
                                name,
                                kind: tar_kind(t, name),
                                link: match pend.link {
                                    Some(l) => l,
                                    None => hd.linkname,
                                },
                                method: 0,
                                encrypted: false,
                                crc: 0,
                                has_crc: false,
                                hdr_off: pos,
                                data_off: data,
                                csize: size,
                                size,
                                mode: hd.mode,
                                mtime: hd.mtime,
                            },
                            next,
                        )
                    }
                },
            }
        }
    }
}

/// The members from the header block at `pos` on.
pub open spec fn tar_from(b: Seq<u8>, pos: int, pend: Pend) -> Option<Seq<SEntry>>
    decreases b.len() - pos,
{
    match tar_step(b, pos, pend) {
        Step::End => Some(Seq::empty()),
        Step::Bad => None,
        Step::Meta(p, next) => if next <= pos || next > b.len() {
            None
        } else {
            tar_from(b, next, p)
        },
        Step::Member(e, next) => if next <= pos || next > b.len() {
            None
        } else {
            match tar_from(b, next, Pend { path: None, link: None, size: None }) {
                None => None,
                Some(r) => Some(seq![e] + r),
            }
        },
    }
}

/// **A tar archive** and its members.
pub open spec fn tar(b: Seq<u8>) -> Option<Seq<SEntry>> {
    tar_from(b, 0, Pend { path: None, link: None, size: None })
}

// ---------------------------------------------------------------------
// Member data.
// ---------------------------------------------------------------------
/// What the bytes `c` decompress to under `method` (APPNOTE 4.4.5): 0 is
/// stored, 8 is DEFLATE (RFC 1951, by vzlib's specification; the stream
/// must use every byte of `c`), 93 is Zstandard (RFC 8878, by vzstd's
/// specification). Other methods are not supported.
pub open spec fn unpack(method: int, c: Seq<u8>) -> Option<Seq<u8>> {
    if method == 0 {
        Some(c)
    } else if method == 8 {
        match verilith_zlib::wrap::spec_decompress(verilith_zlib::wrap::Format::Raw, c) {
            Some((o, used)) => if used == c.len() {
                Some(o)
            } else {
                None
            },
            None => None,
        }
    } else if method == 93 {
        verilith_zstd::spec::decompress(c)
    } else {
        None
    }
}

/// **A member's data.** Its bytes in the archive, decompressed; and only
/// if the result has exactly the declared length and, where the archive
/// declares a CRC-32, that CRC-32. Encrypted members have no readable
/// data.
pub open spec fn entry_data(b: Seq<u8>, e: SEntry) -> Option<Seq<u8>> {
    if e.encrypted {
        None
    } else {
        match unpack(e.method, b.subrange(e.data_off, e.end())) {
            None => None,
            Some(o) => if o.len() == e.size && (e.has_crc ==> verilith_core::checksum::spec::crc32(o) as int == e.crc) {
                Some(o)
            } else {
                None
            },
        }
    }
}

} // verus!

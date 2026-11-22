//! Executable-independent specification of PNG decoding (PNG Specification,
//! Third Edition, W3C 2025; section numbers below refer to it).
//!
//! Everything here is a total function over `Seq<u8>`. This file, the
//! zlib and CRC-32 specifications it uses from vzlib (`verilith_zlib::spec`), Verus
//! and the Rust compiler are the trusted base: the decoder is proven to
//! compute exactly these functions.
//!
//! Where the PNG specification leaves the decoder a choice, or where libpng
//! (the reference decoder) accepts or rejects differently from what the
//! specification alone implies, the choice made here is marked "libpng:" and
//! listed in the README. The guiding rule is libpng 1.6's default reading
//! behaviour: errors in critical chunks reject the file, problems in
//! ancillary chunks make the decoder ignore that chunk ("benign errors").
use vstd::prelude::*;
#[cfg(verus_only)]
use verilith_zlib::spec as z;

verus! {

// ---------------------------------------------------------------------------
// Bytes
// ---------------------------------------------------------------------------

/// The big-endian value of the four bytes at `i` (§7.1).
pub open spec fn be32(b: Seq<u8>, i: int) -> nat {
    ((b[i] as nat * 256 + b[i + 1] as nat) * 256 + b[i + 2] as nat) * 256 + b[i + 3] as nat
}

/// The big-endian value of the two bytes at `i`.
pub open spec fn be16(b: Seq<u8>, i: int) -> nat {
    b[i] as nat * 256 + b[i + 1] as nat
}

/// The PNG signature (§5.2).
pub open spec fn signature() -> Seq<u8> {
    seq![137u8, 80, 78, 71, 13, 10, 26, 10]
}

// ---------------------------------------------------------------------------
// Chunks (§5.3, §5.4)
// ---------------------------------------------------------------------------

/// Chunk types, as the big-endian value of their four ASCII letters.
pub spec const IHDR: nat = 0x4948_4452;

pub spec const PLTE: nat = 0x504c_5445;
pub spec const BKGD: nat = 0x624b_4744;

pub spec const IDAT: nat = 0x4944_4154;

pub spec const IEND: nat = 0x4945_4e44;

pub spec const TRNS: nat = 0x7452_4e53;

/// Largest chunk length (§5.3: at most 2^31 - 1).
pub spec const MAX_LEN: nat = 0x7fff_ffff;

pub open spec fn is_letter(x: u8) -> bool {
    (65 <= x <= 90) || (97 <= x <= 122)
}

/// A chunk is critical when bit 5 of its first type byte is 0 (§5.4).
pub open spec fn is_critical(ty: nat) -> bool {
    (ty / 0x2000_0000) % 2 == 0
}

/// A chunk's framing, read at offset `p`.
pub struct Chunk {
    /// Data length.
    pub len: nat,
    /// Type, as a big-endian number.
    pub ty: nat,
    /// Whether the stored CRC matches the type and data.
    pub crc_ok: bool,
}

/// The chunk at `p`, if its length, type and CRC fields are present, the
/// length is at most 2^31 - 1, the data fits in the file, and the type
/// bytes are letters, the third (reserved bit) uppercase. libpng: a type
/// that breaks either rule is an error for every chunk (`check_chunk_name`
/// in `png_read_chunk_header`).
pub open spec fn chunk_at(b: Seq<u8>, p: int) -> Option<Chunk> {
    if p < 0 || p + 12 > b.len() {
        None
    } else {
        let len = be32(b, p);
        if len > MAX_LEN || p + 12 + len > b.len() {
            None
        } else if !(is_letter(b[p + 4]) && is_letter(b[p + 5]) && 65 <= b[p + 6] <= 90 && is_letter(
            b[p + 7],
        )) {
            None
        } else {
            Some(
                Chunk {
                    len,
                    ty: be32(b, p + 4),
                    crc_ok: be32(b, p + 8 + len) == z::crc32(b.subrange(p + 4, p + 8 + len))
                        as nat,
                },
            )
        }
    }
}

/// The data of the chunk at `p`, whose length is `len`.
pub open spec fn chunk_data(b: Seq<u8>, p: int, len: nat) -> Seq<u8> {
    b.subrange(p + 8, p + 8 + len)
}

// ---------------------------------------------------------------------------
// IHDR (§11.2.1)
// ---------------------------------------------------------------------------

pub struct Ihdr {
    pub w: nat,
    pub h: nat,
    pub depth: nat,
    pub ct: nat,
    pub interlace: nat,
}

/// The allowed bit depths for each colour type (§11.2.1, table 11.1).
pub open spec fn depth_ok(ct: nat, depth: nat) -> bool {
    if ct == 0 {
        depth == 1 || depth == 2 || depth == 4 || depth == 8 || depth == 16
    } else if ct == 3 {
        depth == 1 || depth == 2 || depth == 4 || depth == 8
    } else if ct == 2 || ct == 4 || ct == 6 {
        depth == 8 || depth == 16
    } else {
        false
    }
}

/// Parses IHDR data. The width and height must be 1 to 2^31 - 1, the
/// compression and filter methods 0, the interlace method 0 or 1.
/// libpng: libpng also rejects images wider or taller than 1,000,000 by
/// default (`PNG_USER_WIDTH_MAX`); vpng leaves size limits to the caller.
pub open spec fn parse_ihdr(d: Seq<u8>) -> Option<Ihdr> {
    if d.len() != 13 {
        None
    } else {
        let h = Ihdr {
            w: be32(d, 0),
            h: be32(d, 4),
            depth: d[8] as nat,
            ct: d[9] as nat,
            interlace: d[12] as nat,
        };
        if 1 <= h.w <= MAX_LEN && 1 <= h.h <= MAX_LEN && depth_ok(h.ct, h.depth) && d[10] == 0
            && d[11] == 0 && h.interlace <= 1 {
            Some(h)
        } else {
            None
        }
    }
}

/// Samples per pixel.
pub open spec fn channels(ct: nat) -> nat {
    if ct == 2 {
        3
    } else if ct == 4 {
        2
    } else if ct == 6 {
        4
    } else {
        1
    }
}

/// Bits per pixel.
pub open spec fn pixel_bits(h: Ihdr) -> nat {
    channels(h.ct) * h.depth
}

/// Bytes in a row of `w` pixels, without the filter byte.
pub open spec fn row_bytes(h: Ihdr, w: nat) -> nat {
    (w * pixel_bits(h) + 7) / 8
}

/// The filter's byte distance to the corresponding byte of the pixel to the
/// left (§9.2: `bpp`, at least 1).
pub open spec fn filter_bpp(h: Ihdr) -> nat {
    (pixel_bits(h) + 7) / 8
}

// ---------------------------------------------------------------------------
// The chunk sequence (§5.6)
// ---------------------------------------------------------------------------

/// What the chunks after IHDR have contributed so far.
pub struct Walk {
    /// The palette (after truncation, see `take_plte`), once a PLTE chunk
    /// has been seen.
    pub plte: Option<Seq<u8>>,
    /// The data of an accepted tRNS chunk.
    pub trns: Option<Seq<u8>>,
    /// The concatenated data of the first run of consecutive IDAT chunks.
    pub idat: Seq<u8>,
    /// 0: no IDAT yet; 1: inside the first IDAT run; 2: after it.
    pub phase: nat,
    /// Whether a bKGD chunk of the right length for an RGB image came before
    /// IDAT (it makes libpng ignore a later PLTE in such an image).
    pub bkgd: bool,
}

pub open spec fn walk_start() -> Walk {
    Walk { plte: None, trns: None, idat: Seq::empty(), phase: 0, bkgd: false }
}

/// The palette that PLTE data `d` gives. libpng: a palette with more
/// entries than the bit depth can index is silently truncated
/// (`png_handle_PLTE`, the fix for CVE-2015-8126).
pub open spec fn take_plte(h: Ihdr, d: Seq<u8>) -> Seq<u8> {
    if h.ct == 3 && d.len() / 3 > pow2_nat(h.depth) {
        d.subrange(0, 3 * pow2_nat(h.depth) as int)
    } else {
        d
    }
}

pub open spec fn pow2_nat(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        2 * pow2_nat((n - 1) as nat)
    }
}

/// Whether tRNS data `d` is accepted, given the walk so far (§11.3.1.1).
/// libpng: every rejected tRNS chunk is ignored rather than an error: a
/// second one, one after IDAT, one in a type with an alpha channel, one of
/// the wrong length, and, for palette images, one before PLTE, an empty one
/// or one with more entries than the palette (`png_handle_tRNS`).
pub open spec fn trns_ok(h: Ihdr, st: Walk, d: Seq<u8>) -> bool {
    &&& st.trns is None
    &&& st.phase == 0
    &&& if h.ct == 0 {
        d.len() == 2
    } else if h.ct == 2 {
        d.len() == 6
    } else if h.ct == 3 {
        st.plte matches Some(p) && 1 <= d.len() <= p.len() / 3
    } else {
        false
    }
}

/// The chunk at `p` in a walk that is in state `st`, giving the next state,
/// or `Err(true)` at a valid IEND and `Err(false)` when the file is
/// rejected.
pub open spec fn step(b: Seq<u8>, h: Ihdr, p: int, c: Chunk, st: Walk) -> Result<Walk, bool> {
    let d = chunk_data(b, p, c.len);
    // Any chunk other than IDAT ends the first IDAT run.
    let st1 = if st.phase == 1 && c.ty != IDAT {
        Walk { phase: 2, ..st }
    } else {
        st
    };
    if c.ty == IEND {
        // libpng: IEND's CRC is checked as an ancillary chunk's would be (a
        // bad one is ignored), and a non-empty IEND is ignored too.
        if st.phase == 0 {
            Err(false)
        } else {
            Err(true)
        }
    } else if !c.crc_ok {
        // libpng: a CRC error is an error in a critical chunk; an ancillary
        // chunk with a bad CRC is discarded. Before IDAT, PLTE counts as
        // ancillary in an image without a palette.
        if is_critical(c.ty) && !(c.ty == PLTE && h.ct != 3 && st1.phase == 0) {
            Err(false)
        } else {
            Ok(st1)
        }
    } else if c.ty == IDAT {
        if st.phase == 0 {
            // §5.6: a palette image needs PLTE before IDAT.
            if h.ct == 3 && st.plte is None {
                Err(false)
            } else {
                Ok(Walk { idat: d, phase: 1, ..st })
            }
        } else if st.phase == 1 {
            Ok(Walk { idat: st.idat + d, ..st })
        } else {
            // libpng: IDAT chunks after the first run are ignored once the
            // image data is complete ("Too many IDATs found", benign).
            Ok(st)
        }
    } else if c.ty == IHDR {
        Err(false)
    } else if c.ty == PLTE {
        if st1.phase != 0 {
            // libpng (`png_read_end`): PLTE after the image data is ignored.
            Ok(st1)
        } else if h.ct == 3 {
            // A second PLTE, or one of the wrong length, is an error.
            if st1.plte is Some || d.len() % 3 != 0 || d.len() == 0 || d.len() > 768 {
                Err(false)
            } else {
                Ok(Walk { plte: Some(take_plte(h, d)), ..st1 })
            }
        } else if h.ct == 2 || h.ct == 6 {
            // libpng 1.6.47+: PLTE is a suggested palette that does not
            // affect the image. It is ignored if it is a second one, follows
            // tRNS or bKGD, or has an invalid length; an empty one is an
            // error ("Invalid palette" from `png_set_PLTE`).
            if st1.plte is Some || st1.trns is Some || st1.bkgd || d.len() % 3 != 0 || d.len() > 768 {
                Ok(st1)
            } else if d.len() == 0 {
                Err(false)
            } else {
                Ok(Walk { plte: Some(Seq::empty()), ..st1 })
            }
        } else {
            // libpng: "ignored in grayscale PNG".
            Ok(st1)
        }
    } else if c.ty == BKGD {
        if st1.phase == 0 && (h.ct == 2 || h.ct == 6) && d.len() == 6 {
            Ok(Walk { bkgd: true, ..st1 })
        } else {
            Ok(st1)
        }
    } else if c.ty == TRNS {
        if trns_ok(h, st1, d) {
            Ok(Walk { trns: Some(d), ..st1 })
        } else {
            Ok(st1)
        }
    } else if is_critical(c.ty) {
        // An unknown critical chunk is an error before the image data;
        // libpng (`png_read_end`) ignores one after it.
        if st1.phase == 0 {
            Err(false)
        } else {
            Ok(st1)
        }
    } else {
        // Other ancillary chunks do not affect the image and are skipped
        // unparsed.
        Ok(st1)
    }
}

/// Walks the chunks from `p` to IEND.
pub open spec fn walk(b: Seq<u8>, h: Ihdr, p: int, st: Walk) -> Option<Walk>
    decreases b.len() - p,
{
    match chunk_at(b, p) {
        None => None,
        Some(c) => match step(b, h, p, c, st) {
            Err(true) => Some(st),
            Err(false) => None,
            Ok(st2) => if p + 12 + c.len <= b.len() {
                walk(b, h, p + 12 + c.len, st2)
            } else {
                None
            },
        },
    }
}

/// The parsed file: header, palette, transparency and the image data
/// stream.
pub struct Png {
    pub hdr: Ihdr,
    /// Palette bytes (3 per entry); empty unless the colour type is 3.
    pub plte: Seq<u8>,
    pub trns: Option<Seq<u8>>,
    /// The decompressed image data: filtered scanlines (§7.3).
    pub raw: Seq<u8>,
}

/// The signature, IHDR, and the chunks after it up to IEND.
#[verifier::opaque]
pub open spec fn container(b: Seq<u8>) -> Option<(Ihdr, Walk)> {
    if b.len() < 8 || b.subrange(0, 8) != signature() {
        None
    } else {
        match chunk_at(b, 8) {
            None => None,
            Some(c) => if c.ty != IHDR || !c.crc_ok {
                None
            } else {
                match parse_ihdr(chunk_data(b, 8, c.len)) {
                    None => None,
                    Some(h) => match walk(b, h, (20 + c.len) as int, walk_start()) {
                        None => None,
                        Some(st) => Some((h, st)),
                    },
                }
            },
        }
    }
}

/// zlib decompression (RFC 1950), as vzlib specifies it: the output and the
/// number of input bytes used.
#[verifier::opaque]
pub open spec fn zlib(b: Seq<u8>) -> Option<(Seq<u8>, int)> {
    z::zlib_decompress(b)
}

/// Parses the container and decompresses the image data. The image data is
/// the concatenated data of the first run of IDAT chunks, which must be one
/// zlib stream (§10) that decompresses to at least `raw_size` bytes; the
/// image data is the first `raw_size` of them. Bytes after the end of the
/// zlib stream are ignored.
/// libpng: libpng also ignores decompressed bytes beyond what the image
/// needs ("Extra compressed data", a warning). It reads image data only
/// until the image is complete, so it also accepts a stream whose end or
/// Adler-32 check is damaged after the last needed byte; vpng rejects those.
#[verifier::opaque]
pub open spec fn parse(b: Seq<u8>) -> Option<Png> {
    match container(b) {
        None => None,
        Some((h, st)) => match zlib(st.idat) {
            None => None,
            Some((o, used)) => if o.len() < raw_size(h) {
                None
            } else {
                let raw = o.subrange(0, raw_size(h) as int);
                Some(
                    Png {
                        hdr: h,
                        plte: if h.ct == 3 {
                            st.plte.unwrap()
                        } else {
                            Seq::empty()
                        },
                        trns: st.trns,
                        raw,
                    },
                )
            },
        },
    }
}

// ---------------------------------------------------------------------------
// Interlacing (§8.2)
// ---------------------------------------------------------------------------

pub open spec fn npasses(h: Ihdr) -> nat {
    if h.interlace == 0 {
        1
    } else {
        7
    }
}

pub open spec fn x0(h: Ihdr, p: nat) -> nat {
    if h.interlace == 0 {
        0
    } else {
        seq![0nat, 4, 0, 2, 0, 1, 0][p as int]
    }
}

pub open spec fn y0(h: Ihdr, p: nat) -> nat {
    if h.interlace == 0 {
        0
    } else {
        seq![0nat, 0, 4, 0, 2, 0, 1][p as int]
    }
}

pub open spec fn dx(h: Ihdr, p: nat) -> nat {
    if h.interlace == 0 {
        1
    } else {
        seq![8nat, 8, 4, 4, 2, 2, 1][p as int]
    }
}

pub open spec fn dy(h: Ihdr, p: nat) -> nat {
    if h.interlace == 0 {
        1
    } else {
        seq![8nat, 8, 8, 4, 4, 2, 2][p as int]
    }
}

/// Width of pass `p`'s reduced image.
pub open spec fn pass_w(h: Ihdr, p: nat) -> nat {
    if h.w <= x0(h, p) {
        0
    } else {
        ((h.w - x0(h, p) + dx(h, p) - 1) as nat) / dx(h, p)
    }
}

pub open spec fn pass_h(h: Ihdr, p: nat) -> nat {
    if h.h <= y0(h, p) {
        0
    } else {
        ((h.h - y0(h, p) + dy(h, p) - 1) as nat) / dy(h, p)
    }
}

/// Bytes of image data for pass `p`: an empty pass has none, not even
/// filter bytes (§8.2).
pub open spec fn pass_size(h: Ihdr, p: nat) -> nat {
    if pass_w(h, p) == 0 || pass_h(h, p) == 0 {
        0
    } else {
        pass_h(h, p) * (1 + row_bytes(h, pass_w(h, p)))
    }
}

/// Where pass `p`'s data starts.
pub open spec fn pass_off(h: Ihdr, p: nat) -> nat
    decreases p,
{
    if p == 0 {
        0
    } else {
        pass_off(h, (p - 1) as nat) + pass_size(h, (p - 1) as nat)
    }
}

/// Bytes of decompressed image data.
pub open spec fn raw_size(h: Ihdr) -> nat {
    pass_off(h, npasses(h))
}

/// The pass that pixel `(x, y)` is transmitted in (the Adam7 pattern of
/// §8.2).
pub open spec fn pass_of(h: Ihdr, x: nat, y: nat) -> nat {
    if h.interlace == 0 {
        0
    } else if y % 2 == 1 {
        6
    } else if x % 2 == 1 {
        5
    } else if y % 4 == 2 {
        4
    } else if x % 4 == 2 {
        3
    } else if y % 8 == 4 {
        2
    } else if x % 8 == 4 {
        1
    } else {
        0
    }
}

// ---------------------------------------------------------------------------
// Filtering (§9)
// ---------------------------------------------------------------------------

pub open spec fn abs(x: int) -> int {
    if x < 0 {
        -x
    } else {
        x
    }
}

/// The Paeth predictor (§9.4).
pub open spec fn paeth(a: u8, b: u8, c: u8) -> u8 {
    let p = a as int + b as int - c as int;
    let pa = abs(p - a as int);
    let pb = abs(p - b as int);
    let pc = abs(p - c as int);
    if pa <= pb && pa <= pc {
        a
    } else if pb <= pc {
        b
    } else {
        c
    }
}

/// The predictor of filter type `ft` (§9.2): `a` is the byte to the left,
/// `b` above, `c` above and to the left.
pub open spec fn predict(ft: u8, a: u8, b: u8, c: u8) -> u8 {
    if ft == 1 {
        a
    } else if ft == 2 {
        b
    } else if ft == 3 {
        ((a as nat + b as nat) / 2) as u8
    } else if ft == 4 {
        paeth(a, b, c)
    } else {
        0
    }
}

/// The first `n` reconstructed bytes of a row filtered with type `ft`,
/// whose filtered bytes are `cur` and whose previous reconstructed row is
/// `prev` (§9.2). Bytes left of the row are 0.
pub open spec fn recon(ft: u8, prev: Seq<u8>, cur: Seq<u8>, bpp: nat, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        let r = recon(ft, prev, cur, bpp, (n - 1) as nat);
        let i = n - 1;
        let a = if i >= bpp {
            r[i - bpp]
        } else {
            0u8
        };
        let c = if i >= bpp {
            prev[i - bpp]
        } else {
            0u8
        };
        r.push(((cur[i] as nat + predict(ft, a, prev[i], c) as nat) % 256) as u8)
    }
}

pub open spec fn zeros(n: nat) -> Seq<u8> {
    Seq::new(n, |i: int| 0u8)
}

/// The first `n` reconstructed rows (each `rb` bytes, concatenated) of the
/// filtered rows starting at `raw[off]` (each a filter byte and `rb`
/// bytes). Above the first row is a row of zeros. A filter type above 4 is
/// an error (§9.2).
pub open spec fn recon_rows(raw: Seq<u8>, off: int, rb: nat, bpp: nat, n: nat) -> Option<Seq<u8>>
    decreases n,
{
    if n == 0 {
        Some(Seq::empty())
    } else {
        match recon_rows(raw, off, rb, bpp, (n - 1) as nat) {
            None => None,
            Some(done) => {
                let i = off + (n - 1) * (rb + 1);
                let ft = raw[i];
                if ft > 4 {
                    None
                } else {
                    let prev = if n == 1 {
                        zeros(rb)
                    } else {
                        done.subrange((n - 2) * rb, (n - 1) * rb)
                    };
                    Some(done + recon(ft, prev, raw.subrange(i + 1, i + 1 + rb), bpp, rb))
                }
            },
        }
    }
}

/// Pass `p`'s reconstructed reduced image (rows of `row_bytes(pass_w)`).
pub open spec fn pass_image(h: Ihdr, raw: Seq<u8>, p: nat) -> Option<Seq<u8>> {
    if pass_size(h, p) == 0 {
        Some(Seq::empty())
    } else {
        recon_rows(raw, pass_off(h, p) as int, row_bytes(h, pass_w(h, p)), filter_bpp(h), pass_h(h, p))
    }
}

/// The reconstructed reduced images of passes `0..n`.
pub open spec fn pass_images(h: Ihdr, raw: Seq<u8>, n: nat) -> Option<Seq<Seq<u8>>>
    decreases n,
{
    if n == 0 {
        Some(Seq::empty())
    } else {
        match (pass_images(h, raw, (n - 1) as nat), pass_image(h, raw, (n - 1) as nat)) {
            (Some(s), Some(i)) => Some(s.push(i)),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Samples
// ---------------------------------------------------------------------------

/// Sample `c` of pixel `x` in row `y` of a reduced image with rows of `rb`
/// bytes (§7.2): samples below 8 bits are packed from the most significant
/// bit; 16-bit samples are big-endian.
pub open spec fn sample(h: Ihdr, img: Seq<u8>, rb: nat, x: nat, y: nat, c: nat) -> nat {
    let d = h.depth;
    let k = (x * channels(h.ct) + c) * d;
    let base = y * rb;
    if d == 16 {
        be16(img, (base + k / 8) as int)
    } else if d == 8 {
        img[(base + k / 8) as int] as nat
    } else {
        (img[(base + k / 8) as int] as nat / pow2_nat((8 - k % 8 - d) as nat)) % pow2_nat(d)
    }
}

/// Sample `c` of pixel `(x, y)` of the full image.
pub open spec fn px_sample(h: Ihdr, imgs: Seq<Seq<u8>>, x: nat, y: nat, c: nat) -> nat {
    let p = pass_of(h, x, y);
    sample(h, imgs[p as int], row_bytes(h, pass_w(h, p)), x / dx(h, p), y / dy(h, p), c)
}

// ---------------------------------------------------------------------------
// Output formats
// ---------------------------------------------------------------------------

/// A sample scaled to 8 bits: low bit depths by bit replication (as
/// libpng's `png_set_expand`), 16 bits by keeping the high byte (as
/// `png_set_strip_16`).
pub open spec fn to8(depth: nat, v: nat) -> u8 {
    if depth == 16 {
        (v / 256) as u8
    } else if depth == 8 {
        v as u8
    } else if depth == 4 {
        (v * 17) as u8
    } else if depth == 2 {
        (v * 85) as u8
    } else {
        (v * 255) as u8
    }
}

/// Byte `j` (0 red, 1 green, 2 blue, 3 alpha) of pixel `(x, y)` as 8-bit
/// RGBA: palette indices expanded, grey copied to red, green and blue, and
/// tRNS turned into alpha (§11.3.1.1, as libpng's `png_set_expand`,
/// `png_set_gray_to_rgb`, `png_set_strip_16` and an opaque filler).
/// libpng: a palette index beyond the palette gives black (libpng's
/// palette array is zero-filled to 256 entries); tRNS samples are compared
/// modulo 2^depth (`png_do_expand` masks them).
pub open spec fn rgba_byte(png: Png, imgs: Seq<Seq<u8>>, x: nat, y: nat, j: nat) -> u8 {
    let h = png.hdr;
    let d = h.depth;
    let m = pow2_nat(d);
    if h.ct == 3 {
        let i = px_sample(h, imgs, x, y, 0);
        if j == 3 {
            match png.trns {
                Some(t) => if i < t.len() {
                    t[i as int]
                } else {
                    255u8
                },
                None => 255u8,
            }
        } else if 3 * i + 3 <= png.plte.len() {
            png.plte[(3 * i + j) as int]
        } else {
            0u8
        }
    } else if h.ct == 0 || h.ct == 4 {
        let g = px_sample(h, imgs, x, y, 0);
        if j < 3 {
            to8(d, g)
        } else if h.ct == 4 {
            to8(d, px_sample(h, imgs, x, y, 1))
        } else {
            match png.trns {
                Some(t) => if g == be16(t, 0) % m {
                    0u8
                } else {
                    255u8
                },
                None => 255u8,
            }
        }
    } else {
        if j < 3 {
            to8(d, px_sample(h, imgs, x, y, j))
        } else if h.ct == 6 {
            to8(d, px_sample(h, imgs, x, y, 3))
        } else {
            match png.trns {
                Some(t) => if px_sample(h, imgs, x, y, 0) == be16(t, 0) % m && px_sample(
                    h,
                    imgs,
                    x,
                    y,
                    1,
                ) == be16(t, 2) % m && px_sample(h, imgs, x, y, 2) == be16(t, 4) % m {
                    0u8
                } else {
                    255u8
                },
                None => 255u8,
            }
        }
    }
}

/// The image as 8-bit RGBA, row by row.
pub open spec fn rgba8(png: Png, imgs: Seq<Seq<u8>>) -> Seq<u8> {
    let w = png.hdr.w;
    Seq::new(
        4 * w * png.hdr.h,
        |k: int| rgba_byte(png, imgs, ((k / 4) % w as int) as nat, ((k / 4) / w as int) as nat, (k % 4) as nat),
    )
}

/// Byte `j` of row `y` of the image in its own format (§7.2): pixels of 8
/// or more bits are copied, sub-byte pixels are packed from the most
/// significant bit with the padding bits at the end of a row set to 0.
pub open spec fn native_byte(h: Ihdr, imgs: Seq<Seq<u8>>, j: nat, y: nat) -> u8 {
    let bits = pixel_bits(h);
    if bits >= 8 {
        let bp = bits / 8;
        let x = j / bp;
        let p = pass_of(h, x, y);
        imgs[p as int][((y / dy(h, p)) * row_bytes(h, pass_w(h, p)) + (x / dx(h, p)) * bp + j % bp) as int]
    } else {
        packed(h, imgs, j, y, 8nat / bits)
    }
}

/// The first `n` pixels of byte `j` of row `y`, packed (`pixel_bits < 8`).
pub open spec fn packed(h: Ihdr, imgs: Seq<Seq<u8>>, j: nat, y: nat, n: nat) -> u8
    decreases n,
{
    if n == 0 {
        0u8
    } else {
        let t = (n - 1) as nat;
        let per = 8nat / h.depth;
        let x = j * per + t;
        let rest = packed(h, imgs, j, y, t);
        if x < h.w {
            (rest as nat + px_sample(h, imgs, x, y, 0) * pow2_nat((8 - (t + 1) * h.depth) as nat)) as u8
        } else {
            rest
        }
    }
}

/// The image in its own format: `h` rows of `row_bytes(w)` bytes.
pub open spec fn native(h: Ihdr, imgs: Seq<Seq<u8>>) -> Seq<u8> {
    let rb = row_bytes(h, h.w);
    Seq::new(rb * h.h, |k: int| native_byte(h, imgs, (k % rb as int) as nat, (k / rb as int) as nat))
}

/// Output pixel formats.
pub enum Format {
    /// 8-bit RGBA, 4 bytes per pixel.
    Rgba8,
    /// The file's own format, deinterlaced.
    Native,
}

/// Decodes a PNG file: its header and the image in format `f`.
pub open spec fn decode(b: Seq<u8>, f: Format) -> Option<(Ihdr, Seq<u8>)> {
    match parse(b) {
        None => None,
        Some(png) => match pass_images(png.hdr, png.raw, npasses(png.hdr)) {
            None => None,
            Some(imgs) => Some(
                (
                    png.hdr,
                    match f {
                        Format::Rgba8 => rgba8(png, imgs),
                        Format::Native => native(png.hdr, imgs),
                    },
                ),
            ),
        },
    }
}

} // verus!

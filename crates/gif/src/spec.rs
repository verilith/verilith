//! Executable-independent specification of GIF decoding (Graphics
//! Interchange Format, Version 89a, CompuServe 1990; section numbers below
//! refer to it).
//!
//! Everything here is a total function over `Seq<u8>`. This file, the bit
//! string definitions it uses from verilith-core (`verilith_core::bits`),
//! Verus and the Rust compiler are the trusted base: the decoder is proven
//! to compute exactly these functions.
//!
//! The reference decoder is giflib 5.2.2 (`DGifSlurp`), with the 2026
//! security fixes Debian and Ubuntu ship (`misc-security-issues.patch`,
//! which rejects minimum code sizes below 2). Where giflib accepts
//! or rejects differently from what the GIF specification alone implies,
//! or where the specification leaves a choice, the choice made here is
//! marked "giflib:" and listed in the README.
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
#[cfg(verus_only)]
use verilith_core::bits::bits;

verus! {

// ---------------------------------------------------------------------------
// Bytes
// ---------------------------------------------------------------------------

/// The little-endian value of the two bytes at `i` (§4: "unsigned").
pub open spec fn le16(b: Seq<u8>, i: int) -> nat {
    b[i] as nat + 256 * b[i + 1] as nat
}

/// Bytes in a colour table whose size field is `k` (§18, §20: 3 x
/// 2^(k+1)).
pub open spec fn table_len(k: nat) -> nat {
    3 * pow2(k + 1)
}

// ---------------------------------------------------------------------------
// Data sub-blocks (§15)
// ---------------------------------------------------------------------------

/// The chain of data sub-blocks at `p`: each a size byte and that many
/// bytes, ending with a size byte of 0 (the block terminator, §16). The
/// result is the sub-blocks' data, concatenated, and the position after the
/// terminator; `None` if the chain runs past the end of the file.
pub open spec fn sub_blocks(b: Seq<u8>, p: int) -> Option<(Seq<u8>, int)>
    decreases b.len() - p,
{
    if p < 0 || p >= b.len() {
        None
    } else if b[p] == 0 {
        Some((Seq::empty(), p + 1))
    } else if p + 1 + b[p] as int > b.len() {
        None
    } else {
        match sub_blocks(b, p + 1 + b[p] as int) {
            Some((d, e)) => Some((b.subrange(p + 1, p + 1 + b[p] as int) + d, e)),
            None => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Header and logical screen (§17, §18, §19)
// ---------------------------------------------------------------------------

/// The logical screen descriptor and global colour table.
pub struct Screen {
    pub width: nat,
    pub height: nat,
    /// The packed fields byte: global colour table flag (0x80), colour
    /// resolution (0x70), sort flag (0x08), size of the global colour table
    /// (0x07).
    pub flags: u8,
    pub bg: nat,
    pub aspect: nat,
    /// The global colour table: 3 bytes (red, green, blue) per entry.
    pub gct: Option<Seq<u8>>,
}

/// The header, logical screen descriptor and global colour table, and the
/// position after them. giflib: only the signature "GIF" is checked; the
/// version ("87a", "89a") is not (`DGifOpen`).
pub open spec fn screen(b: Seq<u8>) -> Option<(Screen, int)> {
    if b.len() < 13 || b[0] != 0x47 || b[1] != 0x49 || b[2] != 0x46 {
        None
    } else {
        let flags = b[10];
        let n = if flags & 0x80 != 0 { table_len((flags & 7) as nat) as int } else { 0 };
        if 13 + n > b.len() {
            None
        } else {
            Some((
                Screen {
                    width: le16(b, 6),
                    height: le16(b, 8),
                    flags,
                    bg: b[11] as nat,
                    aspect: b[12] as nat,
                    gct: if flags & 0x80 != 0 { Some(b.subrange(13, 13 + n)) } else { None },
                },
                13 + n,
            ))
        }
    }
}

// ---------------------------------------------------------------------------
// Graphic control extension (§23)
// ---------------------------------------------------------------------------

pub struct Gce {
    /// Disposal method, 0 to 7.
    pub disposal: nat,
    pub user_input: bool,
    /// Delay time, in hundredths of a second.
    pub delay: nat,
    /// The transparent colour index, if the transparency flag is set.
    pub transparent: Option<nat>,
}

/// The graphic control block whose first data sub-block is at `q`: present
/// if that sub-block is 4 bytes long. giflib: a block of another length
/// is not used, and leaves the image with no graphic control
/// (`DGifExtensionToGCB`).
pub open spec fn gce_at(b: Seq<u8>, q: int) -> Option<Gce> {
    if b[q] != 4 {
        None
    } else {
        let f = b[q + 1];
        Some(
            Gce {
                disposal: ((f >> 2) & 7) as nat,
                user_input: f & 2 != 0,
                delay: le16(b, q + 2),
                transparent: if f & 1 != 0 { Some(b[q + 4] as nat) } else { None },
            },
        )
    }
}

// ---------------------------------------------------------------------------
// LZW (Appendix F)
// ---------------------------------------------------------------------------

/// Codes are at most 12 bits, so a table has at most 4096 entries.
pub spec const MAX_CODES: nat = 4096;

/// The clear code for minimum code size `m`; the end-of-information code is
/// one more.
pub open spec fn clear_code(m: nat) -> nat {
    pow2(m)
}

/// The decoder's state between codes.
pub struct Lzw {
    /// The string of each code. Codes below the clear code are the one-byte
    /// roots; the clear and end codes have empty strings and are never
    /// looked up; later entries were added by the decoder.
    pub dict: Seq<Seq<u8>>,
    /// The current code width in bits.
    pub width: nat,
    /// The previous code, unless this is the first code after a clear code.
    pub prev: Option<nat>,
    /// The output so far.
    pub out: Seq<u8>,
}

/// The table after a clear code: the roots, the clear and end codes.
pub open spec fn init_dict(m: nat) -> Seq<Seq<u8>> {
    Seq::new(
        clear_code(m) + 2,
        |i: int| if i < clear_code(m) { seq![i as u8] } else { Seq::empty() },
    )
}

/// The state after a clear code; the output is kept.
pub open spec fn reset(m: nat, out: Seq<u8>) -> Lzw {
    Lzw { dict: init_dict(m), width: m + 1, prev: None, out }
}

/// The code width after a code that leaves the table with `n` entries:
/// one more bit once the table has as many entries as the width can name,
/// up to 12. (The first code after a clear code adds no entry, and with a
/// minimum code size of at least 2 its table is too small to widen the
/// code.)
pub open spec fn next_width(n: nat, w: nat) -> nat {
    if n >= pow2(w) && w < 12 {
        w + 1
    } else {
        w
    }
}

/// One code, `c`, in state `s`, for a code that is neither the clear nor
/// the end code. `None` if the code is not in the table (and is not the
/// one the decoder is about to add).
pub open spec fn lzw_code(m: nat, s: Lzw, c: nat) -> Option<Lzw> {
    match s.prev {
        None => if c < clear_code(m) {
            Some(
                Lzw {
                    dict: s.dict,
                    width: next_width(s.dict.len(), s.width),
                    prev: Some(c),
                    out: s.out + s.dict[c as int],
                },
            )
        } else {
            None
        },
        Some(p) => {
            let n = s.dict.len();
            if c < n {
                // A code in the table: its string, and a new entry of the
                // previous string and the first byte of this one.
                let str = s.dict[c as int];
                let dict = if n < MAX_CODES {
                    s.dict.push(s.dict[p as int] + seq![str[0]])
                } else {
                    s.dict
                };
                Some(
                    Lzw {
                        dict,
                        width: next_width(dict.len(), s.width),
                        prev: Some(c),
                        out: s.out + str,
                    },
                )
            } else if c == n && n < MAX_CODES {
                // The code about to be added: the previous string and its
                // own first byte.
                let str = s.dict[p as int] + seq![s.dict[p as int][0]];
                let dict = s.dict.push(str);
                Some(
                    Lzw {
                        dict,
                        width: next_width(dict.len(), s.width),
                        prev: Some(c),
                        out: s.out + str,
                    },
                )
            } else {
                // giflib: decodes a code past the table into whatever its
                // stale table entries hold; it is an error here.
                None
            }
        },
    }
}

/// Decodes `need` bytes from the codes in `data` from bit `q` on, in
/// state `s`. Codes are packed least significant bit first (Appendix F),
/// as `bits` reads them. Decoding stops once the output has `need` bytes;
/// what follows in `data` is not read, and a longer last string is cut to
/// `need`. giflib: an end code, or the end of the data, before `need`
/// bytes is an error (`DGifGetLine` needs every pixel); codes after the
/// last pixel are not read.
pub open spec fn lzw_run(data: Seq<u8>, m: nat, need: nat, s: Lzw, q: int) -> Option<Seq<u8>>
    decreases 8 * data.len() - q,
{
    if s.out.len() >= need {
        Some(s.out.subrange(0, need as int))
    } else if q < 0 || q + s.width > 8 * data.len() || s.width == 0 {
        None
    } else {
        let c = bits(data, q, s.width);
        if c == clear_code(m) {
            lzw_run(data, m, need, reset(m, s.out), q + s.width)
        } else if c == clear_code(m) + 1 {
            None
        } else {
            match lzw_code(m, s, c) {
                Some(s2) => lzw_run(data, m, need, s2, q + s.width),
                None => None,
            }
        }
    }
}

/// The first `need` bytes that the LZW data `data` with minimum code size
/// `m` decodes to.
pub open spec fn lzw(data: Seq<u8>, m: nat, need: nat) -> Option<Seq<u8>> {
    lzw_run(data, m, need, reset(m, Seq::empty()), 0)
}

// ---------------------------------------------------------------------------
// Interlacing (Appendix E)
// ---------------------------------------------------------------------------

/// Where row `y` of an interlaced image of height `h` comes in the data:
/// pass 1 has every 8th row from 0, pass 2 every 8th from 4, pass 3 every
/// 4th from 2, pass 4 every 2nd from 1.
pub open spec fn interlaced_row(h: nat, y: nat) -> nat {
    let n1 = (h + 7) / 8;
    let n2 = (h + 3) / 8;
    let n3 = (h + 1) / 4;
    if y % 8 == 0 {
        y / 8
    } else if y % 8 == 4 {
        n1 + y / 8
    } else if y % 4 == 2 {
        n1 + n2 + y / 4
    } else {
        n1 + n2 + n3 + y / 2
    }
}

/// The image's rows in order, from the decoded data.
pub open spec fn deinterlace(px: Seq<u8>, w: nat, h: nat) -> Seq<u8> {
    Seq::new(
        w * h,
        |i: int| px[interlaced_row(h, (i / w as int) as nat) * w + i % w as int],
    )
}

// ---------------------------------------------------------------------------
// Images (§20, §22)
// ---------------------------------------------------------------------------

/// One image of the data stream.
pub struct Image {
    pub left: nat,
    pub top: nat,
    pub width: nat,
    pub height: nat,
    /// The packed fields byte: local colour table flag (0x80), interlace
    /// flag (0x40), sort flag (0x20), size of the local colour table (0x07).
    pub flags: u8,
    pub lct: Option<Seq<u8>>,
    /// The graphic control extension that applies to the image.
    pub gce: Option<Gce>,
    /// The LZW minimum code size.
    pub min_code: nat,
    /// The colour index of each pixel, row by row from the top, `width`
    /// per row.
    pub pixels: Seq<u8>,
}

/// Largest number of pixels in an image. giflib: `DGifSlurp` rejects an
/// image with more than `INT_MAX` pixels, and one with a width or height
/// of 0.
pub spec const MAX_PIXELS: nat = 0x7fff_ffff;

/// The image whose descriptor follows the image separator at `p - 1`, with
/// graphic control `gce`, and the position after its data. The LZW
/// minimum code size must be 2 to 8 (Appendix F; giflib checks the same
/// range).
pub open spec fn image_at(b: Seq<u8>, p: int, gce: Option<Gce>) -> Option<(Image, int)> {
    if p + 9 > b.len() {
        None
    } else {
        let w = le16(b, p + 4);
        let h = le16(b, p + 6);
        let flags = b[p + 8];
        let n = if flags & 0x80 != 0 { table_len((flags & 7) as nat) as int } else { 0 };
        let c = p + 9 + n;
        if w == 0 || h == 0 || w * h > MAX_PIXELS || c >= b.len() || b[c] < 2 || b[c] > 8 {
            None
        } else {
            match sub_blocks(b, c + 1) {
                None => None,
                Some((data, e)) => match lzw(data, b[c] as nat, w * h) {
                    None => None,
                    Some(px) => Some((
                        Image {
                            left: le16(b, p),
                            top: le16(b, p + 2),
                            width: w,
                            height: h,
                            flags,
                            lct: if flags & 0x80 != 0 { Some(b.subrange(p + 9, c)) } else { None },
                            gce,
                            min_code: b[c] as nat,
                            pixels: if flags & 0x40 != 0 { deinterlace(px, w, h) } else { px },
                        },
                        e,
                    )),
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The data stream (§16, §27)
// ---------------------------------------------------------------------------

/// The blocks from `p` on, with `gce` the graphic control found since the
/// last image (`None` if none was, `Some(g)` with what the first one said)
/// and `imgs` the images so far.
///
/// An extension (0x21) is a label and a sub-block chain; an image (0x2C) a
/// descriptor and its data; the trailer (0x3B) ends the stream, and what
/// follows it is not read. Any other byte is an error, and so is a stream
/// with no trailer or no image. giflib: of several graphic control
/// extensions before an image, the first one counts (the GIF specification
/// allows at most one); an extension's label is not checked, and
/// extensions other than graphic control are skipped. giflib: an extension
/// with no data sub-blocks (its label followed by the terminator) is read
/// here as the GIF specification defines it; giflib reads one more
/// sub-block after the terminator (`DGifSlurp` calls
/// `DGifGetExtensionNext` again after an empty first block), so it
/// misreads the rest of the file.
pub open spec fn walk(b: Seq<u8>, p: int, gce: Option<Option<Gce>>, imgs: Seq<Image>) -> Option<Seq<Image>>
    decreases b.len() - p,
    via walk_decreases
{
    if p < 0 || p >= b.len() {
        None
    } else if b[p] == 0x3B {
        if imgs.len() > 0 {
            Some(imgs)
        } else {
            None
        }
    } else if b[p] == 0x21 {
        match sub_blocks(b, p + 2) {
            None => None,
            Some((_, e)) => {
                // A graphic control extension's first sub-block, if it has
                // one, is at p + 2.
                let gce2 = if gce is None && b[p + 1] == 0xF9 && b[p + 2] != 0 {
                    Some(gce_at(b, p + 2))
                } else {
                    gce
                };
                walk(b, e, gce2, imgs)
            },
        }
    } else if b[p] == 0x2C {
        match image_at(b, p + 1, match gce { Some(g) => g, None => None }) {
            None => None,
            Some((img, e)) => walk(b, e, None, imgs.push(img)),
        }
    } else {
        None
    }
}

/// A chain of sub-blocks ends after it starts, and inside the file.
pub proof fn lemma_sub_blocks_end(b: Seq<u8>, p: int)
    ensures
        sub_blocks(b, p) matches Some((_, e)) ==> p < e <= b.len(),
    decreases b.len() - p,
{
    if 0 <= p < b.len() && b[p] != 0 && p + 1 + b[p] as int <= b.len() {
        lemma_sub_blocks_end(b, p + 1 + b[p] as int);
    }
}

#[via_fn]
proof fn walk_decreases(b: Seq<u8>, p: int, gce: Option<Option<Gce>>, imgs: Seq<Image>) {
    lemma_sub_blocks_end(b, p + 2);
    if 0 <= p + 1 && p + 1 + 9 <= b.len() {
        let flags = b[p + 9];
        let n = if flags & 0x80 != 0 { table_len((flags & 7) as nat) as int } else { 0 };
        lemma_sub_blocks_end(b, p + 1 + 9 + n + 1);
        assert(table_len((flags & 7) as nat) >= 0);
    }
}

/// A decoded GIF file: the logical screen and the images, in order.
pub struct Gif {
    pub screen: Screen,
    pub images: Seq<Image>,
}

/// Decodes a GIF file, or `None` if it is not one this specification
/// accepts.
pub open spec fn decode(b: Seq<u8>) -> Option<Gif> {
    match screen(b) {
        None => None,
        Some((s, p)) => match walk(b, p, None, Seq::empty()) {
            None => None,
            Some(imgs) => Some(Gif { screen: s, images: imgs }),
        },
    }
}

} // verus!

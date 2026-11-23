//! Executable-independent specification of TIFF decoding (TIFF Revision
//! 6.0, Adobe 1992; section numbers below refer to it).
//!
//! Everything here is a total function over `Seq<u8>`. This file, the zlib
//! specification it uses from verilith-zlib (`verilith_zlib::spec`), Verus
//! and the Rust compiler are the trusted base: the decoder is proven to
//! compute exactly these functions.
//!
//! What is decoded is the first image (IFD 0) of a classic TIFF file, into
//! its samples as stored ("native"): each plane's rows, top to bottom, with
//! multi-byte samples little-endian. The reference decoder is libtiff 4.5
//! (`TIFFReadEncodedStrip` and `TIFFReadEncodedTile` on every strip or
//! tile). libtiff accepts many damaged files by guessing what they meant;
//! this specification does not guess. Where it reads a file differently
//! from libtiff, or where TIFF leaves a choice, the choice made here is
//! marked "libtiff:" and listed in the README.
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
#[cfg(verus_only)]
use verilith_zlib::spec as z;

verus! {

// ---------------------------------------------------------------------------
// Bytes (§2)
// ---------------------------------------------------------------------------

/// The 16-bit value at `i`, little-endian if `le` ("II"), else big-endian
/// ("MM").
pub open spec fn u16_at(b: Seq<u8>, le: bool, i: int) -> nat {
    if le {
        b[i] as nat + 256 * b[i + 1] as nat
    } else {
        256 * b[i] as nat + b[i + 1] as nat
    }
}

/// The 32-bit value at `i`.
pub open spec fn u32_at(b: Seq<u8>, le: bool, i: int) -> nat {
    if le {
        u16_at(b, le, i) + 65536 * u16_at(b, le, i + 2)
    } else {
        65536 * u16_at(b, le, i) + u16_at(b, le, i + 2)
    }
}

// ---------------------------------------------------------------------------
// Header and image file directory (§2)
// ---------------------------------------------------------------------------

/// The byte order and the offset of the first IFD. libtiff: BigTIFF (43)
/// is not read here.
pub open spec fn header(b: Seq<u8>) -> Option<(bool, nat)> {
    if b.len() < 8 {
        None
    } else if !((b[0] == 0x49 && b[1] == 0x49) || (b[0] == 0x4D && b[1] == 0x4D)) {
        None
    } else {
        let le = b[0] == 0x49;
        if u16_at(b, le, 2) != 42 {
            None
        } else {
            Some((le, u32_at(b, le, 4)))
        }
    }
}

/// Where entry `i` of the IFD at `o` starts.
pub open spec fn entry_pos(o: nat, i: nat) -> int {
    (o + 2 + 12 * i) as int
}

/// The index of the first of the IFD's `n` entries, from `i` on, with tag
/// `tag`. libtiff: entries need not be sorted (libtiff warns); of two with
/// the same tag the first is used.
pub open spec fn find(b: Seq<u8>, le: bool, o: nat, n: nat, tag: nat, i: nat) -> Option<nat>
    decreases n - i,
{
    if i >= n {
        None
    } else if u16_at(b, le, entry_pos(o, i)) == tag {
        Some(i)
    } else {
        find(b, le, o, n, tag, i + 1)
    }
}

/// Bytes per value of the field types read here: BYTE (1), SHORT (3) and
/// LONG (4).
pub open spec fn type_size(ty: nat) -> nat {
    if ty == 1 {
        1
    } else if ty == 3 {
        2
    } else {
        4
    }
}

/// Value `k` of a field of type `ty` whose values start at `pos`.
pub open spec fn value(b: Seq<u8>, le: bool, ty: nat, pos: int, k: int) -> nat {
    if ty == 1 {
        b[pos + k] as nat
    } else if ty == 3 {
        u16_at(b, le, pos + 2 * k)
    } else {
        u32_at(b, le, pos + 4 * k)
    }
}

/// The values of the field with tag `tag` in the IFD at `o` with `n`
/// entries: `Some(None)` if there is none, `None` if its type is not an
/// unsigned integer type or its values are not inside the file. Values of
/// at most 4 bytes in all are in the entry itself (§2, "Value/Offset").
/// libtiff: libtiff also converts signed and 64-bit types where the value
/// fits; they are rejected here.
#[verifier::opaque]
pub open spec fn field(b: Seq<u8>, le: bool, o: nat, n: nat, tag: nat) -> Option<Option<Seq<nat>>> {
    match find(b, le, o, n, tag, 0) {
        None => Some(None),
        Some(i) => {
            let e = entry_pos(o, i);
            let ty = u16_at(b, le, e + 2);
            let cnt = u32_at(b, le, e + 4);
            if ty != 1 && ty != 3 && ty != 4 {
                None
            } else {
                let size = cnt * type_size(ty);
                let pos = if size <= 4 { e + 8 } else { u32_at(b, le, e + 8) as int };
                if pos + size > b.len() {
                    None
                } else {
                    Some(Some(Seq::new(cnt, |k: int| value(b, le, ty, pos, k))))
                }
            }
        },
    }
}

/// A field with one value, or `default` if it is absent.
#[verifier::opaque]
pub open spec fn scalar(b: Seq<u8>, le: bool, o: nat, n: nat, tag: nat, default: nat) -> Option<nat> {
    match field(b, le, o, n, tag) {
        None => None,
        Some(None) => Some(default),
        Some(Some(v)) => if v.len() == 1 {
            Some(v[0])
        } else {
            None
        },
    }
}

// Tags (§8, Appendix A).
pub spec const IMAGE_WIDTH: nat = 256;
pub spec const IMAGE_LENGTH: nat = 257;
pub spec const BITS_PER_SAMPLE: nat = 258;
pub spec const COMPRESSION: nat = 259;
pub spec const PHOTOMETRIC: nat = 262;
pub spec const FILL_ORDER: nat = 266;
pub spec const STRIP_OFFSETS: nat = 273;
pub spec const SAMPLES_PER_PIXEL: nat = 277;
pub spec const ROWS_PER_STRIP: nat = 278;
pub spec const STRIP_BYTE_COUNTS: nat = 279;
pub spec const PLANAR_CONFIG: nat = 284;
pub spec const PREDICTOR: nat = 317;
pub spec const COLORMAP: nat = 320;
pub spec const EXTRA_SAMPLES: nat = 338;
pub spec const SAMPLE_FORMAT: nat = 339;
pub spec const SMIN_SAMPLE_VALUE: nat = 340;
pub spec const SMAX_SAMPLE_VALUE: nat = 341;

/// A field that, if present, has `spp` values (whatever its type).
pub open spec fn count_is(b: Seq<u8>, le: bool, o: nat, n: nat, tag: nat, spp: nat) -> bool {
    match find(b, le, o, n, tag, 0) {
        None => true,
        Some(i) => u32_at(b, le, entry_pos(o, i) + 4) == spp,
    }
}
pub spec const TILE_WIDTH: nat = 322;
pub spec const TILE_LENGTH: nat = 323;
pub spec const TILE_OFFSETS: nat = 324;
pub spec const TILE_BYTE_COUNTS: nat = 325;

// Compression schemes read here.
pub spec const NONE: nat = 1;
pub spec const LZW: nat = 5;
pub spec const DEFLATE: nat = 8;
pub spec const DEFLATE_OLD: nat = 32946;
pub spec const PACKBITS: nat = 32773;

pub open spec fn compression_ok(c: nat) -> bool {
    c == NONE || c == LZW || c == DEFLATE || c == DEFLATE_OLD || c == PACKBITS
}

/// Whether the scheme takes a predictor (§14). libtiff: the Predictor tag
/// is only read for LZW and Deflate; for the others it is ignored.
pub open spec fn uses_predictor(c: nat) -> bool {
    c == LZW || c == DEFLATE || c == DEFLATE_OLD
}

/// BitsPerSample: one value, or one per sample, all the same, 1 to 32.
/// libtiff: like libtiff, a single value stands for every sample, and
/// values past the first `spp` are not looked at.
pub open spec fn bits_per_sample(v: Option<Seq<nat>>, spp: nat) -> Option<nat> {
    match v {
        None => Some(1),
        Some(v) => {
            if v.len() == 0 {
                None
            } else if v.len() != 1 && (v.len() < spp || exists|k: int| 0 <= k < spp && #[trigger] v[k] != v[0]) {
                None
            } else if 1 <= v[0] <= 32 {
                Some(v[0])
            } else {
                None
            }
        },
    }
}

/// `ceil(a / 8)`.
pub open spec fn bytes_for(a: nat) -> nat {
    (a + 7) / 8
}

/// `ceil(a / d)`.
pub open spec fn div_up(a: nat, d: nat) -> nat {
    ((a + d - 1) as int / d as int) as nat
}

/// What the IFD says about the image.
pub struct Params {
    pub le: bool,
    pub width: nat,
    pub height: nat,
    pub bps: nat,
    pub spp: nat,
    pub compression: nat,
    pub photometric: Option<nat>,
    /// 1 unsigned, 2 signed, 3 floating point, 4 undefined.
    pub sample_format: nat,
    /// 1 (samples of a pixel together) or 2 (one plane per sample).
    pub planar: nat,
    /// 2 for horizontal differencing, else 1.
    pub predictor: nat,
    pub tiled: bool,
    /// Rows per strip, or the tile size.
    pub rps: nat,
    pub tw: nat,
    pub th: nat,
    pub offsets: Seq<nat>,
    pub counts: Seq<nat>,
}

impl Params {
    /// Planes in the file and in the output.
    pub open spec fn planes(self) -> nat {
        if self.planar == 2 { self.spp } else { 1 }
    }

    /// Samples per pixel in one plane.
    pub open spec fn sc(self) -> nat {
        if self.planar == 2 { 1 } else { self.spp }
    }

    /// Bytes in a row of the image, in one plane.
    pub open spec fn row_bytes(self) -> nat {
        bytes_for(self.width * self.sc() * self.bps)
    }

    /// Bytes in a row of a tile.
    pub open spec fn tile_row_bytes(self) -> nat {
        (self.tw * self.sc() * self.bps) / 8
    }

    /// Strips per plane.
    pub open spec fn strips(self) -> nat {
        div_up(self.height, self.rps)
    }

    pub open spec fn tiles_across(self) -> nat {
        div_up(self.width, self.tw)
    }

    pub open spec fn tiles_down(self) -> nat {
        div_up(self.height, self.th)
    }

    /// Strips or tiles in the file.
    pub open spec fn chunks(self) -> nat {
        if self.tiled {
            self.planes() * (self.tiles_across() * self.tiles_down())
        } else {
            self.planes() * self.strips()
        }
    }

    /// Pixels per row of a strip or tile.
    pub open spec fn chunk_width(self) -> nat {
        if self.tiled { self.tw } else { self.width }
    }

    /// Bytes per row of a strip or tile.
    pub open spec fn chunk_row_bytes(self) -> nat {
        if self.tiled { self.tile_row_bytes() } else { self.row_bytes() }
    }

    /// Rows in strip or tile `k`: every tile has `th`; every strip has
    /// `rps` but the last of each plane, which has the rows that are left.
    pub open spec fn chunk_rows(self, k: nat) -> nat {
        if self.tiled {
            self.th
        } else {
            let j = k % self.strips();
            if (j + 1) * self.rps <= self.height { self.rps } else { (self.height - j * self.rps) as nat }
        }
    }

    /// Bytes strip or tile `k` decodes to.
    pub open spec fn chunk_size(self, k: nat) -> nat {
        self.chunk_rows(k) * self.chunk_row_bytes()
    }

    /// Bytes in the output: every plane, every row.
    pub open spec fn image_size(self) -> nat {
        self.planes() * (self.height * self.row_bytes())
    }
}

/// The image's parameters from the IFD at `o` (§8 baseline fields, §13
/// PackBits, §14 Predictor, §15 tiles, Appendix A defaults). libtiff:
/// StripByteCounts is required here; libtiff estimates it when it is
/// missing or looks wrong for a single uncompressed strip.
pub open spec fn params(b: Seq<u8>, le: bool, o: nat) -> Option<Params> {
    if o + 2 > b.len() {
        None
    } else {
        let n = u16_at(b, le, o as int);
        if n == 0 || o + 2 + 12 * n > b.len() {
            None
        } else {
            match (field(b, le, o, n, IMAGE_WIDTH), field(b, le, o, n, IMAGE_LENGTH)) {
                (Some(Some(wv)), Some(Some(hv))) => {
                    match (
                        scalar(b, le, o, n, SAMPLES_PER_PIXEL, 1),
                        scalar(b, le, o, n, COMPRESSION, 1),
                        scalar(b, le, o, n, PLANAR_CONFIG, 1),
                        scalar(b, le, o, n, PREDICTOR, 1),
                        scalar(b, le, o, n, FILL_ORDER, 1),
                        scalar(b, le, o, n, ROWS_PER_STRIP, 0xffff_ffff),
                        field(b, le, o, n, PHOTOMETRIC),
                    ) {
                        (Some(spp), Some(comp), Some(planar), Some(pred), Some(fill), Some(rps), Some(ph)) => {
                            match field(b, le, o, n, BITS_PER_SAMPLE) {
                                None => None,
                                Some(bv) => match bits_per_sample(bv, spp) {
                                    None => None,
                                    Some(bps) => params2(b, le, o, n, wv, hv, spp, comp, planar, pred, fill, rps, ph, bps),
                                },
                            }
                        },
                        _ => None,
                    }
                },
                _ => None,
            }
        }
    }
}

/// The rest of `params`, once the scalar fields are read.
pub open spec fn params2(
    b: Seq<u8>,
    le: bool,
    o: nat,
    n: nat,
    wv: Seq<nat>,
    hv: Seq<nat>,
    spp: nat,
    comp: nat,
    planar: nat,
    pred: nat,
    fill: nat,
    rps: nat,
    ph: Option<Seq<nat>>,
    bps: nat,
) -> Option<Params> {
    let predictor = if uses_predictor(comp) { pred } else { 1 };
    if wv.len() != 1 || hv.len() != 1 || wv[0] == 0 || hv[0] == 0 || spp == 0 || !compression_ok(comp)
        || (planar != 1 && planar != 2) || rps == 0 {
        None
    } else if fill != 1 {
        // libtiff: FillOrder 2 (bits reversed in each byte) is read by
        // libtiff and not here.
        None
    } else if predictor != 1 && !(predictor == 2 && (bps == 8 || bps == 16 || bps == 32)) {
        // libtiff: the floating-point predictor (3) is read by libtiff and
        // not here; horizontal differencing needs 8-, 16- or 32-bit
        // samples in both.
        None
    } else {
        let photometric = match ph {
            Some(v) => if v.len() == 1 { Some(Some(v[0])) } else { None },
            None => Some(None),
        };
        match (
            photometric,
            field(b, le, o, n, TILE_WIDTH),
            field(b, le, o, n, TILE_LENGTH),
        ) {
            (Some(photometric), Some(twf), Some(thf)) => match extras(b, le, o, n, spp, bps, photometric) {
                None => None,
                Some(fmt) => {
                let base = Params {
                    le,
                    width: wv[0],
                    height: hv[0],
                    bps,
                    spp,
                    compression: comp,
                    photometric,
                    sample_format: fmt,
                    planar,
                    predictor,
                    tiled: false,
                    rps,
                    tw: 0,
                    th: 0,
                    offsets: Seq::empty(),
                    counts: Seq::empty(),
                };
                layout(b, le, o, n, base, twf, thf)
            }},
            _ => None,
        }
    }
}

/// The checks on fields that do not change the samples, as libtiff makes
/// them, and the sample format. libtiff: SampleFormat (§19) is read like
/// BitsPerSample and must be 1 to 6, and the complex formats (5, 6) are not
/// read here (libtiff byte-swaps them differently); ExtraSamples (§18)
/// must have at most one value per sample, each 0, 1, 2 or 999 (a known
/// Corel Draw value); a palette image (§5) of fewer than 8 bits must have a
/// ColorMap of 3 x 2^bits values; SMinSampleValue and SMaxSampleValue
/// must have one value per sample. YCbCr images (§21) are not read here.
pub open spec fn extras(b: Seq<u8>, le: bool, o: nat, n: nat, spp: nat, bps: nat, photometric: Option<nat>) -> Option<nat> {
    match (field(b, le, o, n, SAMPLE_FORMAT), field(b, le, o, n, EXTRA_SAMPLES)) {
        (Some(sf), Some(es)) => {
            let fmt = match sf {
                None => Some(1nat),
                Some(v) => if v.len() == 0 || (v.len() != 1 && (v.len() < spp || exists|k: int|
                    0 <= k < spp && #[trigger] v[k] != v[0])) {
                    None
                } else {
                    Some(v[0])
                },
            };
            let es_ok = match es {
                None => true,
                Some(v) => v.len() <= spp && forall|k: int| 0 <= k < v.len() ==> (#[trigger] v[k] <= 2 || v[k] == 999),
            };
            // libtiff: a ColorMap before the BitsPerSample entry (in an
            // unsorted IFD), or with no BitsPerSample entry, is ignored.
            let cm_ok = match (field(b, le, o, n, COLORMAP), find(b, le, o, n, COLORMAP, 0), find(b, le, o, n, BITS_PER_SAMPLE, 0)) {
                (Some(Some(v)), Some(ic), Some(ib)) => v.len() == 3 * pow2(bps) && ib < ic,
                _ => false,
            };
            match fmt {
                Some(f) => if 1 <= f <= 4 && es_ok && count_is(b, le, o, n, SMIN_SAMPLE_VALUE, spp)
                    && count_is(b, le, o, n, SMAX_SAMPLE_VALUE, spp) && photometric != Some(6nat) && !(photometric == Some(3nat) && bps < 8 && !cm_ok) {
                    Some(f)
                } else {
                    None
                },
                None => None,
            }
        },
        _ => None,
    }
}

/// Where the strips or tiles are (§8 StripOffsets, StripByteCounts; §15
/// TileWidth, TileLength, TileOffsets, TileByteCounts), given the other
/// parameters in `base`.
pub open spec fn layout(
    b: Seq<u8>,
    le: bool,
    o: nat,
    n: nat,
    base: Params,
    twf: Option<Seq<nat>>,
    thf: Option<Seq<nat>>,
) -> Option<Params> {
    match (twf, thf) {
        (None, None) => {
            match (field(b, le, o, n, STRIP_OFFSETS), field(b, le, o, n, STRIP_BYTE_COUNTS)) {
                (Some(Some(offs)), Some(Some(cnts))) => {
                    let p = Params { offsets: offs, counts: cnts, ..base };
                    if offs.len() == p.chunks() && cnts.len() == p.chunks() { Some(p) } else { None }
                },
                _ => None,
            }
        },
        (Some(tw), Some(th)) => {
            match (field(b, le, o, n, TILE_OFFSETS), field(b, le, o, n, TILE_BYTE_COUNTS)) {
                (Some(Some(offs)), Some(Some(cnts))) => {
                    if tw.len() != 1 || th.len() != 1 || tw[0] == 0 || th[0] == 0 {
                        None
                    } else {
                        let p = Params {
                            tiled: true,
                            tw: tw[0],
                            th: th[0],
                            offsets: offs,
                            counts: cnts,
                            ..base
                        };
                        // libtiff: tiles whose rows do not end
                        // on a byte boundary are read by libtiff
                        // and not here (TIFF requires tile widths
                        // that are multiples of 16).
                        if (p.tw * p.sc() * p.bps) % 8 != 0 || offs.len() != p.chunks()
                            || cnts.len() != p.chunks() {
                            None
                        } else {
                            Some(p)
                        }
                    }
                },
                _ => None,
            }
        },
        _ => None,
    }

}

// ---------------------------------------------------------------------------
// PackBits (§9)
// ---------------------------------------------------------------------------

/// The PackBits data `d` from `i` on, after output `out`, until `need`
/// bytes. A run or literal that would go past `need` is cut short, and the
/// data after the last byte needed is not read. libtiff: the same
/// (`PackBitsDecode`): data that runs out before `need` bytes is an error.
pub open spec fn packbits(d: Seq<u8>, i: int, out: Seq<u8>, need: nat) -> Option<Seq<u8>>
    decreases d.len() - i,
{
    if out.len() >= need {
        Some(out)
    } else if i < 0 || i >= d.len() {
        None
    } else if d[i] == 128 {
        packbits(d, i + 1, out, need)
    } else if d[i] > 128 {
        // A run: the next byte, 257 - d[i] times.
        let r = (257 - d[i]) as nat;
        let r = if r <= need - out.len() { r } else { (need - out.len()) as nat };
        if i + 1 >= d.len() {
            None
        } else {
            packbits(d, i + 2, out + Seq::new(r, |k: int| d[i + 1]), need)
        }
    } else {
        // A literal: the next d[i] + 1 bytes.
        let l = d[i] as nat + 1;
        let l = if l <= need - out.len() { l } else { (need - out.len()) as nat };
        if i + 1 + l > d.len() {
            None
        } else {
            packbits(d, i + 1 + l, out + d.subrange(i + 1, i + 1 + l), need)
        }
    }
}

// ---------------------------------------------------------------------------
// LZW (§13)
// ---------------------------------------------------------------------------

/// Bit `k` of `d`, bits numbered from the most significant bit of byte 0
/// (§13: "the high-order bit first").
pub open spec fn mbit(d: Seq<u8>, k: int) -> nat {
    ((d[k / 8] as nat) / pow2((7 - k % 8) as nat)) % 2
}

/// The `n` bits at `q`, first bit most significant.
pub open spec fn mbits(d: Seq<u8>, q: int, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        2 * mbits(d, q, (n - 1) as nat) + mbit(d, q + n - 1)
    }
}

pub spec const CLEAR: nat = 256;
pub spec const EOI: nat = 257;

/// libtiff: the table may grow past 4096 entries, to 5119, when an encoder
/// does not send a clear code once it is full; entries from 4096 on cannot
/// be named by a 12-bit code. After that, a code other than a clear code
/// or the end code is an error (libtiff's `CSIZE`, with `LZW_COMPAT`).
pub spec const TABLE_MAX: nat = 5119;

pub struct Lzw {
    /// The strings of the codes: 256 roots, the clear and end codes (empty),
    /// then the entries added.
    pub dict: Seq<Seq<u8>>,
    pub width: nat,
    /// The previous code, unless this is the first code after a clear code.
    pub prev: Option<nat>,
    /// Whether a clear code has been seen: the data must start with one.
    /// libtiff: libtiff errors on any other first code but the end code.
    pub started: bool,
    pub out: Seq<u8>,
}

pub open spec fn init_dict() -> Seq<Seq<u8>> {
    Seq::new(258, |i: int| if i < 256 { seq![i as u8] } else { Seq::empty() })
}

pub open spec fn lzw_start() -> Lzw {
    Lzw { dict: init_dict(), width: 9, prev: None, started: false, out: Seq::empty() }
}

/// The width once the table has `n` entries: TIFF widens the codes one
/// entry early (§13: "switch to 10-bit codes" after code 510 is added),
/// up to 12.
pub open spec fn next_width(n: nat, w: nat) -> nat {
    if n + 1 >= pow2(w) && w < 12 {
        w + 1
    } else {
        w
    }
}

/// One code other than the clear and end codes.
pub open spec fn lzw_code(s: Lzw, c: nat) -> Option<Lzw> {
    if !s.started {
        None
    } else {
        match s.prev {
            None => if c < 256 {
                Some(Lzw { prev: Some(c), out: s.out + seq![c as u8], ..s })
            } else {
                None
            },
            Some(p) => {
                let n = s.dict.len();
                let str = if c < n {
                    s.dict[c as int]
                } else {
                    s.dict[p as int] + seq![s.dict[p as int][0]]
                };
                if n >= TABLE_MAX || !(c < n || c == n) {
                    None
                } else {
                    let dict = s.dict.push(s.dict[p as int] + seq![str[0]]);
                    Some(
                        Lzw {
                            dict,
                            width: next_width(dict.len(), s.width),
                            prev: Some(c),
                            started: true,
                            out: s.out + str,
                        },
                    )
                }
            },
        }
    }
}

/// Decodes `need` bytes from the codes in `d` from bit `q` on. Decoding
/// stops once the output has `need` bytes, and a longer last string is cut
/// to `need`. libtiff: an end code, or the end of the data, before `need`
/// bytes is an error, as in libtiff; codes after the last byte are not
/// read. libtiff: libtiff also reads the "old-style" LZW of libtiff before
/// 1993 (codes least significant bit first); it is rejected here.
pub open spec fn lzw_run(d: Seq<u8>, need: nat, s: Lzw, q: int) -> Option<Seq<u8>>
    decreases 8 * d.len() - q,
{
    if s.out.len() >= need {
        Some(s.out.subrange(0, need as int))
    } else if q < 0 || q + s.width > 8 * d.len() || s.width == 0 {
        None
    } else {
        let c = mbits(d, q, s.width);
        if c == CLEAR {
            lzw_run(d, need, Lzw { dict: init_dict(), width: 9, prev: None, started: true, out: s.out }, q + s.width)
        } else if c == EOI {
            None
        } else {
            match lzw_code(s, c) {
                Some(s2) => lzw_run(d, need, s2, q + s.width),
                None => None,
            }
        }
    }
}

pub open spec fn lzw(d: Seq<u8>, need: nat) -> Option<Seq<u8>> {
    lzw_run(d, need, lzw_start(), 0)
}

// ---------------------------------------------------------------------------
// Strips and tiles
// ---------------------------------------------------------------------------

/// The first `need` bytes that the data `d` of a strip or tile decompresses
/// to with scheme `comp`. libtiff: a Deflate stream must be valid to its
/// end here; libtiff stops reading once it has `need` bytes.
pub open spec fn decompress(comp: nat, d: Seq<u8>, need: nat) -> Option<Seq<u8>> {
    if comp == NONE {
        if d.len() >= need { Some(d.subrange(0, need as int)) } else { None }
    } else if comp == PACKBITS {
        packbits(d, 0, Seq::empty(), need)
    } else if comp == LZW {
        lzw(d, need)
    } else {
        match z::zlib_decompress(d) {
            Some((o, _)) => if o.len() >= need { Some(o.subrange(0, need as int)) } else { None },
            None => None,
        }
    }
}

/// Multi-byte samples made little-endian: in a big-endian file, each
/// sample of 16, 24 or 32 bits has its bytes reversed. libtiff: the same
/// (`tif_postdecode`), to the host's order; here the output is always
/// little-endian.
pub open spec fn to_le(p: Params, d: Seq<u8>) -> Seq<u8> {
    if p.le || !(p.bps == 16 || p.bps == 24 || p.bps == 32) {
        d
    } else {
        let k = (p.bps / 8) as int;
        Seq::new(d.len(), |i: int| d[i - i % k + (k - 1 - i % k)])
    }
}

/// The little-endian value of the `k` bytes at `i`.
pub open spec fn le_val(d: Seq<u8>, i: int, k: nat) -> nat
    decreases k,
{
    if k == 0 {
        0
    } else {
        d[i] as nat + 256 * le_val(d, i + 1, (k - 1) as nat)
    }
}

/// Byte `j` (from the least significant) of `v`.
pub open spec fn byte_of(v: nat, j: nat) -> u8 {
    ((v / pow2(8 * j)) % 256) as u8
}

/// Sample `s` of a row after horizontal differencing is undone: the sum of
/// the stored samples `s`, `s - stride`, `s - 2 stride`, ... down to the
/// first pixel, modulo 2^bits (§14).
pub open spec fn undiff(row: Seq<u8>, s: nat, stride: nat, k: nat) -> nat
    decreases s,
{
    if s < stride || stride == 0 {
        le_val(row, (s * k) as int, k)
    } else {
        (undiff(row, (s - stride) as nat, stride, k) + le_val(row, (s * k) as int, k)) % pow2(8 * k)
    }
}

/// The data of a strip or tile with horizontal differencing undone in each
/// row of `rb` bytes, samples of `k` bytes, `stride` samples per pixel.
pub open spec fn unpredict(d: Seq<u8>, rb: nat, k: nat, stride: nat) -> Seq<u8> {
    Seq::new(
        d.len(),
        |i: int| {
            let r = i / rb as int;
            let x = i % rb as int;
            byte_of(undiff(d.subrange(r * rb, r * rb + rb), (x / k as int) as nat, stride, k), (x % k as int) as nat)
        },
    )
}

/// Strip or tile `k`, decoded: decompressed, made little-endian, and with
/// the predictor undone. `None` if its data is not inside the file or does
/// not decode.
#[verifier::opaque]
pub open spec fn chunk(b: Seq<u8>, p: Params, k: nat) -> Option<Seq<u8>> {
    let off = p.offsets[k as int];
    let cnt = p.counts[k as int];
    if off + cnt > b.len() {
        None
    } else {
        match decompress(p.compression, b.subrange(off as int, (off + cnt) as int), p.chunk_size(k)) {
            None => None,
            Some(d) => {
                let d = to_le(p, d);
                if p.predictor == 2 {
                    Some(unpredict(d, p.chunk_row_bytes(), p.bps / 8, p.sc()))
                } else {
                    Some(d)
                }
            },
        }
    }
}

/// Where byte `i` of the output comes from: which strip or tile, and
/// which byte of it once decoded. The output is plane after plane, each
/// `height` rows of `row_bytes`. A strip holds `rps` whole rows; a tile row
/// holds `tile_row_bytes` of an image row, and the tiles of the last
/// column are cut at the image's right edge (and those of the last row at
/// its bottom).
#[verifier::opaque]
pub open spec fn owner(p: Params, i: int) -> (int, int) {
    let plane_size = (p.height * p.row_bytes()) as int;
    let pl = i / plane_size;
    let r = i % plane_size;
    if !p.tiled {
        let size = (p.rps * p.row_bytes()) as int;
        (pl * p.strips() + r / size, r % size)
    } else {
        let rb = p.row_bytes() as int;
        let trb = p.tile_row_bytes() as int;
        let y = r / rb;
        let x = r % rb;
        (
            pl * (p.tiles_across() * p.tiles_down()) + (y / p.th as int) * p.tiles_across() + x / trb,
            (y % p.th as int) * trb + x % trb,
        )
    }
}

/// Byte `i` of the output, from the decoded strips or tiles `cs`.
pub open spec fn pixel(p: Params, cs: Seq<Seq<u8>>, i: int) -> u8 {
    cs[owner(p, i).0][owner(p, i).1]
}

/// A decoded image.
pub struct Image {
    /// Whether the file is little-endian ("II").
    pub le: bool,
    pub width: nat,
    pub height: nat,
    pub bits_per_sample: nat,
    pub samples_per_pixel: nat,
    pub compression: nat,
    pub photometric: Option<nat>,
    pub sample_format: nat,
    pub planar: nat,
    /// The output: each plane in turn (one, or one per sample if `planar`
    /// is 2), each `height` rows of `ceil(width * samples * bits / 8)`
    /// bytes, where `samples` is the samples per pixel in a plane. Samples
    /// of fewer than 8 bits are packed from the most significant bit;
    /// samples of 16, 24 and 32 bits are little-endian.
    pub pixels: Seq<u8>,
}

/// Decodes the first image of a TIFF file, or `None` if it is not one this
/// specification accepts.
pub open spec fn decode(b: Seq<u8>) -> Option<Image> {
    match header(b) {
        None => None,
        Some((le, o)) => match params(b, le, o) {
            None => None,
            Some(p) => {
                if exists|k: nat| k < p.chunks() && chunk(b, p, k) is None {
                    None
                } else {
                    let cs = Seq::new(p.chunks(), |k: int| chunk(b, p, k as nat)->Some_0);
                    Some(
                        Image {
                            le,
                            width: p.width,
                            height: p.height,
                            bits_per_sample: p.bps,
                            samples_per_pixel: p.spp,
                            compression: p.compression,
                            photometric: p.photometric,
                            sample_format: p.sample_format,
                            planar: p.planar,
                            pixels: Seq::new(p.image_size(), |i: int| pixel(p, cs, i)),
                        },
                    )
                }
            },
        },
    }
}

} // verus!

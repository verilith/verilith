//! Executable-independent specification of WebP lossless decoding: the
//! VP8L bitstream (RFC 9649) and the RIFF container around it.
//!
//! Everything here is a total function over `Seq<u8>`, written to be read
//! side by side with RFC 9649 (section numbers below refer to it). This
//! file, Verus and the Rust compiler are the trusted base: the decoder is
//! proven to compute exactly these functions.
//!
//! Where the RFC leaves a choice, or where libwebp (the reference decoder)
//! accepts or rejects differently from what the RFC alone implies, the spec
//! follows libwebp 1.6.0, so that vwebp accepts exactly the files libwebp
//! accepts and decodes them to the same pixels. Each such point is marked
//! "libwebp:" and listed in the README.
#[cfg(verus_only)]
pub use verilith_core::bits::{bit, bits, code_bits, nbits};
#[cfg(verus_only)]
pub use verilith_core::huffman::{
    count, count_below, decode, decode_from, first_code, left, nth_with_len, used, MAX_BITS,
};
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
#[cfg(verus_only)]
pub use verilith_core::huffman::{first_used, valid_code};

verus! {

// ---------------------------------------------------------------------------
// Bits (§3.1)
// ---------------------------------------------------------------------------

// `nbits`, `bit`, `bits` (first bit least significant) and `code_bits`
// (first bit most significant) are specified in `verilith_core::bits`.

/// `ReadBits(n)` at `pos`, or `None` if the input ends first.
pub open spec fn rd(b: Seq<u8>, pos: int, n: nat) -> Option<nat> {
    if 0 <= pos && pos + n <= nbits(b) {
        Some(bits(b, pos, n))
    } else {
        None
    }
}

/// libwebp: a bitstream shorter than 8 bytes is read as if padded with
/// zero bytes to 8 bytes (its bit reader holds 64 bits and only reports the
/// end of the stream past them).
pub open spec fn pad(b: Seq<u8>) -> Seq<u8> {
    if b.len() < 8 {
        b + Seq::new((8 - b.len()) as nat, |i: int| 0u8)
    } else {
        b
    }
}

// ---------------------------------------------------------------------------
// Canonical prefix codes (§3.7.2.1, §3.7.2.2)
// ---------------------------------------------------------------------------

// The canonical code itself (`count`, `first_code`, `nth_with_len`,
// `decode`, `left`, `used`) is DEFLATE's (RFC 1951 §3.2.2), specified in
// `verilith_core::huffman`.



/// `ReadSymbol`: the symbol at `pos` and the position after it. A code with
/// a single symbol takes no bits.
pub open spec fn read_symbol(lens: Seq<u8>, b: Seq<u8>, pos: int) -> Option<(nat, int)> {
    if used(lens) == 1 {
        Some((first_used(lens, 0) as nat, pos))
    } else {
        match decode(lens, b, pos) {
            Some((s, k)) => Some((s, pos + k)),
            None => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Reading a prefix code (§3.7.2.1.1, §3.7.2.1.2)
// ---------------------------------------------------------------------------

pub open spec fn zeros(n: nat) -> Seq<u8> {
    Seq::new(n, |i: int| 0u8)
}

/// Gives symbol `s` the code length 1. libwebp: a symbol outside the
/// alphabet (possible for the 40-symbol distance alphabet, as symbols are
/// sent with up to 8 bits) is ignored.
pub open spec fn set_one(lens: Seq<u8>, s: nat) -> Seq<u8> {
    if s < lens.len() {
        lens.update(s as int, 1u8)
    } else {
        lens
    }
}

/// Simple code length code (§3.7.2.1.1), from just after its first bit.
pub open spec fn read_simple(b: Seq<u8>, pos: int, size: nat) -> Option<(Seq<u8>, int)> {
    match rd(b, pos, 1) {
        None => None,
        Some(n1) => match rd(b, pos + 1, 1) {
            None => None,
            Some(f8) => {
                let w: nat = if f8 == 0 {
                    1
                } else {
                    8
                };
                match rd(b, pos + 2, w) {
                    None => None,
                    Some(s0) => {
                        let l1 = set_one(zeros(size), s0);
                        if n1 == 0 {
                            Some((l1, pos + 2 + w))
                        } else {
                            match rd(b, pos + 2 + w, 8) {
                                None => None,
                                Some(s1) => Some((set_one(l1, s1), pos + 2 + w + 8)),
                            }
                        }
                    },
                }
            },
        },
    }
}

/// The order in which the code length code's lengths are sent.
pub open spec fn cl_order() -> Seq<nat> {
    seq![17nat, 18, 0, 1, 2, 3, 4, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
}

/// The code length code's lengths after the first `i` of them (3 bits
/// each, from `pos`) are read; the others are 0.
pub open spec fn cl_lens(b: Seq<u8>, pos: int, i: nat) -> Seq<u8>
    decreases i,
{
    if i == 0 {
        zeros(19)
    } else {
        cl_lens(b, pos, (i - 1) as nat).update(
            cl_order()[i - 1] as int,
            bits(b, pos + 3 * (i - 1), 3) as u8,
        )
    }
}

/// Sets `n` code lengths from `start` to `v`.
pub open spec fn set_run(lens: Seq<u8>, start: nat, n: nat, v: u8) -> Seq<u8> {
    Seq::new(lens.len(), |i: int| if start <= i < start + n { v } else { lens[i] })
}

/// Reads code lengths with the code length code `cl` (§3.7.2.1.2): `sym`
/// lengths are set, `tokens` code length symbols may still be read, and
/// `prev` is the last nonzero length (initially 8).
pub open spec fn read_lens(
    cl: Seq<u8>,
    b: Seq<u8>,
    pos: int,
    size: nat,
    tokens: nat,
    sym: nat,
    prev: u8,
    lens: Seq<u8>,
) -> Option<(Seq<u8>, int)>
    decreases size - sym,
{
    if sym >= size || tokens == 0 {
        Some((lens, pos))
    } else {
        match read_symbol(cl, b, pos) {
            None => None,
            Some((c, p)) => if c < 16 {
                read_lens(
                    cl,
                    b,
                    p,
                    size,
                    (tokens - 1) as nat,
                    sym + 1,
                    if c != 0 {
                        c as u8
                    } else {
                        prev
                    },
                    lens.update(sym as int, c as u8),
                )
            } else {
                let eb: nat = if c == 16 {
                    2
                } else if c == 17 {
                    3
                } else {
                    7
                };
                let off: nat = if c == 18 {
                    11
                } else {
                    3
                };
                match rd(b, p, eb) {
                    None => None,
                    Some(x) => {
                        let rep = x + off;
                        if sym + rep > size {
                            None
                        } else {
                            read_lens(
                                cl,
                                b,
                                p + eb,
                                size,
                                (tokens - 1) as nat,
                                sym + rep,
                                prev,
                                set_run(
                                    lens,
                                    sym,
                                    rep,
                                    if c == 16 {
                                        prev
                                    } else {
                                        0u8
                                    },
                                ),
                            )
                        }
                    },
                }
            },
        }
    }
}

/// Normal code length code (§3.7.2.1.2), from just after its first bit.
pub open spec fn read_normal(b: Seq<u8>, pos: int, size: nat) -> Option<(Seq<u8>, int)> {
    match rd(b, pos, 4) {
        None => None,
        Some(x) => {
            let n = x + 4;
            let p = pos + 4 + 3 * n;
            let cl = cl_lens(b, pos + 4, n);
            if p > nbits(b) || !valid_code(cl) {
                None
            } else {
                match rd(b, p, 1) {
                    None => None,
                    Some(um) => if um == 1 {
                        match rd(b, p + 1, 3) {
                            None => None,
                            Some(y) => {
                                let nb = 2 + 2 * y;
                                match rd(b, p + 4, nb) {
                                    None => None,
                                    Some(z) => {
                                        let tokens = 2 + z;
                                        if tokens > size {
                                            None
                                        } else {
                                            read_lens(cl, b, p + 4 + nb, size, tokens, 0, 8, zeros(size))
                                        }
                                    },
                                }
                            },
                        }
                    } else {
                        read_lens(cl, b, p + 1, size, size, 0, 8, zeros(size))
                    },
                }
            }
        },
    }
}

/// Reads a prefix code for an alphabet of `size` symbols: its code lengths
/// and the position after it.
pub open spec fn read_code(b: Seq<u8>, pos: int, size: nat) -> Option<(Seq<u8>, int)> {
    let r = match rd(b, pos, 1) {
        None => None,
        Some(simple) => if simple == 1 {
            read_simple(b, pos + 1, size)
        } else {
            read_normal(b, pos + 1, size)
        },
    };
    match r {
        Some((lens, p)) => if valid_code(lens) {
            Some((lens, p))
        } else {
            None
        },
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Prefix code groups (§3.7.2.2)
// ---------------------------------------------------------------------------

pub open spec fn cache_size(cb: nat) -> nat {
    if cb == 0 {
        0
    } else {
        pow2(cb)
    }
}

/// Alphabet size of code `j` of a group: green + length prefixes + color
/// cache, red, blue, alpha, distance prefixes.
pub open spec fn alphabet(j: nat, cb: nat) -> nat {
    if j == 0 {
        256 + 24 + cache_size(cb)
    } else if j == 4 {
        40
    } else {
        256
    }
}

/// The first `j` codes of a group.
pub open spec fn read_group_codes(b: Seq<u8>, pos: int, cb: nat, j: nat) -> Option<(Seq<Seq<u8>>, int)>
    decreases j,
{
    if j == 0 {
        Some((seq![], pos))
    } else {
        match read_group_codes(b, pos, cb, (j - 1) as nat) {
            None => None,
            Some((cs, p)) => match read_code(b, p, alphabet((j - 1) as nat, cb)) {
                None => None,
                Some((lens, q)) => Some((cs.push(lens), q)),
            },
        }
    }
}

/// `n` groups of five codes (green, red, blue, alpha, distance).
pub open spec fn read_groups(b: Seq<u8>, pos: int, cb: nat, n: nat) -> Option<(Seq<Seq<Seq<u8>>>, int)>
    decreases n,
{
    if n == 0 {
        Some((seq![], pos))
    } else {
        match read_groups(b, pos, cb, (n - 1) as nat) {
            None => None,
            Some((gs, p)) => match read_group_codes(b, p, cb, 5) {
                None => None,
                Some((g, q)) => Some((gs.push(g), q)),
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Pixels (§5.2)
// ---------------------------------------------------------------------------

pub open spec fn argb(a: nat, r: nat, g: nat, b: nat) -> u32 {
    (a * 0x100_0000 + r * 0x1_0000 + g * 0x100 + b) as u32
}

/// Extra bits of length and distance prefix code `s` (§5.2.2).
pub open spec fn pfx_extra(s: nat) -> nat {
    if s < 4 {
        0
    } else {
        ((s - 2) / 2) as nat
    }
}

/// The value of prefix code `s` is `pfx_base(s) + extra + 1`.
pub open spec fn pfx_base(s: nat) -> nat {
    if s < 4 {
        s
    } else {
        (2 + s % 2) * pow2(pfx_extra(s))
    }
}

/// Distance codes 1..120 address the 2D neighborhood (§5.2.2).
pub open spec fn code_to_plane() -> Seq<nat> {
    seq![
        0x18nat, 0x07, 0x17, 0x19, 0x28, 0x06, 0x27, 0x29, 0x16, 0x1a, 0x26, 0x2a, 0x38, 0x05,
        0x37, 0x39, 0x15, 0x1b, 0x36, 0x3a, 0x25, 0x2b, 0x48, 0x04, 0x47, 0x49, 0x14, 0x1c, 0x35,
        0x3b, 0x46, 0x4a, 0x24, 0x2c, 0x58, 0x45, 0x4b, 0x34, 0x3c, 0x03, 0x57, 0x59, 0x13, 0x1d,
        0x56, 0x5a, 0x23, 0x2d, 0x44, 0x4c, 0x55, 0x5b, 0x33, 0x3d, 0x68, 0x02, 0x67, 0x69, 0x12,
        0x1e, 0x66, 0x6a, 0x22, 0x2e, 0x54, 0x5c, 0x43, 0x4d, 0x65, 0x6b, 0x32, 0x3e, 0x78, 0x01,
        0x77, 0x79, 0x53, 0x5d, 0x11, 0x1f, 0x64, 0x6c, 0x42, 0x4e, 0x76, 0x7a, 0x21, 0x2f, 0x75,
        0x7b, 0x31, 0x3f, 0x63, 0x6d, 0x52, 0x5e, 0x00, 0x74, 0x7c, 0x41, 0x4f, 0x10, 0x20, 0x62,
        0x6e, 0x30, 0x73, 0x7d, 0x51, 0x5f, 0x40, 0x72, 0x7e, 0x61, 0x6f, 0x50, 0x71, 0x7f, 0x60,
        0x70,
    ]
}

/// The distance in pixels of distance code `c >= 1` in an image `w` wide.
pub open spec fn plane_to_dist(w: nat, c: nat) -> nat {
    if c > 120 {
        (c - 120) as nat
    } else {
        let dc = code_to_plane()[c - 1];
        let d = (dc / 16) * w + 8 - (dc % 16) as int;
        if d >= 1 {
            d as nat
        } else {
            1
        }
    }
}

/// Color cache index of a pixel (§5.2.3).
pub open spec fn hash(c: u32, cb: nat) -> nat {
    ((c as nat * 0x1e35a7bd) % 0x1_0000_0000) / pow2((32 - cb) as nat)
}

pub open spec fn cache_insert(cache: Seq<u32>, cb: nat, c: u32) -> Seq<u32> {
    if cb == 0 {
        cache
    } else {
        cache.update(hash(c, cb) as int, c)
    }
}

pub open spec fn cache_insert_all(cache: Seq<u32>, cb: nat, px: Seq<u32>) -> Seq<u32>
    decreases px.len(),
{
    if px.len() == 0 {
        cache
    } else {
        cache_insert(cache_insert_all(cache, cb, px.drop_last()), cb, px.last())
    }
}

/// The `len` pixels a backward reference at distance `d <= out.len()`
/// appends: each copies the pixel `d` back, so a reference may overlap its
/// own output and repeats the last `d` pixels.
pub open spec fn copy_seg(out: Seq<u32>, d: nat, len: nat) -> Seq<u32> {
    Seq::new(len, |k: int| out[out.len() - d + k % (d as int)])
}

/// What decoding an entropy-coded image needs besides the input.
pub struct Img {
    /// Width, and number of pixels.
    pub w: nat,
    pub npix: nat,
    /// Color cache bits (0: none).
    pub cb: nat,
    /// The prefix code groups, each five code length sequences.
    pub groups: Seq<Seq<Seq<u8>>>,
    /// Prefix bits of the entropy image (0: a single group), its width,
    /// and its pixels.
    pub hb: nat,
    pub hx: nat,
    pub meta: Seq<u32>,
}

/// The group of a meta prefix code (§3.7.2.2: red and green of the entropy
/// image's pixel).
pub open spec fn meta_code(p: u32) -> nat {
    ((p as nat) / 0x100) % 0x1_0000
}

/// The prefix code group used at pixel `i`.
pub open spec fn group_at(img: Img, i: nat) -> Seq<Seq<u8>> {
    if img.hb == 0 {
        img.groups[0]
    } else {
        let x = i % img.w;
        let y = i / img.w;
        let t = (y / pow2(img.hb)) * img.hx + x / pow2(img.hb);
        img.groups[meta_code(img.meta[t as int]) as int]
    }
}

/// Decodes the pixels after `out` (§5.2.2): literals, backward references
/// and color cache codes, until there are `img.npix`.
pub open spec fn decode_pixels(b: Seq<u8>, pos: int, img: Img, out: Seq<u32>, cache: Seq<u32>) -> Option<(Seq<u32>, int)>
    decreases img.npix - out.len(),
{
    if out.len() >= img.npix {
        Some((out, pos))
    } else {
        let g = group_at(img, out.len());
        match read_symbol(g[0], b, pos) {
            None => None,
            Some((s, p1)) => if s < 256 {
                match read_symbol(g[1], b, p1) {
                    None => None,
                    Some((r, p2)) => match read_symbol(g[2], b, p2) {
                        None => None,
                        Some((bl, p3)) => match read_symbol(g[3], b, p3) {
                            None => None,
                            Some((a, p4)) => {
                                let c = argb(a, r, s, bl);
                                decode_pixels(b, p4, img, out.push(c), cache_insert(cache, img.cb, c))
                            },
                        },
                    },
                }
            } else if s < 280 {
                let ls = (s - 256) as nat;
                match rd(b, p1, pfx_extra(ls)) {
                    None => None,
                    Some(x) => {
                        let len = pfx_base(ls) + x + 1;
                        match read_symbol(g[4], b, p1 + pfx_extra(ls)) {
                            None => None,
                            Some((ds, p3)) => match rd(b, p3, pfx_extra(ds)) {
                                None => None,
                                Some(y) => {
                                    let d = plane_to_dist(img.w, pfx_base(ds) + y + 1);
                                    if d > out.len() || len > img.npix - out.len() {
                                        None
                                    } else {
                                        let seg = copy_seg(out, d, len);
                                        decode_pixels(
                                            b,
                                            p3 + pfx_extra(ds),
                                            img,
                                            out + seg,
                                            cache_insert_all(cache, img.cb, seg),
                                        )
                                    }
                                },
                            },
                        }
                    },
                }
            } else {
                let c = cache[s - 280];
                decode_pixels(b, p1, img, out.push(c), cache_insert(cache, img.cb, c))
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Entropy-coded images (§5)
// ---------------------------------------------------------------------------

/// `DIV_ROUND_UP(n, 1 << bits)`.
pub open spec fn subsample(n: nat, bits: nat) -> nat {
    ((n + pow2(bits) - 1) / (pow2(bits) as int)) as nat
}

/// The color cache bits (§5.2.3): 0 for none, else 1 to 11.
pub open spec fn read_cache_bits(b: Seq<u8>, pos: int) -> Option<(nat, int)> {
    match rd(b, pos, 1) {
        None => None,
        Some(f) => if f == 0 {
            Some((0, pos + 1))
        } else {
            match rd(b, pos + 1, 4) {
                None => None,
                Some(cb) => if 1 <= cb <= 11 {
                    Some((cb, pos + 5))
                } else {
                    None
                },
            }
        },
    }
}

/// The largest meta prefix code among the first `n` entropy image pixels.
pub open spec fn max_meta(meta: Seq<u32>, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        let m = max_meta(meta, (n - 1) as nat);
        let c = meta_code(meta[n - 1]);
        if c > m {
            c
        } else {
            m
        }
    }
}

/// Decodes the pixels of an image once its color cache and groups are
/// read.
pub open spec fn decode_with(
    b: Seq<u8>,
    pos: int,
    w: nat,
    h: nat,
    cb: nat,
    groups: Seq<Seq<Seq<u8>>>,
    hb: nat,
    meta: Seq<u32>,
) -> Option<(Seq<u32>, int)> {
    let img = Img {
        w,
        npix: w * h,
        cb,
        groups,
        hb,
        hx: if hb == 0 {
            0
        } else {
            subsample(w, hb)
        },
        meta,
    };
    decode_pixels(b, pos, img, seq![], Seq::new(cache_size(cb), |i: int| 0u32))
}

/// An entropy-coded image without meta prefix codes: the transform data
/// and entropy images ("subresolution images", §5.1).
pub open spec fn decode_sub(b: Seq<u8>, pos: int, w: nat, h: nat) -> Option<(Seq<u32>, int)> {
    match read_cache_bits(b, pos) {
        None => None,
        Some((cb, p1)) => match read_groups(b, p1, cb, 1) {
            None => None,
            Some((gs, p2)) => decode_with(b, p2, w, h, cb, gs, 0, seq![]),
        },
    }
}

/// The ARGB image (§5.1), with optional meta prefix codes (§3.7.2.2).
pub open spec fn decode_main(b: Seq<u8>, pos: int, w: nat, h: nat) -> Option<(Seq<u32>, int)> {
    match read_cache_bits(b, pos) {
        None => None,
        Some((cb, p1)) => match rd(b, p1, 1) {
            None => None,
            Some(m) => if m == 0 {
                match read_groups(b, p1 + 1, cb, 1) {
                    None => None,
                    Some((gs, p2)) => decode_with(b, p2, w, h, cb, gs, 0, seq![]),
                }
            } else {
                match rd(b, p1 + 1, 3) {
                    None => None,
                    Some(x) => {
                        let hb = x + 2;
                        match decode_sub(b, p1 + 4, subsample(w, hb), subsample(h, hb)) {
                            None => None,
                            Some((meta, p2)) => {
                                let n = max_meta(meta, meta.len()) + 1;
                                match read_groups(b, p2, cb, n) {
                                    None => None,
                                    Some((gs, p3)) => decode_with(b, p3, w, h, cb, gs, hb, meta),
                                }
                            },
                        }
                    },
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// Transforms (§4)
// ---------------------------------------------------------------------------

pub open spec fn alpha(c: u32) -> u32 {
    c >> 24u32
}

pub open spec fn red(c: u32) -> u32 {
    (c >> 16u32) & 0xffu32
}

pub open spec fn green(c: u32) -> u32 {
    (c >> 8u32) & 0xffu32
}

pub open spec fn blue(c: u32) -> u32 {
    c & 0xffu32
}

/// A transform, with the image width when it was read (§4).
pub enum Transform {
    /// Predictor (§4.1): block bits, width, the predictor modes image.
    Predictor { bits: nat, w: nat, data: Seq<u32> },
    /// Color (§4.2): block bits, width, the color transform image.
    Color { bits: nat, w: nat, data: Seq<u32> },
    /// Subtract green (§4.3).
    SubtractGreen,
    /// Color indexing (§4.4): pixel bundling bits, width before bundling,
    /// the color table expanded to `1 << (8 >> bits)` entries.
    ColorIndexing { bits: nat, w: nat, palette: Seq<u32> },
}

pub open spec fn kind(t: Transform) -> nat {
    match t {
        Transform::Predictor { .. } => 0,
        Transform::Color { .. } => 1,
        Transform::SubtractGreen => 2,
        Transform::ColorIndexing { .. } => 3,
    }
}

/// Adds two pixels channel by channel, modulo 256.
pub open spec fn add_px(a: u32, b: u32) -> u32 {
    argb(
        ((alpha(a) + alpha(b)) % 256) as nat,
        ((red(a) + red(b)) % 256) as nat,
        ((green(a) + green(b)) % 256) as nat,
        ((blue(a) + blue(b)) % 256) as nat,
    )
}

/// The color table, its entries delta coded (§4.4), expanded to `size`
/// entries with transparent black (libwebp: indices past the table give
/// 0x00000000; the RFC only says they should).
pub open spec fn expand(pal: Seq<u32>, size: nat) -> Seq<u32>
    decreases size,
{
    if size == 0 {
        seq![]
    } else {
        let e = expand(pal, (size - 1) as nat);
        let i = size - 1;
        e.push(
            if i >= pal.len() {
                0u32
            } else if i == 0 {
                pal[0]
            } else {
                add_px(pal[i], e[i - 1])
            },
        )
    }
}

/// Reads transforms until the "no more transforms" bit, after `ts`; `w` is
/// the current width (color indexing narrows it). Returns the transforms,
/// the final width and the position after them.
pub open spec fn read_transforms(b: Seq<u8>, pos: int, w: nat, h: nat, ts: Seq<Transform>) -> Option<(Seq<Transform>, nat, int)>
    decreases 4 - ts.len(),
{
    match rd(b, pos, 1) {
        None => None,
        Some(more) => if more == 0 {
            Some((ts, w, pos + 1))
        } else {
            match rd(b, pos + 1, 2) {
                None => None,
                Some(t) => if ts.len() >= 4 || exists|j: int| 0 <= j < ts.len() && kind(#[trigger] ts[j]) == t {
                    // Each transform at most once (§4).
                    None
                } else if t == 0 || t == 1 {
                    match rd(b, pos + 3, 3) {
                        None => None,
                        Some(x) => {
                            let tb = x + 2;
                            match decode_sub(b, pos + 6, subsample(w, tb), subsample(h, tb)) {
                                None => None,
                                Some((data, p)) => read_transforms(
                                    b,
                                    p,
                                    w,
                                    h,
                                    ts.push(
                                        if t == 0 {
                                            Transform::Predictor { bits: tb, w, data }
                                        } else {
                                            Transform::Color { bits: tb, w, data }
                                        },
                                    ),
                                ),
                            }
                        },
                    }
                } else if t == 2 {
                    read_transforms(b, pos + 3, w, h, ts.push(Transform::SubtractGreen))
                } else {
                    match rd(b, pos + 3, 8) {
                        None => None,
                        Some(x) => {
                            let n = x + 1;
                            let wb: nat = if n > 16 {
                                0
                            } else if n > 4 {
                                1
                            } else if n > 2 {
                                2
                            } else {
                                3
                            };
                            match decode_sub(b, pos + 11, n, 1) {
                                None => None,
                                Some((pal, p)) => read_transforms(
                                    b,
                                    p,
                                    subsample(w, wb),
                                    h,
                                    ts.push(
                                        Transform::ColorIndexing {
                                            bits: wb,
                                            w,
                                            palette: expand(pal, pow2((8nat / pow2(wb)) as nat)),
                                        },
                                    ),
                                ),
                            }
                        },
                    }
                },
            }
        },
    }
}

/// Per-channel average, rounded down.
pub open spec fn avg2(a: u32, b: u32) -> u32 {
    argb(
        ((alpha(a) + alpha(b)) / 2) as nat,
        ((red(a) + red(b)) / 2) as nat,
        ((green(a) + green(b)) / 2) as nat,
        ((blue(a) + blue(b)) / 2) as nat,
    )
}

pub open spec fn clamp(x: int) -> nat {
    if x < 0 {
        0
    } else if x > 255 {
        255
    } else {
        x as nat
    }
}

pub open spec fn abs(x: int) -> int {
    if x < 0 {
        -x
    } else {
        x
    }
}

/// C's `x / 2`, which truncates toward zero.
pub open spec fn half_c(x: int) -> int {
    if x >= 0 {
        x / 2
    } else {
        -((-x) / 2)
    }
}

pub open spec fn clamp_add_sub_full(a: u32, b: u32, c: u32) -> u32 {
    argb(
        clamp(alpha(a) + alpha(b) - alpha(c)),
        clamp(red(a) + red(b) - red(c)),
        clamp(green(a) + green(b) - green(c)),
        clamp(blue(a) + blue(b) - blue(c)),
    )
}

pub open spec fn clamp_add_sub_half(a: u32, b: u32) -> u32 {
    argb(
        clamp(alpha(a) + half_c(alpha(a) - alpha(b))),
        clamp(red(a) + half_c(red(a) - red(b))),
        clamp(green(a) + half_c(green(a) - green(b))),
        clamp(blue(a) + half_c(blue(a) - blue(b))),
    )
}

pub open spec fn select(l: u32, t: u32, tl: u32) -> u32 {
    let pl = abs(alpha(t) - alpha(tl)) + abs(red(t) - red(tl)) + abs(green(t) - green(tl)) + abs(
        blue(t) - blue(tl),
    );
    let pt = abs(alpha(l) - alpha(tl)) + abs(red(l) - red(tl)) + abs(green(l) - green(tl)) + abs(
        blue(l) - blue(tl),
    );
    if pl < pt {
        l
    } else {
        t
    }
}

/// The predictors (§4.1). libwebp: modes 14 and 15 predict 0xff000000,
/// like mode 0.
pub open spec fn predict_mode(m: nat, l: u32, t: u32, tr: u32, tl: u32) -> u32 {
    if m == 1 {
        l
    } else if m == 2 {
        t
    } else if m == 3 {
        tr
    } else if m == 4 {
        tl
    } else if m == 5 {
        avg2(avg2(l, tr), t)
    } else if m == 6 {
        avg2(l, tl)
    } else if m == 7 {
        avg2(l, t)
    } else if m == 8 {
        avg2(tl, t)
    } else if m == 9 {
        avg2(t, tr)
    } else if m == 10 {
        avg2(avg2(l, tl), avg2(t, tr))
    } else if m == 11 {
        select(l, t, tl)
    } else if m == 12 {
        clamp_add_sub_full(l, t, tl)
    } else if m == 13 {
        clamp_add_sub_half(avg2(l, t), tl)
    } else {
        0xff00_0000u32
    }
}

/// The prediction for pixel `i` of an image `w` wide from the pixels `o`
/// before it: black for the first, L on the first row, T on the first
/// column, else the block's mode. The top-right pixel of the last column
/// is the first pixel of the current row (§4.1).
pub open spec fn predict(o: Seq<u32>, i: nat, w: nat, bits: nat, data: Seq<u32>) -> u32 {
    let x = i % w;
    let y = i / w;
    if i == 0 {
        0xff00_0000u32
    } else if y == 0 {
        o[i - 1]
    } else if x == 0 {
        o[i - w]
    } else {
        let t = (y / pow2(bits)) * subsample(w, bits) + x / pow2(bits);
        predict_mode(
            green(data[t as int]) as nat % 16,
            o[i - 1],
            o[i - w],
            o[i - w + 1],
            o[i - w - 1],
        )
    }
}

/// The first `n` pixels after undoing the predictor transform.
pub open spec fn unpredict(res: Seq<u32>, w: nat, bits: nat, data: Seq<u32>, n: nat) -> Seq<u32>
    decreases n,
{
    if n == 0 {
        seq![]
    } else {
        let o = unpredict(res, w, bits, data, (n - 1) as nat);
        o.push(add_px(res[n - 1], predict(o, (n - 1) as nat, w, bits, data)))
    }
}

/// `ColorTransformDelta`: signed bytes multiplied, then shifted right
/// arithmetically by 5.
pub open spec fn sbyte(x: u32) -> int {
    if x < 128 {
        x as int
    } else {
        x - 256
    }
}

pub open spec fn delta(t: u32, c: u32) -> int {
    (sbyte(t) * sbyte(c)) / 32
}

/// Undoes the color transform on one pixel with element `e` (§4.2).
pub open spec fn uncolor(c: u32, e: u32) -> u32 {
    let g2r = e & 0xff;
    let g2b = (e >> 8u32) & 0xff;
    let r2b = (e >> 16u32) & 0xff;
    let nr = (red(c) + delta(g2r, green(c))) % 256;
    let nb = (blue(c) + delta(g2b, green(c)) + delta(r2b, nr as u32)) % 256;
    argb(alpha(c) as nat, nr as nat, green(c) as nat, nb as nat)
}

/// Undoes subtract green on one pixel (§4.3).
pub open spec fn add_green(c: u32) -> u32 {
    argb(
        alpha(c) as nat,
        ((red(c) + green(c)) % 256) as nat,
        green(c) as nat,
        ((blue(c) + green(c)) % 256) as nat,
    )
}

/// Pixel `i` after undoing color indexing (§4.4): its index is packed in
/// the green channel of pixel `x >> bits` of its row, `8 >> bits` bits per
/// pixel, first pixel in the low bits.
pub open spec fn unindex_px(px: Seq<u32>, i: nat, w: nat, bits: nat, palette: Seq<u32>) -> u32 {
    let x = i % w;
    let y = i / w;
    let bpp = 8nat / pow2(bits);
    let packed = green(px[(y * subsample(w, bits) + x / pow2(bits)) as int]) as nat;
    let idx = (packed / pow2(((x % pow2(bits)) * bpp) as nat)) % pow2(bpp as nat);
    palette[idx as int]
}

/// Undoes one transform on an image `h` pixels high.
pub open spec fn undo(t: Transform, px: Seq<u32>, h: nat) -> Seq<u32> {
    match t {
        Transform::Predictor { bits, w, data } => unpredict(px, w, bits, data, px.len()),
        Transform::Color { bits, w, data } => Seq::new(
            px.len(),
            |i: int|
                uncolor(
                    px[i],
                    data[((i / w as int) / pow2(bits) as int) * subsample(w, bits) + (i % w as int)
                        / pow2(bits) as int],
                ),
        ),
        Transform::SubtractGreen => Seq::new(px.len(), |i: int| add_green(px[i])),
        Transform::ColorIndexing { bits, w, palette } => Seq::new(
            w * h,
            |i: int| unindex_px(px, i as nat, w, bits, palette),
        ),
    }
}

/// Undoes the transforms, last read first.
pub open spec fn undo_all(ts: Seq<Transform>, px: Seq<u32>, h: nat) -> Seq<u32>
    decreases ts.len(),
{
    if ts.len() == 0 {
        px
    } else {
        undo_all(ts.drop_last(), undo(ts.last(), px, h), h)
    }
}

// ---------------------------------------------------------------------------
// The VP8L bitstream (§3, §7)
// ---------------------------------------------------------------------------

/// A decoded image: width, height, and `width * height` ARGB pixels in
/// scan order.
pub struct Image {
    pub w: nat,
    pub h: nat,
    pub px: Seq<u32>,
}

/// The image header (§3.2): signature 0x2f, width and height minus one in
/// 14 bits each, the alpha hint, and a 3-bit version that must be 0.
/// Returns width, height and the alpha hint.
pub open spec fn vp8l_header(b: Seq<u8>) -> Option<(nat, nat, nat)> {
    match (rd(b, 0, 8), rd(b, 8, 14), rd(b, 22, 14), rd(b, 36, 1), rd(b, 37, 3)) {
        (Some(sig), Some(w), Some(h), Some(a), Some(v)) => if sig == 0x2f && v == 0 {
            Some((w + 1, h + 1, a))
        } else {
            None
        },
        _ => None,
    }
}

/// Decodes a VP8L bitstream. libwebp reads it to the end of the input
/// (bits past the image are ignored).
pub open spec fn vp8l_decode(data: Seq<u8>) -> Option<Image> {
    let b = pad(data);
    match vp8l_header(b) {
        None => None,
        Some((w, h, a)) => match read_transforms(b, 40, w, h, seq![]) {
            None => None,
            Some((ts, xw, p)) => match decode_main(b, p, xw, h) {
                None => None,
                Some((px, q)) => Some(Image { w, h, px: undo_all(ts, px, h) }),
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The container (WebP container specification, as libwebp parses it)
// ---------------------------------------------------------------------------

pub open spec fn le_n(d: Seq<u8>, i: nat, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        d[i as int] as nat + 256 * le_n(d, i + 1, (n - 1) as nat)
    }
}

/// The four bytes at `i` are `t`.
pub open spec fn tag(d: Seq<u8>, i: int, t: Seq<u8>) -> bool {
    0 <= i && i + 4 <= d.len() && d.subrange(i, i + 4) == t
}

pub open spec fn riff_tag() -> Seq<u8> {
    seq![0x52u8, 0x49, 0x46, 0x46]
}

pub open spec fn webp_tag() -> Seq<u8> {
    seq![0x57u8, 0x45, 0x42, 0x50]
}

pub open spec fn vp8x_tag() -> Seq<u8> {
    seq![0x56u8, 0x50, 0x38, 0x58]
}

pub open spec fn vp8_tag() -> Seq<u8> {
    seq![0x56u8, 0x50, 0x38, 0x20]
}

pub open spec fn vp8l_tag() -> Seq<u8> {
    seq![0x56u8, 0x50, 0x38, 0x4c]
}

pub open spec fn alph_tag() -> Seq<u8> {
    seq![0x41u8, 0x4c, 0x50, 0x48]
}

/// `MAX_CHUNK_PAYLOAD`.
pub spec const MAX_PAYLOAD: nat = 0xffff_fff6;

/// What the headers say about the image data.
pub enum Parsed {
    /// A VP8L bitstream starts at this offset.
    Lossless(nat),
    /// A VP8 (lossy) bitstream, which vwebp does not decode.
    Lossy,
    /// Invalid, truncated, or animated.
    Fail,
}

/// Skips the chunks after VP8X up to the VP8/VP8L chunk
/// (`ParseOptionalChunks`): `total` (32-bit, as in libwebp) counts the
/// bytes since "WEBP". Returns the offset of the VP8/VP8L chunk header.
pub open spec fn skip_chunks(d: Seq<u8>, p: nat, riff: nat, total: nat) -> Option<nat>
    decreases d.len() - p,
{
    if p + 8 > d.len() {
        None
    } else {
        let size = le_n(d, p + 4, 4);
        let disk = 2 * ((9 + size) / 2);
        let t = (total + disk) % 0x1_0000_0000;
        if size > MAX_PAYLOAD || (riff > 0 && t > riff) {
            None
        } else if tag(d, p as int, vp8_tag()) || tag(d, p as int, vp8l_tag()) {
            Some(p)
        } else if d.len() - p < disk {
            None
        } else {
            skip_chunks(d, p + disk, riff, t)
        }
    }
}

/// The payload (offset and size) of the last ALPH chunk among the chunks
/// `skip_chunks` passes, or `acc` if there is none.
pub open spec fn find_alph(d: Seq<u8>, p: nat, riff: nat, total: nat, acc: Option<(nat, nat)>) -> Option<(nat, nat)>
    decreases d.len() - p,
{
    if p + 8 > d.len() {
        acc
    } else {
        let size = le_n(d, p + 4, 4);
        let disk = 2 * ((9 + size) / 2);
        let t = (total + disk) % 0x1_0000_0000;
        if size > MAX_PAYLOAD || (riff > 0 && t > riff) {
            acc
        } else if tag(d, p as int, vp8_tag()) || tag(d, p as int, vp8l_tag()) {
            acc
        } else if d.len() - p < disk {
            acc
        } else {
            find_alph(
                d,
                p + disk,
                riff,
                t,
                if tag(d, p as int, alph_tag()) {
                    Some((p + 8, size))
                } else {
                    acc
                },
            )
        }
    }
}

/// `VP8LCheckSignature`.
pub open spec fn vp8l_signature(d: Seq<u8>, p: nat) -> bool {
    p + 5 <= d.len() && d[p as int] == 0x2f && d[p + 4int] / 32 == 0
}

/// The headers before the bitstream, as `WebPParseHeaders` parses them for
/// a complete file (`have_all_data`): an optional RIFF header, an optional
/// VP8X chunk, optional chunks, and a VP8/VP8L chunk header or a raw
/// bitstream.
pub open spec fn parse_headers(d: Seq<u8>) -> Parsed {
    if d.len() < 12 {
        Parsed::Fail
    } else {
        let is_riff = tag(d, 0, riff_tag());
        let riff = le_n(d, 4, 4);
        if is_riff && (!tag(d, 8, webp_tag()) || riff < 12 || riff > MAX_PAYLOAD || riff > d.len()
            - 8) {
            Parsed::Fail
        } else {
            let riff_size: nat = if is_riff {
                riff
            } else {
                0
            };
            let p0: nat = if is_riff {
                12
            } else {
                0
            };
            if d.len() < p0 + 8 {
                Parsed::Fail
            } else {
                let is_vp8x = tag(d, p0 as int, vp8x_tag());
                let flags = le_n(d, p0 + 8, 4);
                let cw = 1 + le_n(d, p0 + 12, 3);
                let ch = 1 + le_n(d, p0 + 15, 3);
                if is_vp8x && (le_n(d, p0 + 4, 4) != 10 || d.len() < p0 + 18 || cw * ch
                    >= 0x1_0000_0000 || (flags / 2) % 2 == 1 || !is_riff) {
                    // Wrong VP8X size, truncated, too large, animated, or
                    // VP8X without RIFF.
                    Parsed::Fail
                } else {
                    let p1: nat = if is_vp8x {
                        p0 + 18
                    } else {
                        p0
                    };
                    if d.len() < p1 + 4 {
                        Parsed::Fail
                    } else {
                        let p2 = if (is_riff && is_vp8x) || (!is_riff && !is_vp8x && tag(
                            d,
                            p1 as int,
                            alph_tag(),
                        )) {
                            skip_chunks(d, p1, riff_size, 22)
                        } else {
                            Some(p1)
                        };
                        match p2 {
                            None => Parsed::Fail,
                            Some(p2) => if d.len() < p2 + 8 {
                                Parsed::Fail
                            } else {
                                let chunk = tag(d, p2 as int, vp8_tag()) || tag(
                                    d,
                                    p2 as int,
                                    vp8l_tag(),
                                );
                                let size = le_n(d, p2 + 4, 4);
                                if chunk && ((riff_size >= 12 && size > riff_size - 12) || size
                                    > d.len() - p2 - 8) {
                                    Parsed::Fail
                                } else {
                                    let p3: nat = if chunk {
                                        p2 + 8
                                    } else {
                                        p2
                                    };
                                    let lossless = if chunk {
                                        tag(d, p2 as int, vp8l_tag())
                                    } else {
                                        vp8l_signature(d, p2)
                                    };
                                    let csize: nat = if chunk {
                                        size
                                    } else {
                                        (d.len() - p2) as nat
                                    };
                                    if csize > MAX_PAYLOAD {
                                        Parsed::Fail
                                    } else if !lossless {
                                        Parsed::Lossy
                                    } else if d.len() < p3 + 5 || !vp8l_signature(d, p3) {
                                        Parsed::Fail
                                    } else {
                                        match vp8l_header(pad(d.subrange(p3 as int, d.len() as int))) {
                                            None => Parsed::Fail,
                                            Some((w, h, a)) => if is_vp8x && (w != cw || h != ch) {
                                                Parsed::Fail
                                            } else {
                                                Parsed::Lossless(p3)
                                            },
                                        }
                                    }
                                }
                            },
                        }
                    }
                }
            }
        }
    }
}

/// Decodes a WebP file whose image is lossless. libwebp: the bitstream is
/// read from the start of the VP8L chunk's payload to the end of the file,
/// not only the chunk's stated size.
pub open spec fn webp_decode(d: Seq<u8>) -> Option<Image> {
    match parse_headers(d) {
        Parsed::Lossless(p) => vp8l_decode(d.subrange(p as int, d.len() as int)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The alpha plane of a lossy file (the ALPH chunk, WebP container
// specification, as libwebp's `src/dec/alpha_dec.c` decodes it)
// ---------------------------------------------------------------------------

/// A VP8L image stream without the VP8L header: the transforms, the
/// entropy-coded image, and the inverse transforms.
pub open spec fn vp8l_headless(b: Seq<u8>, w: nat, h: nat) -> Option<Seq<u32>> {
    match read_transforms(b, 0, w, h, seq![]) {
        None => None,
        Some((ts, xw, p)) => match decode_main(b, p, xw, h) {
            None => None,
            Some((px, q)) => Some(undo_all(ts, px, h)),
        },
    }
}

pub open spec fn alph_clip(v: int) -> int {
    if v < 0 {
        0
    } else if v > 255 {
        255
    } else {
        v
    }
}

/// Value `k` of an alpha plane `w` wide after its filter is undone
/// (`WebPUnfilters`): `raw[k]` plus a prediction, modulo 256. Filter 1
/// predicts from the left, 2 from above, 3 from the gradient
/// `left + above - above-left` clipped to a byte. The first row always
/// predicts from the left (0 for its first value), and the first value of
/// any other row from above.
pub open spec fn alph_unf(raw: Seq<u8>, w: int, filter: int, k: int) -> int
    decreases k,
{
    if k < 0 || w <= 0 {
        0
    } else {
        let x = k % w;
        let pred = if filter == 0 {
            0
        } else if k < w {
            // The first row.
            if k == 0 {
                0
            } else {
                alph_unf(raw, w, filter, k - 1)
            }
        } else if filter == 2 || x == 0 || k == w {
            // (`k == w` is a row's first value too; saying so makes the
            // recursion below plainly well-founded.)
            alph_unf(raw, w, filter, k - w)
        } else if filter == 1 {
            alph_unf(raw, w, filter, k - 1)
        } else {
            alph_clip(
                alph_unf(raw, w, filter, k - 1) + alph_unf(raw, w, filter, k - w) - alph_unf(raw, w, filter, k - w - 1),
            )
        };
        (raw[k] as int + pred) % 256
    }
}

/// The alpha plane of a `w` by `h` frame from an ALPH chunk's payload `d`.
/// The first byte holds the method (0 raw, 1 a VP8L image stream whose
/// green channel is the plane), the filter, and a pre-processing hint that
/// decoding ignores.
pub open spec fn alpha_plane(d: Seq<u8>, w: nat, h: nat) -> Option<Seq<u8>> {
    if d.len() <= 1 {
        None
    } else {
        let hb = d[0] as int;
        let method = hb % 4;
        let filter = (hb / 4) % 4;
        let pre = (hb / 16) % 4;
        let rsrv = hb / 64;
        if method > 1 || pre > 1 || rsrv != 0 {
            None
        } else {
            let raw: Option<Seq<u8>> = if method == 0 {
                if d.len() - 1 < w * h {
                    None
                } else {
                    Some(d.subrange(1, 1 + (w * h) as int))
                }
            } else {
                match vp8l_headless(pad(d.subrange(1, d.len() as int)), w, h) {
                    None => None,
                    Some(px) => Some(Seq::new(w * h, |i: int| ((px[i] / 256) % 256) as u8)),
                }
            };
            match raw {
                None => None,
                Some(r) => Some(Seq::new(w * h, |k: int| alph_unf(r, w as int, filter, k) as u8)),
            }
        }
    }
}

} // verus!

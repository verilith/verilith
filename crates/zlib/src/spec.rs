//! Executable-independent specification of DEFLATE (RFC 1951), zlib
//! (RFC 1950) and gzip (RFC 1952) decompression.
//!
//! Everything here is a total function over `Seq<u8>`, written to be read
//! side by side with the RFCs. This file, Verus and the Rust compiler are the
//! trusted base: every exec function in the crate is proven to compute
//! exactly these functions.
//!
//! Where the RFCs leave a choice (which incomplete Huffman codes to accept,
//! which header flags to reject), the spec follows zlib, so that vzlib
//! accepts exactly the streams zlib accepts.
#[cfg(verus_only)]
pub use verilith_core::bits::{bit, bits, code_bits, nbits};
#[cfg(verus_only)]
pub use verilith_core::bytes::{be32, le16, le32};
#[cfg(verus_only)]
pub use verilith_checksum::spec::*;
#[cfg(verus_only)]
pub use verilith_core::huffman::{
    count, count_below, decode, decode_from, first_code, left, nth_with_len, no_codes, single_code,
    MAX_BITS,
};
use vstd::prelude::*;

verus! {

// Bits (RFC 1951 §3.1.1), canonical Huffman codes (§3.2.2), Adler-32 and
// CRC-32 are specified in vcore (`verilith_core::bits`, `verilith_core::huffman`,
// `verilith_checksum::spec`) and re-exported above.

// ---------------------------------------------------------------------------
// Canonical Huffman codes (RFC 1951 §3.2.2)
// ---------------------------------------------------------------------------

/// Which code length sets are accepted. RFC 1951 does not say; this is
/// zlib's rule (inftrees.c): no length exceeds 15, the code space is not
/// over-subscribed, and the code is complete, empty, or (when `single_ok`)
/// a single one-bit code. zlib allows the single code for the literal/length
/// and distance codes but not the code length code.
pub open spec fn valid_lens(lens: Seq<u8>, single_ok: bool) -> bool {
    &&& forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] as nat <= MAX_BITS
    &&& forall|l: nat| 1 <= l <= MAX_BITS ==> #[trigger] left(lens, l) >= 0
    &&& (left(lens, MAX_BITS) == 0 || no_codes(lens) || (single_ok && single_code(lens)))
}

// ---------------------------------------------------------------------------
// Symbol tables (RFC 1951 §3.2.5, §3.2.6, §3.2.7)
// ---------------------------------------------------------------------------

/// Base match length of length symbols 257..285.
pub open spec fn len_base() -> Seq<nat> {
    seq![
        3nat, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99,
        115, 131, 163, 195, 227, 258,
    ]
}

/// Extra bits of length symbols 257..285.
pub open spec fn len_extra() -> Seq<nat> {
    seq![
        0nat, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
    ]
}

/// Base distance of distance symbols 0..29.
pub open spec fn dist_base() -> Seq<nat> {
    seq![
        1nat, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025,
        1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
    ]
}

/// Extra bits of distance symbols 0..29.
pub open spec fn dist_extra() -> Seq<nat> {
    seq![
        0nat, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12,
        12, 13, 13,
    ]
}

/// Code lengths of the fixed literal/length code (§3.2.6). Symbols 286 and
/// 287 have codes but never occur in valid data.
pub open spec fn fixed_lit_lens() -> Seq<u8> {
    Seq::new(
        288,
        |i: int|
            if i < 144 {
                8u8
            } else if i < 256 {
                9u8
            } else if i < 280 {
                7u8
            } else {
                8u8
            },
    )
}

/// Code lengths of the fixed distance code (§3.2.6). Symbols 30 and 31 have
/// codes but never occur in valid data.
pub open spec fn fixed_dist_lens() -> Seq<u8> {
    Seq::new(32, |i: int| 5u8)
}

// ---------------------------------------------------------------------------
// Blocks (RFC 1951 §3.2.3 to §3.2.7)
// ---------------------------------------------------------------------------

/// `out` followed by the `len` bytes of a match at distance `dist`, copied
/// one byte at a time so the copy may overlap its own output (§3.2.3).
pub open spec fn copy_match(out: Seq<u8>, dist: nat, len: nat) -> Seq<u8>
    decreases len,
{
    if len == 0 {
        out
    } else {
        copy_match(out.push(out[out.len() - dist]), dist, (len - 1) as nat)
    }
}

/// `pos < p <= nbits(b)`: decoding moved forward and stayed in the input.
/// Every recursive call below checks it; the first half always holds (every
/// field takes at least one bit), so it only makes termination evident.
pub open spec fn advances(b: Seq<u8>, pos: int, p: int) -> bool {
    pos < p && p <= nbits(b)
}

/// Decodes the symbols of a compressed block from bit `pos` up to and
/// including its end-of-block symbol, appending to `out` (§3.2.5). Returns
/// the bit position after the block and the output so far.
pub open spec fn inflate_codes(
    b: Seq<u8>,
    pos: int,
    out: Seq<u8>,
    lit: Seq<u8>,
    dist: Seq<u8>,
) -> Option<(int, Seq<u8>)>
    decreases nbits(b) - pos,
{
    match decode(lit, b, pos) {
        None => None,
        Some((sym, l)) => {
            let p1 = pos + l;
            if !advances(b, pos, p1) {
                None
            } else if sym < 256 {
                inflate_codes(b, p1, out.push(sym as u8), lit, dist)
            } else if sym == 256 {
                Some((p1, out))
            } else if sym > 285 {
                None
            } else {
                let le = len_extra()[sym - 257];
                let len = len_base()[sym - 257] + bits(b, p1, le);
                let p2 = p1 + le;
                if p2 > nbits(b) {
                    None
                } else {
                    match decode(dist, b, p2) {
                        None => None,
                        Some((ds, dl)) => {
                            let p3 = p2 + dl;
                            if ds >= 30 {
                                None
                            } else {
                                let de = dist_extra()[ds as int];
                                let d = dist_base()[ds as int] + bits(b, p3, de);
                                let p4 = p3 + de;
                                if !advances(b, pos, p4) || d > out.len() {
                                    None
                                } else {
                                    inflate_codes(b, p4, copy_match(out, d, len), lit, dist)
                                }
                            }
                        },
                    }
                }
            }
        },
    }
}

/// A stored block whose 3 header bits end at bit `pos` (§3.2.4): skip to a
/// byte boundary, read LEN and NLEN (little-endian), check that NLEN is
/// LEN's one's complement, and copy LEN bytes.
pub open spec fn inflate_stored(b: Seq<u8>, pos: int, out: Seq<u8>) -> Option<(int, Seq<u8>)> {
    let i = (pos + 7) / 8;
    if i + 4 > b.len() {
        None
    } else {
        let len = b[i] as int + 256 * b[i + 1] as int;
        let nlen = b[i + 2] as int + 256 * b[i + 3] as int;
        if len + nlen != 0xffff || i + 4 + len > b.len() {
            None
        } else {
            Some((8 * (i + 4 + len), out + b.subrange(i + 4, i + 4 + len)))
        }
    }
}

/// The order in which the code length code's lengths are sent (§3.2.7).
pub open spec fn clen_order() -> Seq<nat> {
    seq![16nat, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]
}

/// The inverse of `clen_order`: where code length symbol `s`'s length is
/// sent. `lemma_clen_slot` checks the two agree.
pub open spec fn clen_slot() -> Seq<nat> {
    seq![3nat, 17, 15, 13, 11, 9, 7, 5, 4, 6, 8, 10, 12, 14, 16, 18, 0, 1, 2]
}

/// The code length code's lengths: `hclen` 3-bit fields at `pos`, in
/// `clen_order`; lengths not sent are 0.
pub open spec fn clen_lens(b: Seq<u8>, pos: int, hclen: nat) -> Seq<u8> {
    Seq::new(
        19,
        |s: int|
            if clen_slot()[s] < hclen {
                bits(b, pos + 3 * clen_slot()[s], 3) as u8
            } else {
                0u8
            },
    )
}

/// Decodes code lengths with the code length code `cl` until there are
/// `total` of them (§3.2.7). Symbols 0..15 are lengths; 16 repeats the
/// previous length 3..6 times, 17 and 18 repeat a zero 3..10 and 11..138
/// times. A repeat may not run past `total`, and 16 needs a previous length.
pub open spec fn read_lens(cl: Seq<u8>, b: Seq<u8>, pos: int, lens: Seq<u8>, total: nat) -> Option<
    (int, Seq<u8>),
>
    decreases total - lens.len(),
{
    if lens.len() >= total {
        Some((pos, lens))
    } else {
        match decode(cl, b, pos) {
            None => None,
            Some((sym, l)) => {
                let p1 = pos + l;
                if sym < 16 {
                    read_lens(cl, b, p1, lens.push(sym as u8), total)
                } else if sym == 16 && lens.len() == 0 {
                    None
                } else {
                    let e: nat = if sym == 16 {
                        2
                    } else if sym == 17 {
                        3
                    } else {
                        7
                    };
                    let base: nat = if sym == 16 {
                        3
                    } else if sym == 17 {
                        3
                    } else {
                        11
                    };
                    let v: u8 = if sym == 16 {
                        lens.last()
                    } else {
                        0
                    };
                    let rep = base + bits(b, p1, e);
                    if p1 + e > nbits(b) || lens.len() + rep > total {
                        None
                    } else {
                        read_lens(cl, b, p1 + e, lens + Seq::new(rep, |i: int| v), total)
                    }
                }
            },
        }
    }
}

/// The header of a dynamic block, from just after its 3 block header bits
/// (§3.2.7). Returns the position after it and the literal/length and
/// distance code lengths. Like zlib, rejects more than 286 literal/length or
/// 30 distance codes, and a literal/length code without end-of-block.
pub open spec fn read_dynamic(b: Seq<u8>, pos: int) -> Option<(int, Seq<u8>, Seq<u8>)> {
    if pos + 14 > nbits(b) {
        None
    } else {
        let hlit = bits(b, pos, 5) + 257;
        let hdist = bits(b, pos + 5, 5) + 1;
        let hclen = bits(b, pos + 10, 4) + 4;
        let p = pos + 14;
        if hlit > 286 || hdist > 30 || p + 3 * hclen > nbits(b) {
            None
        } else {
            let cl = clen_lens(b, p, hclen);
            if !valid_lens(cl, false) {
                None
            } else {
                match read_lens(cl, b, p + 3 * hclen, Seq::empty(), hlit + hdist) {
                    None => None,
                    Some((p2, lens)) => {
                        let lit = lens.subrange(0, hlit as int);
                        let dist = lens.subrange(hlit as int, (hlit + hdist) as int);
                        if lit[256] == 0 || !valid_lens(lit, true) || !valid_lens(dist, true) {
                            None
                        } else {
                            Some((p2, lit, dist))
                        }
                    },
                }
            }
        }
    }
}

/// Decodes blocks from bit `pos` through the block marked final (§3.2.3).
/// Returns the bit position after the final block and the output.
pub open spec fn inflate_blocks(b: Seq<u8>, pos: int, out: Seq<u8>) -> Option<(int, Seq<u8>)>
    decreases nbits(b) - pos,
{
    if pos < 0 || pos + 3 > nbits(b) {
        None
    } else {
        let bfinal = bits(b, pos, 1);
        let btype = bits(b, pos + 1, 2);
        let p = pos + 3;
        let r = if btype == 0 {
            inflate_stored(b, p, out)
        } else if btype == 1 {
            inflate_codes(b, p, out, fixed_lit_lens(), fixed_dist_lens())
        } else if btype == 2 {
            match read_dynamic(b, p) {
                None => None,
                Some((p2, lit, dist)) => inflate_codes(b, p2, out, lit, dist),
            }
        } else {
            None
        };
        match r {
            None => None,
            Some((p2, out2)) => if bfinal == 1 {
                Some((p2, out2))
            } else if !advances(b, pos, p2) {
                None
            } else {
                inflate_blocks(b, p2, out2)
            },
        }
    }
}

/// A raw DEFLATE stream at the start of `b`: the output and the number of
/// input bytes it takes (the final partial byte counts).
pub open spec fn inflate(b: Seq<u8>) -> Option<(Seq<u8>, int)> {
    match inflate_blocks(b, 0, Seq::empty()) {
        None => None,
        Some((end, out)) => Some((out, (end + 7) / 8)),
    }
}

// ---------------------------------------------------------------------------
// zlib (RFC 1950) and gzip (RFC 1952) wrappers
// ---------------------------------------------------------------------------

/// A zlib stream at the start of `b` (RFC 1950 §2.2): the output and the
/// number of input bytes it takes. CM must be 8 (deflate) with a window of
/// at most 32K (CINFO <= 7), FCHECK must make the header a multiple of 31,
/// and a preset dictionary (FDICT) is rejected (`zlib_decompress_dict`
/// takes one). The Adler-32 of the
/// output follows the deflate data, big-endian.
pub open spec fn zlib_decompress(b: Seq<u8>) -> Option<(Seq<u8>, int)> {
    if b.len() < 2 {
        None
    } else {
        let cmf = b[0] as nat;
        let flg = b[1] as nat;
        if cmf % 16 != 8 || cmf / 16 > 7 || (cmf * 256 + flg) % 31 != 0 || (flg / 32) % 2 == 1 {
            None
        } else {
            match inflate_blocks(b, 16, Seq::empty()) {
                None => None,
                Some((end, out)) => {
                    let i = (end + 7) / 8;
                    if i + 4 > b.len() || be32(b, i) != adler32(out) {
                        None
                    } else {
                        Some((out, i + 4))
                    }
                },
            }
        }
    }
}

/// The offset just past the first zero byte at or after `p`.
pub open spec fn skip_zstr(b: Seq<u8>, p: int) -> Option<int>
    decreases b.len() - p,
{
    if p < 0 || p >= b.len() {
        None
    } else if b[p] == 0 {
        Some(p + 1)
    } else {
        skip_zstr(b, p + 1)
    }
}

pub spec const GZ_FHCRC: nat = 2;

pub spec const GZ_FEXTRA: nat = 4;

pub spec const GZ_FNAME: nat = 8;

pub spec const GZ_FCOMMENT: nat = 16;

/// Whether bit `f` (a power of two) is set in `flg`.
pub open spec fn has(flg: nat, f: nat) -> bool {
    (flg / f) % 2 == 1
}

/// The end of a gzip member header (RFC 1952 §2.3.1): ID1 ID2 CM FLG, six
/// bytes of MTIME, XFL and OS, then the optional FEXTRA, FNAME, FCOMMENT and
/// FHCRC fields in that order. Like zlib, rejects reserved flag bits and
/// checks the header CRC (the low 16 bits of the CRC-32 of the header).
pub open spec fn gzip_header(b: Seq<u8>) -> Option<int> {
    if b.len() < 10 || b[0] != 31 || b[1] != 139 || b[2] != 8 || b[3] >= 32 {
        None
    } else {
        let flg = b[3] as nat;
        let p1: Option<int> = if has(flg, GZ_FEXTRA) {
            if 12 > b.len() || 12 + le16(b, 10) > b.len() {
                None
            } else {
                Some(12 + le16(b, 10) as int)
            }
        } else {
            Some(10)
        };
        let p2 = match p1 {
            None => None,
            Some(p) => if has(flg, GZ_FNAME) {
                skip_zstr(b, p)
            } else {
                Some(p)
            },
        };
        let p3 = match p2 {
            None => None,
            Some(p) => if has(flg, GZ_FCOMMENT) {
                skip_zstr(b, p)
            } else {
                Some(p)
            },
        };
        match p3 {
            None => None,
            Some(p) => if has(flg, GZ_FHCRC) {
                if p + 2 > b.len() || le16(b, p) != crc32(b.subrange(0, p)) as nat % 65536 {
                    None
                } else {
                    Some(p + 2)
                }
            } else {
                Some(p)
            },
        }
    }
}

/// One gzip member at the start of `b`: the output and the number of input
/// bytes it takes. The deflate data is followed by the CRC-32 of the output
/// and its length mod 2^32, both little-endian.
/// Raw DEFLATE data with a preset dictionary `dict`: the data may refer
/// back into `dict` as if it were output before the stream. The output
/// excludes `dict`. `inflate(b)` is the case of an empty `dict`.
pub open spec fn inflate_dict(b: Seq<u8>, dict: Seq<u8>) -> Option<(Seq<u8>, int)> {
    match inflate_blocks(b, 0, dict) {
        None => None,
        Some((end, o)) => if o.len() >= dict.len() && o.subrange(0, dict.len() as int) == dict {
            Some((o.subrange(dict.len() as int, o.len() as int), (end + 7) / 8))
        } else {
            None
        },
    }
}

/// A zlib stream with a preset dictionary (RFC 1950 §2.2, FDICT). When
/// FDICT is set, the header is followed by DICTID, the Adler-32 of the
/// dictionary, big-endian; it must equal `adler32(dict)`, and the deflate
/// data may refer back into `dict`, which is not part of the output or of
/// the trailer's Adler-32. When FDICT is clear this is `zlib_decompress`
/// and `dict` is not used.
pub open spec fn zlib_decompress_dict(b: Seq<u8>, dict: Seq<u8>) -> Option<(Seq<u8>, int)> {
    if b.len() < 2 {
        None
    } else {
        let cmf = b[0] as nat;
        let flg = b[1] as nat;
        if (flg / 32) % 2 == 0 {
            zlib_decompress(b)
        } else if cmf % 16 != 8 || cmf / 16 > 7 || (cmf * 256 + flg) % 31 != 0 || b.len() < 6 || be32(b, 2)
            != adler32(dict) {
            None
        } else {
            match inflate_blocks(b, 48, dict) {
                None => None,
                Some((end, o)) => {
                    let i = (end + 7) / 8;
                    if o.len() < dict.len() || o.subrange(0, dict.len() as int) != dict {
                        None
                    } else {
                        let out = o.subrange(dict.len() as int, o.len() as int);
                        if i + 4 > b.len() || be32(b, i) != adler32(out) {
                            None
                        } else {
                            Some((out, i + 4))
                        }
                    }
                },
            }
        }
    }
}

pub open spec fn gzip_decompress(b: Seq<u8>) -> Option<(Seq<u8>, int)> {
    match gzip_header(b) {
        None => None,
        Some(h) => match inflate_blocks(b, 8 * h, Seq::empty()) {
            None => None,
            Some((end, out)) => {
                let i = (end + 7) / 8;
                if i + 8 > b.len() || le32(b, i) != crc32(out) as nat || le32(b, i + 4)
                    != out.len() % 0x1_0000_0000 {
                    None
                } else {
                    Some((out, i + 8))
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// Explicit resource bounds
// ---------------------------------------------------------------------------

/// Most output a DEFLATE stream of `n` input bytes can produce. The
/// densest symbol is a 258-byte match coded in 2 bits (a 1-bit length code
/// and a 1-bit distance code), so output never exceeds 129 bytes per input
/// bit. Proven in `ilemmas::theorem_output_bound`.
pub open spec fn max_output(n: nat) -> nat {
    1032 * n
}

} // verus!

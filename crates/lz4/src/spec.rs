//! The LZ4 block format (lz4_Block_format.md) and frame format
//! (lz4_Frame_format.md, v1.6.x) as pure functions. This file is the
//! trusted specification: everything else is proven against it.
use vstd::prelude::*;

verus! {

#[cfg(verus_only)]
pub use verilith_core::lz::lz_copy;

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

/// The extension of a length field at `i`: bytes are added up until one
/// is not 255. Gives the sum and the index after the last byte read.
pub open spec fn ext_len(s: Seq<u8>, i: int) -> Option<(nat, int)>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        None
    } else if s[i] == 255 {
        match ext_len(s, i + 1) {
            Some((n, j)) => Some((n + 255, j)),
            None => None,
        }
    } else {
        Some((s[i] as nat, i + 1))
    }
}

/// `ext_len` ends after where it starts, inside the input.
pub proof fn lemma_ext_len_next(s: Seq<u8>, i: int)
    ensures
        ext_len(s, i) matches Some((n, j)) ==> i < j <= s.len(),
    decreases s.len() - i,
{
    if 0 <= i < s.len() && s[i] == 255 {
        lemma_ext_len_next(s, i + 1);
    }
}

/// A length field: the token's 4 bits, extended at `i` when they are 15.
pub open spec fn read_len(s: Seq<u8>, i: int, nib: nat) -> Option<(nat, int)> {
    if nib < 15 {
        Some((nib, i))
    } else {
        match ext_len(s, i) {
            Some((n, j)) => Some((15 + n, j)),
            None => None,
        }
    }
}

/// The two bytes at `i`, little-endian.
pub open spec fn le16(s: Seq<u8>, i: int) -> nat {
    s[i] as nat + 256 * (s[i + 1] as nat)
}

/// The end-of-block rules for a match from `mstart` to `mend` of the
/// output ("the last match must start at least 12 bytes before the end of
/// block", "the last 5 bytes of input are always literals"), when the
/// decoded size `t` is given. Compressors must follow them; decoders may
/// or may not check them.
pub open spec fn rules(strict: Option<nat>, mstart: int, mend: int) -> bool {
    strict matches Some(t) ==> mstart + 12 <= t && mend + 5 <= t
}

/// The sequences of a block from `i`, applied to `out`, which already
/// holds the history that matches may reach into (earlier blocks or a
/// dictionary, or nothing) and what the block's earlier sequences
/// produced.
///
/// A sequence is a token, a literal length, literals, a 2-byte offset
/// and a match length (minimum 4). The last sequence stops after its
/// literals, which is where the input ends.
///
/// With `strict` = `Some(t)`, the end-of-block rules are checked too, for
/// a history and block of `t` bytes in all.
pub open spec fn seqs(s: Seq<u8>, i: int, out: Seq<u8>, strict: Option<nat>) -> Option<Seq<u8>>
    decreases s.len() - i,
    via seqs_decreases
{
    if i < 0 || i >= s.len() {
        None
    } else {
        let token = s[i];
        match read_len(s, i + 1, (token / 16) as nat) {
            None => None,
            Some((ll, j)) => {
                if j + ll > s.len() {
                    None
                } else {
                    let out1 = out + s.subrange(j, j + ll);
                    let k = j + ll;
                    if k == s.len() {
                        if strict matches Some(t) && out1.len() != t {
                            None
                        } else {
                            Some(out1)
                        }
                    } else if k + 2 > s.len() {
                        None
                    } else {
                        let off = le16(s, k);
                        match read_len(s, k + 2, (token % 16) as nat) {
                            None => None,
                            Some((ml, m)) => {
                                if off == 0 || off > out1.len() || !rules(
                                    strict,
                                    out1.len() as int,
                                    (out1.len() + ml + 4) as int,
                                ) {
                                    None
                                } else {
                                    seqs(s, m, lz_copy(out1, off as int, ml + 4), strict)
                                }
                            },
                        }
                    }
                }
            },
        }
    }
}

#[via_fn]
proof fn seqs_decreases(s: Seq<u8>, i: int, out: Seq<u8>, strict: Option<nat>) {
    if 0 <= i < s.len() {
        let token = s[i];
        match read_len(s, i + 1, (token / 16) as nat) {
            None => {},
            Some((ll, j)) => {
                lemma_ext_len_next(s, i + 1);
                let k = j + ll;
                if k + 2 <= s.len() {
                    lemma_ext_len_next(s, k + 2);
                }
            },
        }
    }
}

/// What a block decodes to after `hist` (the result starts with `hist`),
/// or `None` if it is not a valid block.
pub open spec fn block(s: Seq<u8>, hist: Seq<u8>) -> Option<Seq<u8>> {
    seqs(s, 0, hist, None)
}

/// A block that also follows the end-of-block rules, as every compressor's
/// output must.
pub open spec fn block_strict(s: Seq<u8>, hist: Seq<u8>, size: nat) -> Option<Seq<u8>> {
    seqs(s, 0, hist, Some(hist.len() + size))
}

// ---------------------------------------------------------------------------
// XXH32 (the frame format's checksums; xxhash_spec.md)
// ---------------------------------------------------------------------------

#[verifier::opaque]
pub open spec fn add32(a: u32, b: u32) -> u32 {
    vstd::wrapping::u32_specs::wrapping_add(a, b)
}

#[verifier::opaque]
pub open spec fn mul32(a: u32, b: u32) -> u32 {
    vstd::wrapping::u32_specs::wrapping_mul(a, b)
}

#[verifier::opaque]
pub open spec fn rotl32(x: u32, r: u32) -> u32 {
    (x << r) | (x >> (32 - r) as u32)
}

pub spec const Q1: u32 = 0x9E3779B1;

pub spec const Q2: u32 = 0x85EBCA77;

pub spec const Q3: u32 = 0xC2B2AE3D;

pub spec const Q4: u32 = 0x27D4EB2F;

pub spec const Q5: u32 = 0x165667B1;

/// The `n` bytes at `i` as a little-endian number.
pub open spec fn le(b: Seq<u8>, i: int, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        b[i] as nat + 256 * le(b, i + 1, (n - 1) as nat)
    }
}

pub open spec fn le32(b: Seq<u8>, i: int) -> u32 {
    le(b, i, 4) as u32
}

#[verifier::opaque]
pub open spec fn xx_round(acc: u32, lane: u32) -> u32 {
    mul32(rotl32(add32(acc, mul32(lane, Q2)), 13), Q1)
}

/// The four accumulators after the 16-byte stripes starting at `i`.
pub open spec fn xx_stripes(b: Seq<u8>, i: int, v: (u32, u32, u32, u32)) -> (u32, u32, u32, u32)
    decreases b.len() - i,
{
    if i < 0 || i + 16 > b.len() {
        v
    } else {
        xx_stripes(
            b,
            i + 16,
            (
                xx_round(v.0, le32(b, i)),
                xx_round(v.1, le32(b, i + 4)),
                xx_round(v.2, le32(b, i + 8)),
                xx_round(v.3, le32(b, i + 12)),
            ),
        )
    }
}

/// The last `b.len() - i` (fewer than 16) bytes.
pub open spec fn xx_tail(b: Seq<u8>, i: int, h: u32) -> u32
    decreases b.len() - i,
{
    if i < 0 || i >= b.len() {
        h
    } else if i + 4 <= b.len() {
        xx_tail(b, i + 4, mul32(rotl32(add32(h, mul32(le32(b, i), Q3)), 17), Q4))
    } else {
        xx_tail(b, i + 1, mul32(rotl32(add32(h, mul32(b[i] as u32, Q5)), 11), Q1))
    }
}

pub open spec fn xx_avalanche(h: u32) -> u32 {
    let h1 = mul32(h ^ (h >> 15), Q2);
    let h2 = mul32(h1 ^ (h1 >> 13), Q3);
    h2 ^ (h2 >> 16)
}

/// XXH32 of `b` with seed 0.
pub open spec fn xxh32(b: Seq<u8>) -> u32 {
    let n = b.len();
    let full = (n / 16 * 16) as int;
    let h0 = if n >= 16 {
        let v = xx_stripes(b, 0, (add32(Q1, Q2), Q2, 0, (0x1_0000_0000 - Q1) as u32));
        add32(add32(add32(rotl32(v.0, 1), rotl32(v.1, 7)), rotl32(v.2, 12)), rotl32(v.3, 18))
    } else {
        Q5
    };
    xx_avalanche(xx_tail(b, full, add32(h0, (n % 0x1_0000_0000) as u32)))
}

// ---------------------------------------------------------------------------
// Frames (lz4_Frame_format.md)
// ---------------------------------------------------------------------------

pub spec const MAGIC: nat = 0x184D2204;

/// A frame descriptor, and where the frame's blocks start.
pub struct Header {
    /// Block independence: matches do not reach into earlier blocks.
    pub indep: bool,
    /// Each block is followed by its checksum.
    pub bsum: bool,
    /// The content size, if the frame gives it.
    pub csize: Option<nat>,
    /// The frame ends with the content's checksum.
    pub csum: bool,
    /// The dictionary ID, if the frame gives one.
    pub dict: Option<nat>,
    /// The largest block, compressed or decoded.
    pub bmax: nat,
    /// The index after the header.
    pub end: int,
}

/// Block maximum sizes: 64 KiB, 256 KiB, 1 MiB, 4 MiB for codes 4 to 7.
pub open spec fn block_max(code: nat) -> nat {
    if code == 4 {
        0x1_0000
    } else if code == 5 {
        0x4_0000
    } else if code == 6 {
        0x10_0000
    } else {
        0x40_0000
    }
}

/// The frame header at `i`: magic number, FLG, BD, the optional content
/// size and dictionary ID, and the header checksum, which is the second
/// byte of XXH32 of the descriptor (FLG up to the checksum). The version
/// must be 01 and reserved bits zero.
pub open spec fn header(s: Seq<u8>, i: int) -> Option<Header> {
    if i < 0 || i + 7 > s.len() {
        None
    } else if le(s, i, 4) != MAGIC {
        None
    } else {
        let flg = s[i + 4] as nat;
        let bd = s[i + 5] as nat;
        let has_size = (flg / 8) % 2 == 1;
        let has_dict = flg % 2 == 1;
        let dlen: int = 2 + (if has_size {
            8int
        } else {
            0
        }) + (if has_dict {
            4int
        } else {
            0
        });
        if flg / 64 != 1 || (flg / 2) % 2 != 0 || bd / 128 != 0 || bd % 16 != 0 || (bd / 16) % 8 < 4 {
            None
        } else if i + 4 + dlen + 1 > s.len() {
            None
        } else if s[i + 4 + dlen] as nat != (xxh32(s.subrange(i + 4, i + 4 + dlen)) as nat / 256) % 256 {
            None
        } else {
            Some(
                Header {
                    indep: (flg / 32) % 2 == 1,
                    bsum: (flg / 16) % 2 == 1,
                    csize: if has_size {
                        Some(le(s, i + 6, 8))
                    } else {
                        None
                    },
                    csum: (flg / 4) % 2 == 1,
                    dict: if has_dict {
                        Some(le(s, i + 4 + dlen - 4, 4))
                    } else {
                        None
                    },
                    bmax: block_max((bd / 16) % 8),
                    end: i + 4 + dlen + 1,
                },
            )
        }
    }
}

/// The content `out` with one more block's data: stored as it is, or
/// compressed, with or without the earlier content as history.
pub open spec fn block_data(data: Seq<u8>, raw: bool, indep: bool, out: Seq<u8>) -> Option<Seq<u8>> {
    if raw {
        Some(out + data)
    } else if indep {
        match block(data, Seq::empty()) {
            Some(b) => Some(out + b),
            None => None,
        }
    } else {
        block(data, out)
    }
}

/// The data blocks from `i`, appended to `out` (the frame's content so
/// far), up to and including the end mark. Gives the content and the
/// index after the end mark.
///
/// A block is a 4-byte size, whose top bit says the data is stored
/// uncompressed, the data, and its XXH32 if the frame has block
/// checksums. A size of zero is the end mark. Neither the data nor what
/// it decodes to may be larger than the frame's block maximum size. With
/// linked blocks, matches may reach into the earlier content.
pub open spec fn blocks(s: Seq<u8>, i: int, h: Header, out: Seq<u8>) -> Option<(Seq<u8>, int)>
    decreases s.len() - i,
{
    if i < 0 || i + 4 > s.len() {
        None
    } else {
        let w = le(s, i, 4);
        let size = w % 0x8000_0000;
        let raw = w >= 0x8000_0000;
        let j = i + 4;
        let e = j + size + (if h.bsum {
            4int
        } else {
            0
        });
        if size == 0 {
            Some((out, j))
        } else if size > h.bmax || e > s.len() {
            None
        } else if h.bsum && le(s, j + size, 4) != xxh32(s.subrange(j, j + size)) {
            None
        } else {
            match block_data(s.subrange(j, j + size), raw, h.indep, out) {
                None => None,
                Some(out2) => if out2.len() - out.len() > h.bmax {
                    None
                } else {
                    blocks(s, e, h, out2)
                },
            }
        }
    }
}

/// The frame at `i`: its content and the index after it. The content
/// must have the size the header gives, if it gives one, and the
/// checksum the frame ends with, if it has one.
pub open spec fn frame(s: Seq<u8>, i: int) -> Option<(Seq<u8>, int)> {
    match header(s, i) {
        None => None,
        Some(h) => match blocks(s, h.end, h, Seq::empty()) {
            None => None,
            Some((content, j)) => {
                if h.csize matches Some(c) && c != content.len() {
                    None
                } else if h.csum {
                    if j + 4 > s.len() || le(s, j, 4) != xxh32(content) {
                        None
                    } else {
                        Some((content, j + 4))
                    }
                } else {
                    Some((content, j))
                }
            },
        },
    }
}

/// The skippable frame at `i` (magic numbers 0x184D2A50 to 0x184D2A5F,
/// then a 4-byte size and that many bytes): the index after it.
pub open spec fn skippable(s: Seq<u8>, i: int) -> Option<int> {
    if i < 0 || i + 8 > s.len() {
        None
    } else if le(s, i, 4) / 16 != 0x184D2A5 {
        None
    } else if i + 8 + le(s, i + 4, 4) > s.len() {
        None
    } else {
        Some(i + 8 + le(s, i + 4, 4))
    }
}

/// The contents of the frames from `i` to the end of the input, one
/// after another, skippable frames left out.
pub open spec fn frames(s: Seq<u8>, i: int) -> Option<Seq<u8>>
    decreases s.len() - i,
{
    if i == s.len() {
        Some(Seq::empty())
    } else {
        match skippable(s, i) {
            Some(j) => frames(s, j),
            None => match frame(s, i) {
                None => None,
                // (A frame always ends after its start and inside the
                // input; the test only shows that this definition
                // terminates.)
                Some((c, j)) => if j <= i || j > s.len() {
                    None
                } else {
                    match frames(s, j) {
                        Some(r) => Some(c + r),
                        None => None,
                    }
                },
            },
        }
    }
}

} // verus!

//! The Brotli format (RFC 7932) as a small-step machine over the input bits.
//!
//! This file is the trusted specification: the decoder in this crate is
//! proven to compute exactly what is written here. Review it against
//! RFC 7932; where the RFC leaves a choice, it follows google/brotli's
//! decoder (`c/dec/decode.c`), and the comments say so.
//!
//! The machine's state `St` holds everything the format carries from one
//! item to the next: the bit position, all output so far, the current
//! meta-block's prefix codes, context maps and block-switch state, and the
//! last four distances. `step` reads one item at `St::pos`: a header field,
//! one code length, one context-map symbol, one block switch, one command,
//! one literal, one distance, or copies one byte. Every step either moves to
//! a new state (`Step::Next`), rejects the stream (`Step::Bad`), or finds the
//! input ends before the item does (`Step::Short`).
//!
//! The input `b` is the whole stream. `Short` is only possible at its end:
//! the decoder, given a prefix of `b`, stops where `step` would read past
//! that prefix, and continues once more of `b` arrives.
//!
//! Prefix codes are given by their code lengths (a `Seq<u8>` with one entry
//! per symbol) and decoded with the canonical code of RFC 7932 §3.2 (which is
//! DEFLATE's, RFC 1951 §3.2.2), specified in `verilith_core::huffman`. A code with a
//! single symbol takes zero bits (§3.4).
pub use crate::tables::*;
pub use verilith_core::bits::*;
pub use verilith_core::huffman::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
#[cfg(verus_only)]
pub use verilith_core::huffman::first_used;

verus! {

// ---------------------------------------------------------------------------
// Constants (RFC 7932 §§4, 5, 6, 8)
// ---------------------------------------------------------------------------

/// Insert length code → base (§5, table "Insert length").
pub const INS_BASE: [u32; 24] = [
    0, 1, 2, 3, 4, 5, 6, 8, 10, 14, 18, 26, 34, 50, 66, 98, 130, 194, 322, 578, 1090, 2114, 6210,
    22594,
];

/// Insert length code → number of extra bits.
pub const INS_EXTRA: [u8; 24] = [
    0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 8, 9, 10, 12, 14, 24,
];

/// Copy length code → base (§5, table "Copy length").
pub const CPY_BASE: [u32; 24] = [
    2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 18, 22, 30, 38, 54, 70, 102, 134, 198, 326, 582, 1094, 2118,
];

/// Copy length code → number of extra bits.
pub const CPY_EXTRA: [u8; 24] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 8, 9, 10, 24,
];

/// The 11 cells of the insert-and-copy alphabet (§5): cell `i` holds symbols
/// `64 i .. 64 i + 63`; `CELL[i]` packs its insert code range (high bits)
/// and copy code range (low two bits), as in google/brotli's `kCellPos`.
pub const CELL: [u8; 11] = [0, 1, 0, 1, 8, 9, 2, 16, 10, 17, 18];

/// Block count code → base (§6).
pub const BLEN_BASE: [u32; 26] = [
    1, 5, 9, 13, 17, 25, 33, 41, 49, 65, 81, 97, 113, 145, 177, 209, 241, 305, 369, 497, 753, 1265,
    2289, 4337, 8433, 16625,
];

/// Block count code → number of extra bits.
pub const BLEN_EXTRA: [u8; 26] = [
    2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 7, 8, 9, 10, 11, 12, 13, 24,
];

/// The order code length code lengths are stored in (§3.5).
pub const CL_ORDER: [u8; 18] = [1, 2, 3, 4, 0, 5, 17, 6, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15];

/// `NDBITS` (§8): log2 of the number of dictionary words of each length.
pub const NDBITS: [u8; 25] = [
    0, 0, 0, 0, 10, 10, 11, 11, 10, 10, 10, 10, 10, 9, 9, 8, 7, 7, 8, 7, 7, 6, 6, 5, 5,
];

/// `DOFFSET` (§8): where the words of each length start in the dictionary.
pub const DOFFSET: [u32; 25] = [
    0, 0, 0, 0, 0, 4096, 9216, 21504, 35840, 44032, 53248, 63488, 74752, 87040, 93696, 100864,
    104704, 106752, 108928, 113536, 115968, 118528, 119872, 121280, 122016,
];

/// Number of transforms (Appendix B).
pub spec const NTRANSFORMS: int = 121;

/// Size of the static dictionary (Appendix A).
pub spec const DICT_SIZE: int = 122784;

/// Block count when a category has a single block type: never reached
/// within a meta-block (google/brotli's `BROTLI_BLOCK_SIZE_CAP`).
pub spec const BLOCK_CAP: int = 0x100_0000;

/// The static dictionary, byte `i` (Appendix A). Its contents are
/// `src/dictionary.bin`, whose SHA-256 `tests/tables.rs` checks against the
/// RFC's.
pub uninterp spec fn dict(i: int) -> u8;

// ---------------------------------------------------------------------------
// Reading bits
// ---------------------------------------------------------------------------

/// The result of reading one item at a bit position: the value and the
/// position after it, or a malformed stream, or the input ends first.
pub enum R<T> {
    Ok(T, int),
    Bad,
    Short,
}

/// `n` bits at `pos`, first bit least significant (§2), if there are that
/// many.
pub open spec fn rd(b: Seq<u8>, pos: int, n: nat) -> Option<int> {
    if 0 <= pos && pos + n <= nbits(b) {
        Some(bits(b, pos, n) as int)
    } else {
        None
    }
}

/// The number of bits needed to write `x`: 0 for 0, else `floor(log2 x) + 1`.
pub open spec fn bitlen(x: nat) -> nat
    decreases x,
{
    if x == 0 {
        0
    } else {
        1 + bitlen(x / 2)
    }
}


/// Reads one symbol with the prefix code of `lens` (§3.2). A code with a
/// single symbol takes no bits (§3.4, NSYM = 1).
pub open spec fn rsym(lens: Seq<u8>, b: Seq<u8>, pos: int) -> R<int> {
    if used(lens) == 1 {
        R::Ok(first_used(lens, 0), pos)
    } else {
        match decode(lens, b, pos) {
            Some((s, k)) => R::Ok(s as int, pos + k),
            None => R::Short,
        }
    }
}

/// The bits from `pos` to the next byte boundary, which must be zero
/// (google/brotli: `BrotliJumpToByteBoundary`). Returns the aligned position.
pub open spec fn pad(b: Seq<u8>, pos: int) -> R<()> {
    let n = ((8 - pos % 8) % 8) as nat;
    match rd(b, pos, n) {
        None => R::Short,
        Some(v) => if v == 0 {
            R::Ok((), pos + n)
        } else {
            R::Bad
        },
    }
}

/// A number in 0..255 written in 1 to 11 bits (§9.2, `NBLTYPES` and
/// `NTREES`).
pub open spec fn varlen8(b: Seq<u8>, pos: int) -> R<int> {
    match rd(b, pos, 1) {
        None => R::Short,
        Some(x) => if x == 0 {
            R::Ok(0, pos + 1)
        } else {
            match rd(b, pos + 1, 3) {
                None => R::Short,
                Some(n) => if n == 0 {
                    R::Ok(1, pos + 4)
                } else {
                    match rd(b, pos + 4, n as nat) {
                        None => R::Short,
                        Some(v) => R::Ok(pow2(n as nat) + v, pos + 4 + n),
                    }
                },
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Stream header (§9.1)
// ---------------------------------------------------------------------------

/// `WBITS`, in 1, 4 or 7 bits. The pattern for large-window Brotli (an
/// extension outside RFC 7932) is rejected.
pub open spec fn read_wbits(b: Seq<u8>, pos: int) -> R<int> {
    match rd(b, pos, 1) {
        None => R::Short,
        Some(x) => if x == 0 {
            R::Ok(16, pos + 1)
        } else {
            match rd(b, pos + 1, 3) {
                None => R::Short,
                Some(n) => if n != 0 {
                    R::Ok(17 + n, pos + 4)
                } else {
                    match rd(b, pos + 4, 3) {
                        None => R::Short,
                        Some(m) => if m == 1 {
                            R::Bad
                        } else if m != 0 {
                            R::Ok(8 + m, pos + 7)
                        } else {
                            R::Ok(17, pos + 7)
                        },
                    }
                },
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Meta-block header (§9.2)
// ---------------------------------------------------------------------------

/// What a meta-block header says.
pub enum Kind {
    /// `ISLAST` and `ISLASTEMPTY`: the stream ends.
    EmptyLast,
    /// Metadata to skip.
    Metadata,
    /// Uncompressed bytes.
    Uncompressed,
    /// Compressed data; the rest of the header follows.
    Compressed,
}

pub struct MetaHeader {
    pub last: bool,
    pub kind: Kind,
    /// `MLEN` or `MSKIPLEN`.
    pub len: int,
}

/// `ISLAST`, `ISLASTEMPTY`, `MNIBBLES`, `MLEN` / `MSKIPLEN`, and
/// `ISUNCOMPRESSED`. For metadata and uncompressed meta-blocks, also the
/// padding to the byte boundary, which must be zero.
pub open spec fn read_meta_header(b: Seq<u8>, pos: int) -> R<MetaHeader> {
    match rd(b, pos, 1) {
        None => R::Short,
        Some(islast) => {
            let last = islast == 1;
            let p = pos + 1;
            if last {
                match rd(b, p, 1) {
                    None => R::Short,
                    Some(empty) => if empty == 1 {
                        R::Ok(MetaHeader { last, kind: Kind::EmptyLast, len: 0 }, p + 1)
                    } else {
                        read_meta_len(b, p + 1, last)
                    },
                }
            } else {
                read_meta_len(b, p, last)
            }
        },
    }
}

pub open spec fn read_meta_len(b: Seq<u8>, pos: int, last: bool) -> R<MetaHeader> {
    match rd(b, pos, 2) {
        None => R::Short,
        Some(mn) => if mn == 3 {
            // MNIBBLES = 0: metadata.
            match rd(b, pos + 2, 1) {
                None => R::Short,
                Some(reserved) => if reserved != 0 {
                    R::Bad
                } else {
                    match rd(b, pos + 3, 2) {
                        None => R::Short,
                        Some(nbytes) => if nbytes == 0 {
                            pad_then(b, pos + 5, MetaHeader { last, kind: Kind::Metadata, len: 0 })
                        } else {
                            match rd(b, pos + 5, (8 * nbytes) as nat) {
                                None => R::Short,
                                Some(v) => if nbytes > 1 && v / pow2((8 * (nbytes - 1)) as nat) as int
                                    == 0 {
                                    // The last byte must not be zero.
                                    R::Bad
                                } else {
                                    pad_then(
                                        b,
                                        pos + 5 + 8 * nbytes,
                                        MetaHeader { last, kind: Kind::Metadata, len: v + 1 },
                                    )
                                },
                            }
                        },
                    }
                },
            }
        } else {
            let nn = mn + 4;
            match rd(b, pos + 2, (4 * nn) as nat) {
                None => R::Short,
                Some(v) => if nn > 4 && v / pow2((4 * (nn - 1)) as nat) as int == 0 {
                    // The last nibble must not be zero.
                    R::Bad
                } else {
                    let p = pos + 2 + 4 * nn;
                    if last {
                        R::Ok(MetaHeader { last, kind: Kind::Compressed, len: v + 1 }, p)
                    } else {
                        match rd(b, p, 1) {
                            None => R::Short,
                            Some(u) => if u == 1 {
                                pad_then(
                                    b,
                                    p + 1,
                                    MetaHeader { last, kind: Kind::Uncompressed, len: v + 1 },
                                )
                            } else {
                                R::Ok(MetaHeader { last, kind: Kind::Compressed, len: v + 1 }, p + 1)
                            },
                        }
                    }
                },
            }
        },
    }
}

pub open spec fn pad_then(b: Seq<u8>, pos: int, h: MetaHeader) -> R<MetaHeader> {
    match pad(b, pos) {
        R::Ok(_, p) => R::Ok(h, p),
        R::Bad => R::Bad,
        R::Short => R::Short,
    }
}

// ---------------------------------------------------------------------------
// Prefix codes (§3.4, §3.5)
// ---------------------------------------------------------------------------

/// The state of reading one prefix code. Before the first item `started` is
/// false; a complex code then reads one code length symbol per step.
pub struct Pc {
    pub started: bool,
    /// Code length code lengths, one per code length symbol 0..17.
    pub cl: Seq<u8>,
    /// Code lengths of the symbols read so far.
    pub lens: Seq<u8>,
    /// The last nonzero code length (initially 8).
    pub prev: int,
    /// The current repeat count and the length it repeats.
    pub rep: int,
    pub replen: int,
    /// 32768 minus the code space used so far (`32768 >> len` per symbol).
    pub space: int,
}

pub open spec fn pc_init() -> Pc {
    Pc { started: false, cl: Seq::empty(), lens: Seq::empty(), prev: 8, rep: 0, replen: 0, space: 0 }
}

pub enum PcRes {
    /// More to read.
    Cont(Pc, int),
    /// The code lengths, one per symbol of the alphabet.
    Fin(Seq<u8>, int),
    Bad,
    Short,
}

/// One code length code length (§3.5), read with the static code
/// 0: `00`, 1: `0111`, 2: `011`, 3: `10`, 4: `01`, 5: `1111`
/// (bits in the order read).
pub open spec fn read_clcl(b: Seq<u8>, pos: int) -> R<int> {
    match rd(b, pos, 2) {
        None => R::Short,
        Some(a) => if a == 0 {
            R::Ok(0, pos + 2)
        } else if a == 1 {
            // bits 1, 0
            R::Ok(4, pos + 2)
        } else if a == 2 {
            // bits 0, 1
            R::Ok(3, pos + 2)
        } else {
            match rd(b, pos + 2, 1) {
                None => R::Short,
                Some(c) => if c == 0 {
                    R::Ok(2, pos + 3)
                } else {
                    match rd(b, pos + 3, 1) {
                        None => R::Short,
                        Some(d) => if d == 0 {
                            R::Ok(1, pos + 4)
                        } else {
                            R::Ok(5, pos + 4)
                        },
                    }
                },
            }
        },
    }
}

/// Reads code length code lengths for `CL_ORDER[i..]` into `cl`, stopping
/// once the code space (32 at the start) is used up or over-subscribed
/// (google/brotli: `ReadCodeLengthCodeLengths`). `num` counts the nonzero
/// lengths. Returns the lengths, `num`, `space` and the position.
pub open spec fn read_cl(b: Seq<u8>, pos: int, i: int, cl: Seq<u8>, num: int, space: int) -> R<(
    Seq<u8>,
    int,
    int,
)>
    decreases 18 - i,
{
    if i >= 18 || i < 0 {
        R::Ok((cl, num, space), pos)
    } else {
        match read_clcl(b, pos) {
            R::Ok(v, p) => {
                let cl2 = cl.update(CL_ORDER[i] as int, v as u8);
                if v != 0 {
                    let space2 = space - pow2((5 - v) as nat);
                    if space2 <= 0 {
                        R::Ok((cl2, num + 1, space2), p)
                    } else {
                        read_cl(b, p, i + 1, cl2, num + 1, space2)
                    }
                } else {
                    read_cl(b, p, i + 1, cl2, num, space)
                }
            },
            R::Bad => R::Bad,
            R::Short => R::Short,
        }
    }
}

/// Reads `n` symbols of `w` bits each, each below `alpha` (§3.4).
pub open spec fn read_simple_syms(b: Seq<u8>, pos: int, n: int, w: nat, alpha: int) -> R<Seq<int>>
    decreases n,
{
    if n <= 0 {
        R::Ok(Seq::empty(), pos)
    } else {
        match rd(b, pos, w) {
            None => R::Short,
            Some(v) => if v >= alpha {
                R::Bad
            } else {
                match read_simple_syms(b, pos + w, n - 1, w, alpha) {
                    R::Ok(rest, p) => R::Ok(seq![v as int] + rest, p),
                    R::Bad => R::Bad,
                    R::Short => R::Short,
                }
            },
        }
    }
}

/// All symbols differ.
pub open spec fn distinct(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

/// Code lengths giving each of `syms` its length from `ls`.
pub open spec fn simple_lens(alpha: int, syms: Seq<int>, ls: Seq<u8>) -> Seq<u8>
    decreases syms.len(),
{
    if syms.len() == 0 {
        Seq::new(alpha as nat, |i: int| 0u8)
    } else {
        simple_lens(alpha, syms.drop_last(), ls.drop_last()).update(syms.last(), ls.last())
    }
}

/// A simple prefix code (§3.4), after `HSKIP` = 1: `NSYM - 1`, the
/// symbols, and for four symbols the tree-select bit. One symbol gets a
/// zero-bit code; the lengths of the others follow the RFC's table.
pub open spec fn read_simple(b: Seq<u8>, pos: int, alpha: int) -> PcRes {
    match rd(b, pos, 2) {
        None => PcRes::Short,
        Some(nm1) => {
            let nsym = nm1 + 1;
            let w = bitlen((alpha - 1) as nat);
            match read_simple_syms(b, pos + 2, nsym as int, w, alpha) {
                R::Bad => PcRes::Bad,
                R::Short => PcRes::Short,
                R::Ok(syms, p) => if !distinct(syms) {
                    PcRes::Bad
                } else if nsym == 1 {
                    PcRes::Fin(simple_lens(alpha, syms, seq![1u8]), p)
                } else if nsym == 2 {
                    PcRes::Fin(simple_lens(alpha, syms, seq![1u8, 1u8]), p)
                } else if nsym == 3 {
                    PcRes::Fin(simple_lens(alpha, syms, seq![1u8, 2u8, 2u8]), p)
                } else {
                    match rd(b, p, 1) {
                        None => PcRes::Short,
                        Some(t) => if t == 0 {
                            PcRes::Fin(simple_lens(alpha, syms, seq![2u8, 2u8, 2u8, 2u8]), p + 1)
                        } else {
                            PcRes::Fin(simple_lens(alpha, syms, seq![1u8, 2u8, 3u8, 3u8]), p + 1)
                        },
                    }
                },
            }
        },
    }
}

/// The code lengths padded with zeros to the alphabet size.
pub open spec fn pad_lens(lens: Seq<u8>, alpha: int) -> Seq<u8> {
    lens + Seq::new((alpha - lens.len()) as nat, |i: int| 0u8)
}

/// Reading a complex code is done: all symbols have a length, or the code
/// space is exactly used up (google/brotli's loop condition in
/// `ReadSymbolCodeLengths`).
pub open spec fn pc_done(pc: Pc, alpha: int) -> bool {
    pc.lens.len() >= alpha || pc.space == 0
}

/// Finishes a complex code: valid only if the code space is exactly used
/// up (Kraft's equality).
pub open spec fn pc_finish(pc: Pc, alpha: int, pos: int) -> PcRes {
    if pc.space == 0 {
        PcRes::Fin(pad_lens(pc.lens, alpha), pos)
    } else {
        PcRes::Bad
    }
}

pub open spec fn pc_next(pc: Pc, alpha: int, pos: int) -> PcRes {
    if pc_done(pc, alpha) {
        pc_finish(pc, alpha, pos)
    } else {
        PcRes::Cont(pc, pos)
    }
}

/// One step of reading a prefix code over an alphabet of `alpha` symbols.
pub open spec fn pc_step(b: Seq<u8>, pos: int, pc: Pc, alpha: int) -> PcRes {
    if !pc.started {
        match rd(b, pos, 2) {
            None => PcRes::Short,
            Some(hskip) => if hskip == 1 {
                read_simple(b, pos + 2, alpha)
            } else {
                match read_cl(b, pos + 2, hskip as int, Seq::new(18, |i: int| 0u8), 0, 32) {
                    R::Bad => PcRes::Bad,
                    R::Short => PcRes::Short,
                    R::Ok((cl, num, space), p) => if num == 1 || space == 0 {
                        PcRes::Cont(
                            Pc {
                                started: true,
                                cl,
                                lens: Seq::empty(),
                                prev: 8,
                                rep: 0,
                                replen: 0,
                                space: 32768,
                            },
                            p,
                        )
                    } else {
                        PcRes::Bad
                    },
                }
            },
        }
    } else {
        match rsym(pc.cl, b, pos) {
            R::Bad => PcRes::Bad,
            R::Short => PcRes::Short,
            R::Ok(c, p) => if c < 16 {
                // A literal code length.
                let pc2 = Pc {
                    lens: pc.lens.push(c as u8),
                    rep: 0,
                    prev: if c != 0 {
                        c
                    } else {
                        pc.prev
                    },
                    space: if c != 0 {
                        pc.space - pow2((15 - c) as nat)
                    } else {
                        pc.space
                    },
                    ..pc
                };
                pc_next(pc2, alpha, p)
            } else {
                // 16: repeat the previous nonzero length; 17: repeat zero.
                let x: nat = if c == 16 {
                    2
                } else {
                    3
                };
                match rd(b, p, x) {
                    None => PcRes::Short,
                    Some(delta) => {
                        let newlen = if c == 16 {
                            pc.prev
                        } else {
                            0
                        };
                        let rep0 = if pc.replen != newlen {
                            0
                        } else {
                            pc.rep
                        };
                        let rep1 = if rep0 > 0 {
                            (rep0 - 2) * pow2(x)
                        } else {
                            0
                        } + delta + 3;
                        let d = rep1 - rep0;
                        if pc.lens.len() + d > alpha {
                            PcRes::Bad
                        } else {
                            let pc2 = Pc {
                                lens: pc.lens + Seq::new(d as nat, |i: int| newlen as u8),
                                rep: rep1,
                                replen: newlen,
                                space: if newlen != 0 {
                                    pc.space - d * pow2((15 - newlen) as nat)
                                } else {
                                    pc.space
                                },
                                ..pc
                            };
                            pc_next(pc2, alpha, p + x)
                        }
                    },
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Context maps (§7.3)
// ---------------------------------------------------------------------------

/// The state of reading a context map.
pub struct Cm {
    /// 0: `NTREES` and `RLEMAX`; 1: the prefix code; 2: the symbols;
    /// 3: the `IMTF` bit.
    pub stage: int,
    pub ntrees: int,
    pub rlemax: int,
    pub code: Seq<u8>,
    pub map: Seq<u8>,
}

pub open spec fn cm_init() -> Cm {
    Cm { stage: 0, ntrees: 0, rlemax: 0, code: Seq::empty(), map: Seq::empty() }
}

/// Inverse move-to-front of `v[i..]`, with the list `l` (§7.3).
pub open spec fn imtf_from(v: Seq<u8>, i: int, l: Seq<u8>) -> Seq<u8>
    decreases v.len() - i,
{
    if i < 0 || i >= v.len() {
        Seq::empty()
    } else {
        let x = v[i] as int;
        let y = l[x];
        seq![y] + imtf_from(v, i + 1, seq![y] + l.remove(x))
    }
}

pub open spec fn imtf(v: Seq<u8>) -> Seq<u8> {
    imtf_from(v, 0, Seq::new(256, |i: int| i as u8))
}

// ---------------------------------------------------------------------------
// Literal context (§7.1)
// ---------------------------------------------------------------------------

/// The context of the next literal, from the last two output bytes, for
/// context mode `mode` (0 LSB6, 1 MSB6, 2 UTF8, 3 Signed).
pub open spec fn lit_context(mode: int, p1: u8, p2: u8) -> int {
    (CONTEXT_LUT[mode * 512 + p1 as int] | CONTEXT_LUT[mode * 512 + 256 + p2 as int]) as int
}

/// The last byte of `out`, or 0.
pub open spec fn p1(out: Seq<u8>) -> u8 {
    if out.len() >= 1 {
        out[out.len() - 1]
    } else {
        0
    }
}

/// The byte before it, or 0.
pub open spec fn p2(out: Seq<u8>) -> u8 {
    if out.len() >= 2 {
        out[out.len() - 2]
    } else {
        0
    }
}

// ---------------------------------------------------------------------------
// Insert and copy lengths (§5)
// ---------------------------------------------------------------------------

pub open spec fn ins_code(sym: int) -> int {
    (CELL[sym / 64] as int / 8) * 8 + (sym / 8) % 8
}

pub open spec fn cpy_code(sym: int) -> int {
    (CELL[sym / 64] as int % 4) * 8 + sym % 8
}

/// The distance context of a copy (§7.2): from the copy length code's base.
pub open spec fn dist_context(sym: int) -> int {
    let c = CPY_BASE[cpy_code(sym)] as int;
    if c > 4 {
        3
    } else {
        c - 2
    }
}

// ---------------------------------------------------------------------------
// Distances (§4)
// ---------------------------------------------------------------------------

/// The distance alphabet size (§9.2).
pub open spec fn dist_alpha(npostfix: int, ndirect: int) -> int {
    16 + ndirect + 48 * pow2(npostfix as nat)
}

/// Number of extra bits of distance code `dcode` (at least `16 + ndirect`).
pub open spec fn dist_extra(dcode: int, npostfix: int, ndirect: int) -> nat {
    (1 + (dcode - ndirect - 16) / pow2((npostfix + 1) as nat) as int) as nat
}

/// The distance of code `dcode` with `extra` as its extra bits.
pub open spec fn dist_value(dcode: int, extra: int, npostfix: int, ndirect: int) -> int {
    let x = dcode - ndirect - 16;
    let ndistbits = dist_extra(dcode, npostfix, ndirect);
    let hcode = x / pow2(npostfix as nat) as int;
    let lcode = x % pow2(npostfix as nat) as int;
    let offset = (2 + hcode % 2) * pow2(ndistbits) - 4;
    (offset + extra) * pow2(npostfix as nat) + lcode + ndirect + 1
}

/// The distance of short code `dcode < 16`, from the last four distances
/// `dr` (most recent first).
pub open spec fn short_dist(dcode: int, dr: Seq<int>) -> int {
    if dcode < 4 {
        dr[dcode]
    } else if dcode < 10 {
        dr[0] + short_delta(dcode - 4)
    } else {
        dr[1] + short_delta(dcode - 10)
    }
}

/// -1, +1, -2, +2, -3, +3.
pub open spec fn short_delta(k: int) -> int {
    if k % 2 == 0 {
        -(k / 2 + 1)
    } else {
        k / 2 + 1
    }
}

/// The largest backward distance: the output so far, at most the window
/// size minus 16 (§9.1).
pub open spec fn max_distance(out_len: int, wbits: int) -> int {
    let w = pow2(wbits as nat) as int - 16;
    if out_len < w {
        out_len
    } else {
        w
    }
}

// ---------------------------------------------------------------------------
// The static dictionary and its transforms (§8, Appendix B)
// ---------------------------------------------------------------------------

pub open spec fn dict_word(len: int, idx: int) -> Seq<u8> {
    Seq::new(len as nat, |i: int| dict(DOFFSET[len] as int + idx * len + i))
}

/// Prefix or suffix string `id` of the transforms: a length byte, then the
/// bytes.
pub open spec fn ps_string(id: int) -> Seq<u8> {
    let off = PS_MAP[id] as int;
    let n = PREFIX_SUFFIX[off] as int;
    Seq::new(n as nat, |i: int| PREFIX_SUFFIX[off + 1 + i])
}

/// `ToUpperCase` at `i` (Appendix B): returns the word and the step.
/// Changes past the end of the word are dropped.
pub open spec fn uc_step(w: Seq<u8>, i: int) -> (Seq<u8>, int) {
    let c = w[i];
    if c < 0xc0 {
        if 97 <= c <= 122 {
            (w.update(i, c ^ 32), 1)
        } else {
            (w, 1)
        }
    } else if c < 0xe0 {
        if i + 1 < w.len() {
            (w.update(i + 1, w[i + 1] ^ 32), 2)
        } else {
            (w, 2)
        }
    } else {
        if i + 2 < w.len() {
            (w.update(i + 2, w[i + 2] ^ 5), 3)
        } else {
            (w, 3)
        }
    }
}

/// Uppercases from `i` on, in steps of 1 to 3 bytes; `n` is the word's
/// length, which `uc_step` keeps.
pub open spec fn uc_all(w: Seq<u8>, i: int, n: int) -> Seq<u8>
    decreases if i < n {
        n - i
    } else {
        0
    },
{
    if i < 0 || i >= n || i >= w.len() {
        w
    } else {
        let k: int = if w[i] < 0xc0 {
            1
        } else if w[i] < 0xe0 {
            2
        } else {
            3
        };
        uc_all(uc_step(w, i).0, i + k, n)
    }
}

/// The transform's middle part applied to a word: `t` is the type byte
/// (0..9 omit last `t`, 10 uppercase first, 11 uppercase all, 12..20 omit
/// first `t - 11`).
pub open spec fn transform_word(w: Seq<u8>, t: int) -> Seq<u8> {
    if t <= 9 {
        if w.len() > t {
            w.subrange(0, w.len() - t)
        } else {
            Seq::empty()
        }
    } else if t == 10 {
        if w.len() > 0 {
            uc_step(w, 0).0
        } else {
            w
        }
    } else if t == 11 {
        uc_all(w, 0, w.len() as int)
    } else {
        let k = t - 11;
        if w.len() > k {
            w.subrange(k, w.len() as int)
        } else {
            Seq::empty()
        }
    }
}

/// Transform `id` applied to a dictionary word.
pub open spec fn transform(w: Seq<u8>, id: int) -> Seq<u8> {
    ps_string(TRANSFORMS[3 * id] as int) + transform_word(w, TRANSFORMS[3 * id + 1] as int)
        + ps_string(TRANSFORMS[3 * id + 2] as int)
}

// ---------------------------------------------------------------------------
// The machine
// ---------------------------------------------------------------------------

pub enum Phase {
    /// The stream header.
    WBits,
    /// A meta-block header (`ISLAST` ... `ISUNCOMPRESSED`).
    MetaHeader,
    /// Metadata bytes to skip, `mrem` of them.
    Metadata,
    /// Uncompressed bytes to copy, `mrem` of them.
    Uncompressed,
    /// `NBLTYPES` of category `c` (0 literal, 1 insert-and-copy, 2 distance).
    NBlockTypes(int),
    /// The block type code, block count code and first block count of a
    /// category with at least two block types.
    BTypeCode(int),
    BCountCode(int),
    BCount(int),
    /// `NPOSTFIX` and `NDIRECT`.
    DistParams,
    /// One context mode per literal block type.
    CModes,
    /// The literal (0) or distance (1) context map.
    CMap(int),
    /// The literal (0), insert-and-copy (1) or distance (2) prefix codes.
    Trees(int),
    /// The start of a command.
    CmdBegin,
    /// `ilen` literals to go.
    Insert,
    /// The distance of the command.
    Dist,
    /// `clen` bytes to copy from `dist` back.
    Copy,
    /// The end of a meta-block.
    MetaDone,
    /// The end of the stream.
    Done,
}

pub struct St {
    pub phase: Phase,
    /// The bit position in the input.
    pub pos: int,
    /// Everything decoded so far.
    pub out: Seq<u8>,
    pub wbits: int,
    /// The current meta-block is the last one.
    pub last: bool,
    /// Bytes left in the current meta-block (or metadata bytes to skip).
    pub mrem: int,
    /// Per category: `NBLTYPES`, the block type and block count codes, the
    /// block count left, the current and the previous block type.
    pub nbt: Seq<int>,
    pub btc: Seq<Seq<u8>>,
    pub bcc: Seq<Seq<u8>>,
    pub blen: Seq<int>,
    pub bt: Seq<int>,
    pub bt2: Seq<int>,
    pub npostfix: int,
    pub ndirect: int,
    pub cmodes: Seq<u8>,
    /// The literal and distance context maps, and their numbers of trees.
    pub cmap: Seq<u8>,
    pub dmap: Seq<u8>,
    pub ntl: int,
    pub ntd: int,
    /// The literal, insert-and-copy and distance prefix codes.
    pub lit: Seq<Seq<u8>>,
    pub cmd: Seq<Seq<u8>>,
    pub dst: Seq<Seq<u8>>,
    /// The last four distances, most recent first.
    pub dr: Seq<int>,
    /// The current command: literals left, copy length, distance context,
    /// and whether the distance is implicitly the last one.
    pub ilen: int,
    pub clen: int,
    pub dctx: int,
    pub implicit: bool,
    /// The distance of the copy in progress.
    pub dist: int,
    pub pc: Pc,
    pub cm: Cm,
}

pub open spec fn init() -> St {
    St {
        phase: Phase::WBits,
        pos: 0,
        out: Seq::empty(),
        wbits: 0,
        last: false,
        mrem: 0,
        nbt: seq![1, 1, 1],
        btc: seq![Seq::empty(), Seq::empty(), Seq::empty()],
        bcc: seq![Seq::empty(), Seq::empty(), Seq::empty()],
        blen: seq![BLOCK_CAP, BLOCK_CAP, BLOCK_CAP],
        bt: seq![0, 0, 0],
        bt2: seq![1, 1, 1],
        npostfix: 0,
        ndirect: 0,
        cmodes: Seq::empty(),
        cmap: Seq::empty(),
        dmap: Seq::empty(),
        ntl: 0,
        ntd: 0,
        lit: Seq::empty(),
        cmd: Seq::empty(),
        dst: Seq::empty(),
        dr: seq![4, 11, 15, 16],
        ilen: 0,
        clen: 0,
        dctx: 0,
        implicit: false,
        dist: 0,
        pc: pc_init(),
        cm: cm_init(),
    }
}

/// The state at the start of a compressed meta-block's header.
pub open spec fn begin_compressed(s: St) -> St {
    St {
        phase: Phase::NBlockTypes(0),
        nbt: seq![1, 1, 1],
        btc: seq![Seq::empty(), Seq::empty(), Seq::empty()],
        bcc: seq![Seq::empty(), Seq::empty(), Seq::empty()],
        blen: seq![BLOCK_CAP, BLOCK_CAP, BLOCK_CAP],
        bt: seq![0, 0, 0],
        bt2: seq![1, 1, 1],
        cmodes: Seq::empty(),
        cmap: Seq::empty(),
        dmap: Seq::empty(),
        lit: Seq::empty(),
        cmd: Seq::empty(),
        dst: Seq::empty(),
        pc: pc_init(),
        cm: cm_init(),
        ..s
    }
}

pub enum Step {
    Next(St),
    Bad,
    Short,
}

/// The alphabet size of the prefix code being read in phase `ph`.
pub open spec fn pc_alpha(s: St) -> int {
    match s.phase {
        Phase::BTypeCode(c) => s.nbt[c] + 2,
        Phase::BCountCode(_) => 26,
        Phase::CMap(_) => s.cm.ntrees + s.cm.rlemax,
        Phase::Trees(g) => if g == 0 {
            256
        } else if g == 1 {
            704
        } else {
            dist_alpha(s.npostfix, s.ndirect)
        },
        _ => 0,
    }
}

/// The phase after the block type information of category `c`.
pub open spec fn after_cat(c: int) -> Phase {
    if c < 2 {
        Phase::NBlockTypes(c + 1)
    } else {
        Phase::DistParams
    }
}

/// The size of the literal (0) or distance (1) context map.
pub open spec fn cmap_size(s: St, w: int) -> int {
    if w == 0 {
        s.nbt[0] * 64
    } else {
        s.nbt[2] * 4
    }
}

/// The number of prefix codes in group `g`.
pub open spec fn ntrees(s: St, g: int) -> int {
    if g == 0 {
        s.ntl
    } else if g == 1 {
        s.nbt[1]
    } else {
        s.ntd
    }
}

/// The number of prefix codes of group `g` read so far.
pub open spec fn nread(s: St, g: int) -> int {
    if g == 0 {
        s.lit.len() as int
    } else if g == 1 {
        s.cmd.len() as int
    } else {
        s.dst.len() as int
    }
}

/// A block count (§6), read with the block count code `code`.
pub open spec fn read_blen(code: Seq<u8>, b: Seq<u8>, pos: int) -> R<int> {
    match rsym(code, b, pos) {
        R::Ok(sym, p) => match rd(b, p, BLEN_EXTRA[sym] as nat) {
            None => R::Short,
            Some(e) => R::Ok(BLEN_BASE[sym] as int + e, p + BLEN_EXTRA[sym] as int),
        },
        R::Bad => R::Bad,
        R::Short => R::Short,
    }
}

/// A block switch command for category `c` (§6): the new block type and
/// count. Only possible with at least two block types (google/brotli:
/// `DecodeBlockTypeAndLength`, error `BLOCK_SWITCH`).
pub open spec fn block_switch(s: St, b: Seq<u8>, c: int) -> Step {
    if s.nbt[c] < 2 {
        Step::Bad
    } else {
        match rsym(s.btc[c], b, s.pos) {
            R::Bad => Step::Bad,
            R::Short => Step::Short,
            R::Ok(sym, p) => match read_blen(s.bcc[c], b, p) {
                R::Bad => Step::Bad,
                R::Short => Step::Short,
                R::Ok(len, p2) => {
                    let t0 = if sym == 0 {
                        s.bt2[c]
                    } else if sym == 1 {
                        s.bt[c] + 1
                    } else {
                        sym - 2
                    };
                    let t = if t0 >= s.nbt[c] {
                        t0 - s.nbt[c]
                    } else {
                        t0
                    };
                    Step::Next(
                        St {
                            pos: p2,
                            bt: s.bt.update(c, t),
                            bt2: s.bt2.update(c, s.bt[c]),
                            blen: s.blen.update(c, len),
                            ..s
                        },
                    )
                },
            },
        }
    }
}

/// The phase after a meta-block's data ends.
pub open spec fn after_data(mrem: int) -> Phase {
    if mrem == 0 {
        Phase::MetaDone
    } else {
        Phase::CmdBegin
    }
}

/// One step of the machine. `Done` has no step. (Opaque only to keep the
/// prover fast: proofs reveal it where they need it.)
#[verifier::opaque]
pub open spec fn step(b: Seq<u8>, s: St) -> Step {
    match s.phase {
        Phase::WBits => match read_wbits(b, s.pos) {
            R::Ok(w, p) => Step::Next(St { phase: Phase::MetaHeader, pos: p, wbits: w, ..s }),
            R::Bad => Step::Bad,
            R::Short => Step::Short,
        },
        Phase::MetaHeader => match read_meta_header(b, s.pos) {
            R::Bad => Step::Bad,
            R::Short => Step::Short,
            R::Ok(h, p) => {
                let s1 = St { pos: p, last: h.last, mrem: h.len, ..s };
                match h.kind {
                    Kind::EmptyLast => match pad(b, p) {
                        R::Ok(_, p2) => Step::Next(St { phase: Phase::Done, pos: p2, ..s1 }),
                        R::Bad => Step::Bad,
                        R::Short => Step::Short,
                    },
                    Kind::Metadata => Step::Next(St { phase: Phase::Metadata, ..s1 }),
                    Kind::Uncompressed => Step::Next(St { phase: Phase::Uncompressed, ..s1 }),
                    Kind::Compressed => Step::Next(begin_compressed(s1)),
                }
            },
        },
        Phase::Metadata => if s.mrem <= 0 {
            Step::Next(St { phase: Phase::MetaDone, ..s })
        } else {
            match rd(b, s.pos, 8) {
                None => Step::Short,
                Some(_) => Step::Next(St { pos: s.pos + 8, mrem: s.mrem - 1, ..s }),
            }
        },
        Phase::Uncompressed => if s.mrem <= 0 {
            Step::Next(St { phase: Phase::MetaDone, ..s })
        } else {
            match rd(b, s.pos, 8) {
                None => Step::Short,
                Some(x) => Step::Next(
                    St { pos: s.pos + 8, mrem: s.mrem - 1, out: s.out.push(x as u8), ..s },
                ),
            }
        },
        Phase::NBlockTypes(c) => match varlen8(b, s.pos) {
            R::Bad => Step::Bad,
            R::Short => Step::Short,
            R::Ok(v, p) => {
                let s1 = St { pos: p, nbt: s.nbt.update(c, v + 1), ..s };
                if v + 1 >= 2 {
                    Step::Next(St { phase: Phase::BTypeCode(c), pc: pc_init(), ..s1 })
                } else {
                    Step::Next(St { phase: after_cat(c), ..s1 })
                }
            },
        },
        Phase::BTypeCode(c) => match pc_step(b, s.pos, s.pc, pc_alpha(s)) {
            PcRes::Bad => Step::Bad,
            PcRes::Short => Step::Short,
            PcRes::Cont(pc, p) => Step::Next(St { pos: p, pc, ..s }),
            PcRes::Fin(lens, p) => Step::Next(
                St {
                    phase: Phase::BCountCode(c),
                    pos: p,
                    btc: s.btc.update(c, lens),
                    pc: pc_init(),
                    ..s
                },
            ),
        },
        Phase::BCountCode(c) => match pc_step(b, s.pos, s.pc, pc_alpha(s)) {
            PcRes::Bad => Step::Bad,
            PcRes::Short => Step::Short,
            PcRes::Cont(pc, p) => Step::Next(St { pos: p, pc, ..s }),
            PcRes::Fin(lens, p) => Step::Next(
                St {
                    phase: Phase::BCount(c),
                    pos: p,
                    bcc: s.bcc.update(c, lens),
                    pc: pc_init(),
                    ..s
                },
            ),
        },
        Phase::BCount(c) => match read_blen(s.bcc[c], b, s.pos) {
            R::Bad => Step::Bad,
            R::Short => Step::Short,
            R::Ok(len, p) => Step::Next(
                St { phase: after_cat(c), pos: p, blen: s.blen.update(c, len), ..s },
            ),
        },
        Phase::DistParams => match rd(b, s.pos, 6) {
            None => Step::Short,
            Some(v) => {
                let np = (v % 4) as int;
                Step::Next(
                    St {
                        phase: Phase::CModes,
                        pos: s.pos + 6,
                        npostfix: np,
                        ndirect: (v / 4) as int * pow2(np as nat),
                        cmodes: Seq::empty(),
                        ..s
                    },
                )
            },
        },
        Phase::CModes => if s.cmodes.len() >= s.nbt[0] {
            Step::Next(St { phase: Phase::CMap(0), cm: cm_init(), ..s })
        } else {
            match rd(b, s.pos, 2) {
                None => Step::Short,
                Some(m) => Step::Next(
                    St { pos: s.pos + 2, cmodes: s.cmodes.push(m as u8), ..s },
                ),
            }
        },
        Phase::CMap(w) => cmap_step(b, s, w),
        Phase::Trees(g) => if nread(s, g) >= ntrees(s, g) {
            if g < 2 {
                Step::Next(St { phase: Phase::Trees(g + 1), pc: pc_init(), ..s })
            } else {
                Step::Next(St { phase: Phase::CmdBegin, ..s })
            }
        } else {
            match pc_step(b, s.pos, s.pc, pc_alpha(s)) {
                PcRes::Bad => Step::Bad,
                PcRes::Short => Step::Short,
                PcRes::Cont(pc, p) => Step::Next(St { pos: p, pc, ..s }),
                PcRes::Fin(lens, p) => {
                    let s1 = St { pos: p, pc: pc_init(), ..s };
                    if g == 0 {
                        Step::Next(St { lit: s.lit.push(lens), ..s1 })
                    } else if g == 1 {
                        Step::Next(St { cmd: s.cmd.push(lens), ..s1 })
                    } else {
                        Step::Next(St { dst: s.dst.push(lens), ..s1 })
                    }
                },
            }
        },
        Phase::CmdBegin => if s.blen[1] == 0 {
            block_switch(s, b, 1)
        } else {
            command(b, s)
        },
        Phase::Insert => if s.blen[0] == 0 {
            block_switch(s, b, 0)
        } else {
            literal(b, s)
        },
        Phase::Dist => distance(b, s),
        Phase::Copy => {
            let x = s.out[s.out.len() - s.dist];
            let s1 = St { out: s.out.push(x), clen: s.clen - 1, mrem: s.mrem - 1, ..s };
            if s1.clen == 0 {
                Step::Next(St { phase: after_data(s1.mrem), ..s1 })
            } else {
                Step::Next(s1)
            }
        },
        Phase::MetaDone => if s.last {
            match pad(b, s.pos) {
                R::Ok(_, p) => Step::Next(St { phase: Phase::Done, pos: p, ..s }),
                R::Bad => Step::Bad,
                R::Short => Step::Short,
            }
        } else {
            Step::Next(St { phase: Phase::MetaHeader, ..s })
        },
        Phase::Done => Step::Next(s),
    }
}

/// One step of reading context map `w` (0 literal, 1 distance).
pub open spec fn cmap_step(b: Seq<u8>, s: St, w: int) -> Step {
    let cm = s.cm;
    let size = cmap_size(s, w);
    if cm.stage == 0 {
        match varlen8(b, s.pos) {
            R::Bad => Step::Bad,
            R::Short => Step::Short,
            R::Ok(v, p) => if v == 0 {
                cmap_finish(St { pos: p, ..s }, w, 1, Seq::new(size as nat, |i: int| 0u8))
            } else {
                match rd(b, p, 1) {
                    None => Step::Short,
                    Some(r) => if r == 0 {
                        Step::Next(
                            St {
                                pos: p + 1,
                                cm: Cm { stage: 1, ntrees: v + 1, rlemax: 0, ..cm },
                                pc: pc_init(),
                                ..s
                            },
                        )
                    } else {
                        match rd(b, p + 1, 4) {
                            None => Step::Short,
                            Some(r4) => Step::Next(
                                St {
                                    pos: p + 5,
                                    cm: Cm { stage: 1, ntrees: v + 1, rlemax: r4 + 1, ..cm },
                                    pc: pc_init(),
                                    ..s
                                },
                            ),
                        }
                    },
                }
            },
        }
    } else if cm.stage == 1 {
        match pc_step(b, s.pos, s.pc, pc_alpha(s)) {
            PcRes::Bad => Step::Bad,
            PcRes::Short => Step::Short,
            PcRes::Cont(pc, p) => Step::Next(St { pos: p, pc, ..s }),
            PcRes::Fin(lens, p) => Step::Next(
                St {
                    pos: p,
                    cm: Cm { stage: 2, code: lens, map: Seq::empty(), ..cm },
                    pc: pc_init(),
                    ..s
                },
            ),
        }
    } else if cm.stage == 2 {
        if cm.map.len() >= size {
            Step::Next(St { cm: Cm { stage: 3, ..cm }, ..s })
        } else {
            match rsym(cm.code, b, s.pos) {
                R::Bad => Step::Bad,
                R::Short => Step::Short,
                R::Ok(sym, p) => if sym == 0 {
                    Step::Next(St { pos: p, cm: Cm { map: cm.map.push(0), ..cm }, ..s })
                } else if sym > cm.rlemax {
                    Step::Next(
                        St {
                            pos: p,
                            cm: Cm { map: cm.map.push((sym - cm.rlemax) as u8), ..cm },
                            ..s
                        },
                    )
                } else {
                    // A run of zeros.
                    match rd(b, p, sym as nat) {
                        None => Step::Short,
                        Some(e) => {
                            let reps = pow2(sym as nat) + e;
                            if cm.map.len() + reps > size {
                                Step::Bad
                            } else {
                                Step::Next(
                                    St {
                                        pos: p + sym,
                                        cm: Cm {
                                            map: cm.map + Seq::new(reps as nat, |i: int| 0u8),
                                            ..cm
                                        },
                                        ..s
                                    },
                                )
                            }
                        },
                    }
                },
            }
        }
    } else {
        match rd(b, s.pos, 1) {
            None => Step::Short,
            Some(x) => cmap_finish(
                St { pos: s.pos + 1, ..s },
                w,
                cm.ntrees,
                if x == 1 {
                    imtf(cm.map)
                } else {
                    cm.map
                },
            ),
        }
    }
}

pub open spec fn cmap_finish(s: St, w: int, nt: int, map: Seq<u8>) -> Step {
    if w == 0 {
        Step::Next(St { phase: Phase::CMap(1), cmap: map, ntl: nt, cm: cm_init(), ..s })
    } else {
        Step::Next(St { phase: Phase::Trees(0), dmap: map, ntd: nt, cm: cm_init(), pc: pc_init(), ..s })
    }
}

/// An insert-and-copy command (§5): its symbol and extra bits.
pub open spec fn command(b: Seq<u8>, s: St) -> Step {
    match rsym(s.cmd[s.bt[1]], b, s.pos) {
        R::Bad => Step::Bad,
        R::Short => Step::Short,
        R::Ok(sym, p) => {
            let ic = ins_code(sym);
            let cc = cpy_code(sym);
            let ie = INS_EXTRA[ic] as nat;
            let ce = CPY_EXTRA[cc] as nat;
            match rd(b, p, ie) {
                None => Step::Short,
                Some(ix) => match rd(b, p + ie, ce) {
                    None => Step::Short,
                    Some(cx) => {
                        let ilen = INS_BASE[ic] as int + ix;
                        let clen = CPY_BASE[cc] as int + cx;
                        if ilen > s.mrem {
                            // google/brotli decodes the literals first and
                            // then fails (BLOCK_LENGTH_2); see README.
                            Step::Bad
                        } else {
                            Step::Next(
                                St {
                                    phase: if ilen > 0 {
                                        Phase::Insert
                                    } else {
                                        Phase::Dist
                                    },
                                    pos: p + ie + ce,
                                    blen: s.blen.update(1, s.blen[1] - 1),
                                    ilen,
                                    clen,
                                    dctx: dist_context(sym),
                                    implicit: sym < 128,
                                    ..s
                                },
                            )
                        }
                    },
                },
            }
        },
    }
}

/// One literal (§7.1, §7.3).
pub open spec fn literal(b: Seq<u8>, s: St) -> Step {
    let t = s.bt[0];
    let ctx = lit_context(s.cmodes[t] as int, p1(s.out), p2(s.out));
    let tree = s.cmap[t * 64 + ctx] as int;
    match rsym(s.lit[tree], b, s.pos) {
        R::Bad => Step::Bad,
        R::Short => Step::Short,
        R::Ok(x, p) => {
            let s1 = St {
                pos: p,
                out: s.out.push(x as u8),
                blen: s.blen.update(0, s.blen[0] - 1),
                ilen: s.ilen - 1,
                mrem: s.mrem - 1,
                ..s
            };
            if s1.ilen > 0 {
                Step::Next(s1)
            } else if s1.mrem == 0 {
                Step::Next(St { phase: Phase::MetaDone, ..s1 })
            } else {
                Step::Next(St { phase: Phase::Dist, ..s1 })
            }
        },
    }
}

/// The distance of the command, then the backward copy or dictionary
/// reference it makes (§4, §8).
pub open spec fn distance(b: Seq<u8>, s: St) -> Step {
    if s.implicit {
        resolve(s, s.dr[0], true)
    } else if s.blen[2] == 0 {
        block_switch(s, b, 2)
    } else {
        let tree = s.dmap[s.bt[2] * 4 + s.dctx] as int;
        match rsym(s.dst[tree], b, s.pos) {
            R::Bad => Step::Bad,
            R::Short => Step::Short,
            R::Ok(dcode, p) => {
                let s1 = St { pos: p, blen: s.blen.update(2, s.blen[2] - 1), ..s };
                if dcode < 16 {
                    let d = short_dist(dcode, s.dr);
                    if d <= 0 {
                        Step::Bad
                    } else {
                        resolve(s1, d, dcode == 0)
                    }
                } else if dcode < 16 + s.ndirect {
                    resolve(s1, dcode - 15, false)
                } else {
                    let n = dist_extra(dcode, s.npostfix, s.ndirect);
                    match rd(b, p, n) {
                        None => Step::Short,
                        Some(e) => resolve(
                            St { pos: p + n, ..s1 },
                            dist_value(dcode, e as int, s.npostfix, s.ndirect),
                            false,
                        ),
                    }
                }
            },
        }
    }
}

/// A backward copy of `s.clen` bytes from distance `d`, or, past the
/// window, a static dictionary word. `last` is set for distance code 0 (and
/// implicit distances), which do not enter the ring of last distances;
/// dictionary references never do.
///
/// Opaque, like `step`, so that proofs unfold it only where they need it.
#[verifier::opaque]
pub open spec fn resolve(s: St, d: int, last: bool) -> Step {
    let maxd = max_distance(s.out.len() as int, s.wbits);
    if d <= maxd {
        if s.clen > s.mrem {
            Step::Bad
        } else {
            Step::Next(
                St {
                    phase: Phase::Copy,
                    dist: d,
                    dr: if last {
                        s.dr
                    } else {
                        seq![d, s.dr[0], s.dr[1], s.dr[2]]
                    },
                    ..s
                },
            )
        }
    } else if d > 0x7FFF_FFFC || s.clen < 4 || s.clen > 24 {
        Step::Bad
    } else {
        let len = s.clen;
        let addr = d - maxd - 1;
        let n = NDBITS[len] as nat;
        let idx = addr % pow2(n) as int;
        let tid = addr / pow2(n) as int;
        if tid >= NTRANSFORMS {
            Step::Bad
        } else {
            let w = transform(dict_word(len, idx), tid);
            if w.len() == 0 && d <= 120 {
                // google/brotli: "Invalid length-0 dictionary word after
                // transform".
                Step::Bad
            } else if w.len() > s.mrem {
                Step::Bad
            } else {
                Step::Next(
                    St {
                        phase: after_data(s.mrem - w.len()),
                        out: s.out + w,
                        mrem: s.mrem - w.len(),
                        ..s
                    },
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Runs
// ---------------------------------------------------------------------------

/// `n` steps from `s`, stopping early at `Done`.
pub open spec fn run(b: Seq<u8>, s: St, n: nat) -> Step
    decreases n,
{
    if n == 0 || s.phase is Done {
        Step::Next(s)
    } else {
        match step(b, s) {
            Step::Next(s1) => run(b, s1, (n - 1) as nat),
            Step::Bad => Step::Bad,
            Step::Short => Step::Short,
        }
    }
}

/// `s` is a state the machine reaches on input `b`.
pub open spec fn reaches(b: Seq<u8>, s: St) -> bool {
    exists|n: nat| run(b, init(), n) == Step::Next(s)
}

/// `b` decodes to `out`, using its first `used` bytes.
pub open spec fn decodes(b: Seq<u8>, out: Seq<u8>, used: int) -> bool {
    exists|s: St| #[trigger] reaches(b, s) && s.phase is Done && s.out == out && 8 * used == s.pos
}

/// `b` is malformed (whatever follows it).
pub open spec fn rejects(b: Seq<u8>) -> bool {
    exists|n: nat| run(b, init(), n) == Step::Bad
}

} // verus!

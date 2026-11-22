//! The Snappy format (format_description.txt) as pure functions. This
//! file is the trusted specification: everything else is proven against
//! it.
use vstd::prelude::*;

verus! {

#[cfg(verus_only)]
pub use verilith_core::lz::lz_copy;

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

/// The preamble: the uncompressed length as a little-endian varint, 7
/// bits a byte, the top bit saying another byte follows. It is at most
/// 2^32 - 1, so there are at most 5 bytes and the fifth holds 4 bits.
/// `k` counts the bytes read. Gives the value and the index after it.
pub open spec fn varint(s: Seq<u8>, i: int, k: nat) -> Option<(nat, int)>
    decreases 5 - k,
{
    if k >= 5 || i < 0 || i >= s.len() {
        None
    } else {
        let b = s[i] as nat;
        let v = b % 128;
        if k == 4 && v >= 16 {
            None
        } else if b < 128 {
            Some((v, i + 1))
        } else {
            match varint(s, i + 1, k + 1) {
                Some((r, j)) => Some((v + 128 * r, j)),
                None => None,
            }
        }
    }
}

/// The elements from `i`, applied to `out`, for an uncompressed length
/// of `n`: the input must end with an element, with exactly `n` bytes
/// produced.
///
/// The low two bits of an element's tag byte say what it is:
/// - 00, a literal. The upper six bits are its length minus 1, or 60 to
///   63 to say the length minus 1 is in the next 1 to 4 bytes.
/// - 01, a copy of 4 to 11 bytes (three bits of the tag) from up to 2047
///   back (the tag's top three bits, then a byte).
/// - 10, a copy of 1 to 64 bytes (the tag's upper six bits) from an
///   offset in the next 2 bytes.
/// - 11, the same with an offset in the next 4 bytes.
///
/// An offset is never 0 and never reaches before the start of the
/// output. Copies may overlap what they write.
pub open spec fn elems(s: Seq<u8>, i: int, out: Seq<u8>, n: nat) -> Option<Seq<u8>>
    decreases s.len() - i,
{
    if i < 0 || i > s.len() {
        None
    } else if i == s.len() {
        if out.len() == n {
            Some(out)
        } else {
            None
        }
    } else {
        let tag = s[i] as nat;
        let kind = tag % 4;
        let hi = tag / 4;
        if kind == 0 {
            let nb: nat = if hi < 60 {
                0
            } else {
                (hi - 59) as nat
            };
            if i + 1 + nb > s.len() {
                None
            } else {
                let len = if hi < 60 {
                    hi + 1
                } else {
                    le(s, i + 1, nb) + 1
                };
                let j = i + 1 + nb;
                if j + len > s.len() {
                    None
                } else {
                    elems(s, j + len, out + s.subrange(j, j + len), n)
                }
            }
        } else {
            let nb: nat = if kind == 1 {
                1
            } else if kind == 2 {
                2
            } else {
                4
            };
            if i + 1 + nb > s.len() {
                None
            } else {
                let len = if kind == 1 {
                    4 + hi % 8
                } else {
                    1 + hi
                };
                let off = if kind == 1 {
                    (hi / 8) * 256 + s[i + 1] as nat
                } else {
                    le(s, i + 1, nb)
                };
                if off == 0 || off > out.len() {
                    None
                } else {
                    elems(s, i + 1 + nb, lz_copy(out, off as int, len), n)
                }
            }
        }
    }
}

/// What a compressed buffer decompresses to, or `None` if it is not
/// valid.
pub open spec fn decompress(s: Seq<u8>) -> Option<Seq<u8>> {
    match varint(s, 0, 0) {
        Some((n, i)) => elems(s, i, Seq::empty(), n),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// The framing format (framing_format.txt)
// ---------------------------------------------------------------------------

/// CRC-32C's polynomial (Castagnoli, RFC 3720 appendix B.4), bit
/// reversed.
pub spec const CRC32C_POLY: u32 = 0x82f63b78;

/// One bit of the CRC register update.
pub open spec fn crc_step(c: u32) -> u32 {
    if c & 1 == 1 {
        (c >> 1u32) ^ CRC32C_POLY
    } else {
        c >> 1u32
    }
}

/// `n` bit steps.
pub open spec fn crc_steps(c: u32, n: nat) -> u32
    decreases n,
{
    if n == 0 {
        c
    } else {
        crc_steps(crc_step(c), (n - 1) as nat)
    }
}

/// The CRC register after one more byte.
pub open spec fn crc_byte(c: u32, x: u8) -> u32 {
    crc_steps(c ^ (x as u32), 8)
}

/// The CRC register after `d`, starting from all ones.
pub open spec fn crc_reg(d: Seq<u8>) -> u32
    decreases d.len(),
{
    if d.len() == 0 {
        0xffff_ffff
    } else {
        crc_byte(crc_reg(d.drop_last()), d.last())
    }
}

/// CRC-32C: the final register, complemented.
pub open spec fn crc32c(d: Seq<u8>) -> u32 {
    !crc_reg(d)
}

/// How the framing format stores a checksum: rotated right by 15 bits,
/// plus a constant (modulo 2^32).
pub open spec fn mask(crc: u32) -> nat {
    ((((crc >> 15u32) | (crc << 17u32)) as int + 0xa282ead8) % 0x1_0000_0000) as nat
}

/// The stream identifier chunk: type 0xff, length 6, "sNaPpY".
pub open spec fn stream_id() -> Seq<u8> {
    seq![0xffu8, 6, 0, 0, 0x73, 0x4e, 0x61, 0x50, 0x70, 0x59]
}

/// The most data a chunk may hold, uncompressed.
pub spec const CHUNK_MAX: nat = 65536;

/// The chunks from `i`, their data appended to `out`. A chunk is a type
/// byte, a 3-byte little-endian length, and that many bytes:
///
/// - 0x00, compressed data: a masked CRC-32C of the uncompressed data (4
///   bytes, little-endian), then the data in the Snappy format.
/// - 0x01, uncompressed data: the same checksum, then the data.
/// - 0xff, the stream identifier again: it must be exactly that.
/// - 0x80 to 0xfe: skipped (padding, and types reserved as skippable).
/// - 0x02 to 0x7f: not allowed.
///
/// A data chunk holds at most `CHUNK_MAX` bytes of uncompressed data.
pub open spec fn chunks(s: Seq<u8>, i: int, out: Seq<u8>) -> Option<Seq<u8>>
    decreases s.len() - i,
{
    if i < 0 || i > s.len() {
        None
    } else if i == s.len() {
        Some(out)
    } else if i + 4 > s.len() {
        None
    } else {
        let t = s[i];
        let j = i + 4;
        let e = j + le(s, i + 1, 3);
        if e > s.len() {
            None
        } else if t == 0 || t == 1 {
            if e - j < 4 {
                None
            } else {
                let data = if t == 0 {
                    decompress(s.subrange(j + 4, e))
                } else {
                    Some(s.subrange(j + 4, e))
                };
                match data {
                    Some(d) => if d.len() <= CHUNK_MAX && le(s, j, 4) == mask(crc32c(d)) {
                        chunks(s, e, out + d)
                    } else {
                        None
                    },
                    None => None,
                }
            }
        } else if t == 0xff {
            if s.subrange(i, e) == stream_id() {
                chunks(s, e, out)
            } else {
                None
            }
        } else if t >= 0x80 {
            chunks(s, e, out)
        } else {
            None
        }
    }
}

/// What a stream in the framing format holds, or `None` if it is not
/// valid: the stream identifier, then chunks. A stream with no bytes at
/// all holds nothing (the format does not say; this is what the Go and
/// Rust implementations do, and what they write for no data).
pub open spec fn stream(s: Seq<u8>) -> Option<Seq<u8>> {
    if s.len() == 0 {
        Some(Seq::empty())
    } else if s.len() >= 10 && s.subrange(0, 10) == stream_id() {
        chunks(s, 10, Seq::empty())
    } else {
        None
    }
}

} // verus!

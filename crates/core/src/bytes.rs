//! Fixed-width integers in byte strings: their values as spec functions, and
//! bounds-checked readers proven to return them.
use vstd::prelude::*;

verus! {

/// The big-endian value of the 2 bytes at `i`.
pub open spec fn be16(b: Seq<u8>, i: int) -> nat {
    b[i] as nat * 256 + b[i + 1] as nat
}

/// The big-endian value of the 4 bytes at `i`.
pub open spec fn be32(b: Seq<u8>, i: int) -> nat {
    ((b[i] as nat * 256 + b[i + 1] as nat) * 256 + b[i + 2] as nat) * 256 + b[i + 3] as nat
}

/// The little-endian value of the 2 bytes at `i`.
pub open spec fn le16(b: Seq<u8>, i: int) -> nat {
    b[i] as nat + 256 * b[i + 1] as nat
}

/// The little-endian value of the 4 bytes at `i`.
pub open spec fn le32(b: Seq<u8>, i: int) -> nat {
    le16(b, i) + 65536 * le16(b, i + 2)
}

/// A big-endian `u16` at `pos` and the position after it, or `None` if
/// fewer than 2 bytes are left.
pub open spec fn parse_u16(b: Seq<u8>, pos: int) -> Option<(u16, int)> {
    if 0 <= pos && pos + 2 <= b.len() {
        Some(((b[pos] as int * 256 + b[pos + 1] as int) as u16, pos + 2))
    } else {
        None
    }
}

/// A big-endian `u32` at `pos` and the position after it, or `None` if
/// fewer than 4 bytes are left.
pub open spec fn parse_u32(b: Seq<u8>, pos: int) -> Option<(u32, int)> {
    if 0 <= pos && pos + 4 <= b.len() {
        Some(
            (
                (b[pos] as int * 0x100_0000 + b[pos + 1] as int * 0x1_0000 + b[pos + 2] as int
                    * 256 + b[pos + 3] as int) as u32,
                pos + 4,
            ),
        )
    } else {
        None
    }
}

pub proof fn lemma_parse_u16(b: Seq<u8>, pos: int)
    requires
        0 <= pos,
        pos + 2 <= b.len(),
    ensures
        parse_u16(b, pos) == Some((be16(b, pos) as u16, pos + 2)),
        be16(b, pos) < 0x1_0000,
{
}

pub proof fn lemma_parse_u32(b: Seq<u8>, pos: int)
    requires
        0 <= pos,
        pos + 4 <= b.len(),
    ensures
        parse_u32(b, pos) == Some((be32(b, pos) as u32, pos + 4)),
        be32(b, pos) < 0x1_0000_0000,
{
}

/// `parse_u16`.
#[inline(always)]
pub fn read_u16(b: &[u8], pos: usize) -> (r: Option<(u16, usize)>)
    ensures
        r matches Some((x, p)) ==> parse_u16(b@, pos as int) == Some((x, p as int)),
        r is None ==> parse_u16(b@, pos as int) is None,
{
    if pos > b.len() || b.len() - pos < 2 {
        None
    } else {
        Some(((b[pos] as u16) * 256 + b[pos + 1] as u16, pos + 2))
    }
}

/// `parse_u32`.
#[inline(always)]
pub fn read_u32(b: &[u8], pos: usize) -> (r: Option<(u32, usize)>)
    ensures
        r matches Some((x, p)) ==> parse_u32(b@, pos as int) == Some((x, p as int)),
        r is None ==> parse_u32(b@, pos as int) is None,
{
    if pos > b.len() || b.len() - pos < 4 {
        None
    } else {
        let x = (b[pos] as u32) * 0x100_0000 + (b[pos + 1] as u32) * 0x1_0000 + (b[pos + 2] as u32)
            * 256 + b[pos + 3] as u32;
        Some((x, pos + 4))
    }
}

} // verus!

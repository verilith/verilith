//! QUIC variable-length integers (RFC 9000 §16), which HTTP/3 (RFC 9114)
//! and QPACK's streams use too: the specification, the verified reader and
//! writers, and the round trip. The two most significant bits of the first
//! byte give the length (1, 2, 4 or 8 bytes); the rest, most significant
//! first, are the value, below `2^62`.
use alloc::vec::Vec;
use crate::prims::set;
use vstd::prelude::*;

verus! {

/// `2^62`: every variable-length integer is below it.
pub const VARINT_LIMIT: u64 = 0x4000_0000_0000_0000;

/// `2^62 - 1`, the largest variable-length integer.
pub const VARINT_MAX: u64 = 0x3fff_ffff_ffff_ffff;

/// The length of the variable-length integer whose first byte is `first`:
/// its two most significant bits are the base-2 logarithm of the length.
pub open spec fn vlen(first: u8) -> int {
    if first < 0x40 {
        1
    } else if first < 0x80 {
        2
    } else if first < 0xc0 {
        4
    } else {
        8
    }
}

/// Byte `b[i]` as a `u64`.
pub open spec fn by(b: Seq<u8>, i: int) -> u64 {
    b[i] as u64
}

/// The variable-length integer at `b[pos]` (§16): its value and the
/// position after it. The remaining bits of the first byte and the bytes
/// after it are the value, most significant first. Any of the four lengths
/// may encode any value that fits.
pub open spec fn varint(b: Seq<u8>, pos: int) -> Option<(u64, int)> {
    if pos < 0 || pos >= b.len() {
        None
    } else {
        let n = vlen(b[pos]);
        if pos + n > b.len() {
            None
        } else {
            let v0 = by(b, pos) & 0x3f;
            let v = if n == 1 {
                v0
            } else if n == 2 {
                (v0 << 8) | by(b, pos + 1)
            } else if n == 4 {
                (v0 << 24) | (by(b, pos + 1) << 16) | (by(b, pos + 2) << 8) | by(b, pos + 3)
            } else {
                (v0 << 56) | (by(b, pos + 1) << 48) | (by(b, pos + 2) << 40) | (by(b, pos + 3) << 32)
                    | (by(b, pos + 4) << 24) | (by(b, pos + 5) << 16) | (by(b, pos + 6) << 8) | by(
                    b,
                    pos + 7,
                )
            };
            Some((v, pos + n))
        }
    }
}

/// The low 8 bits of `x`.
pub open spec fn b8(x: u64) -> u8 {
    x as u8
}

/// The shortest encoding of `v` (which must be below `2^62`).
pub open spec fn varint_enc(v: u64) -> Seq<u8> {
    if v < 0x40 {
        seq![b8(v)]
    } else if v < 0x4000 {
        seq![b8(0x40 | (v >> 8)), b8(v)]
    } else if v < 0x4000_0000 {
        seq![b8(0x80 | (v >> 24)), b8(v >> 16), b8(v >> 8), b8(v)]
    } else {
        seq![
            b8(0xc0 | (v >> 56)),
            b8(v >> 48),
            b8(v >> 40),
            b8(v >> 32),
            b8(v >> 24),
            b8(v >> 16),
            b8(v >> 8),
            b8(v),
        ]
    }
}

/// The length of `varint_enc(v)`.
pub open spec fn varint_size(v: u64) -> int {
    if v < 0x40 {
        1
    } else if v < 0x4000 {
        2
    } else if v < 0x4000_0000 {
        4
    } else {
        8
    }
}


/// Every decoded value is below `2^62`, and the position moves forward by
/// 1, 2, 4 or 8.
pub proof fn lemma_varint_bound(b: Seq<u8>, pos: int)
    ensures
        varint(b, pos) matches Some((v, e)) ==> v < VARINT_LIMIT && e == pos + vlen(b[pos]) && pos
            < e <= b.len(),
{
    if let Some((v, e)) = varint(b, pos) {
        let b0 = by(b, pos);
        let b1 = by(b, pos + 1);
        let b2 = by(b, pos + 2);
        let b3 = by(b, pos + 3);
        let b4 = by(b, pos + 4);
        let b5 = by(b, pos + 5);
        let b6 = by(b, pos + 6);
        let b7 = by(b, pos + 7);
        assert(b0 < 256 && b1 < 256 && b2 < 256 && b3 < 256);
        assert(b4 < 256 && b5 < 256 && b6 < 256 && b7 < 256);
        let n = vlen(b[pos]);
        if n == 1 {
            assert(b0 & 0x3f < 0x4000_0000_0000_0000) by (bit_vector);
        } else if n == 2 {
            assert(((b0 & 0x3f) << 8) | b1 < 0x4000_0000_0000_0000) by (bit_vector)
                requires
                    b1 < 256,
            ;
        } else if n == 4 {
            assert(((b0 & 0x3f) << 24) | (b1 << 16) | (b2 << 8) | b3 < 0x4000_0000_0000_0000)
                by (bit_vector)
                requires
                    b1 < 256,
                    b2 < 256,
                    b3 < 256,
            ;
        } else {
            assert(((b0 & 0x3f) << 56) | (b1 << 48) | (b2 << 40) | (b3 << 32) | (b4 << 24) | (b5
                << 16) | (b6 << 8) | b7 < 0x4000_0000_0000_0000) by (bit_vector)
                requires
                    b1 < 256,
                    b2 < 256,
                    b3 < 256,
                    b4 < 256,
                    b5 < 256,
                    b6 < 256,
                    b7 < 256,
            ;
        }
    }
}

/// A varint that parses parses the same with more input after it, and
/// with other bytes before it.
pub proof fn lemma_varint_frame(b: Seq<u8>, pos: int, c: Seq<u8>, q: int)
    requires
        varint(b, pos) is Some,
        0 <= q,
        q + (varint(b, pos).unwrap().1 - pos) <= c.len(),
        c.subrange(q, q + (varint(b, pos).unwrap().1 - pos)) == b.subrange(
            pos,
            varint(b, pos).unwrap().1,
        ),
    ensures
        varint(c, q) matches Some((v, e)) && v == varint(b, pos).unwrap().0 && e - q == varint(
            b,
            pos,
        ).unwrap().1 - pos,
{
    let n = varint(b, pos).unwrap().1 - pos;
    lemma_varint_bound(b, pos);
    let sc = c.subrange(q, q + n);
    let sb = b.subrange(pos, pos + n);
    assert(sc[0] == sb[0]);
    if n >= 2 {
        assert(sc[1] == sb[1]);
    }
    if n >= 4 {
        assert(sc[2] == sb[2]);
        assert(sc[3] == sb[3]);
    }
    if n >= 8 {
        assert(sc[4] == sb[4]);
        assert(sc[5] == sb[5]);
        assert(sc[6] == sb[6]);
        assert(sc[7] == sb[7]);
    }
}

/// Parsing the encoding of `v`, followed by anything, gives `v` back.
pub proof fn lemma_varint_roundtrip(v: u64, pre: Seq<u8>, rest: Seq<u8>)
    requires
        v < VARINT_LIMIT,
    ensures
        varint(pre + varint_enc(v) + rest, pre.len() as int) == Some(
            (v, pre.len() + varint_size(v)),
        ),
        varint_enc(v).len() == varint_size(v),
{
    let e = varint_enc(v);
    let b = pre + e + rest;
    let p = pre.len() as int;
    assert(b[p] == e[0]);
    if v < 0x40 {
        assert(0 <= (v as u8) < 0x40 && ((v as u8) as u64) & 0x3f == v) by (bit_vector)
            requires
                v < 0x40,
        ;
    } else if v < 0x4000 {
        assert(b[p + 1] == e[1]);
        assert(0x40 <= ((0x40 | (v >> 8)) as u8) < 0x80 && (((((0x40 | (v >> 8)) as u8) as u64)
            & 0x3f) << 8) | ((v as u8) as u64) == v) by (bit_vector)
            requires
                0x40 <= v < 0x4000,
        ;
    } else if v < 0x4000_0000 {
        assert(b[p + 1] == e[1] && b[p + 2] == e[2] && b[p + 3] == e[3]);
        assert(0x80 <= ((0x80 | (v >> 24)) as u8) < 0xc0 && (((((0x80 | (v >> 24)) as u8) as u64)
            & 0x3f) << 24) | ((((v >> 16) as u8) as u64) << 16) | ((((v >> 8) as u8) as u64) << 8)
            | ((v as u8) as u64) == v) by (bit_vector)
            requires
                0x4000 <= v < 0x4000_0000,
        ;
    } else {
        assert(b[p + 1] == e[1] && b[p + 2] == e[2] && b[p + 3] == e[3]);
        assert(b[p + 4] == e[4] && b[p + 5] == e[5] && b[p + 6] == e[6] && b[p + 7] == e[7]);
        assert(0xc0 <= ((0xc0 | (v >> 56)) as u8) && (((((0xc0 | (v >> 56)) as u8) as u64) & 0x3f)
            << 56) | ((((v >> 48) as u8) as u64) << 48) | ((((v >> 40) as u8) as u64) << 40) | ((((v
            >> 32) as u8) as u64) << 32) | ((((v >> 24) as u8) as u64) << 24) | ((((v >> 16) as u8)
            as u64) << 16) | ((((v >> 8) as u8) as u64) << 8) | ((v as u8) as u64) == v)
            by (bit_vector)
            requires
                0x4000_0000 <= v < 0x4000_0000_0000_0000,
        ;
    }
}

/// Reads the variable-length integer at `b[pos]`.
#[inline(always)]
pub fn read(b: &[u8], pos: usize) -> (r: Option<(u64, usize)>)
    ensures
        match (r, varint(b@, pos as int)) {
            (None, None) => true,
            (Some((v, e)), Some((sv, se))) => v == sv && e == se,
            _ => false,
        },
        r matches Some((v, e)) ==> v < VARINT_LIMIT && pos < e <= b@.len(),
{
    proof {
        lemma_varint_bound(b@, pos as int);
    }
    if pos >= b.len() {
        return None;
    }
    let b0 = b[pos];
    let v0 = (b0 as u64) & 0x3f;
    if b0 < 0x40 {
        Some((v0, pos + 1))
    } else if b0 < 0x80 {
        if b.len() - pos < 2 {
            return None;
        }
        Some(((v0 << 8) | b[pos + 1] as u64, pos + 2))
    } else if b0 < 0xc0 {
        if b.len() - pos < 4 {
            return None;
        }
        Some(
            (
                (v0 << 24) | ((b[pos + 1] as u64) << 16) | ((b[pos + 2] as u64) << 8) | (b[pos
                    + 3] as u64),
                pos + 4,
            ),
        )
    } else {
        if b.len() - pos < 8 {
            return None;
        }
        Some(
            (
                (v0 << 56) | ((b[pos + 1] as u64) << 48) | ((b[pos + 2] as u64) << 40) | ((b[pos
                    + 3] as u64) << 32) | ((b[pos + 4] as u64) << 24) | ((b[pos + 5] as u64) << 16)
                    | ((b[pos + 6] as u64) << 8) | (b[pos + 7] as u64),
                pos + 8,
            ),
        )
    }
}

/// The length of the shortest encoding of `v`.
#[inline(always)]
pub fn size(v: u64) -> (r: usize)
    ensures
        r == varint_size(v),
{
    if v < 0x40 {
        1
    } else if v < 0x4000 {
        2
    } else if v < 0x4000_0000 {
        4
    } else {
        8
    }
}

/// Appends the shortest encoding of `v` (below `2^62`) to `out`.
#[inline(always)]
pub fn write(out: &mut Vec<u8>, v: u64)
    requires
        v < VARINT_LIMIT,
    ensures
        final(out)@ == old(out)@ + varint_enc(v),
{
    if v < 0x40 {
        out.push(lo8(v));
    } else if v < 0x4000 {
        out.push(lo8(0x40 | (v >> 8)));
        out.push(lo8(v));
    } else if v < 0x4000_0000 {
        out.push(lo8(0x80 | (v >> 24)));
        out.push(lo8(v >> 16));
        out.push(lo8(v >> 8));
        out.push(lo8(v));
    } else {
        out.push(lo8(0xc0 | (v >> 56)));
        out.push(lo8(v >> 48));
        out.push(lo8(v >> 40));
        out.push(lo8(v >> 32));
        out.push(lo8(v >> 24));
        out.push(lo8(v >> 16));
        out.push(lo8(v >> 8));
        out.push(lo8(v));
    }
    proof {
        assert(final(out)@ =~= old(out)@ + varint_enc(v));
    }
}

/// Writes the shortest encoding of `v` (below `2^62`) at `out[at..]` and
/// returns where it ends; the rest of `out` is unchanged.
#[inline(always)]
pub fn put(out: &mut [u8], at: usize, v: u64) -> (r: usize)
    requires
        v < VARINT_LIMIT,
        at + varint_size(v) <= old(out)@.len(),
    ensures
        r == at + varint_size(v),
        final(out)@.len() == old(out)@.len(),
        final(out)@.subrange(at as int, r as int) == varint_enc(v),
        final(out)@.subrange(0, at as int) == old(out)@.subrange(0, at as int),
        final(out)@.subrange(r as int, final(out)@.len() as int) == old(out)@.subrange(
            r as int,
            old(out)@.len() as int,
        ),
{
    let ghost o = out@;
    let len = out.len();
    let r;
    if v < 0x40 {
        set(out, at, lo8(v));
        r = at + 1;
    } else if v < 0x4000 {
        set(out, at, lo8(0x40 | (v >> 8)));
        set(out, at + 1, lo8(v));
        r = at + 2;
    } else if v < 0x4000_0000 {
        set(out, at, lo8(0x80 | (v >> 24)));
        set(out, at + 1, lo8(v >> 16));
        set(out, at + 2, lo8(v >> 8));
        set(out, at + 3, lo8(v));
        r = at + 4;
    } else {
        set(out, at, lo8(0xc0 | (v >> 56)));
        set(out, at + 1, lo8(v >> 48));
        set(out, at + 2, lo8(v >> 40));
        set(out, at + 3, lo8(v >> 32));
        set(out, at + 4, lo8(v >> 24));
        set(out, at + 5, lo8(v >> 16));
        set(out, at + 6, lo8(v >> 8));
        set(out, at + 7, lo8(v));
        r = at + 8;
    }
    proof {
        assert(out@.subrange(at as int, r as int) =~= varint_enc(v));
        assert(out@.subrange(0, at as int) =~= o.subrange(0, at as int));
        assert(out@.subrange(r as int, out@.len() as int) =~= o.subrange(r as int, o.len() as int));
    }
    r
}

/// The low 8 bits of `x`.
#[inline(always)]
pub fn lo8(x: u64) -> (r: u8)
    ensures
        r == b8(x),
{
    assert(x & 0xff <= 0xff && (x & 0xff) as u8 == x as u8) by (bit_vector);
    (x & 0xff) as u8
}

} // verus!

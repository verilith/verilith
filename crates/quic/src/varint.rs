//! Variable-length integers (§16): the verified reader and writer, and the
//! round trip.
use crate::spec::*;
use vstd::prelude::*;

verus! {

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

/// The low 8 bits of `x`.
#[inline(always)]
pub fn lo8(x: u64) -> (r: u8)
    ensures
        r == b8(x),
{
    #[verifier::truncate]
    (x as u8)
}

} // verus!

//! The decompressor, proven equal to `spec::decompress`. It writes
//! straight into the caller's buffer. The inner loop (`fast_loop`) has no
//! branch on whether an element is a literal or a copy; the copies are
//! vcore's, 16 bytes at a time where there is room.
use crate::spec::*;
use verilith_core::lz::{copy_lits, copy_lits_wild, copy_match, copy_match16, copy_match_wild, load32};
use verilith_core::prims::{copy16_in, copy16_pick, pick};
#[cfg(verus_only)]
use verilith_core::lz::{lemma_le_digit, lemma_lz_copy_len, lemma_matched, matched, placed};
#[cfg(verus_only)]
use verilith_core::prims::le_bytes;
#[cfg(verus_only)]
use vstd::arithmetic::power2::{lemma2_to64, pow2};
use verilith_core::prims::get;
use vstd::prelude::*;

verus! {

/// Why decompression failed.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Error {
    /// The input is not what the format allows.
    Corrupt,
    /// The output buffer is shorter than the uncompressed length, or the
    /// length is over the limit given.
    TooSmall,
}

/// `acc + mult * x` for the value `r` holds.
pub open spec fn lift(r: Option<(nat, int)>, acc: nat, mult: nat) -> Option<(nat, int)> {
    match r {
        Some((x, j)) => Some((acc + mult * x, j)),
        None => None,
    }
}

/// The preamble (`spec::varint`): the uncompressed length and the index
/// after it.
pub fn read_varint(src: &[u8]) -> (r: Option<(usize, usize)>)
    ensures
        match r {
            Some((n, i)) => varint(src@, 0, 0) == Some((n as nat, i as int)) && n <= 0xffff_ffff && 1 <= i <= 5 && i
                <= src@.len(),
            None => varint(src@, 0, 0).is_none(),
        },
{
    let slen = src.len();
    let mut acc: usize = 0;
    let mut mult: usize = 1;
    let mut k: usize = 0;
    proof {
        assert(lift(varint(src@, 0, 0), 0, 1) =~= varint(src@, 0, 0));
    }
    while k < 5
        invariant
            slen == src@.len(),
            k <= 5,
            k == 0 ==> mult == 1,
            k == 1 ==> mult == 128,
            k == 2 ==> mult == 16384,
            k == 3 ==> mult == 2097152,
            k == 4 ==> mult == 268435456,
            k < 5 ==> acc < mult,
            mult <= 268435456,
            k < 5 ==> varint(src@, 0, 0) == lift(varint(src@, k as int, k as nat), acc as nat, mult as nat),
            k == 5 ==> varint(src@, 0, 0).is_none(),
        decreases 5 - k,
    {
        if k >= slen {
            return None;
        }
        let b = get(src, k) as usize;
        let v = b % 128;
        if k == 4 && v >= 16 {
            return None;
        }
        assert(mult * v <= mult * 127 && (v < 16 ==> mult * v <= mult * 15)) by (nonlinear_arith)
            requires
                v < 128,
        ;
        let acc2 = acc + mult * v;
        if b < 128 {
            return Some((acc2, k + 1));
        }
        proof {
            let r = varint(src@, k + 1, (k + 1) as nat);
            if k < 4 {
                if r.is_some() {
                    let x = r.unwrap().0;
                    assert(acc + mult * (v + 128 * x) == (acc + mult * v) + (mult * 128) * x) by (nonlinear_arith);
                }
            }
        }
        if k < 4 {
            mult = mult * 128;
        }
        acc = acc2;
        k = k + 1;
    }
    None
}

/// The `nb` bytes at `i`, little-endian (`spec::le`).
#[inline(always)]
pub fn read_le(src: &[u8], i: usize, nb: usize) -> (r: usize)
    requires
        nb <= 4,
        i + nb <= src@.len(),
    ensures
        r == le(src@, i as int, nb as nat),
        r <= 0xffff_ffff,
{
    let slen = src.len();
    let mut acc: usize = 0;
    let mut k = nb;
    let ghost bound: nat = 1;
    while k > 0
        invariant
            slen == src@.len(),
            k <= nb <= 4,
            i + nb <= slen,
            acc == le(src@, i + k, (nb - k) as nat),
            nb - k == 0 ==> acc < 1,
            nb - k == 1 ==> acc < 0x100,
            nb - k == 2 ==> acc < 0x1_0000,
            nb - k == 3 ==> acc < 0x100_0000,
            nb - k == 4 ==> acc <= 0xffff_ffff,
        decreases k,
    {
        k = k - 1;
        acc = acc * 256 + get(src, i + k) as usize;
        proof {
            assert(i + k + 1 == i + (k + 1));
        }
    }
    acc
}

/// A copy's offset, for the tag at `ip` (`kind` 1 to 3, upper bits `hi`).
#[inline(always)]
fn read_off(src: &[u8], ip: usize, kind: usize, hi: usize) -> (off: usize)
    requires
        1 <= kind <= 3,
        hi < 64,
        ip + 1 + (if kind == 1 { 1int } else if kind == 2 { 2int } else { 4int }) <= src@.len(),
    ensures
        off == (if kind == 1 {
            ((hi / 8) * 256 + src@[ip + 1]) as nat
        } else if kind == 2 {
            le(src@, ip + 1, 2)
        } else {
            le(src@, ip + 1, 4)
        }),
        off <= 0xffff_ffff,
{
    let n = src.len();
    if kind == 1 {
        (hi / 8) * 256 + get(src, ip + 1) as usize
    } else if kind == 2 {
        proof {
            reveal_with_fuel(le, 3);
        }
        get(src, ip + 1) as usize + 256 * (get(src, ip + 2) as usize)
    } else {
        read_le(src, ip + 1, 4)
    }
}

/// The length of a copy's offset field, by kind.
pub open spec fn off_bytes(kind: nat) -> nat {
    if kind == 1 {
        1
    } else if kind == 2 {
        2
    } else {
        4
    }
}

/// A copy's length, as `spec::elems` has it.
pub open spec fn copy_len(kind: nat, hi: nat) -> nat {
    if kind == 1 {
        4 + hi % 8
    } else {
        1 + hi
    }
}

/// A copy's offset, as `spec::elems` has it.
pub open spec fn copy_off(s: Seq<u8>, i: int, kind: nat, hi: nat) -> nat {
    if kind == 1 {
        (hi / 8) * 256 + s[i + 1] as nat
    } else {
        le(s, i + 1, off_bytes(kind))
    }
}

/// Masks for an offset field of 1, 2 or 4 bytes, by kind.
const OFF_MASK: [u32; 4] = [0, 0xff, 0xffff, 0xffff_ffff];

/// The fields of the copy whose tag is at `ip`, when four bytes can be
/// read after the tag: one load and no branch on the kind, which is what
/// keeps the decoder fast on input whose kinds cannot be predicted.
/// Gives the offset field's size, the copy's length and its offset.
#[inline(always)]
fn copy_fields(src: &[u8], ip: usize, kind: usize, hi: usize) -> (r: (usize, usize, usize))
    requires
        1 <= kind <= 3,
        hi < 64,
        ip + 5 <= src@.len(),
    ensures
        r.0 == off_bytes(kind as nat),
        r.1 == copy_len(kind as nat, hi as nat),
        r.2 == copy_off(src@, ip as int, kind as nat, hi as nat),
        r.2 <= 0xffff_ffff,
{
    let slen = src.len();
    assert(hi & 7 == hi % 8 && (hi >> 3) << 8 == (hi / 8) * 256 && (hi >> 3) << 8 < 2048) by (bit_vector)
        requires
            hi < 64,
    ;
    assert(kind + (kind >> 1 & kind) == if kind == 1 {
        1usize
    } else if kind == 2 {
        2usize
    } else {
        4usize
    } && (kind >> 1 & kind) <= 1) by (bit_vector)
        requires
            1 <= kind <= 3,
    ;
    let w = load32(src, ip + 1);
    let t = (w & OFF_MASK[kind]) as usize;
    let one = kind == 1;
    let nb = kind + (kind >> 1 & kind);
    let len = if one {
        4 + (hi & 7)
    } else {
        1 + hi
    };
    proof {
        // So that `t + ...` below fits a 32-bit usize too.
        assert(w & 0xff <= 0xff) by (bit_vector);
        assert(OFF_MASK[1] == 0xff);
    }
    let off = t + if one {
        (hi >> 3) << 8
    } else {
        0
    };
    proof {
        let s = src@;
        let i = ip + 1;
        reveal_with_fuel(verilith_core::prims::le_bytes, 5);
        reveal_with_fuel(le, 5);
        assert(w == s[i] + 256 * s[i + 1] + 65536 * s[i + 2] + 16777216 * s[i + 3]);
        assert(le(s, i, 4) == w);
        assert(le(s, i, 2) == s[i] + 256 * s[i + 1]);
        assert(w & 0xff == w % 256 && w & 0xffff == w % 65536 && w & 0xffff_ffff == w) by (bit_vector);
    }
    (nb, len, off)
}

/// The same fields a byte at a time, for the last copies of an input.
/// `None` if the offset field runs past the end.
#[inline(always)]
fn copy_fields_slow(src: &[u8], ip: usize, kind: usize, hi: usize) -> (r: Option<(usize, usize, usize)>)
    requires
        1 <= kind <= 3,
        hi < 64,
        ip < src@.len(),
    ensures
        match r {
            Some(r) => ip + 1 + r.0 <= src@.len() && r.0 == off_bytes(kind as nat) && r.1 == copy_len(
                kind as nat,
                hi as nat,
            ) && r.2 == copy_off(src@, ip as int, kind as nat, hi as nat) && r.2 <= 0xffff_ffff,
            None => ip + 1 + off_bytes(kind as nat) > src@.len(),
        },
{
    let slen = src.len();
    let nb: usize = if kind == 1 {
        1
    } else if kind == 2 {
        2
    } else {
        4
    };
    if slen - ip - 1 < nb {
        return None;
    }
    let len = if kind == 1 {
        4 + hi % 8
    } else {
        1 + hi
    };
    Some((nb, len, read_off(src, ip, kind, hi)))
}

/// What `elems` gives is exactly `n` long, and no shorter than what it
/// started from.
pub proof fn lemma_elems_len(s: Seq<u8>, i: int, out: Seq<u8>, n: nat)
    ensures
        elems(s, i, out, n) matches Some(o) ==> o.len() == n && out.len() <= n,
    decreases s.len() - i,
{
    if 0 <= i < s.len() {
        let tag = s[i] as nat;
        let kind = tag % 4;
        let hi = tag / 4;
        if kind == 0 {
            let nb: nat = if hi < 60 {
                0
            } else {
                (hi - 59) as nat
            };
            if i + 1 + nb <= s.len() {
                let len = if hi < 60 {
                    hi + 1
                } else {
                    le(s, i + 1, nb) + 1
                };
                let j = i + 1 + nb;
                if j + len <= s.len() {
                    lemma_elems_len(s, j + len, out + s.subrange(j, j + len), n);
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
            if i + 1 + nb <= s.len() {
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
                if off != 0 && off <= out.len() {
                    lemma_lz_copy_len(out, off as int, len);
                    lemma_elems_len(s, i + 1 + nb, lz_copy(out, off as int, len), n);
                }
            }
        }
    }
}

/// By tag, what `fields` needs, so that one load gets all of it: the
/// length (bits 0 to 7), a number to add to the offset field (8 to 19),
/// and the mask for the offset field (32 to 47). For a literal whose
/// length is in the tag the number to add is 16 and the mask is 0, which
/// gives it "offset" 16; for a longer literal and for a four-byte copy
/// both are 0, which gives offset 0 and sends them to the general step.
const FIELDS: [u64; 256] = [
    0x1001, 0xff00000004, 0xffff00000001, 0x1,
    0x1002, 0xff00000005, 0xffff00000002, 0x1,
    0x1003, 0xff00000006, 0xffff00000003, 0x1,
    0x1004, 0xff00000007, 0xffff00000004, 0x1,
    0x1005, 0xff00000008, 0xffff00000005, 0x1,
    0x1006, 0xff00000009, 0xffff00000006, 0x1,
    0x1007, 0xff0000000a, 0xffff00000007, 0x1,
    0x1008, 0xff0000000b, 0xffff00000008, 0x1,
    0x1009, 0xff00010004, 0xffff00000009, 0x1,
    0x100a, 0xff00010005, 0xffff0000000a, 0x1,
    0x100b, 0xff00010006, 0xffff0000000b, 0x1,
    0x100c, 0xff00010007, 0xffff0000000c, 0x1,
    0x100d, 0xff00010008, 0xffff0000000d, 0x1,
    0x100e, 0xff00010009, 0xffff0000000e, 0x1,
    0x100f, 0xff0001000a, 0xffff0000000f, 0x1,
    0x1010, 0xff0001000b, 0xffff00000010, 0x1,
    0x1011, 0xff00020004, 0xffff00000011, 0x1,
    0x1012, 0xff00020005, 0xffff00000012, 0x1,
    0x1013, 0xff00020006, 0xffff00000013, 0x1,
    0x1014, 0xff00020007, 0xffff00000014, 0x1,
    0x1015, 0xff00020008, 0xffff00000015, 0x1,
    0x1016, 0xff00020009, 0xffff00000016, 0x1,
    0x1017, 0xff0002000a, 0xffff00000017, 0x1,
    0x1018, 0xff0002000b, 0xffff00000018, 0x1,
    0x1019, 0xff00030004, 0xffff00000019, 0x1,
    0x101a, 0xff00030005, 0xffff0000001a, 0x1,
    0x101b, 0xff00030006, 0xffff0000001b, 0x1,
    0x101c, 0xff00030007, 0xffff0000001c, 0x1,
    0x101d, 0xff00030008, 0xffff0000001d, 0x1,
    0x101e, 0xff00030009, 0xffff0000001e, 0x1,
    0x101f, 0xff0003000a, 0xffff0000001f, 0x1,
    0x1020, 0xff0003000b, 0xffff00000020, 0x1,
    0x1021, 0xff00040004, 0xffff00000021, 0x1,
    0x1022, 0xff00040005, 0xffff00000022, 0x1,
    0x1023, 0xff00040006, 0xffff00000023, 0x1,
    0x1024, 0xff00040007, 0xffff00000024, 0x1,
    0x1025, 0xff00040008, 0xffff00000025, 0x1,
    0x1026, 0xff00040009, 0xffff00000026, 0x1,
    0x1027, 0xff0004000a, 0xffff00000027, 0x1,
    0x1028, 0xff0004000b, 0xffff00000028, 0x1,
    0x1029, 0xff00050004, 0xffff00000029, 0x1,
    0x102a, 0xff00050005, 0xffff0000002a, 0x1,
    0x102b, 0xff00050006, 0xffff0000002b, 0x1,
    0x102c, 0xff00050007, 0xffff0000002c, 0x1,
    0x102d, 0xff00050008, 0xffff0000002d, 0x1,
    0x102e, 0xff00050009, 0xffff0000002e, 0x1,
    0x102f, 0xff0005000a, 0xffff0000002f, 0x1,
    0x1030, 0xff0005000b, 0xffff00000030, 0x1,
    0x1031, 0xff00060004, 0xffff00000031, 0x1,
    0x1032, 0xff00060005, 0xffff00000032, 0x1,
    0x1033, 0xff00060006, 0xffff00000033, 0x1,
    0x1034, 0xff00060007, 0xffff00000034, 0x1,
    0x1035, 0xff00060008, 0xffff00000035, 0x1,
    0x1036, 0xff00060009, 0xffff00000036, 0x1,
    0x1037, 0xff0006000a, 0xffff00000037, 0x1,
    0x1038, 0xff0006000b, 0xffff00000038, 0x1,
    0x1039, 0xff00070004, 0xffff00000039, 0x1,
    0x103a, 0xff00070005, 0xffff0000003a, 0x1,
    0x103b, 0xff00070006, 0xffff0000003b, 0x1,
    0x103c, 0xff00070007, 0xffff0000003c, 0x1,
    0x1, 0xff00070008, 0xffff0000003d, 0x1,
    0x1, 0xff00070009, 0xffff0000003e, 0x1,
    0x1, 0xff0007000a, 0xffff0000003f, 0x1,
    0x1, 0xff0007000b, 0xffff00000040, 0x1,
];

/// What an entry of `FIELDS` has to be for tag `t`.
pub open spec fn entry_ok(t: int, e: u64) -> bool {
    let k = t % 4;
    let hi = t / 4;
    let len = e % 256;
    let base = (e / 256) % 4096;
    let om = e / 0x1_0000_0000;
    if k == 0 {
        if hi < 60 {
            len == hi + 1 && base == 16 && om == 0
        } else {
            len == 1 && base == 0 && om == 0
        }
    } else if k == 1 {
        len == 4 + hi % 8 && base == (hi / 8) * 256 && om == 0xff
    } else if k == 2 {
        len == hi + 1 && base == 0 && om == 0xffff
    } else {
        len == 1 && base == 0 && om == 0
    }
}

proof fn lemma_fields_0()
    ensures
        forall|t: int| 0 <= t < 32 ==> entry_ok(t, #[trigger] FIELDS@[t]),
{
    assert(entry_ok(0, 0x1001)) by (compute_only);
    assert(entry_ok(1, 0xff00000004)) by (compute_only);
    assert(entry_ok(2, 0xffff00000001)) by (compute_only);
    assert(entry_ok(3, 0x1)) by (compute_only);
    assert(entry_ok(4, 0x1002)) by (compute_only);
    assert(entry_ok(5, 0xff00000005)) by (compute_only);
    assert(entry_ok(6, 0xffff00000002)) by (compute_only);
    assert(entry_ok(7, 0x1)) by (compute_only);
    assert(entry_ok(8, 0x1003)) by (compute_only);
    assert(entry_ok(9, 0xff00000006)) by (compute_only);
    assert(entry_ok(10, 0xffff00000003)) by (compute_only);
    assert(entry_ok(11, 0x1)) by (compute_only);
    assert(entry_ok(12, 0x1004)) by (compute_only);
    assert(entry_ok(13, 0xff00000007)) by (compute_only);
    assert(entry_ok(14, 0xffff00000004)) by (compute_only);
    assert(entry_ok(15, 0x1)) by (compute_only);
    assert(entry_ok(16, 0x1005)) by (compute_only);
    assert(entry_ok(17, 0xff00000008)) by (compute_only);
    assert(entry_ok(18, 0xffff00000005)) by (compute_only);
    assert(entry_ok(19, 0x1)) by (compute_only);
    assert(entry_ok(20, 0x1006)) by (compute_only);
    assert(entry_ok(21, 0xff00000009)) by (compute_only);
    assert(entry_ok(22, 0xffff00000006)) by (compute_only);
    assert(entry_ok(23, 0x1)) by (compute_only);
    assert(entry_ok(24, 0x1007)) by (compute_only);
    assert(entry_ok(25, 0xff0000000a)) by (compute_only);
    assert(entry_ok(26, 0xffff00000007)) by (compute_only);
    assert(entry_ok(27, 0x1)) by (compute_only);
    assert(entry_ok(28, 0x1008)) by (compute_only);
    assert(entry_ok(29, 0xff0000000b)) by (compute_only);
    assert(entry_ok(30, 0xffff00000008)) by (compute_only);
    assert(entry_ok(31, 0x1)) by (compute_only);
}

proof fn lemma_fields_1()
    ensures
        forall|t: int| 32 <= t < 64 ==> entry_ok(t, #[trigger] FIELDS@[t]),
{
    assert(entry_ok(32, 0x1009)) by (compute_only);
    assert(entry_ok(33, 0xff00010004)) by (compute_only);
    assert(entry_ok(34, 0xffff00000009)) by (compute_only);
    assert(entry_ok(35, 0x1)) by (compute_only);
    assert(entry_ok(36, 0x100a)) by (compute_only);
    assert(entry_ok(37, 0xff00010005)) by (compute_only);
    assert(entry_ok(38, 0xffff0000000a)) by (compute_only);
    assert(entry_ok(39, 0x1)) by (compute_only);
    assert(entry_ok(40, 0x100b)) by (compute_only);
    assert(entry_ok(41, 0xff00010006)) by (compute_only);
    assert(entry_ok(42, 0xffff0000000b)) by (compute_only);
    assert(entry_ok(43, 0x1)) by (compute_only);
    assert(entry_ok(44, 0x100c)) by (compute_only);
    assert(entry_ok(45, 0xff00010007)) by (compute_only);
    assert(entry_ok(46, 0xffff0000000c)) by (compute_only);
    assert(entry_ok(47, 0x1)) by (compute_only);
    assert(entry_ok(48, 0x100d)) by (compute_only);
    assert(entry_ok(49, 0xff00010008)) by (compute_only);
    assert(entry_ok(50, 0xffff0000000d)) by (compute_only);
    assert(entry_ok(51, 0x1)) by (compute_only);
    assert(entry_ok(52, 0x100e)) by (compute_only);
    assert(entry_ok(53, 0xff00010009)) by (compute_only);
    assert(entry_ok(54, 0xffff0000000e)) by (compute_only);
    assert(entry_ok(55, 0x1)) by (compute_only);
    assert(entry_ok(56, 0x100f)) by (compute_only);
    assert(entry_ok(57, 0xff0001000a)) by (compute_only);
    assert(entry_ok(58, 0xffff0000000f)) by (compute_only);
    assert(entry_ok(59, 0x1)) by (compute_only);
    assert(entry_ok(60, 0x1010)) by (compute_only);
    assert(entry_ok(61, 0xff0001000b)) by (compute_only);
    assert(entry_ok(62, 0xffff00000010)) by (compute_only);
    assert(entry_ok(63, 0x1)) by (compute_only);
}

proof fn lemma_fields_2()
    ensures
        forall|t: int| 64 <= t < 96 ==> entry_ok(t, #[trigger] FIELDS@[t]),
{
    assert(entry_ok(64, 0x1011)) by (compute_only);
    assert(entry_ok(65, 0xff00020004)) by (compute_only);
    assert(entry_ok(66, 0xffff00000011)) by (compute_only);
    assert(entry_ok(67, 0x1)) by (compute_only);
    assert(entry_ok(68, 0x1012)) by (compute_only);
    assert(entry_ok(69, 0xff00020005)) by (compute_only);
    assert(entry_ok(70, 0xffff00000012)) by (compute_only);
    assert(entry_ok(71, 0x1)) by (compute_only);
    assert(entry_ok(72, 0x1013)) by (compute_only);
    assert(entry_ok(73, 0xff00020006)) by (compute_only);
    assert(entry_ok(74, 0xffff00000013)) by (compute_only);
    assert(entry_ok(75, 0x1)) by (compute_only);
    assert(entry_ok(76, 0x1014)) by (compute_only);
    assert(entry_ok(77, 0xff00020007)) by (compute_only);
    assert(entry_ok(78, 0xffff00000014)) by (compute_only);
    assert(entry_ok(79, 0x1)) by (compute_only);
    assert(entry_ok(80, 0x1015)) by (compute_only);
    assert(entry_ok(81, 0xff00020008)) by (compute_only);
    assert(entry_ok(82, 0xffff00000015)) by (compute_only);
    assert(entry_ok(83, 0x1)) by (compute_only);
    assert(entry_ok(84, 0x1016)) by (compute_only);
    assert(entry_ok(85, 0xff00020009)) by (compute_only);
    assert(entry_ok(86, 0xffff00000016)) by (compute_only);
    assert(entry_ok(87, 0x1)) by (compute_only);
    assert(entry_ok(88, 0x1017)) by (compute_only);
    assert(entry_ok(89, 0xff0002000a)) by (compute_only);
    assert(entry_ok(90, 0xffff00000017)) by (compute_only);
    assert(entry_ok(91, 0x1)) by (compute_only);
    assert(entry_ok(92, 0x1018)) by (compute_only);
    assert(entry_ok(93, 0xff0002000b)) by (compute_only);
    assert(entry_ok(94, 0xffff00000018)) by (compute_only);
    assert(entry_ok(95, 0x1)) by (compute_only);
}

proof fn lemma_fields_3()
    ensures
        forall|t: int| 96 <= t < 128 ==> entry_ok(t, #[trigger] FIELDS@[t]),
{
    assert(entry_ok(96, 0x1019)) by (compute_only);
    assert(entry_ok(97, 0xff00030004)) by (compute_only);
    assert(entry_ok(98, 0xffff00000019)) by (compute_only);
    assert(entry_ok(99, 0x1)) by (compute_only);
    assert(entry_ok(100, 0x101a)) by (compute_only);
    assert(entry_ok(101, 0xff00030005)) by (compute_only);
    assert(entry_ok(102, 0xffff0000001a)) by (compute_only);
    assert(entry_ok(103, 0x1)) by (compute_only);
    assert(entry_ok(104, 0x101b)) by (compute_only);
    assert(entry_ok(105, 0xff00030006)) by (compute_only);
    assert(entry_ok(106, 0xffff0000001b)) by (compute_only);
    assert(entry_ok(107, 0x1)) by (compute_only);
    assert(entry_ok(108, 0x101c)) by (compute_only);
    assert(entry_ok(109, 0xff00030007)) by (compute_only);
    assert(entry_ok(110, 0xffff0000001c)) by (compute_only);
    assert(entry_ok(111, 0x1)) by (compute_only);
    assert(entry_ok(112, 0x101d)) by (compute_only);
    assert(entry_ok(113, 0xff00030008)) by (compute_only);
    assert(entry_ok(114, 0xffff0000001d)) by (compute_only);
    assert(entry_ok(115, 0x1)) by (compute_only);
    assert(entry_ok(116, 0x101e)) by (compute_only);
    assert(entry_ok(117, 0xff00030009)) by (compute_only);
    assert(entry_ok(118, 0xffff0000001e)) by (compute_only);
    assert(entry_ok(119, 0x1)) by (compute_only);
    assert(entry_ok(120, 0x101f)) by (compute_only);
    assert(entry_ok(121, 0xff0003000a)) by (compute_only);
    assert(entry_ok(122, 0xffff0000001f)) by (compute_only);
    assert(entry_ok(123, 0x1)) by (compute_only);
    assert(entry_ok(124, 0x1020)) by (compute_only);
    assert(entry_ok(125, 0xff0003000b)) by (compute_only);
    assert(entry_ok(126, 0xffff00000020)) by (compute_only);
    assert(entry_ok(127, 0x1)) by (compute_only);
}

proof fn lemma_fields_4()
    ensures
        forall|t: int| 128 <= t < 160 ==> entry_ok(t, #[trigger] FIELDS@[t]),
{
    assert(entry_ok(128, 0x1021)) by (compute_only);
    assert(entry_ok(129, 0xff00040004)) by (compute_only);
    assert(entry_ok(130, 0xffff00000021)) by (compute_only);
    assert(entry_ok(131, 0x1)) by (compute_only);
    assert(entry_ok(132, 0x1022)) by (compute_only);
    assert(entry_ok(133, 0xff00040005)) by (compute_only);
    assert(entry_ok(134, 0xffff00000022)) by (compute_only);
    assert(entry_ok(135, 0x1)) by (compute_only);
    assert(entry_ok(136, 0x1023)) by (compute_only);
    assert(entry_ok(137, 0xff00040006)) by (compute_only);
    assert(entry_ok(138, 0xffff00000023)) by (compute_only);
    assert(entry_ok(139, 0x1)) by (compute_only);
    assert(entry_ok(140, 0x1024)) by (compute_only);
    assert(entry_ok(141, 0xff00040007)) by (compute_only);
    assert(entry_ok(142, 0xffff00000024)) by (compute_only);
    assert(entry_ok(143, 0x1)) by (compute_only);
    assert(entry_ok(144, 0x1025)) by (compute_only);
    assert(entry_ok(145, 0xff00040008)) by (compute_only);
    assert(entry_ok(146, 0xffff00000025)) by (compute_only);
    assert(entry_ok(147, 0x1)) by (compute_only);
    assert(entry_ok(148, 0x1026)) by (compute_only);
    assert(entry_ok(149, 0xff00040009)) by (compute_only);
    assert(entry_ok(150, 0xffff00000026)) by (compute_only);
    assert(entry_ok(151, 0x1)) by (compute_only);
    assert(entry_ok(152, 0x1027)) by (compute_only);
    assert(entry_ok(153, 0xff0004000a)) by (compute_only);
    assert(entry_ok(154, 0xffff00000027)) by (compute_only);
    assert(entry_ok(155, 0x1)) by (compute_only);
    assert(entry_ok(156, 0x1028)) by (compute_only);
    assert(entry_ok(157, 0xff0004000b)) by (compute_only);
    assert(entry_ok(158, 0xffff00000028)) by (compute_only);
    assert(entry_ok(159, 0x1)) by (compute_only);
}

proof fn lemma_fields_5()
    ensures
        forall|t: int| 160 <= t < 192 ==> entry_ok(t, #[trigger] FIELDS@[t]),
{
    assert(entry_ok(160, 0x1029)) by (compute_only);
    assert(entry_ok(161, 0xff00050004)) by (compute_only);
    assert(entry_ok(162, 0xffff00000029)) by (compute_only);
    assert(entry_ok(163, 0x1)) by (compute_only);
    assert(entry_ok(164, 0x102a)) by (compute_only);
    assert(entry_ok(165, 0xff00050005)) by (compute_only);
    assert(entry_ok(166, 0xffff0000002a)) by (compute_only);
    assert(entry_ok(167, 0x1)) by (compute_only);
    assert(entry_ok(168, 0x102b)) by (compute_only);
    assert(entry_ok(169, 0xff00050006)) by (compute_only);
    assert(entry_ok(170, 0xffff0000002b)) by (compute_only);
    assert(entry_ok(171, 0x1)) by (compute_only);
    assert(entry_ok(172, 0x102c)) by (compute_only);
    assert(entry_ok(173, 0xff00050007)) by (compute_only);
    assert(entry_ok(174, 0xffff0000002c)) by (compute_only);
    assert(entry_ok(175, 0x1)) by (compute_only);
    assert(entry_ok(176, 0x102d)) by (compute_only);
    assert(entry_ok(177, 0xff00050008)) by (compute_only);
    assert(entry_ok(178, 0xffff0000002d)) by (compute_only);
    assert(entry_ok(179, 0x1)) by (compute_only);
    assert(entry_ok(180, 0x102e)) by (compute_only);
    assert(entry_ok(181, 0xff00050009)) by (compute_only);
    assert(entry_ok(182, 0xffff0000002e)) by (compute_only);
    assert(entry_ok(183, 0x1)) by (compute_only);
    assert(entry_ok(184, 0x102f)) by (compute_only);
    assert(entry_ok(185, 0xff0005000a)) by (compute_only);
    assert(entry_ok(186, 0xffff0000002f)) by (compute_only);
    assert(entry_ok(187, 0x1)) by (compute_only);
    assert(entry_ok(188, 0x1030)) by (compute_only);
    assert(entry_ok(189, 0xff0005000b)) by (compute_only);
    assert(entry_ok(190, 0xffff00000030)) by (compute_only);
    assert(entry_ok(191, 0x1)) by (compute_only);
}

proof fn lemma_fields_6()
    ensures
        forall|t: int| 192 <= t < 224 ==> entry_ok(t, #[trigger] FIELDS@[t]),
{
    assert(entry_ok(192, 0x1031)) by (compute_only);
    assert(entry_ok(193, 0xff00060004)) by (compute_only);
    assert(entry_ok(194, 0xffff00000031)) by (compute_only);
    assert(entry_ok(195, 0x1)) by (compute_only);
    assert(entry_ok(196, 0x1032)) by (compute_only);
    assert(entry_ok(197, 0xff00060005)) by (compute_only);
    assert(entry_ok(198, 0xffff00000032)) by (compute_only);
    assert(entry_ok(199, 0x1)) by (compute_only);
    assert(entry_ok(200, 0x1033)) by (compute_only);
    assert(entry_ok(201, 0xff00060006)) by (compute_only);
    assert(entry_ok(202, 0xffff00000033)) by (compute_only);
    assert(entry_ok(203, 0x1)) by (compute_only);
    assert(entry_ok(204, 0x1034)) by (compute_only);
    assert(entry_ok(205, 0xff00060007)) by (compute_only);
    assert(entry_ok(206, 0xffff00000034)) by (compute_only);
    assert(entry_ok(207, 0x1)) by (compute_only);
    assert(entry_ok(208, 0x1035)) by (compute_only);
    assert(entry_ok(209, 0xff00060008)) by (compute_only);
    assert(entry_ok(210, 0xffff00000035)) by (compute_only);
    assert(entry_ok(211, 0x1)) by (compute_only);
    assert(entry_ok(212, 0x1036)) by (compute_only);
    assert(entry_ok(213, 0xff00060009)) by (compute_only);
    assert(entry_ok(214, 0xffff00000036)) by (compute_only);
    assert(entry_ok(215, 0x1)) by (compute_only);
    assert(entry_ok(216, 0x1037)) by (compute_only);
    assert(entry_ok(217, 0xff0006000a)) by (compute_only);
    assert(entry_ok(218, 0xffff00000037)) by (compute_only);
    assert(entry_ok(219, 0x1)) by (compute_only);
    assert(entry_ok(220, 0x1038)) by (compute_only);
    assert(entry_ok(221, 0xff0006000b)) by (compute_only);
    assert(entry_ok(222, 0xffff00000038)) by (compute_only);
    assert(entry_ok(223, 0x1)) by (compute_only);
}

proof fn lemma_fields_7()
    ensures
        forall|t: int| 224 <= t < 256 ==> entry_ok(t, #[trigger] FIELDS@[t]),
{
    assert(entry_ok(224, 0x1039)) by (compute_only);
    assert(entry_ok(225, 0xff00070004)) by (compute_only);
    assert(entry_ok(226, 0xffff00000039)) by (compute_only);
    assert(entry_ok(227, 0x1)) by (compute_only);
    assert(entry_ok(228, 0x103a)) by (compute_only);
    assert(entry_ok(229, 0xff00070005)) by (compute_only);
    assert(entry_ok(230, 0xffff0000003a)) by (compute_only);
    assert(entry_ok(231, 0x1)) by (compute_only);
    assert(entry_ok(232, 0x103b)) by (compute_only);
    assert(entry_ok(233, 0xff00070006)) by (compute_only);
    assert(entry_ok(234, 0xffff0000003b)) by (compute_only);
    assert(entry_ok(235, 0x1)) by (compute_only);
    assert(entry_ok(236, 0x103c)) by (compute_only);
    assert(entry_ok(237, 0xff00070007)) by (compute_only);
    assert(entry_ok(238, 0xffff0000003c)) by (compute_only);
    assert(entry_ok(239, 0x1)) by (compute_only);
    assert(entry_ok(240, 0x1)) by (compute_only);
    assert(entry_ok(241, 0xff00070008)) by (compute_only);
    assert(entry_ok(242, 0xffff0000003d)) by (compute_only);
    assert(entry_ok(243, 0x1)) by (compute_only);
    assert(entry_ok(244, 0x1)) by (compute_only);
    assert(entry_ok(245, 0xff00070009)) by (compute_only);
    assert(entry_ok(246, 0xffff0000003e)) by (compute_only);
    assert(entry_ok(247, 0x1)) by (compute_only);
    assert(entry_ok(248, 0x1)) by (compute_only);
    assert(entry_ok(249, 0xff0007000a)) by (compute_only);
    assert(entry_ok(250, 0xffff0000003f)) by (compute_only);
    assert(entry_ok(251, 0x1)) by (compute_only);
    assert(entry_ok(252, 0x1)) by (compute_only);
    assert(entry_ok(253, 0xff0007000b)) by (compute_only);
    assert(entry_ok(254, 0xffff00000040)) by (compute_only);
    assert(entry_ok(255, 0x1)) by (compute_only);
}

/// Every entry of `FIELDS` is right.
proof fn lemma_fields(t: int)
    requires
        0 <= t < 256,
    ensures
        entry_ok(t, FIELDS@[t]),
{
    lemma_fields_0();
    lemma_fields_1();
    lemma_fields_2();
    lemma_fields_3();
    lemma_fields_4();
    lemma_fields_5();
    lemma_fields_6();
    lemma_fields_7();
}

/// The offset field of a one- or two-byte copy, from the four bytes
/// loaded after its tag.
proof fn lemma_off_field(s: Seq<u8>, i: int, w: u64)
    requires
        0 <= i,
        i + 4 <= s.len(),
        w == le_bytes(s, i, 4),
    ensures
        w & 0xff == s[i],
        w & 0xffff == le(s, i, 2),
        w & 0 == 0,
        w <= 0xffff_ffff,
{
    reveal_with_fuel(verilith_core::prims::le_bytes, 5);
    reveal_with_fuel(le, 5);
    assert(w == s[i] + 256 * s[i + 1] + 65536 * s[i + 2] + 16777216 * s[i + 3]);
    assert(le(s, i, 2) == s[i] + 256 * s[i + 1]);
    assert(w & 0xff == w % 256 && w & 0xffff == w % 65536 && w & 0 == 0) by (bit_vector);
}

/// The fields of the element with tag `tag` at `ip`, literal or copy,
/// with no branch: one table lookup by tag and the four bytes after the
/// tag. Gives the length, the offset, and those four bytes. The offset
/// is 16 for a literal whose length is in the tag, and 0 for a longer
/// literal and for a four-byte copy, whose lengths are then not given.
#[inline(always)]
fn fields(src: &[u8], ip: usize, tag: usize) -> (r: (usize, usize, u64))
    requires
        ip + 5 <= src@.len(),
        tag == src@[ip as int],
    ensures
        ({
            let kind = (src@[ip as int] % 4) as nat;
            let hi = (src@[ip as int] / 4) as nat;
            if kind == 0 {
                if hi < 60 {
                    r.0 == hi + 1 && r.1 == 16
                } else {
                    r.1 == 0
                }
            } else if kind == 3 {
                r.1 == 0
            } else {
                r.0 == copy_len(kind, hi) && r.1 == copy_off(src@, ip as int, kind, hi)
            }
        }),
        1 <= r.0 <= 64,
        r.1 <= 0x1_0000_1000,
        r.2 == le_bytes(src@, ip + 1, 4),
{
    let slen = src.len();
    let e = FIELDS[tag];
    let w = load32(src, ip + 1) as u64;
    let om = e >> 32;
    let base = (e >> 8) & 0xfff;
    let len = (e & 0xff) as usize;
    proof {
        lemma_fields(tag as int);
        lemma_off_field(src@, ip + 1, w);
        assert(e & 0xff == e % 256 && (e >> 8) & 0xfff == (e / 256) % 4096 && e >> 32 == e / 0x1_0000_0000)
            by (bit_vector);
        assert(w & om <= w) by (bit_vector);
        assert(base < 4096);
    }
    let off = ((w & om) + base) as usize;
    (len, off, w)
}

/// Room the inner loop wants on both sides: the longest element it takes
/// (64 bytes) and the 32 that the copies may run over, with some to spare.
const ROOM: usize = 104;

/// The decoder's inner loop: elements whose kind cannot be predicted,
/// decoded without a branch on the kind. It takes literals of up to 60
/// bytes and copies from at least 16 back while both sides have `ROOM`,
/// and stops at anything else, which the caller's general step handles.
///
/// Each turn does both a match copy and a literal copy, and aims the one
/// that is not wanted where it does no harm: for a literal the match copy
/// writes first, from the start of the output (reading what was just
/// written would make each element wait for the one before), and the
/// literal covers it; for a copy the literal copy is
/// of no bytes and its overrun lands after the match.
#[inline(never)]
#[verifier::rlimit(300)]
fn fast_loop(src: &[u8], out: &mut [u8], n: usize, ip0: usize, op0: usize) -> (r: (usize, usize))
    requires
        ip0 <= src@.len(),
        op0 <= n <= old(out)@.len(),
        n <= 0xffff_ffff,
    ensures
        final(out)@.len() == old(out)@.len(),
        ip0 <= r.0 <= src@.len(),
        r.1 <= n,
        elems(src@, r.0 as int, final(out)@.subrange(0, r.1 as int), n as nat) == elems(
            src@,
            ip0 as int,
            old(out)@.subrange(0, op0 as int),
            n as nat,
        ),
{
    let slen = src.len();
    let cap = out.len();
    let mut ip = ip0;
    let mut op = op0;
    let ghost goal = elems(src@, ip0 as int, out@.subrange(0, op0 as int), n as nat);
    if slen - ip < ROOM || n - op < ROOM || op < 16 {
        return (ip, op);
    }
    let ip_max = slen - ROOM;
    let op_max = n - ROOM;
    // The tag at `ip`. The next one is read before it is known where it
    // is: both places it can be are read, and one is kept.
    let mut tag = get(src, ip) as usize;
    loop
        invariant_except_break
            slen - ip >= ROOM,
            n - op >= ROOM,
            op >= 16,
            tag == src@[ip as int],
        invariant
            slen == src@.len(),
            cap == out@.len(),
            cap == old(out)@.len(),
            ip_max == slen - ROOM,
            op_max == n - ROOM,
            ip0 <= ip <= slen,
            op <= n <= cap,
            n <= 0xffff_ffff,
            elems(src@, ip as int, out@.subrange(0, op as int), n as nat) == goal,
        decreases slen - ip,
    {
        let ghost cur = out@.subrange(0, op as int);
        let ghost kind = src@[ip as int] % 4;
        let k = tag & 3;
        let hi = tag >> 2;
        assert(k == tag % 4 && hi == tag / 4 && hi < 64 && k < 4) by (bit_vector)
            requires
                tag < 256,
                k == tag & 3,
                hi == tag >> 2,
        ;
        let (len, off, w) = fields(src, ip, tag);
        // Where the next tag is: after the literal's bytes or after the
        // copy's offset. Both are read before the choice is known, and
        // the choice is a conditional move.
        let lit = k == 0;
        // The tag after a copy is in the four bytes already loaded for
        // its offset; the tag after a literal has to be read.
        let tag_c = ((w >> (8 * k as u64)) & 0xff) as usize;
        let tag_l = get(src, ip + 2 + hi) as usize;
        proof {
            let x = w;
            assert((x >> 8) & 0xff == (x / 0x100) % 256 && (x >> 16) & 0xff == (x / 0x1_0000) % 256 && (x >> 24) & 0xff
                == (x / 0x100_0000) % 256) by (bit_vector);
            lemma2_to64();
            if k != 0 {
                lemma_le_digit(src@, ip + 1, 4, k as nat);
                assert(tag_c == src@[ip + 1 + k]);
            }
        }
        let ip2 = pick(lit, ip + 2 + hi, ip + 1 + k);
        let tag2 = pick(lit, tag_l, tag_c);
        if (off == 0) | (off > op) {
            break;
        }
        let ghost mid = out@;
        if (off < 16) & (len > off) {
            // A copy from close behind that runs into itself: rare, and it
            // needs the copy that repeats a pattern. (One from close
            // behind that ends before where it started is like any
            // other: only its first `len` bytes have to be right.)
            copy_match(out, op, off, len);
            proof {
                lemma_matched(mid, out@, 0, op as int, off as int, len as int);
            }
            op = op + len;
            ip = ip2;
            tag = tag2;
            if ip > ip_max || op > op_max {
                break;
            }
            continue;
        }
        // One copy of 32 bytes, from the input for a literal and from
        // `off` back for a copy, with the source chosen without a branch.
        copy16_pick(out, op, src, ip + 1, op - off, lit);
        let ghost o1 = out@;
        copy16_pick(out, op + 16, src, ip + 17, op - off + 16, lit);
        let ghost o2 = out@;
        proof {
            if !lit && off >= 16 {
                assert forall|j: int| op <= j < op + 32 implies #[trigger] o2[j] == o2[j - off] by {
                    if j < op + 16 {
                        assert(o1[j] == mid[j - off]);
                    } else {
                        assert(o2[j] == o1[j - off]);
                    }
                }
                assert(matched(mid, o2, op as int, off as int, 32));
            }
        }
        // Whether there are more than 32 bytes is read off the tag itself
        // rather than the length from the table, so that when this branch
        // is mispredicted it is found out a table lookup sooner.
        let long = (tag & 0x81) == 0x80;
        proof {
            assert(tag < 256);
            assert(long <==> ((tag % 4 == 0 || tag % 4 == 2) && tag / 4 >= 32)) by (bit_vector)
                requires
                    tag < 256,
                    long == ((tag & 0x81) == 0x80),
            ;
            assert(long <==> len > 32);
        }
        if long {
            // 32 more, again with no branch on the kind of element; a copy
            // never has more than 64 bytes, so only a long literal goes on.
            copy16_pick(out, op + 32, src, ip + 33, op - off + 32, lit);
            let ghost o3 = out@;
            copy16_pick(out, op + 48, src, ip + 49, op - off + 48, lit);
            let ghost o4 = out@;
            proof {
                if !lit {
                    assert(off >= 16);
                    assert forall|j: int| op <= j < op + 64 implies #[trigger] o4[j] == o4[j - off] by {
                        if j < op + 32 {
                            assert(o4[j] == o2[j]);
                            assert(o4[j - off] == o2[j - off]);
                        } else if j < op + 48 {
                            assert(o3[j] == o2[j - off]);
                        } else {
                            assert(o4[j] == o3[j - off]);
                        }
                    }
                    assert(matched(mid, o4, op as int, off as int, 64));
                }
            }
            if len > 64 {
                if lit {
                    copy_lits_wild(out, op + 64, src, ip + 65, len - 64);
                } else {
                    copy_match_wild(out, op + 64, off, len - 64);
                }
            }
            proof {
                if lit {
                    assert(out@.subrange(0, op + len) =~= cur + src@.subrange(ip + 1, ip + 1 + len));
                } else {
                    assert(matched(mid, out@, op as int, off as int, len as int)) by {
                        assert forall|j: int| op <= j < op + len implies #[trigger] out@[j] == out@[j - off] by {
                            if j < op + 64 {
                                assert(out@[j] == o4[j]);
                                assert(out@[j - off] == o4[j - off]);
                            }
                        }
                    }
                }
            }
        }
        proof {
            if lit {
                assert(out@.subrange(0, op + len) =~= cur + src@.subrange(ip + 1, ip + 1 + len));
            } else {
                if len <= 32 {
                    assert(matched(mid, out@, op as int, off as int, len as int)) by {
                        assert forall|j: int| op <= j < op + len implies #[trigger] out@[j] == out@[j - off] by {
                            if off < 16 {
                                assert(o2[j] == o1[j]);
                                assert(o1[j] == mid[j - off]);
                                assert(o2[j - off] == mid[j - off]);
                            }
                        }
                    }
                }
                lemma_matched(mid, out@, 0, op as int, off as int, len as int);
            }
        }
        op = op + len;
        ip = ip2;
        tag = tag2;
        if ip > ip_max || op > op_max {
            break;
        }
    }
    (ip, op)
}

/// Decompresses `src` into `out`.
///
/// - `Ok(n)`: `src` is valid and decompresses to `out[..n]`.
/// - `Err(Corrupt)`: `src` is not valid.
/// - `Err(TooSmall)`: `src` is not valid, or what it decompresses to is
///   longer than `out`.
///
/// Bytes of `out` after the result may be changed.
#[verifier::rlimit(60)]
pub fn decompress_into(src: &[u8], out: &mut [u8]) -> (r: Result<usize, Error>)
    ensures
        final(out)@.len() == old(out)@.len(),
        match r {
            Ok(n) => n <= final(out)@.len() && decompress(src@) == Some(final(out)@.subrange(0, n as int)),
            Err(Error::Corrupt) => decompress(src@).is_none(),
            Err(Error::TooSmall) => decompress(src@) matches Some(o) ==> o.len() > old(out)@.len(),
        },
{
    let slen = src.len();
    let cap = out.len();
    let (n, i0) = match read_varint(src) {
        None => {
            return Err(Error::Corrupt);
        },
        Some(x) => x,
    };
    let ghost goal = elems(src@, i0 as int, Seq::empty(), n as nat);
    if n > cap {
        proof {
            lemma_elems_len(src@, i0 as int, Seq::empty(), n as nat);
        }
        return Err(Error::TooSmall);
    }
    let mut ip = i0;
    let mut op: usize = 0;
    proof {
        assert(out@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while ip < slen
        invariant
            slen == src@.len(),
            cap == out@.len(),
            cap == old(out)@.len(),
            ip <= slen,
            op <= n <= cap,
            n <= 0xffff_ffff,
            goal == decompress(src@),
            elems(src@, ip as int, out@.subrange(0, op as int), n as nat) == goal,
        ensures
            ip == slen,
        decreases slen - ip,
    {
        if slen - ip >= ROOM && n - op >= ROOM && op >= 16 {
            let (i2, o2) = fast_loop(src, out, n, ip, op);
            ip = i2;
            op = o2;
            if ip >= slen {
                break;
            }
        }
        let ghost cur = out@.subrange(0, op as int);
        let tag = get(src, ip) as usize;
        let kind = tag % 4;
        let hi = tag / 4;
        if kind == 0 {
            let nb: usize = if hi < 60 {
                0
            } else {
                hi - 59
            };
            if slen - ip - 1 < nb {
                return Err(Error::Corrupt);
            }
            let len = if hi < 60 {
                hi + 1
            } else {
                let v = read_le(src, ip + 1, nb);
                // A 32-bit usize cannot hold 2^32, and no literal that
                // long fits in the input (checked again just below).
                #[cfg(target_pointer_width = "32")]
                if v >= slen {
                    return Err(Error::Corrupt);
                }
                v + 1
            };
            let j = ip + 1 + nb;
            if len > slen - j {
                return Err(Error::Corrupt);
            }
            if len > n - op {
                proof {
                    lemma_elems_len(src@, j + len, cur + src@.subrange(j as int, j + len), n as nat);
                }
                return Err(Error::Corrupt);
            }
            if len <= 16 && slen - j >= 16 && cap - op >= 16 {
                // The common case: copy 16 bytes whatever the length.
                copy16_in(out, op, src, j);
            } else {
                copy_lits(out, op, src, j, len);
            }
            proof {
                assert(out@.subrange(0, op + len) =~= cur + src@.subrange(j as int, j + len));
            }
            op = op + len;
            ip = j + len;
        } else {
            let (nb, len, off) = if slen - ip >= 5 {
                copy_fields(src, ip, kind, hi)
            } else {
                match copy_fields_slow(src, ip, kind, hi) {
                    Some(f) => f,
                    None => {
                        return Err(Error::Corrupt);
                    },
                }
            };
            if off == 0 || off > op {
                return Err(Error::Corrupt);
            }
            if len > n - op {
                proof {
                    lemma_lz_copy_len(cur, off as int, len as nat);
                    lemma_elems_len(src@, ip + 1 + nb, lz_copy(cur, off as int, len as nat), n as nat);
                }
                return Err(Error::Corrupt);
            }
            let ghost mid = out@;
            if off >= 8 && len <= 16 && cap - op >= 16 {
                // The common case: two 8-byte copies whatever the length.
                copy_match16(out, op, off, len);
            } else {
                copy_match(out, op, off, len);
            }
            proof {
                lemma_matched(mid, out@, 0, op as int, off as int, len as int);
            }
            op = op + len;
            ip = ip + 1 + nb;
        }
    }
    if op == n {
        Ok(n)
    } else {
        Err(Error::Corrupt)
    }
}

/// `fast_loop` without the copies, for `validate`: the same walk from tag
/// to tag with no branch on the kind of element, keeping only how long
/// the output would be.
#[inline(never)]
fn fast_check(src: &[u8], n: usize, ip0: usize, op0: usize, Ghost(cur0): Ghost<Seq<u8>>) -> (r: (
    usize,
    usize,
    Ghost<Seq<u8>>,
))
    requires
        ip0 <= src@.len(),
        op0 <= n,
        n <= 0xffff_ffff,
        op0 == cur0.len(),
    ensures
        ip0 <= r.0 <= src@.len(),
        r.1 <= n,
        r.1 == r.2@.len(),
        elems(src@, r.0 as int, r.2@, n as nat) == elems(src@, ip0 as int, cur0, n as nat),
{
    let slen = src.len();
    let mut ip = ip0;
    let mut op = op0;
    let ghost mut cur = cur0;
    let ghost goal = elems(src@, ip0 as int, cur0, n as nat);
    if slen - ip < ROOM || n - op < ROOM || op < 16 {
        return (ip, op, Ghost(cur));
    }
    let ip_max = slen - ROOM;
    let op_max = n - ROOM;
    let mut tag = get(src, ip) as usize;
    loop
        invariant_except_break
            slen - ip >= ROOM,
            n - op >= ROOM,
            op >= 16,
            tag == src@[ip as int],
        invariant
            slen == src@.len(),
            ip_max == slen - ROOM,
            op_max == n - ROOM,
            ip0 <= ip <= slen,
            op <= n,
            n <= 0xffff_ffff,
            op == cur.len(),
            elems(src@, ip as int, cur, n as nat) == goal,
        decreases slen - ip,
    {
        let k = tag & 3;
        let hi = tag >> 2;
        assert(k == tag % 4 && hi == tag / 4 && hi < 64 && k < 4) by (bit_vector)
            requires
                tag < 256,
                k == tag & 3,
                hi == tag >> 2,
        ;
        let (len, off, w) = fields(src, ip, tag);
        let lit = k == 0;
        let tag_c = ((w >> (8 * k as u64)) & 0xff) as usize;
        let tag_l = get(src, ip + 2 + hi) as usize;
        proof {
            let x = w;
            assert((x >> 8) & 0xff == (x / 0x100) % 256 && (x >> 16) & 0xff == (x / 0x1_0000) % 256 && (x >> 24) & 0xff
                == (x / 0x100_0000) % 256) by (bit_vector);
            lemma2_to64();
            if k != 0 {
                lemma_le_digit(src@, ip + 1, 4, k as nat);
                assert(tag_c == src@[ip + 1 + k]);
            }
        }
        let ip2 = pick(lit, ip + 2 + hi, ip + 1 + k);
        let tag2 = pick(lit, tag_l, tag_c);
        if (off == 0) | (off > op) {
            break;
        }
        proof {
            if lit {
                cur = cur + src@.subrange(ip + 1, ip + 1 + len);
            } else {
                lemma_lz_copy_len(cur, off as int, len as nat);
                cur = lz_copy(cur, off as int, len as nat);
            }
        }
        op = op + len;
        ip = ip2;
        tag = tag2;
        if ip > ip_max || op > op_max {
            break;
        }
    }
    (ip, op, Ghost(cur))
}

/// Whether `src` is valid, without producing what it decompresses to.
pub fn validate(src: &[u8]) -> (r: bool)
    ensures
        r == decompress(src@).is_some(),
{
    let slen = src.len();
    let (n, i0) = match read_varint(src) {
        None => {
            return false;
        },
        Some(x) => x,
    };
    let ghost goal = elems(src@, i0 as int, Seq::empty(), n as nat);
    let ghost mut cur: Seq<u8> = Seq::empty();
    let mut ip = i0;
    let mut op: usize = 0;
    while ip < slen
        invariant
            slen == src@.len(),
            ip <= slen,
            op <= n,
            n <= 0xffff_ffff,
            op == cur.len(),
            goal == decompress(src@),
            elems(src@, ip as int, cur, n as nat) == goal,
        ensures
            ip == slen,
        decreases slen - ip,
    {
        if slen - ip >= ROOM && n - op >= ROOM && op >= 16 {
            let (i2, o2, c2) = fast_check(src, n, ip, op, Ghost(cur));
            ip = i2;
            op = o2;
            proof {
                cur = c2@;
            }
            if ip >= slen {
                break;
            }
        }
        let tag = get(src, ip) as usize;
        let kind = tag % 4;
        let hi = tag / 4;
        if kind == 0 {
            let nb: usize = if hi < 60 {
                0
            } else {
                hi - 59
            };
            if slen - ip - 1 < nb {
                return false;
            }
            let len = if hi < 60 {
                hi + 1
            } else {
                let v = read_le(src, ip + 1, nb);
                // A 32-bit usize cannot hold 2^32, and no literal that
                // long fits in the input (checked again just below).
                #[cfg(target_pointer_width = "32")]
                if v >= slen {
                    return false;
                }
                v + 1
            };
            let j = ip + 1 + nb;
            if len > slen - j {
                return false;
            }
            if len > n - op {
                proof {
                    lemma_elems_len(src@, j + len, cur + src@.subrange(j as int, j + len), n as nat);
                }
                return false;
            }
            proof {
                cur = cur + src@.subrange(j as int, j + len);
            }
            op = op + len;
            ip = j + len;
        } else {
            let (nb, len, off) = if slen - ip >= 5 {
                copy_fields(src, ip, kind, hi)
            } else {
                match copy_fields_slow(src, ip, kind, hi) {
                    Some(f) => f,
                    None => {
                        return false;
                    },
                }
            };
            if off == 0 || off > op {
                return false;
            }
            proof {
                lemma_lz_copy_len(cur, off as int, len as nat);
            }
            if len > n - op {
                proof {
                    lemma_elems_len(src@, ip + 1 + nb, lz_copy(cur, off as int, len as nat), n as nat);
                }
                return false;
            }
            proof {
                cur = lz_copy(cur, off as int, len as nat);
            }
            op = op + len;
            ip = ip + 1 + nb;
        }
    }
    op == n
}

/// The uncompressed length a compressed buffer declares, if its preamble
/// is valid.
pub fn uncompressed_length(src: &[u8]) -> (r: Option<usize>)
    ensures
        match r {
            Some(n) => varint(src@, 0, 0) matches Some((m, _i)) && m == n,
            None => varint(src@, 0, 0).is_none(),
        },
{
    match read_varint(src) {
        Some((n, _i)) => Some(n),
        None => None,
    }
}

/// Decompresses `src`, if its uncompressed length is at most `limit`.
pub fn decompress_vec(src: &[u8], limit: usize) -> (r: Result<Vec<u8>, Error>)
    ensures
        match r {
            Ok(v) => decompress(src@) == Some(v@) && v@.len() <= limit,
            Err(Error::Corrupt) => decompress(src@).is_none(),
            Err(Error::TooSmall) => decompress(src@) matches Some(o) ==> o.len() > limit,
        },
{
    let n = match read_varint(src) {
        None => {
            return Err(Error::Corrupt);
        },
        Some((n, _i)) => n,
    };
    if n > limit {
        proof {
            let i = varint(src@, 0, 0).unwrap().1;
            lemma_elems_len(src@, i, Seq::empty(), n as nat);
        }
        return Err(Error::TooSmall);
    }
    let mut v: Vec<u8> = vec![0u8; n];
    match decompress_into(src, v.as_mut_slice()) {
        Ok(m) => {
            proof {
                let i = varint(src@, 0, 0).unwrap().1;
                lemma_elems_len(src@, i, Seq::empty(), n as nat);
                assert(v@.subrange(0, m as int) =~= v@);
            }
            Ok(v)
        },
        Err(Error::Corrupt) => Err(Error::Corrupt),
        Err(Error::TooSmall) => {
            proof {
                let i = varint(src@, 0, 0).unwrap().1;
                lemma_elems_len(src@, i, Seq::empty(), n as nat);
            }
            Err(Error::Corrupt)
        },
    }
}

} // verus!

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::Corrupt => "corrupt Snappy data",
            Error::TooSmall => "the output is longer than the buffer or the limit",
        })
    }
}

impl std::error::Error for Error {}

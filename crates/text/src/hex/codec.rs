//! Hexadecimal (RFC 4648 §8, "base16"), in either case: the spec, the round
//! trip, and a verified codec.
//!
//! `encode` writes two digits per byte, high nibble first. `decode` accepts
//! digits of either case, as the hex crate does, and returns `None` on an
//! odd length or a non-digit. Proven: `decode(encode(x)) == Some(x)` in
//! both cases, and whatever `decode` accepts is an encoding of its result
//! up to the case of each digit.
use verilith_core::prims::{get, set};
use vstd::compute::RangeAll;
use vstd::prelude::*;

verus! {

/// The digit for a nibble.
pub open spec fn digit(upper: bool, v: u8) -> u8 {
    if v < 10 {
        (v + 48) as u8
    } else if upper {
        (v + 55) as u8
    } else {
        (v + 87) as u8
    }
}

/// The value of a digit of either case.
pub open spec fn dval(c: u8) -> Option<u8> {
    if 48 <= c <= 57 {
        Some((c - 48) as u8)
    } else if 65 <= c <= 70 {
        Some((c - 55) as u8)
    } else if 97 <= c <= 102 {
        Some((c - 87) as u8)
    } else {
        None
    }
}

/// ASCII lowercase.
pub open spec fn lower(c: u8) -> u8 {
    if 65 <= c <= 90 {
        (c + 32) as u8
    } else {
        c
    }
}

pub open spec fn encode(upper: bool, x: Seq<u8>) -> Seq<u8> {
    Seq::new(2 * x.len(), |i: int| digit(upper, if i % 2 == 0 { x[i / 2] >> 4 } else { x[i / 2] & 15 }))
}

pub open spec fn dv(s: Seq<u8>, j: int) -> u8 {
    match dval(s[j]) {
        Some(v) => v,
        None => 0,
    }
}

pub open spec fn decode(s: Seq<u8>) -> Option<Seq<u8>> {
    if s.len() % 2 == 0 && forall|j: int| 0 <= j < s.len() ==> (#[trigger] dval(s[j])) is Some {
        Some(Seq::new(s.len() / 2, |i: int| ((dv(s, 2 * i) << 4) | dv(s, 2 * i + 1)) as u8))
    } else {
        None
    }
}

proof fn lemma_nibbles(b: u8)
    ensures
        b >> 4 < 16,
        b & 15 < 16,
        ((b >> 4) << 4) | (b & 15) == b,
{
    assert(b >> 4 < 16) by (bit_vector);
    assert(b & 15 < 16) by (bit_vector);
    assert(((b >> 4) << 4) | (b & 15) == b) by (bit_vector);
}

proof fn lemma_halves(i: int)
    requires
        i >= 0,
    ensures
        (2 * i) / 2 == i,
        (2 * i) % 2 == 0,
        (2 * i + 1) / 2 == i,
        (2 * i + 1) % 2 == 1,
{
}

/// The round trip.
pub proof fn lemma_decode_encode(upper: bool, x: Seq<u8>)
    ensures
        decode(encode(upper, x)) == Some(x),
{
    let s = encode(upper, x);
    assert forall|j: int| 0 <= j < s.len() implies (#[trigger] dval(s[j])) is Some && dv(s, j) == (if j % 2
        == 0 {
        x[j / 2] >> 4
    } else {
        x[j / 2] & 15
    }) by {
        lemma_nibbles(x[j / 2]);
    }
    let d = decode(s)->0;
    assert forall|i: int| 0 <= i < x.len() implies d[i] == x[i] by {
        lemma_halves(i);
        lemma_nibbles(x[i]);
    }
    assert(d =~= x);
}

/// Canonicity up to case.
pub proof fn lemma_encode_decode(s: Seq<u8>)
    requires
        decode(s) is Some,
    ensures
        forall|i: int| 0 <= i < s.len() ==> #[trigger] lower(s[i]) == encode(false, decode(s)->0)[i],
        s.len() == encode(false, decode(s)->0).len(),
{
    let x = decode(s)->0;
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] lower(s[i]) == encode(false, x)[i] by {
        let k = i / 2;
        assert(dval(s[2 * k]) is Some);
        assert(dval(s[2 * k + 1]) is Some);
        let p = dv(s, 2 * k);
        let q = dv(s, 2 * k + 1);
        assert(p < 16 && q < 16);
        assert(p < 16 && q < 16 ==> ((p << 4) | q) >> 4 == p && ((p << 4) | q) & 15 == q) by (bit_vector);
        assert(x[k] == ((p << 4) | q) as u8);
    }
}

/// Lowercase digits, in pairs: `DIGITS2[2 * b]` and `DIGITS2[2 * b + 1]`
/// encode `b`.
pub const DIGITS_LO: [u8; 16] = [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 97, 98, 99, 100, 101, 102];

pub const DIGITS_UP: [u8; 16] = [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 65, 66, 67, 68, 69, 70];

/// `dval(c)`, with 255 for `None`.
pub const DVAL: [u8; 256] = [
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 255, 255, 255, 255, 255, 255,
    255, 10, 11, 12, 13, 14, 15, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 10, 11, 12, 13, 14, 15, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
];

pub open spec fn dval_entry(c: u8) -> u8 {
    match dval(c) {
        Some(v) => v,
        None => 255,
    }
}

pub proof fn lemma_tables()
    ensures
        forall|v: u8| v < 16 ==> #[trigger] DIGITS_LO@[v as int] == digit(false, v),
        forall|v: u8| v < 16 ==> #[trigger] DIGITS_UP@[v as int] == digit(true, v),
        forall|c: u8| #[trigger] DVAL@[c as int] == dval_entry(c),
{
    let p0 = |i: int| DIGITS_LO@[i] == digit(false, i as u8);
    assert((0..16int).all_spec(|i: int| DIGITS_LO@[i] == digit(false, i as u8))) by (compute_only);
    vstd::compute::all_spec_ensures(0..16int, p0);
    let p1 = |i: int| DIGITS_UP@[i] == digit(true, i as u8);
    assert((0..16int).all_spec(|i: int| DIGITS_UP@[i] == digit(true, i as u8))) by (compute_only);
    vstd::compute::all_spec_ensures(0..16int, p1);
    let p2 = |i: int| DVAL@[i] == dval_entry(i as u8);
    assert((0..256int).all_spec(|i: int| DVAL@[i] == dval_entry(i as u8))) by (compute_only);
    vstd::compute::all_spec_ensures(0..256int, p2);
    assert forall|v: u8| v < 16 implies #[trigger] DIGITS_LO@[v as int] == digit(false, v) by {
        assert(p0(v as int));
    }
    assert forall|v: u8| v < 16 implies #[trigger] DIGITS_UP@[v as int] == digit(true, v) by {
        assert(p1(v as int));
    }
    assert forall|c: u8| #[trigger] DVAL@[c as int] == dval_entry(c) by {
        assert(p2(c as int));
    }
}

/// Writes `encode(upper, x)` into `out`.
pub fn encode_into(upper: bool, x: &[u8], out: &mut [u8])
    requires
        old(out).len() == 2 * x.len(),
    ensures
        final(out)@ == encode(upper, x@),
{
    proof {
        lemma_tables();
    }
    let tab: &[u8; 16] = if upper {
        &DIGITS_UP
    } else {
        &DIGITS_LO
    };
    let mut i = if verilith_simd::cpu::has_avx2() {
        // SAFETY: the CPU has AVX2.
        unsafe { super::avx2::encode_bulk(upper, x, out) }
    } else {
        0
    };
    while i < x.len()
        invariant
            forall|v: u8| v < 16 ==> #[trigger] tab@[v as int] == digit(upper, v),
            out.len() == 2 * x.len(),
            i <= x.len(),
            forall|j: int| 0 <= j < 2 * i ==> #[trigger] out@[j] == encode(upper, x@)[j],
        decreases x.len() - i,
    {
        let b = get(x, i);
        proof {
            lemma_nibbles(b);
            lemma_halves(i as int);
        }
        set(out, 2 * i, tab[(b >> 4) as usize]);
        set(out, 2 * i + 1, tab[(b & 15) as usize]);
        i = i + 1;
    }
    assert(out@ =~= encode(upper, x@));
}

/// Decodes `s` into `out` (of length `s.len() / 2`); returns whether `s`
/// is a hex string, in which case `out` holds `decode(s)`.
pub fn decode_into(s: &[u8], out: &mut [u8]) -> (ok: bool)
    requires
        old(out).len() == s.len() / 2,
    ensures
        ok == decode(s@) is Some,
        ok ==> final(out)@ == decode(s@)->0,
{
    proof {
        lemma_tables();
    }
    if s.len() % 2 != 0 {
        return false;
    }
    let n = s.len() / 2;
    let (mut i, ok) = if verilith_simd::cpu::has_avx2() {
        // SAFETY: the CPU has AVX2.
        unsafe { super::avx2::decode_bulk(s, out) }
    } else {
        (0, true)
    };
    if !ok {
        return false;
    }
    let mut acc: u8 = 0;
    assert(0u8 & 0x80 == 0) by (bit_vector);
    while i < n
        invariant
            forall|c: u8| #[trigger] DVAL@[c as int] == dval_entry(c),
            out.len() == n,
            n == s.len() / 2,
            s.len() % 2 == 0,
            i <= n,
            (acc & 0x80 == 0) <==> forall|j: int| 0 <= j < 2 * i ==> (#[trigger] dval(s@[j])) is Some,
            (acc & 0x80 == 0) ==> forall|k: int| 0 <= k < i ==> #[trigger] out@[k] == ((dv(s@, 2 * k) << 4) | dv(
                s@,
                2 * k + 1,
            )) as u8,
        decreases n - i,
    {
        let p = DVAL[get(s, 2 * i) as usize];
        let q = DVAL[get(s, 2 * i + 1) as usize];
        let ghost a0 = acc;
        acc = acc | p | q;
        proof {
            assert(p < 16 || p == 255);
            assert(q < 16 || q == 255);
            assert((p < 16 || p == 255) && (q < 16 || q == 255) ==> ((((a0 | p) | q) & 0x80 == 0) <==> (a0 & 0x80
                == 0 && p < 16 && q < 16))) by (bit_vector);
            assert((acc & 0x80 == 0) <==> forall|j: int| 0 <= j < 2 * (i + 1) ==> (#[trigger] dval(s@[j])) is Some)
                by {
                if forall|j: int| 0 <= j < 2 * (i + 1) ==> (#[trigger] dval(s@[j])) is Some {
                    assert(dval(s@[2 * i as int]) is Some);
                    assert(dval(s@[2 * i + 1]) is Some);
                }
            }
        }
        set(out, i, (p << 4) | q);
        i = i + 1;
    }
    if acc & 0x80 != 0 {
        return false;
    }
    assert(out@ =~= decode(s@)->0);
    true
}

} // verus!


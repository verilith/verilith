//! Percent-encoding (RFC 3986 §2.1), with the percent-encoding crate's
//! semantics: the spec, the round trip, and a verified codec.
//!
//! `encode(set, x)` replaces every byte that is in `set` or not ASCII with
//! `%` and two uppercase hex digits. `decode` replaces every `%` followed
//! by two hex digits (either case) with the byte they spell, and keeps
//! every other byte, including a `%` that does not start an escape.
//! Proven: if `set` contains `%`, then `decode(encode(set, x)) == x`; and
//! no byte that `encode` leaves alone is in `set` or above 0x7F.
use crate::hex::codec::{DIGITS_UP, DVAL};
#[cfg(verus_only)]
use crate::hex::codec::{digit, dv, dval, lemma_tables as lemma_hex_tables};
use verilith_core::prims::{extend, get};
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

pub const PCT: u8 = 0x25;  // '%'

/// A set of ASCII bytes, as the percent-encoding crate's `AsciiSet`: bit
/// `b % 32` of `mask[b / 32]` says whether `b` is in it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AsciiSet {
    pub mask: [u32; 4],
}

impl AsciiSet {
    pub open spec fn has(self, b: u8) -> bool {
        b < 128 && (self.mask@[(b / 32) as int] >> ((b % 32) as u32)) & 1 == 1
    }

    #[inline(always)]
    pub fn contains(&self, b: u8) -> (r: bool)
        ensures
            r == self.has(b),
    {
        b < 128 && (self.mask[(b / 32) as usize] >> ((b % 32) as u32)) & 1 == 1
    }

    /// Whether `encode` escapes `b`.
    pub open spec fn needs(self, b: u8) -> bool {
        b >= 128 || self.has(b)
    }

    #[inline(always)]
    pub fn should_encode(&self, b: u8) -> (r: bool)
        ensures
            r == self.needs(b),
    {
        b >= 128 || self.contains(b)
    }
}

/// What `encode` writes for one byte.
pub open spec fn piece(set: AsciiSet, b: u8) -> Seq<u8> {
    if set.needs(b) {
        seq![PCT, digit(true, b >> 4), digit(true, b & 15)]
    } else {
        seq![b]
    }
}

pub open spec fn encode(set: AsciiSet, x: Seq<u8>) -> Seq<u8>
    decreases x.len(),
{
    if x.len() == 0 {
        Seq::empty()
    } else {
        encode(set, x.drop_last()) + piece(set, x.last())
    }
}

/// `s` starts with an escape: `%` and two hex digits.
pub open spec fn is_escape(s: Seq<u8>) -> bool {
    s.len() >= 3 && s[0] == PCT && dval(s[1]) is Some && dval(s[2]) is Some
}

pub open spec fn decode(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if is_escape(s) {
        seq![((dv(s, 1) << 4) | dv(s, 2)) as u8] + decode(s.skip(3))
    } else {
        seq![s[0]] + decode(s.skip(1))
    }
}

// ---------------------------------------------------------------------------
// The round trip
// ---------------------------------------------------------------------------

/// `encode` from the front.
pub proof fn lemma_encode_cons(set: AsciiSet, b: u8, x: Seq<u8>)
    ensures
        encode(set, seq![b] + x) == piece(set, b) + encode(set, x),
    decreases x.len(),
{
    if x.len() == 0 {
        assert(seq![b] + x =~= seq![b]);
        assert((seq![b] + x).drop_last() =~= Seq::<u8>::empty());
        assert(encode(set, Seq::<u8>::empty()) =~= Seq::<u8>::empty());
        assert(encode(set, seq![b] + x) =~= piece(set, b) + encode(set, x));
    } else {
        lemma_encode_cons(set, b, x.drop_last());
        assert((seq![b] + x).drop_last() =~= seq![b] + x.drop_last());
        assert((seq![b] + x).last() == x.last());
        assert(encode(set, seq![b] + x) =~= piece(set, b) + encode(set, x));
    }
}

proof fn lemma_digit_val(b: u8)
    ensures
        dval(digit(true, b >> 4)) == Some(b >> 4),
        dval(digit(true, b & 15)) == Some(b & 15),
        ((b >> 4) << 4) | (b & 15) == b,
{
    assert(b >> 4 < 16) by (bit_vector);
    assert(b & 15 < 16) by (bit_vector);
    assert(((b >> 4) << 4) | (b & 15) == b) by (bit_vector);
}

/// Decoding a piece and then the rest.
proof fn lemma_decode_piece(set: AsciiSet, b: u8, rest: Seq<u8>)
    requires
        set.has(PCT),
    ensures
        decode(piece(set, b) + rest) == seq![b] + decode(rest),
{
    let s = piece(set, b) + rest;
    if set.needs(b) {
        lemma_digit_val(b);
        assert(is_escape(s));
        assert(s.skip(3) =~= rest);
    } else {
        assert(b != PCT);
        assert(!is_escape(s));
        assert(s.skip(1) =~= rest);
    }
}

/// The round trip, when `set` escapes `%` itself.
pub proof fn lemma_decode_encode(set: AsciiSet, x: Seq<u8>)
    requires
        set.has(PCT),
    ensures
        decode(encode(set, x)) == x,
    decreases x.len(),
{
    if x.len() == 0 {
        assert(encode(set, x) =~= Seq::<u8>::empty());
    } else {
        let t = x.skip(1);
        assert(x =~= seq![x[0]] + t);
        lemma_encode_cons(set, x[0], t);
        lemma_decode_piece(set, x[0], encode(set, t));
        lemma_decode_encode(set, t);
    }
}

/// What `encode` leaves unescaped is outside `set` and ASCII.
pub proof fn lemma_encode_safe(set: AsciiSet, x: Seq<u8>)
    ensures
        forall|i: int|
            0 <= i < encode(set, x).len() ==> {
                let c = #[trigger] encode(set, x)[i];
                c == PCT || dval(c) is Some || !set.needs(c)
            },
    decreases x.len(),
{
    if x.len() > 0 {
        lemma_encode_safe(set, x.drop_last());
        let b = x.last();
        lemma_digit_val(b);
        let e0 = encode(set, x.drop_last());
        assert forall|i: int| 0 <= i < encode(set, x).len() implies {
            let c = #[trigger] encode(set, x)[i];
            c == PCT || dval(c) is Some || !set.needs(c)
        } by {
            if i >= e0.len() {
                assert(encode(set, x)[i] == piece(set, b)[i - e0.len()]);
            } else {
                assert(encode(set, x)[i] == e0[i]);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The codec
// ---------------------------------------------------------------------------

/// A run of bytes `encode` keeps is copied as is.
proof fn lemma_encode_run(set: AsciiSet, x: Seq<u8>, a: int, b: int)
    requires
        0 <= a <= b <= x.len(),
        forall|k: int| a <= k < b ==> !set.needs(#[trigger] x[k]),
    ensures
        encode(set, x.take(b)) == encode(set, x.take(a)) + x.subrange(a, b),
    decreases b - a,
{
    if b > a {
        lemma_encode_run(set, x, a, b - 1);
        assert(x.take(b).drop_last() =~= x.take(b - 1));
        assert(x.subrange(a, b) =~= x.subrange(a, b - 1) + seq![x[b - 1]]);
    } else {
        assert(x.subrange(a, b) =~= Seq::<u8>::empty());
    }
}

/// `t[b]` is whether `set` needs `b` escaped.
fn needs_table(set: &AsciiSet) -> (t: [bool; 256])
    ensures
        forall|b: u8| #[trigger] t@[b as int] == set.needs(b),
{
    let mut t = [true; 256];
    let mut b: usize = 0;
    while b < 128
        invariant
            b <= 128,
            t@.len() == 256,
            forall|c: u8| c >= 128 ==> #[trigger] t@[c as int],
            forall|c: u8| c < b ==> #[trigger] t@[c as int] == set.needs(c),
        decreases 128 - b,
    {
        t[b] = set.contains(b as u8);
        proof {
            assert forall|c: u8| c < b + 1 implies #[trigger] t@[c as int] == set.needs(c) by {
                if c as usize == b {
                    assert(t@[c as int] == set.has(c));
                }
            }
        }
        b += 1;
    }
    t
}

/// Appends `encode(set, x)` to `out`.
pub fn encode_to(set: &AsciiSet, x: &[u8], out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + encode(*set, x@),
{
    proof {
        lemma_hex_tables();
    }
    let n = x.len();
    // Building the table costs about as much as checking 128 bytes.
    let use_table = n >= 128;
    let t = if use_table { needs_table(set) } else { [true; 256] };
    let mut i = 0;
    let mut start = 0;
    while i < n
        invariant
            forall|v: u8| v < 16 ==> #[trigger] DIGITS_UP@[v as int] == digit(true, v),
            use_table ==> forall|c: u8| #[trigger] t@[c as int] == set.needs(c),
            use_table == (n >= 128),
            n == x.len(),
            start <= i <= n,
            out@ == old(out)@ + encode(*set, x@.take(start as int)),
            forall|k: int| start <= k < i ==> !set.needs(#[trigger] x@[k]),
        decreases n - i,
    {
        let b = get(x, i);
        if if use_table { t[b as usize] } else { set.should_encode(b) } {
            proof {
                lemma_encode_run(*set, x@, start as int, i as int);
            }
            extend(out, slice_subrange(x, start, i));
            proof {
                assert(b >> 4 < 16) by (bit_vector);
                assert(b & 15 < 16) by (bit_vector);
            }
            let esc = [PCT, DIGITS_UP[(b >> 4) as usize], DIGITS_UP[(b & 15) as usize]];
            extend(out, esc.as_slice());
            assert(esc@ == seq![PCT, digit(true, b >> 4), digit(true, b & 15)]);
            proof {
                assert(x@.take(i + 1).drop_last() =~= x@.take(i as int));
                assert(x@.take(i + 1).last() == b);
                assert(out@ =~= old(out)@ + encode(*set, x@.take(i + 1)));
            }
            i = i + 1;
            start = i;
        } else {
            i = i + 1;
        }
    }
    proof {
        lemma_encode_run(*set, x@, start as int, n as int);
        assert(x@.take(n as int) =~= x@);
    }
    extend(out, slice_subrange(x, start, n));
    assert(out@ =~= old(out)@ + encode(*set, x@));
}

/// A run without `%` decodes to itself.
proof fn lemma_decode_run(s: Seq<u8>, a: int, b: int)
    requires
        0 <= a <= b <= s.len(),
        forall|k: int| a <= k < b ==> #[trigger] s[k] != PCT,
    ensures
        decode(s.skip(a)) == s.subrange(a, b) + decode(s.skip(b)),
    decreases b - a,
{
    if b > a {
        lemma_decode_run(s, a + 1, b);
        let t = s.skip(a);
        assert(t[0] == s[a]);
        assert(!is_escape(t));
        assert(t.skip(1) =~= s.skip(a + 1));
        assert(s.subrange(a, b) =~= seq![s[a]] + s.subrange(a + 1, b));
    } else {
        assert(s.subrange(a, b) =~= Seq::<u8>::empty());
    }
}

/// One step of the decoder: the run `s[start..i]` without `%`, then
/// either an escape at `i` (`esc`, decoding to `byte`) or the single byte
/// `s[i]`.
proof fn lemma_decode_step(s: Seq<u8>, start: int, i: int, esc: bool, byte: u8)
    requires
        0 <= start <= i < s.len(),
        forall|k: int| start <= k < i ==> #[trigger] s[k] != PCT,
        esc == is_escape(s.skip(i)),
        esc ==> byte == ((dv(s.skip(i), 1) << 4) | dv(s.skip(i), 2)) as u8,
        !esc ==> byte == s[i],
    ensures
        decode(s.skip(start)) == s.subrange(start, i) + seq![byte] + decode(s.skip(i + if esc { 3int } else { 1int })),
{
    lemma_decode_run(s, start, i);
    let t = s.skip(i);
    if esc {
        assert(t.skip(3) =~= s.skip(i + 3));
    } else {
        assert(t.skip(1) =~= s.skip(i + 1));
    }
    assert(decode(t) == seq![byte] + decode(s.skip(i + if esc { 3int } else { 1int })));
}

/// Appends `decode(s)` to `out`.
pub fn decode_to(s: &[u8], out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + decode(s@),
{
    proof {
        lemma_hex_tables();
    }
    let n = s.len();
    let mut i = 0;
    let mut start = 0;
    assert(s@.skip(0) =~= s@);
    while i < n
        invariant
            forall|c: u8| #[trigger] DVAL@[c as int] == crate::hex::codec::dval_entry(c),
            n == s.len(),
            start <= i <= n,
            out@ + decode(s@.skip(start as int)) == old(out)@ + decode(s@),
            forall|k: int| start <= k < i ==> #[trigger] s@[k] != PCT,
        decreases n - i,
    {
        let b = get(s, i);
        if b == PCT {
            let mut esc = false;
            let mut byte = b;
            if n - i > 2 {
                let p = DVAL[get(s, i + 1) as usize];
                let q = DVAL[get(s, i + 2) as usize];
                if p < 16 && q < 16 {
                    esc = true;
                    byte = (p << 4) | q;
                }
                proof {
                    let t = s@.skip(i as int);
                    assert(t[0] == PCT && t[1] == s@[i + 1] && t[2] == s@[i + 2]);
                    if esc {
                        assert(dv(t, 1) == p && dv(t, 2) == q);
                    }
                }
            }
            proof {
                lemma_decode_step(s@, start as int, i as int, esc, byte);
            }
            let ghost o0 = out@;
            extend(out, slice_subrange(s, start, i));
            out.push(byte);
            let step: usize = if esc {
                3
            } else {
                1
            };
            proof {
                assert(out@ =~= o0 + s@.subrange(start as int, i as int) + seq![byte]);
            }
            i = i + step;
            start = i;
        } else {
            i = i + 1;
        }
    }
    proof {
        lemma_decode_run(s@, start as int, n as int);
        assert(s@.skip(n as int) =~= Seq::<u8>::empty());
        assert(decode(s@.skip(n as int)) =~= Seq::<u8>::empty());
    }
    extend(out, slice_subrange(s, start, n));
    assert(out@ =~= old(out)@ + decode(s@));
}

} // verus!

// ---------------------------------------------------------------------------
// Public interface, shaped like the percent-encoding crate's. Unverified
// glue around the verified codec.
// ---------------------------------------------------------------------------

use std::borrow::Cow;
use std::fmt;

impl AsciiSet {
    pub const EMPTY: AsciiSet = AsciiSet { mask: [0; 4] };

    /// The set with `byte` added (`byte` must be ASCII).
    pub const fn add(&self, byte: u8) -> Self {
        let mut mask = self.mask;
        mask[byte as usize / 32] |= 1 << (byte as usize % 32);
        AsciiSet { mask }
    }

    pub const fn remove(&self, byte: u8) -> Self {
        let mut mask = self.mask;
        mask[byte as usize / 32] &= !(1 << (byte as usize % 32));
        AsciiSet { mask }
    }

    pub const fn union(&self, other: AsciiSet) -> Self {
        AsciiSet {
            mask: [
                self.mask[0] | other.mask[0],
                self.mask[1] | other.mask[1],
                self.mask[2] | other.mask[2],
                self.mask[3] | other.mask[3],
            ],
        }
    }

    pub const fn complement(&self) -> Self {
        AsciiSet { mask: [!self.mask[0], !self.mask[1], !self.mask[2], !self.mask[3]] }
    }
}

/// The C0 controls and DEL.
pub const CONTROLS: &AsciiSet = &AsciiSet { mask: [!0u32, 0, 0, 1 << (0x7F_u32 % 32)] };

/// Everything but ASCII letters and digits.
pub const NON_ALPHANUMERIC: &AsciiSet = &AsciiSet {
    mask: [
        !0u32,
        !0u32 & !(0x3FF << 16),  // keep '0'..='9' (0x30..0x39)
        !0u32 & !(0x3FFFFFF << 1),  // keep 'A'..='Z' (0x41..0x5A)
        !0u32 & !(0x3FFFFFF << 1),  // keep 'a'..='z' (0x61..0x7A)
    ],
};

/// The percent-encoding of some bytes; `Display` writes it.
#[derive(Clone, Debug)]
pub struct PercentEncode<'a> {
    bytes: &'a [u8],
    set: &'static AsciiSet,
}

impl<'a> PercentEncode<'a> {
    fn to_vec(&self) -> Vec<u8> {
        let escapes = self.bytes.iter().filter(|&&b| self.set.should_encode(b)).count();
        let mut out = Vec::with_capacity(self.bytes.len() + 2 * escapes);
        encode_to(self.set, self.bytes, &mut out);
        out
    }
}

impl<'a> fmt::Display for PercentEncode<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // `encode` is a fold over the bytes, so the encoding of the whole is
        // the encodings of the chunks one after another.
        const CHUNK: usize = 1024;
        let mut buf = Vec::with_capacity(3 * CHUNK.min(self.bytes.len()));
        for chunk in self.bytes.chunks(CHUNK) {
            buf.clear();
            encode_to(self.set, chunk, &mut buf);
            // SAFETY: the encoding of any bytes is ASCII outside of copied
            // runs; a copied run is ASCII too (`lemma_encode_safe`:
            // unescaped bytes are never >= 0x80).
            f.write_str(unsafe { std::str::from_utf8_unchecked(&buf) })?;
        }
        Ok(())
    }
}

impl<'a> From<PercentEncode<'a>> for Cow<'a, str> {
    fn from(e: PercentEncode<'a>) -> Self {
        let v = e.to_vec();
        if v.len() == e.bytes.len() {
            // Nothing was escaped, so the output is the (ASCII) input.
            // SAFETY: as above, every unescaped byte is ASCII.
            Cow::Borrowed(unsafe { std::str::from_utf8_unchecked(e.bytes) })
        } else {
            // SAFETY: as above.
            Cow::Owned(unsafe { String::from_utf8_unchecked(v) })
        }
    }
}

pub fn percent_encode<'a>(input: &'a [u8], set: &'static AsciiSet) -> PercentEncode<'a> {
    PercentEncode { bytes: input, set }
}

pub fn utf8_percent_encode<'a>(input: &'a str, set: &'static AsciiSet) -> PercentEncode<'a> {
    percent_encode(input.as_bytes(), set)
}

/// The percent-decoding of some bytes.
#[derive(Clone, Debug)]
pub struct PercentDecode<'a> {
    bytes: &'a [u8],
    pos: usize,
    out: Option<Vec<u8>>,
}

impl<'a> PercentDecode<'a> {
    fn decoded(&self) -> Cow<'a, [u8]> {
        let s = &self.bytes[self.pos..];
        if !s.contains(&PCT) {
            return Cow::Borrowed(s);
        }
        let mut out = Vec::with_capacity(s.len());
        decode_to(s, &mut out);
        Cow::Owned(out)
    }

    pub fn decode_utf8(self) -> Result<Cow<'a, str>, std::str::Utf8Error> {
        match self.decoded() {
            Cow::Borrowed(b) => std::str::from_utf8(b).map(Cow::Borrowed),
            Cow::Owned(v) => match String::from_utf8(v) {
                Ok(s) => Ok(Cow::Owned(s)),
                Err(e) => Err(e.utf8_error()),
            },
        }
    }

    pub fn decode_utf8_lossy(self) -> Cow<'a, str> {
        match self.decoded() {
            Cow::Borrowed(b) => String::from_utf8_lossy(b),
            Cow::Owned(v) => Cow::Owned(String::from_utf8_lossy(&v).into_owned()),
        }
    }
}

impl<'a> Iterator for PercentDecode<'a> {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        if self.out.is_none() {
            self.out = Some(self.decoded().into_owned());
            self.pos = 0;
        }
        let v = self.out.as_ref().unwrap();
        let b = v.get(self.pos).copied();
        self.pos += 1;
        b
    }
}

impl<'a> From<PercentDecode<'a>> for Cow<'a, [u8]> {
    fn from(d: PercentDecode<'a>) -> Self {
        match d.out {
            Some(v) => Cow::Owned(v[d.pos.min(v.len())..].to_vec()),
            None => d.decoded(),
        }
    }
}

pub fn percent_decode(input: &[u8]) -> PercentDecode<'_> {
    PercentDecode { bytes: input, pos: 0, out: None }
}

pub fn percent_decode_str(input: &str) -> PercentDecode<'_> {
    percent_decode(input.as_bytes())
}

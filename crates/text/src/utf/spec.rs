//! What the transcoders compute, as spec functions.
//!
//! UTF-8 well-formedness is vcore's `utf8_from`, read off Unicode's Table
//! 3-7, and `utf8_encode` is the UTF-8 encoding of a scalar (Table 3-6).
//! UTF-16 is defined here the same way, from section 3.9 (D91): a code unit
//! outside the surrogates is a scalar, a high surrogate followed by a low
//! one is a pair, and anything else is ill-formed.
//!
//! Each conversion is a fold from the front: the output for the text from
//! position `i` is the encoding of the character at `i`, then the output
//! for the rest. A converter proves, at each step, that what it has written
//! followed by the fold from where it is reading is the fold of the whole
//! text.
//!
//! The `cnt_*` functions are the output sizes simdutf documents
//! (`utf8_length_from_latin1`, `utf16_length_from_utf8`,
//! `utf8_length_from_utf16`), which callers use to size buffers. They are
//! defined per input byte or unit, as simdutf computes them, and proven
//! equal to the output length for well-formed input.
#[allow(unused_imports)]
use verilith_core::utf8::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// UTF-8
// ---------------------------------------------------------------------------

/// The scalar value of the well-formed sequence of length `l` at `i`: the
/// bit distribution of Table 3-6, read backwards.
pub open spec fn dec8_at(s: Seq<u8>, i: int, l: int) -> u32 {
    if l == 1 {
        s[i] as u32
    } else if l == 2 {
        (((s[i] & 0x1F) as u32) << 6u32) | ((s[i + 1] & 0x3F) as u32)
    } else if l == 3 {
        (((s[i] & 0x0F) as u32) << 12u32) | (((s[i + 1] & 0x3F) as u32) << 6u32) | ((s[i + 2] & 0x3F) as u32)
    } else {
        (((s[i] & 0x07) as u32) << 18u32) | (((s[i + 1] & 0x3F) as u32) << 12u32) | (((s[i + 2] & 0x3F) as u32)
            << 6u32) | ((s[i + 3] & 0x3F) as u32)
    }
}

/// The UTF-16 encoding of a scalar.
pub open spec fn enc16(c: u32) -> Seq<u16> {
    if c < 0x10000 {
        seq![c as u16]
    } else {
        seq![(0xD800 + (c - 0x10000) / 1024) as u16, (0xDC00 + (c - 0x10000) % 1024) as u16]
    }
}

/// UTF-16 of the UTF-8 text `s[i..]`, up to the first ill-formed sequence.
pub open spec fn u8to16(s: Seq<u8>, i: int) -> Seq<u16>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        seq![]
    } else {
        match utf8_len(s, i) {
            Some(l) => enc16(dec8_at(s, i, l)) + u8to16(s, i + l),
            None => seq![],
        }
    }
}

/// Latin-1 of the UTF-8 text `s[i..]`, when every character is below
/// U+0100.
pub open spec fn latin1_from(s: Seq<u8>, i: int) -> bool
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        true
    } else {
        match utf8_len(s, i) {
            Some(l) => dec8_at(s, i, l) < 0x100 && latin1_from(s, i + l),
            None => false,
        }
    }
}

pub open spec fn u8tol1(s: Seq<u8>, i: int) -> Seq<u8>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        seq![]
    } else {
        match utf8_len(s, i) {
            Some(l) => seq![dec8_at(s, i, l) as u8] + u8tol1(s, i + l),
            None => seq![],
        }
    }
}

/// simdutf's `utf16_length_from_utf8`: one unit per byte that is not a
/// continuation byte, and one more for each four-byte lead.
pub open spec fn cnt8(s: Seq<u8>, i: int) -> nat
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        0
    } else {
        (if cont(s[i]) { 0nat } else { 1nat }) + (if s[i] >= 0xF0 { 1nat } else { 0nat }) + cnt8(s, i + 1)
    }
}

/// simdutf's `latin1_length_from_utf8`: one byte per byte that is not a
/// continuation byte.
pub open spec fn cnt8l1(s: Seq<u8>, i: int) -> nat
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        0
    } else {
        (if cont(s[i]) { 0nat } else { 1nat }) + cnt8l1(s, i + 1)
    }
}

// ---------------------------------------------------------------------------
// UTF-16
// ---------------------------------------------------------------------------

pub open spec fn is_sur(u: u16) -> bool {
    0xD800 <= u <= 0xDFFF
}

pub open spec fn is_hi(u: u16) -> bool {
    0xD800 <= u <= 0xDBFF
}

pub open spec fn is_lo(u: u16) -> bool {
    0xDC00 <= u <= 0xDFFF
}

/// Length of the well-formed code unit sequence at `i`, if there is one.
pub open spec fn utf16_len(s: Seq<u16>, i: int) -> Option<int> {
    if !is_sur(s[i]) {
        Some(1)
    } else if is_hi(s[i]) && i + 1 < s.len() && is_lo(s[i + 1]) {
        Some(2)
    } else {
        None
    }
}

/// `s[i..]` is well-formed UTF-16.
pub open spec fn utf16_from(s: Seq<u16>, i: int) -> bool
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        true
    } else {
        match utf16_len(s, i) {
            Some(l) => utf16_from(s, i + l),
            None => false,
        }
    }
}

/// The scalar value of the sequence of length `l` at `i`.
pub open spec fn dec16_at(s: Seq<u16>, i: int, l: int) -> u32 {
    if l == 1 {
        s[i] as u32
    } else {
        (0x10000 + (s[i] - 0xD800) * 1024 + (s[i + 1] - 0xDC00)) as u32
    }
}

/// UTF-8 of the UTF-16 text `s[i..]`, up to the first ill-formed unit.
pub open spec fn u16to8(s: Seq<u16>, i: int) -> Seq<u8>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        seq![]
    } else {
        match utf16_len(s, i) {
            Some(l) => utf8_encode(dec16_at(s, i, l)) + u16to8(s, i + l),
            None => seq![],
        }
    }
}

/// simdutf's `utf8_length_from_utf16`: per unit, 1 below U+0080, 2 below
/// U+0800 or for a surrogate (a pair makes 4), else 3.
pub open spec fn cnt16_unit(u: u16) -> nat {
    if u <= 0x7F {
        1
    } else if u <= 0x7FF || is_sur(u) {
        2
    } else {
        3
    }
}

pub open spec fn cnt16(s: Seq<u16>, i: int) -> nat
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        0
    } else {
        cnt16_unit(s[i]) + cnt16(s, i + 1)
    }
}

/// Every unit is below U+0100, so the text is Latin-1.
pub open spec fn latin1_units(s: Seq<u16>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] <= 0xFF
}

// ---------------------------------------------------------------------------
// Latin-1
// ---------------------------------------------------------------------------

/// UTF-8 of the Latin-1 text `s[i..]`.
pub open spec fn l1to8(s: Seq<u8>, i: int) -> Seq<u8>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        seq![]
    } else {
        utf8_encode(s[i] as u32) + l1to8(s, i + 1)
    }
}

/// simdutf's `utf8_length_from_latin1`.
pub open spec fn cnt_l1(s: Seq<u8>, i: int) -> nat
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        0
    } else {
        (if s[i] >= 0x80 { 2nat } else { 1nat }) + cnt_l1(s, i + 1)
    }
}

/// Every byte is ASCII.
pub open spec fn ascii(s: Seq<u8>, a: int, b: int) -> bool {
    forall|k: int| a <= k < b ==> #[trigger] s[k] < 0x80
}

pub open spec fn ascii16(s: Seq<u16>, a: int, b: int) -> bool {
    forall|k: int| a <= k < b ==> #[trigger] s[k] < 0x80
}

// ---------------------------------------------------------------------------
// The specs are the standard encodings
// ---------------------------------------------------------------------------

/// Decoding a well-formed UTF-8 sequence and encoding the scalar again gives
/// the same bytes; the scalar is a scalar (not a surrogate, at most
/// U+10FFFF), and its length is the one `utf8_encode` picks.
pub proof fn lemma_dec8_roundtrip(s: Seq<u8>, i: int)
    requires
        0 <= i < s.len(),
        utf8_len(s, i) is Some,
    ensures
        ({
            let l = utf8_len(s, i)->0;
            let c = dec8_at(s, i, l);
            &&& i + l <= s.len()
            &&& utf8_encode(c) == s.subrange(i, i + l)
            &&& c <= 0x10FFFF
            &&& !(0xD800 <= c <= 0xDFFF)
            &&& (l <= 3) == (c < 0x10000)
            &&& (l == 1) == (c < 0x80)
        }),
{
    let l = utf8_len(s, i)->0;
    let b0 = s[i];
    if l == 1 {
        assert(utf8_encode(b0 as u32) =~= s.subrange(i, i + 1));
    } else if l == 2 {
        let b1 = s[i + 1];
        let c = dec8_at(s, i, l);
        assert(0xC2 <= b0 <= 0xDF && 0x80 <= b1 <= 0xBF ==> ({
            let c = (((b0 & 0x1F) as u32) << 6u32) | ((b1 & 0x3F) as u32);
            0x80 <= c < 0x800 && (0xC0 + c / 64) as u8 == b0 && (0x80 + c % 64) as u8 == b1
        })) by (bit_vector);
        assert(utf8_encode(c) =~= s.subrange(i, i + 2));
    } else if l == 3 {
        let b1 = s[i + 1];
        let b2 = s[i + 2];
        let c = dec8_at(s, i, l);
        assert(0xE0 <= b0 <= 0xEF && 0x80 <= b1 <= 0xBF && 0x80 <= b2 <= 0xBF ==> ({
            let c = (((b0 & 0x0F) as u32) << 12u32) | (((b1 & 0x3F) as u32) << 6u32) | ((b2 & 0x3F) as u32);
            c < 0x10000 && (0xE0 + c / 4096) as u8 == b0 && (0x80 + (c / 64) % 64) as u8 == b1 && (0x80 + c % 64) as u8
                == b2 && (b0 == 0xE0 ==> (b1 >= 0xA0 <==> c >= 0x800)) && (b0 != 0xE0 ==> c >= 0x1000) && (b0
                == 0xED ==> (b1 <= 0x9F <==> c < 0xD800)) && (b0 != 0xED ==> !(0xD800 <= c <= 0xDFFF))
        })) by (bit_vector);
        assert(utf8_encode(c) =~= s.subrange(i, i + 3));
    } else {
        let b1 = s[i + 1];
        let b2 = s[i + 2];
        let b3 = s[i + 3];
        let c = dec8_at(s, i, l);
        assert(0xF0 <= b0 <= 0xF4 && 0x80 <= b1 <= 0xBF && 0x80 <= b2 <= 0xBF && 0x80 <= b3 <= 0xBF ==> ({
            let c = (((b0 & 0x07) as u32) << 18u32) | (((b1 & 0x3F) as u32) << 12u32) | (((b2 & 0x3F) as u32) << 6u32)
                | ((b3 & 0x3F) as u32);
            (0xF0 + c / 262144) as u8 == b0 && (0x80 + (c / 4096) % 64) as u8 == b1 && (0x80 + (c / 64) % 64) as u8
                == b2 && (0x80 + c % 64) as u8 == b3 && (b0 == 0xF0 ==> (b1 >= 0x90 <==> c >= 0x10000)) && (b0
                != 0xF0 ==> c >= 0x40000) && (b0 == 0xF4 ==> (b1 <= 0x8F <==> c <= 0x10FFFF)) && (b0 != 0xF4
                ==> c < 0x100000)
        })) by (bit_vector);
        assert(utf8_encode(c) =~= s.subrange(i, i + 4));
    }
}

/// A well-formed UTF-16 sequence is a scalar, and encoding it again gives
/// the same units.
pub proof fn lemma_dec16_roundtrip(s: Seq<u16>, i: int)
    requires
        0 <= i < s.len(),
        utf16_len(s, i) is Some,
    ensures
        ({
            let l = utf16_len(s, i)->0;
            let c = dec16_at(s, i, l);
            &&& i + l <= s.len()
            &&& enc16(c) == s.subrange(i, i + l)
            &&& c <= 0x10FFFF
            &&& !(0xD800 <= c <= 0xDFFF)
            &&& (l == 2) == (c >= 0x10000)
        }),
{
    let l = utf16_len(s, i)->0;
    if l == 1 {
        assert(enc16(s[i] as u32) =~= s.subrange(i, i + 1));
    } else {
        let c = dec16_at(s, i, l);
        assert(enc16(c) =~= s.subrange(i, i + 2));
    }
}

// ---------------------------------------------------------------------------
// Lengths
// ---------------------------------------------------------------------------

pub proof fn lemma_l1_len(s: Seq<u8>, i: int)
    ensures
        l1to8(s, i).len() == cnt_l1(s, i),
    decreases s.len() - i,
{
    if 0 <= i < s.len() {
        lemma_l1_len(s, i + 1);
    }
}

/// `cnt8` over a sequence of length `l` at `i`: the lead counts, the
/// continuation bytes do not.
proof fn lemma_cnt8_step(s: Seq<u8>, i: int)
    requires
        0 <= i < s.len(),
        utf8_len(s, i) is Some,
    ensures
        cnt8(s, i) == (if utf8_len(s, i)->0 == 4 { 2nat } else { 1nat }) + cnt8(s, i + utf8_len(s, i)->0),
        cnt8l1(s, i) == 1 + cnt8l1(s, i + utf8_len(s, i)->0),
{
    let l = utf8_len(s, i)->0;
    reveal_with_fuel(cnt8, 5);
    reveal_with_fuel(cnt8l1, 5);
}

pub proof fn lemma_u8to16_len(s: Seq<u8>, i: int)
    requires
        0 <= i,
        utf8_from(s, i),
    ensures
        u8to16(s, i).len() == cnt8(s, i),
    decreases s.len() - i,
{
    if i < s.len() {
        let l = utf8_len(s, i)->0;
        lemma_dec8_roundtrip(s, i);
        lemma_cnt8_step(s, i);
        lemma_u8to16_len(s, i + l);
    }
}

pub proof fn lemma_u8tol1_len(s: Seq<u8>, i: int)
    requires
        0 <= i,
        utf8_from(s, i),
    ensures
        u8tol1(s, i).len() == cnt8l1(s, i),
    decreases s.len() - i,
{
    if i < s.len() {
        let l = utf8_len(s, i)->0;
        lemma_cnt8_step(s, i);
        lemma_u8tol1_len(s, i + l);
    }
}

/// The UTF-8 written for a UTF-16 text never exceeds `cnt16`, and is
/// exactly that for a well-formed text.
pub proof fn lemma_u16to8_len(s: Seq<u16>, i: int)
    requires
        0 <= i,
    ensures
        u16to8(s, i).len() <= cnt16(s, i),
        utf16_from(s, i) ==> u16to8(s, i).len() == cnt16(s, i),
    decreases s.len() - i,
{
    if i < s.len() {
        match utf16_len(s, i) {
            Some(l) => {
                lemma_u16to8_len(s, i + l);
                reveal_with_fuel(cnt16, 3);
                let c = dec16_at(s, i, l);
                if l == 2 {
                    assert(c >= 0x10000);
                }
            },
            None => {
                lemma_cnt16_nonneg(s, i);
            },
        }
    }
}

proof fn lemma_cnt16_nonneg(s: Seq<u16>, i: int)
    ensures
        cnt16(s, i) >= 0,
{
}

// ---------------------------------------------------------------------------
// Runs of ASCII
// ---------------------------------------------------------------------------

/// A run of `k` ASCII bytes at `i` widens one unit per byte.
pub proof fn lemma_ascii_u8to16(s: Seq<u8>, i: int, k: int)
    requires
        0 <= i,
        0 <= k,
        i + k <= s.len(),
        ascii(s, i, i + k),
    ensures
        u8to16(s, i) == Seq::new(k as nat, |t: int| s[i + t] as u16) + u8to16(s, i + k),
        utf8_from(s, i) == utf8_from(s, i + k),
        cnt8(s, i) == k + cnt8(s, i + k),
        latin1_from(s, i) == latin1_from(s, i + k),
        u8tol1(s, i) == s.subrange(i, i + k) + u8tol1(s, i + k),
        cnt8l1(s, i) == k + cnt8l1(s, i + k),
    decreases k,
{
    if k > 0 {
        lemma_ascii_u8to16(s, i + 1, k - 1);
        assert(s[i] < 0x80);
        assert(u8to16(s, i) == seq![s[i] as u16] + u8to16(s, i + 1));
        assert(Seq::new(k as nat, |t: int| s[i + t] as u16) =~= seq![s[i] as u16] + Seq::new((k - 1) as nat, |t: int|
            s[i + 1 + t] as u16));
        assert(s.subrange(i, i + k) =~= seq![s[i]] + s.subrange(i + 1, i + k));
    } else {
        assert(Seq::new(0, |t: int| s[i + t] as u16) =~= Seq::<u16>::empty());
        assert(s.subrange(i, i) =~= Seq::<u8>::empty());
    }
}

/// A run of `k` ASCII bytes at `i` of Latin-1 is copied as it is.
pub proof fn lemma_ascii_l1to8(s: Seq<u8>, i: int, k: int)
    requires
        0 <= i,
        0 <= k,
        i + k <= s.len(),
        ascii(s, i, i + k),
    ensures
        l1to8(s, i) == s.subrange(i, i + k) + l1to8(s, i + k),
        cnt_l1(s, i) == k + cnt_l1(s, i + k),
    decreases k,
{
    if k > 0 {
        lemma_ascii_l1to8(s, i + 1, k - 1);
        assert(s[i] < 0x80);
        assert(utf8_encode(s[i] as u32) =~= seq![s[i]]);
        assert(s.subrange(i, i + k) =~= seq![s[i]] + s.subrange(i + 1, i + k));
    } else {
        assert(s.subrange(i, i) =~= Seq::<u8>::empty());
    }
}

/// A run of `k` ASCII units at `i` narrows one byte per unit.
pub proof fn lemma_ascii_u16to8(s: Seq<u16>, i: int, k: int)
    requires
        0 <= i,
        0 <= k,
        i + k <= s.len(),
        ascii16(s, i, i + k),
    ensures
        u16to8(s, i) == Seq::new(k as nat, |t: int| s[i + t] as u8) + u16to8(s, i + k),
        utf16_from(s, i) == utf16_from(s, i + k),
        cnt16(s, i) == k + cnt16(s, i + k),
    decreases k,
{
    if k > 0 {
        lemma_ascii_u16to8(s, i + 1, k - 1);
        assert(s[i] < 0x80);
        assert(utf8_encode(s[i] as u32) =~= seq![s[i] as u8]);
        assert(Seq::new(k as nat, |t: int| s[i + t] as u8) =~= seq![s[i] as u8] + Seq::new((k - 1) as nat, |t: int|
            s[i + 1 + t] as u8));
    } else {
        assert(Seq::new(0, |t: int| s[i + t] as u8) =~= Seq::<u8>::empty());
    }
}

} // verus!

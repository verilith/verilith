//! Verified primitives of the recovering parser (`recover`, libxml2's
//! parser.c, which runs only after the verified parser has rejected a
//! document): reading a byte past the end, UTF-8 in and out, and the
//! character classes of XML 1.0 Fifth Edition.
//!
//! Each function does what libxml2's C does, and its contract says how
//! that relates to the specification in `chars` and verilith-core: where
//! libxml2 agrees with the spec, the contract is equality; where it does
//! not (`utf8_char` takes lead bytes F8 to FB), the contract says where.
use crate::chars::*;
#[cfg(verus_keep_ghost)]
use crate::enc::cat;
#[cfg(verus_keep_ghost)]
use crate::spec::{latin1_dec, unit16, utf16_dec};
use crate::ent::push_utf8;
#[cfg(verus_keep_ghost)]
use verilith_core::utf8::{byte_in, utf8_encode, utf8_len};
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// The byte at `i`, 0 past the end (libxml2's buffers end in a NUL).
pub open spec fn at_spec(b: Seq<u8>, i: int) -> u8 {
    if 0 <= i < b.len() { b[i] } else { 0 }
}

/// A byte of `b`, 0 past its end.
#[inline]
pub fn at(b: &[u8], i: usize) -> (r: u8)
    ensures
        r == at_spec(b@, i as int),
{
    if i < b.len() { b[i] } else { 0 }
}

/// The byte `k` after `i`, 0 past the end (and where `i + k` would not
/// fit in a `usize`, which is past the end of any slice).
#[inline]
pub fn at_off(b: &[u8], i: usize, k: usize) -> (r: u8)
    ensures
        r == at_spec(b@, i + k),
{
    if i < b.len() && k < b.len() - i { b[i + k] } else { 0 }
}

/// `IS_BLANK_CH`.
#[inline]
pub fn blank(c: u8) -> (r: bool)
    ensures
        r == is_ws(c),
{
    c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D
}

/// `xmlCopyCharMultiByte`, appended: the UTF-8 encoding of `c`, nothing
/// for a value above U+10FFFF.
pub fn push_char(out: &mut Vec<u8>, c: u32)
    ensures
        c <= 0x10FFFF ==> final(out)@ == old(out)@ + utf8_encode(c),
        c > 0x10FFFF ==> final(out)@ == old(out)@,
{
    if c <= 0x10FFFF {
        push_utf8(out, c);
    }
}

/// The byte is a continuation byte.
proof fn lemma_cont(d: u8)
    ensures
        (d & 0xC0 == 0x80) == (0x80 <= d <= 0xBF),
        0x80 <= d <= 0xBF ==> (d & 0x3F) as int == d as int - 0x80,
{
    assert((d & 0xC0 == 0x80) == (0x80 <= d && d <= 0xBF)) by (bit_vector);
    assert(0x80 <= d && d <= 0xBF ==> (d & 0x3F) == d - 0x80) by (bit_vector);
}

proof fn lemma_lead(c: u32)
    requires
        0x80 <= c <= 0xFF,
    ensures
        0xC0 <= c <= 0xDF ==> (c & 0x1F) as int == c as int - 0xC0,
        0xE0 <= c <= 0xEF ==> (c & 0xF) as int == c as int - 0xE0,
        0xF0 <= c <= 0xF7 ==> (c & 0x7) as int == c as int - 0xF0,
{
    assert(0xC0 <= c && c <= 0xDF ==> (c & 0x1F) == c - 0xC0) by (bit_vector);
    assert(0xE0 <= c && c <= 0xEF ==> (c & 0xF) == c - 0xE0) by (bit_vector);
    assert(0xF0 <= c && c <= 0xF7 ==> (c & 0x7) == c - 0xF0) by (bit_vector);
}

proof fn lemma_or2(a: u32, b: u32)
    requires
        a < 32,
        b < 64,
    ensures
        (a << 6u32) | b == a * 64 + b,
{
    assert((a << 6u32) | b == a * 64 + b) by (bit_vector)
        requires
            a < 32 && b < 64,
    ;
}

proof fn lemma_or3(a: u32, b: u32, d: u32)
    requires
        a < 16,
        b < 64,
        d < 64,
    ensures
        (a << 12u32) | (b << 6u32) | d == a * 4096 + b * 64 + d,
{
    assert((a << 12u32) | (b << 6u32) | d == a * 4096 + b * 64 + d) by (bit_vector)
        requires
            a < 16 && b < 64 && d < 64,
    ;
}

proof fn lemma_or4(a: u32, b: u32, d: u32, e: u32)
    requires
        a < 8,
        b < 64,
        d < 64,
        e < 64,
    ensures
        (a << 18u32) | (b << 12u32) | (d << 6u32) | e == a * 262144 + b * 4096 + d * 64 + e,
{
    assert((a << 18u32) | (b << 12u32) | (d << 6u32) | e == a * 262144 + b * 4096 + d * 64 + e) by (bit_vector)
        requires
            a < 8 && b < 64 && d < 64 && e < 64,
    ;
}

/// `xmlGetUTF8Char`: the character at `i` and its length, read from at
/// most `avail` bytes; `None` for a sequence libxml2 does not take.
///
/// Below lead byte F8 it reads UTF-8 exactly as the spec does (`cp_at`,
/// Unicode Table 3-7), when the sequence fits in `avail`. Lead bytes F8
/// to FB are taken as F0 to F3 are, as libxml2 does (it masks the lead
/// byte with 7). Past the end it reads NUL, as one byte.
pub fn utf8_char(s: &[u8], i: usize, avail: usize) -> (r: Option<(u32, usize)>)
    ensures
        match r {
            Some((v, l)) => 1 <= l <= 4 && l <= avail && v <= 0x10FFFF && (l == 1 <==> v < 0x80) && (l == 1 ==> v
                == at_spec(s@, i as int)) && (l >= 2 ==> i + l <= s@.len()),
            None => true,
        },
        i < s@.len() && s@[i as int] < 0xF8 ==> match cp_at(s@, i as int) {
            Some((v, l)) => if l <= avail && i + l <= s@.len() {
                r == Some((v as u32, l as usize))
            } else {
                r is None
            },
            None => r is None,
        },
{
    let c = at(s, i) as u32;
    if avail < 1 {
        return None;
    }
    if c < 0x80 {
        return Some((c, 1));
    }
    let d1 = at_off(s, i, 1);
    proof {
        lemma_cont(d1);
        lemma_lead(c);
    }
    if avail < 2 || (d1 & 0xC0) != 0x80 {
        return None;
    }
    if c < 0xE0 {
        if c < 0xC2 {
            return None;
        }
        proof {
            lemma_or2(c & 0x1F, d1 as u32 & 0x3F);
            assert((d1 as u32 & 0x3F) == (d1 & 0x3F) as u32) by (bit_vector);
        }
        return Some((((c & 0x1F) << 6) | (d1 as u32 & 0x3F), 2));
    }
    let d2 = at_off(s, i, 2);
    proof {
        lemma_cont(d2);
    }
    if avail < 3 || (d2 & 0xC0) != 0x80 {
        return None;
    }
    if c < 0xF0 {
        proof {
            lemma_or3(c & 0xF, d1 as u32 & 0x3F, d2 as u32 & 0x3F);
            assert((d1 as u32 & 0x3F) == (d1 & 0x3F) as u32) by (bit_vector);
            assert((d2 as u32 & 0x3F) == (d2 & 0x3F) as u32) by (bit_vector);
        }
        let v = ((c & 0xF) << 12) | ((d1 as u32 & 0x3F) << 6) | (d2 as u32 & 0x3F);
        if v < 0x800 || (0xD800 <= v && v < 0xE000) {
            return None;
        }
        return Some((v, 3));
    }
    let d3 = at_off(s, i, 3);
    proof {
        lemma_cont(d3);
    }
    if avail < 4 || (d3 & 0xC0) != 0x80 {
        return None;
    }
    proof {
        assert((c & 0x7) < 8) by (bit_vector);
        lemma_or4(c & 0x7, d1 as u32 & 0x3F, d2 as u32 & 0x3F, d3 as u32 & 0x3F);
        assert((d1 as u32 & 0x3F) == (d1 & 0x3F) as u32) by (bit_vector);
        assert((d2 as u32 & 0x3F) == (d2 & 0x3F) as u32) by (bit_vector);
        assert((d3 as u32 & 0x3F) == (d3 & 0x3F) as u32) by (bit_vector);
    }
    let v = ((c & 0x7) << 18) | ((d1 as u32 & 0x3F) << 12) | ((d2 as u32 & 0x3F) << 6) | (d3 as u32 & 0x3F);
    if !(0x10000 <= v && v < 0x110000) {
        return None;
    }
    Some((v, 4))
}

/// `xmlStringCurrentChar` over a NUL-terminated string: the character at
/// `i` and its length; (0, 4) where no character is.
pub fn string_char(s: &[u8], i: usize) -> (r: (u32, usize))
    ensures
        1 <= r.1 <= 4,
        r.0 <= 0x10FFFF,
{
    match utf8_char(s, i, 4) {
        Some(r) => r,
        None => (0, 4),
    }
}

/// `IS_CHAR`: the spec's `Char`.
pub fn is_xml_char(c: u32) -> (r: bool)
    ensures
        r == is_char(c as int),
{
    if c < 0x100 {
        c == 0x9 || c == 0xA || c == 0xD || c >= 0x20
    } else {
        (0x100 <= c && c <= 0xD7FF) || (0xE000 <= c && c <= 0xFFFD) || (0x10000 <= c && c <= 0x10FFFF)
    }
}

/// `xmlIsNameStartChar` without XML_PARSE_OLD10: the spec's
/// `NameStartChar`.
pub fn name_start_new(c: u32) -> (r: bool)
    ensures
        r == name_start_cp(c as int),
{
    c != 0x20 && c != 0x3E && c != 0x2F && ((0x61 <= c && c <= 0x7A) || (0x41 <= c && c <= 0x5A) || c == 0x5F
        || c == 0x3A || (0xC0 <= c && c <= 0xD6) || (0xD8 <= c && c <= 0xF6) || (0xF8 <= c && c <= 0x2FF) || (0x370
        <= c && c <= 0x37D) || (0x37F <= c && c <= 0x1FFF) || (0x200C <= c && c <= 0x200D) || (0x2070 <= c && c
        <= 0x218F) || (0x2C00 <= c && c <= 0x2FEF) || (0x3001 <= c && c <= 0xD7FF) || (0xF900 <= c && c <= 0xFDCF)
        || (0xFDF0 <= c && c <= 0xFFFD) || (0x10000 <= c && c <= 0xEFFFF))
}

/// `xmlIsNameChar` without XML_PARSE_OLD10: the spec's `NameChar`.
pub fn name_char_new(c: u32) -> (r: bool)
    ensures
        r == name_cp(c as int),
{
    name_start_new(c) || (c != 0x20 && ((0x30 <= c && c <= 0x39) || c == 0x2D || c == 0x2E || c == 0xB7 || (0x300
        <= c && c <= 0x36F) || (0x203F <= c && c <= 0x2040)))
}

/// `IS_PUBIDCHAR_CH`: the spec's `PubidChar`.
pub fn is_pubid_char(c: u8) -> (r: bool)
    ensures
        r == pubid_char(c),
{
    c == 0x20 || c == 0x0D || c == 0x0A || (0x61 <= c && c <= 0x7A) || (0x41 <= c && c <= 0x5A) || (0x30 <= c && c
        <= 0x39) || c == 0x2D || c == 0x27 || c == 0x28 || c == 0x29 || c == 0x2B || c == 0x2C || c == 0x2E || c
        == 0x2F || c == 0x3A || c == 0x3D || c == 0x3F || c == 0x3B || c == 0x21 || c == 0x2A || c == 0x23 || c
        == 0x40 || c == 0x24 || c == 0x5F || c == 0x25
}

// ---------------------------------------------------------------------------
// The built-in decoders (encoding.c's UTF16LEToUTF8, UTF16BEToUTF8,
// latin1ToUTF8, asciiToAscii), one chunk at a time
// ---------------------------------------------------------------------------

/// A chunk was converted whole (`XML_ENC_ERR_SUCCESS`), stopped for room
/// (`XML_ENC_ERR_SPACE`), or stopped at bytes that are not the encoding
/// (`XML_ENC_ERR_INPUT`).
pub const CHUNK_OK: u8 = 0;
pub const CHUNK_SPACE: u8 = 1;
pub const CHUNK_INPUT: u8 = 2;

/// The UTF-8 bytes of `c` appended, if `room` allows; `room` less them.
pub fn put(out: &mut Vec<u8>, c: u32, room: &mut usize) -> (r: bool)
    requires
        c <= 0x10FFFF,
    ensures
        r ==> final(out)@ == old(out)@ + utf8_encode(c) && *final(room) == *old(room) - utf8_encode(c).len(),
        !r ==> final(out)@ == old(out)@ && *final(room) == *old(room) && *old(room) < utf8_encode(c).len(),
{
    let n: usize = if c < 0x80 { 1 } else if c < 0x800 { 2 } else if c < 0x10000 { 3 } else { 4 };
    if *room < n {
        return false;
    }
    *room = *room - n;
    push_utf8(out, c);
    true
}

/// The 16-bit unit at `i`.
fn unit(inp: &[u8], i: usize, le: bool) -> (r: u32)
    requires
        i + 2 <= inp@.len(),
    ensures
        r as int == unit16(inp@, i as int, le),
        r <= 0xFFFF,
{
    let x0 = inp[i] as u32;
    let x1 = inp[i + 1] as u32;
    if le { x0 + x1 * 256 } else { x0 * 256 + x1 }
}


proof fn lemma_cat_assoc(d: Seq<u8>, e: Seq<u8>, x: Option<Seq<u8>>)
    ensures
        cat(d, cat(e, x)) == cat(d + e, x),
{
    match x {
        Some(t) => assert(d + (e + t) =~= (d + e) + t),
        None => {},
    }
}

/// A unit that is not a surrogate decodes to itself.
proof fn lemma_utf16_one(b: Seq<u8>, i: int, le: bool)
    requires
        0 <= i,
        i + 2 <= b.len(),
        !(0xD800 <= unit16(b, i, le) <= 0xDFFF),
    ensures
        utf16_dec(b, i, le) == cat(utf8_encode(unit16(b, i, le) as u32), utf16_dec(b, i + 2, le)),
{
}

/// A surrogate pair decodes to the code point it stands for.
proof fn lemma_utf16_pair(b: Seq<u8>, i: int, le: bool)
    requires
        0 <= i,
        i + 4 <= b.len(),
        0xD800 <= unit16(b, i, le) <= 0xDBFF,
        0xDC00 <= unit16(b, i + 2, le) <= 0xDFFF,
    ensures
        utf16_dec(b, i, le) == cat(
            utf8_encode((0x10000 + (unit16(b, i, le) - 0xD800) * 1024 + (unit16(b, i + 2, le) - 0xDC00)) as u32),
            utf16_dec(b, i + 4, le),
        ),
{
}

/// A unit that is not the start of a well-formed sequence, or is cut off.
proof fn lemma_utf16_bad(b: Seq<u8>, i: int, le: bool)
    requires
        0 <= i,
        i + 2 <= b.len(),
        (0xDC00 <= unit16(b, i, le) <= 0xDFFF) || (0xD800 <= unit16(b, i, le) <= 0xDBFF && i + 4 <= b.len() && !(
        0xDC00 <= unit16(b, i + 2, le) <= 0xDFFF)),
    ensures
        utf16_dec(b, i, le) is None,
{
}

/// The bytes past the last whole unit.
proof fn lemma_utf16_tail(b: Seq<u8>, i: int, le: bool)
    requires
        0 <= i < b.len(),
        i + 2 > b.len(),
    ensures
        utf16_dec(b, i, le) is None,
{
}

/// UTF-16 (little-endian if `le`) to UTF-8, into at most `room` bytes of
/// `out`: the bytes read and how the chunk ended. What it writes is the
/// spec's decoding (`utf16_dec`) of what it read; a chunk that ends at
/// bytes that are not UTF-16 (`CHUNK_INPUT`) is one the spec does not
/// decode; one read to the end with success is the spec's decoding of
/// the whole. A high surrogate cut off at the end is left unread.
pub fn chunk_utf16(le: bool, inp: &[u8], out: &mut Vec<u8>, room: usize) -> (r: (usize, u8))
    ensures
        r.0 <= inp@.len(),
        r.1 <= CHUNK_INPUT,
        old(out)@.len() <= final(out)@.len() <= old(out)@.len() + room,
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        utf16_dec(inp@, 0, le) == cat(final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int), utf16_dec(inp@, r.0 as int, le)),
        r.1 == CHUNK_INPUT ==> utf16_dec(inp@, r.0 as int, le) is None,
        r.1 == CHUNK_OK ==> inp@.len() - r.0 <= 3,
{
    hide(utf16_dec);
    hide(utf8_encode);
    let n = inp.len();
    let end = n - n % 2;
    let mut i: usize = 0;
    let mut left = room;
    let ghost o = old(out)@;
    proof {
        assert(out@.subrange(o.len() as int, out@.len() as int) =~= Seq::<u8>::empty());
        match utf16_dec(inp@, 0, le) {
            Some(t) => assert(Seq::<u8>::empty() + t =~= t),
            None => {},
        }
    }
    while i < end
        invariant
            i <= end <= n == inp@.len(),
            end % 2 == 0,
            n - end <= 1,
            i % 2 == 0,
            o == old(out)@,
            o.len() <= out@.len(),
            out@.len() + left == o.len() + room,
            out@.subrange(0, o.len() as int) == o,
            utf16_dec(inp@, 0, le) == cat(out@.subrange(o.len() as int, out@.len() as int), utf16_dec(inp@, i as int, le)),
        decreases end - i,
    {
        let ghost before = out@;
        let c = unit(inp, i, le);
        if !(0xD800 <= c && c <= 0xDFFF) {
            if !put(out, c, &mut left) {
                return (i, CHUNK_SPACE);
            }
            proof {
                let d = before.subrange(o.len() as int, before.len() as int);
                assert(out@.subrange(o.len() as int, out@.len() as int) =~= d + utf8_encode(c));
                assert(out@.subrange(0, o.len() as int) =~= before.subrange(0, o.len() as int));
                lemma_utf16_one(inp@, i as int, le);
                lemma_cat_assoc(d, utf8_encode(c), utf16_dec(inp@, i + 2, le));
            }
            i = i + 2;
        } else {
            if c > 0xDBFF {
                proof {
                    lemma_utf16_bad(inp@, i as int, le);
                }
                return (i, CHUNK_INPUT);
            }
            if end - i < 4 {
                return (i, CHUNK_OK);
            }
            let d = unit(inp, i + 2, le);
            if !(0xDC00 <= d && d <= 0xDFFF) {
                proof {
                    lemma_utf16_bad(inp@, i as int, le);
                }
                return (i, CHUNK_INPUT);
            }
            let cp = (c - 0xD800) * 1024 + (d - 0xDC00) + 0x10000;
            if !put(out, cp, &mut left) {
                return (i, CHUNK_SPACE);
            }
            proof {
                let dd = before.subrange(o.len() as int, before.len() as int);
                assert(out@.subrange(o.len() as int, out@.len() as int) =~= dd + utf8_encode(cp));
                assert(out@.subrange(0, o.len() as int) =~= before.subrange(0, o.len() as int));
                lemma_utf16_pair(inp@, i as int, le);
                lemma_cat_assoc(dd, utf8_encode(cp), utf16_dec(inp@, i + 4, le));
            }
            i = i + 4;
        }
    }
    (i, CHUNK_OK)
}

/// ISO-8859-1 to UTF-8, into at most `room` bytes of `out`: what it
/// writes is the spec's decoding (`latin1_dec`) of what it read.
pub fn chunk_latin1(inp: &[u8], out: &mut Vec<u8>, room: usize) -> (r: (usize, u8))
    ensures
        r.0 <= inp@.len(),
        r.1 == CHUNK_OK || r.1 == CHUNK_SPACE,
        r.1 == CHUNK_OK ==> r.0 == inp@.len(),
        old(out)@.len() <= final(out)@.len() <= old(out)@.len() + room,
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        latin1_dec(inp@, 0) == final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int) + latin1_dec(inp@, r.0 as int),
{
    let n = inp.len();
    let mut i: usize = 0;
    let mut left = room;
    let ghost o = old(out)@;
    proof {
        assert(out@.subrange(o.len() as int, out@.len() as int) + latin1_dec(inp@, 0) =~= latin1_dec(inp@, 0));
    }
    while i < n
        invariant
            i <= n == inp@.len(),
            o == old(out)@,
            o.len() <= out@.len(),
            out@.len() + left == o.len() + room,
            out@.subrange(0, o.len() as int) == o,
            latin1_dec(inp@, 0) == out@.subrange(o.len() as int, out@.len() as int) + latin1_dec(inp@, i as int),
        decreases n - i,
    {
        let ghost before = out@;
        let b = inp[i] as u32;
        if !put(out, b, &mut left) {
            return (i, CHUNK_SPACE);
        }
        proof {
            let d = before.subrange(o.len() as int, before.len() as int);
            assert(out@.subrange(o.len() as int, out@.len() as int) =~= d + utf8_encode(b));
            assert(out@.subrange(0, o.len() as int) =~= before.subrange(0, o.len() as int));
            assert(d + (utf8_encode(b) + latin1_dec(inp@, i + 1)) =~= (d + utf8_encode(b)) + latin1_dec(inp@, i + 1));
        }
        i = i + 1;
    }
    (i, CHUNK_OK)
}

/// US-ASCII, checked and copied, into at most `room` bytes of `out`
/// (`asciiToAscii` checks the room first, then the bytes): what it
/// copies is ASCII, and it stops for input only at a byte above 0x7F.
pub fn chunk_ascii(inp: &[u8], out: &mut Vec<u8>, room: usize) -> (r: (usize, u8))
    ensures
        r.0 <= inp@.len(),
        r.0 <= room,
        r.1 <= CHUNK_INPUT,
        r.1 == CHUNK_OK ==> r.0 == inp@.len(),
        r.1 == CHUNK_INPUT ==> r.0 < inp@.len() && inp@[r.0 as int] >= 0x80,
        final(out)@ == old(out)@ + inp@.subrange(0, r.0 as int),
        forall|k: int| 0 <= k < r.0 ==> #[trigger] inp@[k] < 0x80,
{
    let n = inp.len();
    let take = if room < n { room } else { n };
    let mut i: usize = 0;
    let ghost o = old(out)@;
    while i < take
        invariant
            i <= take <= n == inp@.len(),
            take <= room,
            take == n || take == room,
            o == old(out)@,
            out@ == o + inp@.subrange(0, i as int),
            forall|k: int| 0 <= k < i ==> #[trigger] inp@[k] < 0x80,
        decreases take - i,
    {
        if inp[i] >= 0x80 {
            return (i, CHUNK_INPUT);
        }
        out.push(inp[i]);
        proof {
            assert(out@ =~= o + inp@.subrange(0, i + 1));
        }
        i = i + 1;
    }
    (i, if take < n { CHUNK_SPACE } else { CHUNK_OK })
}

// ---------------------------------------------------------------------------
// Small helpers of the recovering parser
// ---------------------------------------------------------------------------

/// `xmlUTF8MultibyteLen`'s classification of the sequence `c c1 c2 c3`
/// (lead byte `c` at least 0x80): its length when it is UTF-8 and a
/// `Char`, 33 for U+FFFE and U+FFFF (length 3, not `Char`s), 0 when it is
/// not UTF-8. Exactly the spec's `utf8_len` and `char_seq_ok`.
pub fn multibyte_len(c: u8, c1: u8, c2: u8, c3: u8) -> (r: usize)
    ensures
        c >= 0x80 ==> ({
            let q = seq![c, c1, c2, c3];
            match utf8_len(q, 0) {
                Some(l) => if char_seq_ok(q, 0, l) { r == l } else { r == 33 },
                None => r == 0,
            }
        }),
{
    let ghost q = seq![c, c1, c2, c3];
    proof {
        lemma_cont(c1);
        lemma_cont(c2);
        lemma_cont(c3);
        assert(q[0] == c && q[1] == c1 && q[2] == c2 && q[3] == c3);
    }
    if c1 & 0xC0 != 0x80 {
        return 0;
    }
    if c < 0xE0 {
        if c < 0xC2 {
            return 0;
        }
        return 2;
    }
    if c2 & 0xC0 != 0x80 {
        return 0;
    }
    if c < 0xF0 {
        if c == 0xE0 {
            if c1 < 0xA0 {
                return 0;
            }
        } else if c == 0xED {
            if c1 >= 0xA0 {
                return 0;
            }
        } else if c == 0xEF && c1 == 0xBF && c2 >= 0xBE {
            return 33;
        }
        return 3;
    }
    if c3 & 0xC0 != 0x80 {
        return 0;
    }
    if c == 0xF0 {
        if c1 < 0x90 {
            return 0;
        }
    } else if c >= 0xF4 && (c > 0xF4 || c1 >= 0x90) {
        return 0;
    }
    4
}

/// `IS_BYTE_CHAR`: a byte that is not one of the C0 controls a document
/// cannot hold.
pub fn is_byte_char(c: u8) -> (r: bool)
    ensures
        r == !bad_byte(c),
{
    c >= 0x20 || c == 0x09 || c == 0x0A || c == 0x0D
}

/// The bytes the fast character data loop takes (`test_char_data`).
pub fn test_char_data(c: u8) -> (r: bool)
    ensures
        r ==> !bad_byte(c) && c < 0x80 && c != 0x26 && c != 0x3C,
{
    c == 0x09 || (0x20 <= c && c <= 0x7F && c != 0x26 && c != 0x3C && c != 0x5D)
}

/// `%02X`.
pub fn hex2(v: u8) -> (r: Vec<u8>)
    ensures
        r@.len() == 2,
{
    let hi = v / 16;
    let lo = v % 16;
    let mut out = Vec::new();
    out.push(if hi < 10 { 0x30 + hi } else { 0x37 + hi });
    out.push(if lo < 10 { 0x30 + lo } else { 0x37 + lo });
    out
}

/// `xmlGrowCapacity(cap, _, min, max)`: the new capacity, at most `max`,
/// more than `cap`; `None` at the limit.
pub fn grow_capacity_min(cap: usize, min: usize, max: usize) -> (r: Option<usize>)
    ensures
        cap == 0 ==> r == Some(min),
        cap != 0 ==> match r {
            Some(n) => cap < n <= max,
            None => cap >= max,
        },
{
    if cap == 0 {
        return Some(min);
    }
    if cap >= max {
        return None;
    }
    let extra = cap / 2 + cap % 2;
    if cap > max - extra {
        return Some(max);
    }
    Some(cap + extra)
}

/// `xmlGrowCapacity(cap, 1, 1, max)`.
pub fn grow_capacity(cap: usize, max: usize) -> (r: Option<usize>)
    ensures
        cap == 0 ==> r == Some(1usize),
        cap != 0 ==> match r {
            Some(n) => cap < n <= max,
            None => cap >= max,
        },
{
    grow_capacity_min(cap, 1, max)
}

/// The first `n` bytes of `s` (`%.ns`).
pub fn prefix_n(s: &[u8], n: usize) -> (r: &[u8])
    ensures
        r@ == if s@.len() > n { s@.subrange(0, n as int) } else { s@ },
{
    if s.len() > n {
        slice_subrange(s, 0, n)
    } else {
        s
    }
}

/// `xmlAttrNormalizeSpace`: leading and trailing spaces dropped, each run
/// of spaces inside made one (the non-CDATA normalization of §3.3.3, on a
/// value whose white space is already spaces).
pub fn attr_normalize_space(v: &Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@.len() <= v@.len(),
{
    let n = v.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n && v[i] == 0x20
        invariant
            i <= n == v@.len(),
            out@.len() == 0,
        decreases n - i,
    {
        i = i + 1;
    }
    let ghost i0 = i;
    while i < n
        invariant
            i0 <= i <= n == v@.len(),
            out@.len() <= i - i0,
        decreases n - i,
    {
        if v[i] == 0x20 {
            let ghost s0 = i;
            i = i + 1;
            while i < n && v[i] == 0x20
                invariant
                    s0 < i,
                    i0 <= i <= n == v@.len(),
                    out@.len() < i - i0,
                decreases n - i,
            {
                i = i + 1;
            }
            if i < n {
                out.push(0x20);
            }
        } else {
            out.push(v[i]);
            i = i + 1;
        }
    }
    out
}

/// `xmlSplitQName3`: (prefix, local) when `name` is `p:l` with both
/// non-empty, split at the first colon.
pub fn split_qname3(name: &[u8]) -> (r: Option<(&[u8], &[u8])>)
    ensures
        match r {
            Some((p, l)) => p@.len() > 0 && l@.len() > 0 && name@ == p@ + seq![0x3Au8] + l@ && !p@.contains(0x3Au8),
            None => true,
        },
{
    let n = name.len();
    if n > 0 && name[0] == 0x3A {
        return None;
    }
    let mut i: usize = 0;
    while i < n && name[i] != 0x3A
        invariant
            i <= n == name@.len(),
            forall|k: int| 0 <= k < i ==> name@[k] != 0x3A,
        decreases n - i,
    {
        i = i + 1;
    }
    if i >= n || i + 1 >= n {
        return None;
    }
    let p = slice_subrange(name, 0, i);
    let l = slice_subrange(name, i + 1, n);
    proof {
        assert(name@ =~= p@ + seq![0x3Au8] + l@);
        assert forall|k: int| 0 <= k < p@.len() implies p@[k] != 0x3A by {}
    }
    Some((p, l))
}

/// The ASCII letters, lower-cased.
pub open spec fn lower(c: u8) -> u8 {
    if 0x41 <= c <= 0x5A { (c + 0x20) as u8 } else { c }
}

#[inline]
pub fn to_lower(c: u8) -> (r: u8)
    ensures
        r == lower(c),
{
    if 0x41 <= c && c <= 0x5A { c + 0x20 } else { c }
}

/// `xmlStrcasecmp(a, b) == 0` over ASCII: the same length, and the same
/// letters but for case.
pub fn eq_ci(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@.len() == b@.len() && forall|k: int| 0 <= k < a@.len() ==> lower(#[trigger] a@[k]) == lower(b@[k])),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len() == b@.len(),
            forall|k: int| 0 <= k < i ==> lower(#[trigger] a@[k]) == lower(b@[k]),
        decreases a@.len() - i,
    {
        if to_lower(a[i]) != to_lower(b[i]) {
            return false;
        }
        i = i + 1;
    }
    true
}

/// `xmlStrcasecmp` over NUL-terminated ASCII strings (each slice ends at
/// its end or its first NUL): negative, 0 or positive.
pub fn cmp_ci(a: &[u8], b: &[u8]) -> (r: i32)
{
    let _la = a.len();
    let mut i: usize = 0;
    loop
        invariant
            _la == a@.len(),
            i <= _la,
        decreases _la + 1 - i,
    {
        let x = to_lower(at(a, i));
        let y = to_lower(at(b, i));
        if x != y || x == 0 {
            return x as i32 - y as i32;
        }
        i = i + 1;
    }
}

fn alpha(c: u8) -> (r: bool)
    ensures
        r ==> c != 0,
{
    (0x41 <= c && c <= 0x5A) || (0x61 <= c && c <= 0x7A)
}

fn digit(c: u8) -> (r: bool)
    ensures
        r ==> c != 0,
{
    0x30 <= c && c <= 0x39
}

/// The end of the run of letters at `i`.
fn letters(lang: &[u8], i: usize) -> (r: usize)
    requires
        i <= lang@.len(),
    ensures
        i <= r <= lang@.len(),
{
    let _n = lang.len();
    let mut j = i;
    while alpha(at(lang, j))
        invariant
            _n == lang@.len(),
            i <= j <= lang@.len(),
        decreases lang@.len() - j,
    {
        j = j + 1;
    }
    j
}

/// `xmlCheckLanguageID`: whether the value of `xml:lang` has the form of
/// a language tag (RFC 3066, as libxml2 reads it).
pub fn check_language_id(lang: &[u8]) -> bool {
    let _len = lang.len();
    let b0 = at(lang, 0);
    if (b0 == 0x69 || b0 == 0x49 || b0 == 0x78 || b0 == 0x58) && at(lang, 1) == 0x2D {
        if lang.len() < 2 {
            return false;
        }
        let e = letters(lang, 2);
        return e >= lang.len();
    }
    let cur: usize = 0;
    let mut nxt = letters(lang, cur);
    if nxt - cur >= 4 {
        return !(nxt - cur > 8 || at(lang, nxt) != 0);
    }
    if nxt - cur < 2 {
        return false;
    }
    // Labels: 0 after the language, 1 after extlang, 2 script, 3 region,
    // 4 variant, 5 region_m49.
    let mut state: u8;
    if at(lang, nxt) == 0 {
        return true;
    }
    if at(lang, nxt) != 0x2D {
        return false;
    }
    nxt = nxt + 1;
    let mut cur = nxt;
    if digit(at(lang, nxt)) {
        state = 5;
    } else {
        nxt = letters(lang, nxt);
        let n = nxt - cur;
        if n == 4 {
            state = 2;
        } else if n == 2 {
            state = 3;
        } else if 5 <= n && n <= 8 {
            state = 4;
        } else if n != 3 {
            return false;
        } else {
            // extlang
            if at(lang, nxt) == 0 {
                return true;
            }
            if at(lang, nxt) != 0x2D {
                return false;
            }
            nxt = nxt + 1;
            cur = nxt;
            if digit(at(lang, nxt)) {
                state = 5;
            } else {
                nxt = letters(lang, nxt);
                let n = nxt - cur;
                if n == 2 {
                    state = 3;
                } else if 5 <= n && n <= 8 {
                    state = 4;
                } else if n != 4 {
                    return false;
                } else {
                    state = 2;
                }
            }
        }
    }
    // Each step reads on from `nxt`, which stays within the string.
    loop
        invariant
            _len == lang@.len(),
            nxt <= lang@.len(),
            2 <= state <= 5,
        // 2 goes to 3, 4 or 5; 5 to 3; 3 to 4; 4 ends.
        decreases (if state == 2 { 4int } else if state == 5 { 3int } else if state == 3 { 2int } else { 1int }),
    {
        if state == 2 {
            if at(lang, nxt) == 0 {
                return true;
            }
            if at(lang, nxt) != 0x2D {
                return false;
            }
            nxt = nxt + 1;
            cur = nxt;
            if digit(at(lang, nxt)) {
                state = 5;
            } else {
                nxt = letters(lang, nxt);
                let n = nxt - cur;
                if 5 <= n && n <= 8 {
                    state = 4;
                } else if n != 2 {
                    return false;
                } else {
                    state = 3;
                }
            }
        } else if state == 3 {
            if at(lang, nxt) == 0 {
                return true;
            }
            if at(lang, nxt) != 0x2D {
                return false;
            }
            nxt = nxt + 1;
            cur = nxt;
            nxt = letters(lang, nxt);
            let n = nxt - cur;
            if !(5 <= n && n <= 8) {
                return false;
            }
            state = 4;
        } else if state == 4 {
            if at(lang, nxt) == 0 {
                return true;
            }
            return at(lang, nxt) == 0x2D;
        } else {
            if digit(at_off(lang, nxt, 1)) && digit(at_off(lang, nxt, 2)) {
                nxt = nxt + 3;
                state = 3;
            } else {
                return false;
            }
        }
    }
}

} // verus!

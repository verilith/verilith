//! Normalization of UTF-8, verified against `spec::nf`.
//!
//! The scan skips characters that are fast for the form (each is its own
//! normal form and a boundary). At a character that is not, it backs up to
//! the last boundary, takes the segment up to the next boundary, and
//! normalizes the segment by the folds of the spec. `lemma_nf_split` puts
//! the pieces together.
use super::data::*;
use super::spec::*;
use super::tables::REC_CCC_LEN;
use verilith_core::prims::{extend, get, load_u64_le};
#[cfg(verus_only)]
use verilith_core::prims::{le_bytes, le_word};
#[cfg(verus_only)]
use vstd::std_specs::bits::{axiom_u64_trailing_zeros, u64_trailing_zeros};
#[cfg(verus_only)]
use verilith_core::utf8::utf8_encode;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

// ---------------------------------------------------------------------------
// UTF-8
// ---------------------------------------------------------------------------

proof fn lemma_utf8_bytes(c: u32)
    requires
        is_scalar(c),
    ensures
        ({
            let e = utf8_encode(c);
            &&& c < 0x80 ==> e.len() == 1 && e[0] < 0x80 && e[0] as u32 == c
            &&& 0x80 <= c < 0x800 ==> e.len() == 2 && 0xC0 <= e[0] < 0xE0 && e[0] == (0xC0u32 | (c >> 6u32)) as u8
                && e[1] == (0x80u32 | (c & 0x3F)) as u8 && ((((e[0] & 0x1F) as u32) << 6u32) | ((e[1] & 0x3F) as u32))
                == c
            &&& 0x800 <= c < 0x10000 ==> e.len() == 3 && 0xE0 <= e[0] < 0xF0 && e[0] == (0xE0u32 | (c >> 12u32)) as u8
                && e[1] == (0x80u32 | ((c >> 6u32) & 0x3F)) as u8 && e[2] == (0x80u32 | (c & 0x3F)) as u8 && ((((e[0]
                & 0x0F) as u32) << 12u32) | (((e[1] & 0x3F) as u32) << 6u32) | ((e[2] & 0x3F) as u32)) == c
            &&& 0x10000 <= c ==> e.len() == 4 && 0xF0 <= e[0] && e[0] == (0xF0u32 | (c >> 18u32)) as u8 && e[1] == (0x80u32
                | ((c >> 12u32) & 0x3F)) as u8 && e[2] == (0x80u32 | ((c >> 6u32) & 0x3F)) as u8 && e[3] == (0x80u32 | (c
                & 0x3F)) as u8 && ((((e[0] & 0x07) as u32) << 18u32) | (((e[1] & 0x3F) as u32) << 12u32) | (((e[2]
                & 0x3F) as u32) << 6u32) | ((e[3] & 0x3F) as u32)) == c
        }),
{
    let e = utf8_encode(c);
    if c < 0x80 {
    } else if c < 0x800 {
        let (a, b) = ((c / 64) as u32, (c % 64) as u32);
        assert(e[0] == (0xC0 + a) as u8 && e[1] == (0x80 + b) as u8);
        assert(0x80 <= c < 0x800 && a == c / 64 && b == c % 64 ==> (0xC0 + a) as u8 == (0xC0u32 | (c >> 6u32)) as u8
            && (0x80 + b) as u8 == (0x80u32 | (c & 0x3F)) as u8 && 0xC0 <= (0xC0 + a) as u8 && ((0xC0 + a) as u8) < 0xE0)
            by (bit_vector);
        let (x0, x1) = (e[0], e[1]);
        assert(0x80 <= c < 0x800 && x0 == (0xC0u32 | (c >> 6u32)) as u8 && x1 == (0x80u32 | (c & 0x3F)) as u8 ==> ((((
        x0 & 0x1F) as u32) << 6u32) | ((x1 & 0x3F) as u32)) == c) by (bit_vector);
    } else if c < 0x10000 {
        let (a, b, d) = ((c / 4096) as u32, ((c / 64) % 64) as u32, (c % 64) as u32);
        assert(e[0] == (0xE0 + a) as u8 && e[1] == (0x80 + b) as u8 && e[2] == (0x80 + d) as u8);
        assert(0x800 <= c < 0x10000 && a == c / 4096 && b == (c / 64) % 64 && d == c % 64 ==> (0xE0 + a) as u8 == (0xE0u32
            | (c >> 12u32)) as u8 && (0x80 + b) as u8 == (0x80u32 | ((c >> 6u32) & 0x3F)) as u8 && (0x80 + d) as u8 == (
        0x80u32 | (c & 0x3F)) as u8 && 0xE0 <= (0xE0 + a) as u8 && ((0xE0 + a) as u8) < 0xF0) by (bit_vector);
        let (x0, x1, x2) = (e[0], e[1], e[2]);
        assert(0x800 <= c < 0x10000 && x0 == (0xE0u32 | (c >> 12u32)) as u8 && x1 == (0x80u32 | ((c >> 6u32) & 0x3F)) as u8
            && x2 == (0x80u32 | (c & 0x3F)) as u8 ==> ((((x0 & 0x0F) as u32) << 12u32) | (((x1 & 0x3F) as u32) << 6u32)
            | ((x2 & 0x3F) as u32)) == c) by (bit_vector);
    } else {
        let (a, b, d, f) = ((c / 262144) as u32, ((c / 4096) % 64) as u32, ((c / 64) % 64) as u32, (c % 64) as u32);
        assert(e[0] == (0xF0 + a) as u8 && e[1] == (0x80 + b) as u8 && e[2] == (0x80 + d) as u8 && e[3] == (0x80 + f) as u8);
        assert(0x10000 <= c <= 0x10FFFF && a == c / 262144 && b == (c / 4096) % 64 && d == (c / 64) % 64 && f == c % 64
            ==> (0xF0 + a) as u8 == (0xF0u32 | (c >> 18u32)) as u8 && (0x80 + b) as u8 == (0x80u32 | ((c >> 12u32) & 0x3F))
            as u8 && (0x80 + d) as u8 == (0x80u32 | ((c >> 6u32) & 0x3F)) as u8 && (0x80 + f) as u8 == (0x80u32 | (c
            & 0x3F)) as u8 && 0xF0 <= (0xF0 + a) as u8) by (bit_vector);
        let (x0, x1, x2, x3) = (e[0], e[1], e[2], e[3]);
        assert(0x10000 <= c <= 0x10FFFF && x0 == (0xF0u32 | (c >> 18u32)) as u8 && x1 == (0x80u32 | ((c >> 12u32) & 0x3F))
            as u8 && x2 == (0x80u32 | ((c >> 6u32) & 0x3F)) as u8 && x3 == (0x80u32 | (c & 0x3F)) as u8 ==> ((((x0
            & 0x07) as u32) << 18u32) | (((x1 & 0x3F) as u32) << 12u32) | (((x2 & 0x3F) as u32) << 6u32) | ((x3 & 0x3F)
            as u32)) == c) by (bit_vector);
    }
}

/// Decodes the character at `s[i..]`, which the caller knows is `c`.
#[inline(always)]
pub(crate) fn decode(s: &[u8], i: usize, Ghost(c): Ghost<u32>) -> (r: (u32, usize))
    requires
        is_scalar(c),
        i + utf8_encode(c).len() <= s@.len(),
        s@.subrange(i as int, i + utf8_encode(c).len()) == utf8_encode(c),
    ensures
        r.0 == c,
        r.1 == utf8_encode(c).len(),
{
    proof {
        lemma_utf8_bytes(c);
        let e = utf8_encode(c);
        assert forall|k: int| 0 <= k < e.len() implies s@[i + k] == e[k] by {
            assert(s@.subrange(i as int, i + e.len())[k] == s@[i + k]);
        }
        assert(s@[i as int] == e[0]);
    }
    let ghost e = utf8_encode(c);
    let _n = s.len();
    let b0 = get(s, i);
    if b0 < 0x80 {
        (b0 as u32, 1)
    } else if b0 < 0xE0 {
        assert(!(c < 0x80));
        assert(!(0x800 <= c < 0x10000));
        assert(!(0x10000 <= c));
        assert(e.len() == 2);
        let b1 = get(s, i + 1);
        ((((b0 & 0x1F) as u32) << 6) | ((b1 & 0x3F) as u32), 2)
    } else if b0 < 0xF0 {
        assert(!(c < 0x800));
        assert(!(0x10000 <= c));
        assert(e.len() == 3);
        let b1 = get(s, i + 1);
        let b2 = get(s, i + 2);
        ((((b0 & 0x0F) as u32) << 12) | (((b1 & 0x3F) as u32) << 6) | ((b2 & 0x3F) as u32), 3)
    } else {
        assert(!(c < 0x10000));
        assert(e.len() == 4);
        let b1 = get(s, i + 1);
        let b2 = get(s, i + 2);
        let b3 = get(s, i + 3);
        ((((b0 & 0x07) as u32) << 18) | (((b1 & 0x3F) as u32) << 12) | (((b2 & 0x3F) as u32) << 6) | ((b3 & 0x3F)
            as u32), 4)
    }
}

/// `decode` when the lead byte `b0 >= 0x80` is already read.
#[inline(always)]
fn decode_lead(s: &[u8], i: usize, b0: u8, Ghost(c): Ghost<u32>) -> (r: (u32, usize))
    requires
        is_scalar(c),
        i + utf8_encode(c).len() <= s@.len(),
        s@.subrange(i as int, i + utf8_encode(c).len()) == utf8_encode(c),
        s@[i as int] == b0,
        b0 >= 0x80,
    ensures
        r.0 == c,
        r.1 == utf8_encode(c).len(),
{
    proof {
        lemma_utf8_bytes(c);
        let e = utf8_encode(c);
        assert forall|k: int| 0 <= k < e.len() implies s@[i + k] == e[k] by {
            assert(s@.subrange(i as int, i + e.len())[k] == s@[i + k]);
        }
        assert(s@[i as int] == e[0]);
    }
    let ghost e = utf8_encode(c);
    let _n = s.len();
    if b0 < 0xE0 {
        assert(!(c < 0x80));
        assert(!(0x800 <= c < 0x10000));
        assert(!(0x10000 <= c));
        let b1 = get(s, i + 1);
        ((((b0 & 0x1F) as u32) << 6) | ((b1 & 0x3F) as u32), 2)
    } else if b0 < 0xF0 {
        assert(!(c < 0x800));
        assert(!(0x10000 <= c));
        let b1 = get(s, i + 1);
        let b2 = get(s, i + 2);
        ((((b0 & 0x0F) as u32) << 12) | (((b1 & 0x3F) as u32) << 6) | ((b2 & 0x3F) as u32), 3)
    } else {
        assert(!(c < 0x10000));
        let b1 = get(s, i + 1);
        let b2 = get(s, i + 2);
        let b3 = get(s, i + 3);
        ((((b0 & 0x07) as u32) << 18) | (((b1 & 0x3F) as u32) << 12) | (((b2 & 0x3F) as u32) << 6) | ((b3 & 0x3F)
            as u32), 4)
    }
}

/// Appends the UTF-8 encoding of `c` to `out`.
///
/// ```text
/// requires is_scalar(c)
/// ensures  final(out)@ == old(out)@ + utf8_encode(c)
/// ```
#[inline(always)]
pub fn push_utf8(out: &mut Vec<u8>, c: u32)
    requires
        is_scalar(c),
    ensures
        final(out)@ == old(out)@ + utf8_encode(c),
{
    proof {
        lemma_utf8_bytes(c);
    }
    let ghost e = utf8_encode(c);
    if c < 0x80 {
        out.push(c as u8);
        assert(out@ =~= old(out)@ + e);
    } else if c < 0x800 {
        out.push((0xC0 | (c >> 6)) as u8);
        out.push((0x80 | (c & 0x3F)) as u8);
        assert(out@ =~= old(out)@ + e);
    } else if c < 0x10000 {
        let a = [(0xE0 | (c >> 12)) as u8, (0x80 | ((c >> 6) & 0x3F)) as u8, (0x80 | (c & 0x3F)) as u8];
        extend(out, a.as_slice());
        assert(a@ =~= e);
    } else {
        out.push((0xF0 | (c >> 18)) as u8);
        out.push((0x80 | ((c >> 12) & 0x3F)) as u8);
        out.push((0x80 | ((c >> 6) & 0x3F)) as u8);
        out.push((0x80 | (c & 0x3F)) as u8);
        assert(out@ =~= old(out)@ + e);
    }
}

/// `enc(cs)` splits at character `k`.
proof fn lemma_enc_at(cs: Seq<u32>, k: int)
    requires
        0 <= k < cs.len(),
    ensures
        enc(cs.skip(k)) == utf8_encode(cs[k]) + enc(cs.skip(k + 1)),
        enc(cs.take(k + 1)) == enc(cs.take(k)) + utf8_encode(cs[k]),
{
    assert(cs.skip(k) =~= seq![cs[k]] + cs.skip(k + 1));
    lemma_enc_append(seq![cs[k]], cs.skip(k + 1));
    lemma_enc_one(cs[k]);
    assert(cs.take(k + 1).drop_last() =~= cs.take(k));
}

pub(crate) proof fn lemma_enc_whole(cs: Seq<u32>, k: int)
    requires
        0 <= k <= cs.len(),
    ensures
        enc(cs) == enc(cs.take(k)) + enc(cs.skip(k)),
{
    assert(cs =~= cs.take(k) + cs.skip(k));
    lemma_enc_append(cs.take(k), cs.skip(k));
}

proof fn lemma_enc_empty(cs: Seq<u32>)
    ensures
        enc(cs).len() == 0 <==> cs.len() == 0,
{
    if cs.len() > 0 {
        assert(cs =~= cs.drop_last() + seq![cs.last()]);
        lemma_enc_append(cs.drop_last(), seq![cs.last()]);
        lemma_enc_one(cs.last());
        lemma_utf8_bytes_len(cs.last());
    }
}

proof fn lemma_utf8_bytes_len(c: u32)
    ensures
        utf8_encode(c).len() >= 1,
{
}

// ---------------------------------------------------------------------------
// ASCII
// ---------------------------------------------------------------------------

/// The 8 bytes of a word with no high bit set are ASCII.
proof fn lemma_word_ascii(b: Seq<u8>, i: int, w: u64)
    requires
        0 <= i,
        i + 8 <= b.len(),
        w as nat == le_word(b, i),
        w & 0x8080808080808080 == 0,
    ensures
        forall|k: int| i <= k < i + 8 ==> #[trigger] b[k] < 0x80,
{
    reveal_with_fuel(le_bytes, 9);
    let (b0, b1, b2, b3, b4, b5, b6, b7) = (b[i], b[i + 1], b[i + 2], b[i + 3], b[i + 4], b[i + 5], b[i + 6], b[i + 7]);
    assert(w == (b0 as u64) + 256 * ((b1 as u64) + 256 * ((b2 as u64) + 256 * ((b3 as u64) + 256 * ((b4 as u64) + 256 * ((
    b5 as u64) + 256 * ((b6 as u64) + 256 * (b7 as u64))))))));
    assert(w == (b0 as u64) + 256 * ((b1 as u64) + 256 * ((b2 as u64) + 256 * ((b3 as u64) + 256 * ((b4 as u64) + 256 * ((
    b5 as u64) + 256 * ((b6 as u64) + 256 * (b7 as u64))))))) && w & 0x8080808080808080 == 0 ==> b0 < 0x80 && b1 < 0x80
        && b2 < 0x80 && b3 < 0x80 && b4 < 0x80 && b5 < 0x80 && b6 < 0x80 && b7 < 0x80) by (bit_vector);
    assert forall|k: int| i <= k < i + 8 implies #[trigger] b[k] < 0x80 by {
        let d = k - i;
        assert(d == 0 || d == 1 || d == 2 || d == 3 || d == 4 || d == 5 || d == 6 || d == 7);
    }
}

/// A character whose lead byte is below `0xC0 + (fb >> 6)` is a two-byte
/// character below `fb`.
proof fn lemma_lead_below(c: u32, b: u8, fb: u32)
    requires
        is_scalar(c),
        c >= 0x80,
        utf8_encode(c)[0] == b,
        fb == 0xA0 || fb == 0x300 || fb == 0xC0,
        b < (0xC0 + (fb >> 6)) as u8,
    ensures
        c < fb,
        utf8_encode(c).len() == 2,
{
    lemma_utf8_bytes(c);
    if c >= 0x800 {
        assert(b >= 0xE0);
        assert((fb >> 6u32) <= 12) by (bit_vector)
            requires
                fb == 0xA0 || fb == 0x300 || fb == 0xC0;
    } else {
        assert(b == (0xC0u32 | (c >> 6u32)) as u8);
        assert(0x80 <= c < 0x800 && (fb == 0xA0 || fb == 0x300 || fb == 0xC0) && ((0xC0u32 | (c >> 6u32)) as u8) < (0xC0
            + (fb >> 6u32)) as u8 ==> c < fb) by (bit_vector);
    }
}

/// Byte `k` of a little-endian word is `(w >> 8k) & 0xff`.
proof fn lemma_word_bytes(b: Seq<u8>, i: int, w: u64)
    requires
        0 <= i,
        i + 8 <= b.len(),
        w as nat == le_word(b, i),
    ensures
        forall|k: u64| k < 8 ==> #[trigger] b[i + k] == ((w >> (8 * k)) & 0xff) as u8,
{
    reveal_with_fuel(le_bytes, 9);
    let (b0, b1, b2, b3, b4, b5, b6, b7) = (b[i], b[i + 1], b[i + 2], b[i + 3], b[i + 4], b[i + 5], b[i + 6], b[i + 7]);
    assert(w == (b0 as u64) + 256 * ((b1 as u64) + 256 * ((b2 as u64) + 256 * ((b3 as u64) + 256 * ((b4 as u64) + 256 * ((
    b5 as u64) + 256 * ((b6 as u64) + 256 * (b7 as u64))))))));
    assert(w == (b0 as u64) + 256 * ((b1 as u64) + 256 * ((b2 as u64) + 256 * ((b3 as u64) + 256 * ((b4 as u64) + 256 * ((
    b5 as u64) + 256 * ((b6 as u64) + 256 * (b7 as u64))))))) ==> ((w >> 0u64) & 0xff) as u8 == b0 && ((w >> 8u64)
        & 0xff) as u8 == b1 && ((w >> 16u64) & 0xff) as u8 == b2 && ((w >> 24u64) & 0xff) as u8 == b3 && ((w >> 32u64)
        & 0xff) as u8 == b4 && ((w >> 40u64) & 0xff) as u8 == b5 && ((w >> 48u64) & 0xff) as u8 == b6 && ((w >> 56u64)
        & 0xff) as u8 == b7) by (bit_vector);
    assert forall|k: u64| k < 8 implies #[trigger] b[i + k] == ((w >> (8 * k)) & 0xff) as u8 by {
        assert(k == 0 || k == 1 || k == 2 || k == 3 || k == 4 || k == 5 || k == 6 || k == 7);
    }
}

/// The first high bit of a word, found by `trailing_zeros` of its high
/// bits, ends its run of ASCII bytes.
proof fn lemma_word_tz(b: Seq<u8>, i: int, w: u64, z: u32)
    requires
        0 <= i,
        i + 8 <= b.len(),
        w as nat == le_word(b, i),
        w & 0x8080808080808080 != 0,
        z == u64_trailing_zeros(w & 0x8080808080808080),
    ensures
        z < 64,
        b[i + z / 8] >= 0x80,
        forall|k: int| i <= k < i + z / 8 ==> #[trigger] b[k] < 0x80,
{
    let m = w & 0x8080808080808080;
    axiom_u64_trailing_zeros(m);
    lemma_word_bytes(b, i, w);
    let zz = z as u64;
    assert(zz < 64 && (m >> zz) & 1 == 1 && m == w & 0x8080808080808080 ==> ((w >> (8 * (zz / 8))) & 0xff) as u8 >= 0x80)
        by (bit_vector);
    assert(b[i + zz / 8] >= 0x80);
    assert forall|k: int| i <= k < i + z / 8 implies #[trigger] b[k] < 0x80 by {
        let d = (k - i) as u64;
        assert(d < 8);
        assert(b[i + d] == ((w >> (8 * d)) & 0xff) as u8);
        assert(8 * d + 7 < zz);
        assert((m >> (8 * d + 7)) & 1u64 == 0u64);
        assert(d < 8 && (m >> (8 * d + 7)) & 1 == 0 && m == w & 0x8080808080808080 ==> (((w >> (8 * d)) & 0xff) as u8)
            < 0x80) by (bit_vector);
    }
}

/// An ASCII byte where a character starts is that character.
proof fn lemma_ascii_char(s: Seq<u8>, cs: Seq<u32>, k: int)
    requires
        s == enc(cs),
        scalars(cs),
        0 <= k <= cs.len(),
        enc(cs.take(k)).len() < s.len(),
        s[enc(cs.take(k)).len() as int] < 0x80,
    ensures
        k < cs.len(),
        cs[k] == s[enc(cs.take(k)).len() as int] as u32,
        enc(cs.take(k + 1)).len() == enc(cs.take(k)).len() + 1,
{
    if k == cs.len() {
        assert(cs.take(k) =~= cs);
    }
    lemma_enc_char(s, cs, k);
    lemma_utf8_bytes(cs[k]);
    let i = enc(cs.take(k)).len() as int;
    assert(s.subrange(i, enc(cs.take(k + 1)).len() as int)[0] == s[i]);
}

/// A run of `m` ASCII bytes where a character starts is `m` characters.
proof fn lemma_ascii_run(s: Seq<u8>, cs: Seq<u32>, k: int, m: int)
    requires
        s == enc(cs),
        scalars(cs),
        0 <= k <= cs.len(),
        0 <= m,
        enc(cs.take(k)).len() + m <= s.len(),
        forall|j: int| enc(cs.take(k)).len() <= j < enc(cs.take(k)).len() + m ==> #[trigger] s[j] < 0x80,
    ensures
        k + m <= cs.len(),
        enc(cs.take(k + m)).len() == enc(cs.take(k)).len() + m,
        forall|j: int| k <= j < k + m ==> #[trigger] cs[j] < 0x80,
    decreases m,
{
    if m > 0 {
        let i = enc(cs.take(k)).len() as int;
        assert(s[i] < 0x80);
        lemma_ascii_char(s, cs, k);
        lemma_ascii_run(s, cs, k + 1, m - 1);
    }
}

/// UTF-8 that is all ASCII bytes encodes those bytes.
pub proof fn lemma_ascii_all(s: Seq<u8>, cs: Seq<u32>)
    requires
        s == enc(cs),
        scalars(cs),
        forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j] < 0x80,
    ensures
        cs.len() == s.len(),
        forall|k: int| 0 <= k < cs.len() ==> #[trigger] cs[k] == s[k] as u32,
{
    lemma_ascii_prefix(s, cs, s.len() as int);
    lemma_enc_len_full(cs, s.len() as int);
}

proof fn lemma_ascii_prefix(s: Seq<u8>, cs: Seq<u32>, k: int)
    requires
        s == enc(cs),
        scalars(cs),
        0 <= k <= s.len(),
        forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j] < 0x80,
    ensures
        k <= cs.len(),
        enc(cs.take(k)).len() == k,
        forall|q: int| 0 <= q < k ==> #[trigger] cs[q] == s[q] as u32,
    decreases k,
{
    if k == 0 {
        assert(cs.take(0) =~= Seq::<u32>::empty());
    } else {
        lemma_ascii_prefix(s, cs, k - 1);
        assert(s[k - 1] < 0x80);
        lemma_ascii_char(s, cs, k - 1);
    }
}

/// ASCII characters are stable.
pub proof fn lemma_ascii_stable(cs: Seq<u32>, a: int, b: int, compose: bool, compat: bool)
    requires
        forall|j: int| a <= j < b ==> #[trigger] cs[j] < 0x80,
    ensures
        forall|j: int| a <= j < b ==> stable(#[trigger] cs[j], compose, compat) && ccc(cs[j]) == 0,
{
    assert forall|j: int| a <= j < b implies stable(#[trigger] cs[j], compose, compat) && ccc(cs[j]) == 0 by {
        axiom_ascii(cs[j], compose, compat);
        axiom_fast(cs[j], compose, compat);
    }
}

/// The end of the run of ASCII bytes at `i`.
#[inline(always)]
fn skip_ascii(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s@.len(),
    ensures
        i <= r <= s@.len(),
        r == s@.len() || s@[r as int] >= 0x80,
        forall|k: int| i <= k < r ==> #[trigger] s@[k] < 0x80,
{
    let n = s.len();
    let mut j = i;
    while n - j >= 8
        invariant
            i <= j <= n == s@.len(),
            forall|k: int| i <= k < j ==> #[trigger] s@[k] < 0x80,
        decreases n - j,
    {
        let w = load_u64_le(s, j);
        if w & 0x8080808080808080 != 0 {
            let z = (w & 0x8080808080808080).trailing_zeros();
            proof {
                lemma_word_tz(s@, j as int, w, z);
            }
            return j + (z / 8) as usize;
        }
        proof {
            lemma_word_ascii(s@, j as int, w);
        }
        j += 8;
    }
    while j < n && get(s, j) < 0x80
        invariant
            i <= j <= n == s@.len(),
            forall|k: int| i <= k < j ==> #[trigger] s@[k] < 0x80,
        decreases n - j,
    {
        j += 1;
    }
    j
}

// ---------------------------------------------------------------------------
// Folds
// ---------------------------------------------------------------------------

/// Code points with their combining classes alongside.
pub struct Buf {
    /// The code points.
    pub cp: Vec<u32>,
    /// Their combining classes.
    pub cc: Vec<u8>,
}

impl Buf {
    pub open spec fn wf(&self) -> bool {
        &&& self.cp@.len() == self.cc@.len()
        &&& forall|k: int| 0 <= k < self.cp@.len() ==> #[trigger] self.cc@[k] == ccc(self.cp@[k])
    }

    pub open spec fn view(&self) -> Seq<u32> {
        self.cp@
    }

    /// An empty buffer.
    ///
    /// ```text
    /// ensures  r.wf()
    ///          r@ == Seq::<u32>::empty()
    /// ```
    pub fn new() -> (r: Buf)
        ensures
            r.wf(),
            r@ == Seq::<u32>::empty(),
    {
        Buf { cp: Vec::new(), cc: Vec::new() }
    }

    fn clear(&mut self)
        ensures
            final(self).wf(),
            final(self)@ == Seq::<u32>::empty(),
    {
        self.cp.clear();
        self.cc.clear();
    }

    #[inline(always)]
    fn push(&mut self, c: u32, k: u8)
        requires
            old(self).wf(),
            k == ccc(c),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.push(c),
    {
        self.cp.push(c);
        self.cc.push(k);
        proof {
            assert forall|j: int| 0 <= j < self.cp@.len() implies #[trigger] self.cc@[j] == ccc(self.cp@[j]) by {
                if j < old(self).cp@.len() {
                    assert(self.cc@[j] == old(self).cc@[j]);
                }
            }
        }
    }
}

/// `buf = insert(buf, c)`; `k` is `ccc(c)`.
#[inline(always)]
fn insert_exec(buf: &mut Buf, c: u32, k: u8)
    requires
        old(buf).wf(),
        k == ccc(c),
    ensures
        final(buf).wf(),
        final(buf)@ == insert(old(buf)@, c),
{
    if k == 0 {
        buf.push(c, k);
        return;
    }
    let n = buf.cp.len();
    let mut p = n;
    while p > 0 && buf.cc[p - 1] > k
        invariant
            p <= n == buf@.len(),
            buf.wf(),
            buf@ == old(buf)@,
            insert_pos(buf@, k, n as int) == insert_pos(buf@, k, p as int),
        decreases p,
    {
        p -= 1;
    }
    if p == n {
        buf.push(c, k);
        return;
    }
    let ghost o = buf.cc@;
    buf.cp.insert(p, c);
    buf.cc.insert(p, k);
    proof {
        assert forall|j: int| 0 <= j < buf.cp@.len() implies #[trigger] buf.cc@[j] == ccc(buf.cp@[j]) by {
            if j < p {
                assert(buf.cc@[j] == old(buf).cc@[j]);
            } else if j > p {
                assert(buf.cc@[j] == old(buf).cc@[j - 1]);
                assert(buf.cp@[j] == old(buf).cp@[j - 1]);
            }
        }
    }
}

/// `o = compose_step(o, c)`; `kc` is `ccc(c)`.
#[inline(always)]
fn compose_step_exec(o: &mut Buf, c: u32, kc: u8)
    requires
        old(o).wf(),
        kc == ccc(c),
    ensures
        final(o).wf(),
        final(o)@ == compose_step(old(o)@, c),
{
    let n = o.cp.len();
    let mut p = n;
    while p > 0 && o.cc[p - 1] != 0
        invariant
            p <= n == o@.len(),
            o.wf(),
            o@ == old(o)@,
            last_starter(o@, n as int) == last_starter(o@, p as int),
        decreases p,
    {
        p -= 1;
    }
    if p > 0 {
        let l = p - 1;
        let mut k = p;
        let mut blk = false;
        while k < n && !blk
            invariant
                p <= k <= n == o@.len(),
                o.wf(),
                o@ == old(o)@,
                l == p - 1,
                kc == ccc(c),
                blk ==> blocked(o@, l as int, c),
                !blk ==> forall|j: int| p <= j < k ==> !(ccc(#[trigger] o@[j]) == 0 || ccc(o@[j]) >= ccc(c)),
            decreases n - k + if blk { 0int } else { 1int },
        {
            let x = o.cc[k];
            if x == 0 || x >= kc {
                blk = true;
            } else {
                k += 1;
            }
        }
        if !blk {
            assert(!blocked(o@, l as int, c));
            match comp_of(o.cp[l], c) {
                Some(r) => {
                    proof {
                        axiom_comp(o@[l as int], c);
                    }
                    o.cp.set(l, r);
                    proof {
                        assert forall|j: int| 0 <= j < o.cp@.len() implies #[trigger] o.cc@[j] == ccc(o.cp@[j]) by {
                            if j != l {
                                assert(o.cp@[j] == old(o).cp@[j]);
                            }
                        }
                    }
                    return;
                },
                None => {},
            }
        }
    }
    o.push(c, kc);
}

/// `buf = reorder_from(buf, decomp(c, compat))`; `w` is `tword(c)`.
#[inline(always)]
fn insert_decomp(buf: &mut Buf, c: u32, w: u32, compat: bool)
    requires
        old(buf).wf(),
        is_scalar(c),
        w == tword(c),
        (w & 0xFFFF) < REC_CCC_LEN,
    ensures
        final(buf).wf(),
        final(buf)@ == reorder_from(old(buf)@, decomp(c, compat)),
{
    // A character that is fast for decomposition is its own decomposition.
    let fd = fast_flag_of(false, compat);
    if (w >> 16) as u16 & fd != 0 {
        proof {
            axiom_fast(c, false, compat);
            axiom_decomp_ordered(c, compat);
            lemma_decomp_all_one(c, compat);
            assert(decomp(c, compat) == seq![c]);
            lemma_reorder_one(old(buf)@, c);
        }
        buf.push(c, 0);
        return;
    }
    let kc = rec_ccc_at((w & 0xFFFF) as usize);
    let d = decomp_of(c, compat, w);
    let ghost dc = decomp(c, compat);
    let mut m = 0;
    proof {
        assert(dc.take(0) =~= Seq::<u32>::empty());
    }
    while m < d.len
        invariant
            d.wf(c, compat),
            m <= d.len == dc.len(),
            dc == decomp(c, compat),
            kc == ccc(c),
            buf.wf(),
            buf@ == reorder_from(old(buf)@, dc.take(m as int)),
        decreases d.len - m,
    {
        let (x, kx) = decomp_elem(c, kc, compat, &d, m);
        insert_exec(buf, x, kx);
        proof {
            assert(dc.take(m + 1).drop_last() =~= dc.take(m as int));
        }
        m += 1;
    }
    proof {
        assert(dc.take(m as int) =~= dc);
    }
}

/// Appends the encoding of `decomp(c, compat)`; `w` is `tword(c)`.
#[inline(always)]
fn emit_decomp(out: &mut Vec<u8>, c: u32, w: u32, compat: bool)
    requires
        is_scalar(c),
        w == tword(c),
        (w & 0xFFFF) < REC_CCC_LEN,
    ensures
        final(out)@ == old(out)@ + enc(decomp(c, compat)),
{
    let kc = rec_ccc_at((w & 0xFFFF) as usize);
    let d = decomp_of(c, compat, w);
    let ghost dc = decomp(c, compat);
    proof {
        axiom_decomp_scalar(c, compat);
        assert(dc.take(0) =~= Seq::<u32>::empty());
    }
    let mut m = 0;
    while m < d.len
        invariant
            d.wf(c, compat),
            m <= d.len == dc.len(),
            dc == decomp(c, compat),
            scalars(dc),
            kc == ccc(c),
            out@ == old(out)@ + enc(dc.take(m as int)),
        decreases d.len - m,
    {
        let (x, _kx) = decomp_elem(c, kc, compat, &d, m);
        push_utf8(out, x);
        proof {
            lemma_enc_at(dc, m as int);
            assert(old(out)@ + enc(dc.take(m as int)) + utf8_encode(x) =~= old(out)@ + (enc(dc.take(m as int))
                + utf8_encode(x)));
        }
        m += 1;
    }
    proof {
        assert(dc.take(m as int) =~= dc);
    }
}

/// Decomposes characters from `st` (character `kst`, already decoded as
/// `c0`, `len0`, `w0`) into `buf`, in canonical order: at least up to
/// character `kmin`, then up to the next character with flag `bbf`, or
/// the end. Returns where it stopped, with the length and trie word of the
/// character there.
fn decompose_seg(
    s: &[u8],
    st: usize,
    c0: u32,
    len0: usize,
    w0: u32,
    imin: usize,
    bbf: u16,
    compat: bool,
    buf: &mut Buf,
    Ghost(cs): Ghost<Seq<u32>>,
    Ghost(kst): Ghost<int>,
    Ghost(kmin): Ghost<int>,
) -> (r: (usize, Ghost<int>, usize, u32))
    requires
        s@ == enc(cs),
        scalars(cs),
        0 <= kst < kmin <= cs.len(),
        st == enc(cs.take(kst)).len(),
        imin == enc(cs.take(kmin)).len(),
        c0 == cs[kst],
        len0 == utf8_encode(c0).len(),
        w0 == tword(c0),
    ensures
        final(buf).wf(),
        kmin <= r.1@ <= cs.len(),
        r.0 == enc(cs.take(r.1@)).len(),
        r.1@ < cs.len() ==> has_flag(cs[r.1@], bbf) && r.2 == utf8_encode(cs[r.1@]).len() && r.3 == tword(cs[r.1@]),
        final(buf)@ == reorder_from(seq![], decomp_all(cs.subrange(kst, r.1@), compat)),
{
    let n = s.len();
    buf.clear();
    proof {
        lemma_enc_char(s@, cs, kst);
        lemma_tword(c0);
    }
    insert_decomp(buf, c0, w0, compat);
    let mut i = st + len0;
    let ghost mut k = kst + 1;
    proof {
        reveal_with_fuel(decomp_all, 2);
        reveal_with_fuel(reorder_from, 1);
        assert(cs.subrange(kst, kst + 1) =~= seq![c0]);
        assert(seq![c0].drop_last() =~= Seq::<u32>::empty());
        assert(Seq::<u32>::empty() + decomp(c0, compat) =~= decomp(c0, compat));
    }
    loop
        invariant
            n == s@.len(),
            s@ == enc(cs),
            scalars(cs),
            0 <= kst < k <= cs.len(),
            kst < kmin <= cs.len(),
            imin == enc(cs.take(kmin)).len(),
            i == enc(cs.take(k)).len(),
            buf.wf(),
            buf@ == reorder_from(seq![], decomp_all(cs.subrange(kst, k), compat)),
        decreases n - i,
    {
        proof {
            lemma_enc_whole(cs, k);
        }
        if i >= n {
            proof {
                lemma_enc_len_full(cs, k);
            }
            return (i, Ghost(k), 0, 0);
        }
        proof {
            if k == cs.len() {
                assert(cs.take(k) =~= cs);
            }
            lemma_enc_char(s@, cs, k);
            lemma_utf8_bytes_len(cs[k]);
        }
        let (c, len) = decode(s, i, Ghost(cs[k]));
        let w = word_of(c);
        if i >= imin && (w >> 16) as u16 & bbf != 0 {
            proof {
                if k < kmin {
                    lemma_enc_strict(cs, k, kmin);
                }
            }
            return (i, Ghost(k), len, w);
        }
        let ghost r0 = buf@;
        insert_decomp(buf, c, w, compat);
        proof {
            assert(cs.subrange(kst, k + 1).drop_last() =~= cs.subrange(kst, k));
            assert(cs.subrange(kst, k + 1).last() == c);
            lemma_reorder_append(seq![], decomp_all(cs.subrange(kst, k), compat), decomp(c, compat));
        }
        i += len;
        proof {
            k = k + 1;
        }
    }
}

/// Composes (if `compose`) the canonically ordered decomposition of `seg`
/// in `buf`, and appends the encoding of the result.
fn finish(compose: bool, compat: bool, buf: &Buf, cb: &mut Buf, out: &mut Vec<u8>, Ghost(seg): Ghost<Seq<u32>>)
    requires
        buf.wf(),
        old(cb).wf(),
        scalars(seg),
        buf@ == reorder_from(seq![], decomp_all(seg, compat)),
    ensures
        final(cb).wf(),
        final(out)@ == old(out)@ + enc(nf(seg, compose, compat)),
{
    let ghost r = buf@;
    let n = buf.cp.len();
    let mut k = 0;
    if compose {
        cb.clear();
        proof {
            assert(r.take(0) =~= Seq::<u32>::empty());
        }
        while k < n
            invariant
                k <= n == buf@.len(),
                buf.wf(),
                cb.wf(),
                buf@ == r,
                cb@ == compose_from(seq![], r.take(k as int)),
            decreases n - k,
        {
            compose_step_exec(cb, buf.cp[k], buf.cc[k]);
            proof {
                assert(r.take(k + 1).drop_last() =~= r.take(k as int));
            }
            k += 1;
        }
        proof {
            assert(r.take(k as int) =~= r);
        }
        emit(&cb.cp, out, Ghost(seg), compose, compat);
    } else {
        emit(&buf.cp, out, Ghost(seg), compose, compat);
    }
}


/// Appends the encoding of `v`, the normal form of `seg`.
fn emit(v: &Vec<u32>, out: &mut Vec<u8>, Ghost(seg): Ghost<Seq<u32>>, compose: bool, compat: bool)
    requires
        scalars(seg),
        v@ == nf(seg, compose, compat),
    ensures
        final(out)@ == old(out)@ + enc(nf(seg, compose, compat)),
{
    proof {
        lemma_nf_scalars(seg, compose, compat);
        assert(v@.take(0) =~= Seq::<u32>::empty());
    }
    let n = v.len();
    let mut k = 0;
    while k < n
        invariant
            k <= n == v@.len(),
            scalars(v@),
            out@ == old(out)@ + enc(v@.take(k as int)),
        decreases n - k,
    {
        push_utf8(out, v[k]);
        proof {
            lemma_enc_at(v@, k as int);
            assert(old(out)@ + enc(v@.take(k as int)) + utf8_encode(v@[k as int]) =~= old(out)@ + (enc(v@.take(k as int))
                + utf8_encode(v@[k as int])));
        }
        k += 1;
    }
    proof {
        assert(v@.take(k as int) =~= v@);
    }
}

// ---------------------------------------------------------------------------
// The scan
// ---------------------------------------------------------------------------

/// The bytes of characters `a..b` of `cs` are `s[enc(cs.take(a)).len()..enc(cs.take(b)).len()]`.
proof fn lemma_enc_range(s: Seq<u8>, cs: Seq<u32>, a: int, b: int)
    requires
        s == enc(cs),
        0 <= a <= b <= cs.len(),
    ensures
        enc(cs.take(a)).len() <= enc(cs.take(b)).len() <= s.len(),
        s.subrange(enc(cs.take(a)).len() as int, enc(cs.take(b)).len() as int) == enc(cs.subrange(a, b)),
{
    assert(cs.take(b) =~= cs.take(a) + cs.subrange(a, b));
    lemma_enc_append(cs.take(a), cs.subrange(a, b));
    lemma_enc_whole(cs, b);
    assert(s.subrange(enc(cs.take(a)).len() as int, enc(cs.take(b)).len() as int) =~= enc(cs.subrange(a, b)));
}

/// Character `k` of `cs` is at byte `enc(cs.take(k)).len()` of `s`.
pub(crate) proof fn lemma_enc_char(s: Seq<u8>, cs: Seq<u32>, k: int)
    requires
        s == enc(cs),
        0 <= k < cs.len(),
    ensures
        enc(cs.take(k)).len() + utf8_encode(cs[k]).len() == enc(cs.take(k + 1)).len() <= s.len(),
        s.subrange(enc(cs.take(k)).len() as int, enc(cs.take(k + 1)).len() as int) == utf8_encode(cs[k]),
{
    lemma_enc_range(s, cs, k, k + 1);
    lemma_enc_at(cs, k);
    assert(cs.subrange(k, k + 1) =~= seq![cs[k]]);
    lemma_enc_one(cs[k]);
}

proof fn lemma_enc_strict(cs: Seq<u32>, a: int, b: int)
    requires
        0 <= a < b <= cs.len(),
    ensures
        enc(cs.take(a)).len() < enc(cs.take(b)).len(),
{
    assert(cs.take(b) =~= cs.take(a) + cs.subrange(a, b));
    lemma_enc_append(cs.take(a), cs.subrange(a, b));
    lemma_enc_empty(cs.subrange(a, b));
}

pub(crate) proof fn lemma_enc_len_full(cs: Seq<u32>, k: int)
    requires
        0 <= k <= cs.len(),
        enc(cs.take(k)).len() == enc(cs).len(),
    ensures
        k == cs.len(),
{
    lemma_enc_whole(cs, k);
    lemma_enc_empty(cs.skip(k));
}

/// The scalars that `s` encodes.
pub fn decode_all(s: &[u8], Ghost(cs): Ghost<Seq<u32>>) -> (r: Vec<u32>)
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        r@ == cs,
{
    let n = s.len();
    let mut r: Vec<u32> = Vec::with_capacity(n);
    let mut i = 0;
    proof {
        assert(cs.take(0) =~= Seq::<u32>::empty());
        lemma_enc_whole(cs, 0);
    }
    while i < n
        invariant
            n == s@.len(),
            s@ == enc(cs),
            scalars(cs),
            r@ == cs.take(r@.len() as int),
            r@.len() <= cs.len(),
            i == enc(cs.take(r@.len() as int)).len(),
            i <= n,
        decreases n - i,
    {
        let ghost k = r@.len() as int;
        proof {
            if k == cs.len() {
                assert(cs.take(k) =~= cs);
            }
            lemma_enc_char(s@, cs, k);
        }
        let (c, len) = decode(s, i, Ghost(cs[k]));
        r.push(c);
        i += len;
        proof {
            assert(r@ =~= cs.take(k + 1));
        }
    }
    proof {
        lemma_enc_len_full(cs, r@.len() as int);
        assert(cs.take(cs.len() as int) =~= cs);
    }
    r
}

/// Appends the UTF-8 encoding of `v`.
pub fn encode_all(v: &[u32], out: &mut Vec<u8>)
    requires
        scalars(v@),
    ensures
        final(out)@ == old(out)@ + enc(v@),
{
    let mut j = 0;
    proof {
        assert(v@.take(0) =~= Seq::<u32>::empty());
        assert(old(out)@ + enc(Seq::<u32>::empty()) =~= old(out)@);
    }
    while j < v.len()
        invariant
            j <= v@.len(),
            scalars(v@),
            out@ == old(out)@ + enc(v@.take(j as int)),
        decreases v@.len() - j,
    {
        push_utf8(out, v[j]);
        proof {
            lemma_enc_at(v@, j as int);
            assert(old(out)@ + enc(v@.take(j as int)) + utf8_encode(v@[j as int]) =~= old(out)@ + (enc(
                v@.take(j as int),
            ) + utf8_encode(v@[j as int])));
        }
        j += 1;
    }
    proof {
        assert(v@.take(v@.len() as int) =~= v@);
    }
}

/// Characters `a..b` of `cs` are stable, so normalizing through them appends
/// their bytes.
proof fn lemma_commit(s: Seq<u8>, cs: Seq<u32>, a: int, b: int, compose: bool, compat: bool)
    requires
        s == enc(cs),
        0 <= a <= b <= cs.len(),
        forall|k: int| a <= k < b ==> #[trigger] passable(cs, a, k, compose, compat),
    ensures
        enc(cs.take(a)).len() <= enc(cs.take(b)).len() <= s.len(),
        enc(nf(cs.take(a), compose, compat)) + s.subrange(enc(cs.take(a)).len() as int, enc(cs.take(b)).len() as int)
            == enc(nf(cs.take(b), compose, compat)),
{
    lemma_enc_range(s, cs, a, b);
    lemma_nf_pass_run(cs, a, b, compose, compat);
    lemma_enc_append(nf(cs.take(a), compose, compat), cs.subrange(a, b));
}

/// Normalizing through a segment that starts at a boundary (or at the
/// start) appends the segment's normal form.
proof fn lemma_join(cs: Seq<u32>, a: int, b: int, compose: bool, compat: bool)
    requires
        0 <= a < b <= cs.len(),
        a == 0 || boundary(cs[a], compose, compat),
    ensures
        enc(nf(cs.take(b), compose, compat)) == enc(nf(cs.take(a), compose, compat)) + enc(nf(cs.subrange(a, b), compose, compat)),
{
    let seg = cs.subrange(a, b);
    assert(cs.take(a) + seg =~= cs.take(b));
    if a == 0 {
        assert(cs.take(a) =~= Seq::<u32>::empty());
        assert(cs.take(a) + seg =~= seg);
        reveal_with_fuel(decomp_all, 1);
        reveal_with_fuel(reorder_from, 1);
        reveal_with_fuel(compose_from, 1);
        assert(nf(cs.take(a), compose, compat) =~= Seq::<u32>::empty());
        assert(nf(cs.take(a), compose, compat) + nf(seg, compose, compat) =~= nf(seg, compose, compat));
    } else {
        assert(seg[0] == cs[a]);
        lemma_nf_split(cs.take(a), seg, compose, compat);
    }
    lemma_enc_append(nf(cs.take(a), compose, compat), nf(seg, compose, compat));
}

proof fn lemma_seg_scalars(cs: Seq<u32>, a: int, b: int)
    requires
        scalars(cs),
        0 <= a <= b <= cs.len(),
    ensures
        scalars(cs.subrange(a, b)),
{
    assert forall|k: int| 0 <= k < cs.subrange(a, b).len() implies is_scalar(#[trigger] cs.subrange(a, b)[k]) by {
        assert(cs.subrange(a, b)[k] == cs[a + k]);
    }
}

/// Where the scan of `normalize_into` stands: `out` holds the normal form
/// of the characters before `done` (character `kd`), the characters from
/// `done` to `i` (character `ki`) are stable, and `prev` is where the last
/// of them starts.
pub struct Scan {
    /// The byte offset up to which `out` holds the normal form.
    pub done: usize,
    /// The byte offset scanned to.
    pub i: usize,
    /// The byte offset of the last stable character before `i`.
    pub prev: usize,
    /// The combining class of the character before `i`.
    pub lastcc: u8,
    /// `done` as a character index.
    pub kd: Ghost<int>,
    /// `i` as a character index.
    pub ki: Ghost<int>,
    /// `prev` as a character index.
    pub kp: Ghost<int>,
}

#[verifier::opaque]
pub open spec fn scan_inv(s: Seq<u8>, cs: Seq<u32>, compose: bool, compat: bool, t: Scan, out: Seq<u8>) -> bool {
    let (kd, ki, kp) = (t.kd@, t.ki@, t.kp@);
    &&& s == enc(cs)
    &&& scalars(cs)
    &&& 0 <= kd <= ki <= cs.len()
    &&& t.done == enc(cs.take(kd)).len()
    &&& t.i == enc(cs.take(ki)).len()
    &&& out == enc(nf(cs.take(kd), compose, compat))
    &&& forall|k: int| kd <= k < ki ==> #[trigger] passable(cs, kd, k, compose, compat)
    &&& kd == 0 || kd == cs.len() || boundary(cs[kd], compose, compat)
    &&& ki > kd ==> kd <= kp < ki && stable(cs[kp], compose, compat) && t.prev == enc(cs.take(kp)).len() && t.lastcc
        == ccc(cs[ki - 1])
}

/// Steps over a run of ASCII at `t.i`, if there is one.
#[inline(always)]
fn step_ascii(s: &[u8], t: &mut Scan, Ghost(cs): Ghost<Seq<u32>>, Ghost(out): Ghost<Seq<u8>>, compose: bool, compat: bool) -> (r: bool)
    requires
        scan_inv(s@, cs, compose, compat, *old(t), out),
        old(t).i < s@.len(),
    ensures
        scan_inv(s@, cs, compose, compat, *final(t), out),
        final(t).done == old(t).done,
        r ==> old(t).i < final(t).i <= s@.len(),
        !r ==> *final(t) == *old(t) && s@[old(t).i as int] >= 0x80,
{
    reveal(scan_inv);
    let i = t.i;
    let j = skip_ascii(s, i);
    if j > i {
        let ghost ki = t.ki@;
        proof {
            lemma_ascii_run(s@, cs, ki, j - i);
            lemma_ascii_stable(cs, ki, ki + (j - i), compose, compat);
            lemma_ascii_run(s@, cs, ki, j - i - 1);
        }
        proof {
            assert(stable(cs[ki + (j - i) - 1], compose, compat));
            assert forall|k: int| t.kd@ <= k < ki + (j - i) implies #[trigger] passable(cs, t.kd@, k, compose, compat) by {
                if k >= ki {
                    assert(stable(cs[k], compose, compat));
                }
            }
        }
        t.kp = Ghost(ki + (j - i) - 1);
        t.ki = Ghost(ki + (j - i));
        t.prev = j - 1;
        t.lastcc = 0;
        t.i = j;
        true
    } else {
        false
    }
}

/// Steps over fast characters from `t.i`, one at a time, up to the first
/// character that is not fast or the end.
// Without a fixed pointer width (the crate verifies for 32- and 64-bit
// targets alike) this loop needs a little over the default budget.
#[verifier::rlimit(30)]
#[inline(always)]
fn skip_fast(s: &[u8], t: &mut Scan, fast: u16, Ghost(cs): Ghost<Seq<u32>>, Ghost(out): Ghost<Seq<u8>>, compose: bool, compat: bool) -> (r: (
    u32,
    usize,
    u32,
))
    requires
        scan_inv(s@, cs, compose, compat, *old(t), out),
        fast == fast_flag(compose, compat),
    ensures
        scan_inv(s@, cs, compose, compat, *final(t), out),
        final(t).done == old(t).done,
        final(t).kd == old(t).kd,
        old(t).i <= final(t).i <= s@.len(),
        final(t).i < s@.len() ==> s@[final(t).i as int] >= 0x80 && !has_flag(cs[final(t).ki@], fast)
            && final(t).ki@ < cs.len() && r.0 == cs[final(t).ki@] && r.1 == utf8_encode(r.0).len() && r.2 == tword(r.0),
{
    reveal(scan_inv);
    let n = s.len();
    let done = t.done;
    let mut i = t.i;
    let mut prev = t.prev;
    let mut lastcc = t.lastcc;
    let ghost kd = t.kd@;
    let ghost mut ki = t.ki@;
    let ghost mut kp = t.kp@;
    let mut res: (u32, usize, u32) = (0, 0, 0);
    let fb = fast_below_of(compose, compat);
    assert((fb >> 6u32) <= 12) by (bit_vector)
        requires
            fb == 0xA0 || fb == 0x300 || fb == 0xC0;
    let lead_lim = (0xC0 + (fb >> 6)) as u8;
    proof {
        lemma_enc_whole(cs, ki);
    }
    while i < n
        invariant
            n == s@.len(),
            s@ == enc(cs),
            scalars(cs),
            fast == fast_flag(compose, compat),
            fb == fast_below(compose, compat),
            lead_lim == (0xC0 + (fb >> 6)) as u8,
            0 <= kd <= ki <= cs.len(),
            done == enc(cs.take(kd)).len(),
            i == enc(cs.take(ki)).len(),
            forall|k: int| kd <= k < ki ==> #[trigger] passable(cs, kd, k, compose, compat),
            ki > kd ==> kd <= kp < ki && stable(cs[kp], compose, compat) && prev == enc(cs.take(kp)).len() && lastcc
                == ccc(cs[ki - 1]),
            ki == old(t).ki@ ==> kp == old(t).kp@ && prev == old(t).prev && lastcc == old(t).lastcc,
            old(t).ki@ <= ki,
            old(t).i <= i <= n,
        ensures
            i <= n,
            i < n ==> s@[i as int] >= 0x80 && ki < cs.len() && !has_flag(cs[ki], fast) && res.0 == cs[ki] && res.1
                == utf8_encode(res.0).len() && res.2 == tword(res.0),
        decreases n - i,
    {
        let b = get(s, i);
        if b < 0x80 {
            let j = skip_ascii(s, i);
            proof {
                lemma_ascii_run(s@, cs, ki, j - i);
                lemma_ascii_stable(cs, ki, ki + (j - i), compose, compat);
                lemma_ascii_run(s@, cs, ki, j - i - 1);
                assert forall|k: int| kd <= k < ki + (j - i) implies #[trigger] passable(cs, kd, k, compose, compat) by {
                    if k >= ki {
                        assert(stable(cs[k], compose, compat));
                    }
                }
                kp = ki + (j - i) - 1;
                ki = ki + (j - i);
                assert(stable(cs[kp], compose, compat));
            }
            prev = j - 1;
            lastcc = 0;
            i = j;
        } else if b < lead_lim {
            // A two-byte character below `fast_below`.
            proof {
                if ki == cs.len() {
                    assert(cs.take(ki) =~= cs);
                }
                lemma_enc_char(s@, cs, ki);
                lemma_utf8_bytes(cs[ki]);
                let c = cs[ki];
                let e = utf8_encode(c);
                assert(s@.subrange(i as int, enc(cs.take(ki + 1)).len() as int)[0] == s@[i as int]);
                assert(e[0] == b);
                lemma_lead_below(c, b, fb);
                axiom_fast_below(c, compose, compat);
                axiom_fast(c, compose, compat);
                kp = ki;
                ki = ki + 1;
                assert(passable(cs, kd, ki - 1, compose, compat));
            }
            prev = i;
            lastcc = 0;
            i += 2;
        } else {
            proof {
                if ki == cs.len() {
                    assert(cs.take(ki) =~= cs);
                }
                lemma_enc_char(s@, cs, ki);
                lemma_utf8_bytes_len(cs[ki]);
                lemma_tword(cs[ki]);
            }
            let (c, len) = decode_lead(s, i, b, Ghost(cs[ki]));
            let w = word_of(c);
            if (w >> 16) as u16 & fast != 0 {
                proof {
                    axiom_fast(c, compose, compat);
                    kp = ki;
                    ki = ki + 1;
                    assert(passable(cs, kd, ki - 1, compose, compat));
                }
                prev = i;
                lastcc = 0;
                i += len;
            } else {
                // When decomposing, a character that does not decompose and
                // is in order with the one before it is copied through.
                let r = (w & 0xFFFF) as usize;
                if compose || i <= done || (S_BASE <= c && c < S_BASE + S_COUNT) {
                    res = (c, len, w);
                    break;
                }
                let dw = if compat { rec_kd_at(r) } else { rec_fd_at(r) };
                let k = rec_ccc_at(r);
                if dw & 31 != 0 || k < lastcc {
                    res = (c, len, w);
                    break;
                }
                proof {
                    if ki == kd {
                        assert(false);
                    }
                    assert(!dword_ok(dword(c, compat))) by {
                        assert(dw & 31 == 0);
                    }
                    assert(decomp(c, compat) == seq![c]);
                    ki = ki + 1;
                    assert(passable(cs, kd, ki - 1, compose, compat));
                }
                lastcc = k;
                i += len;
            }
        }
    }
    t.i = i;
    t.prev = prev;
    t.lastcc = lastcc;
    t.ki = Ghost(ki);
    t.kp = Ghost(kp);
    res
}

/// Right after a segment, steps over the boundary character at `t.i`
/// (already decoded: length `len`, trie word `w`) if it is fast.
#[inline(always)]
fn absorb(s: &[u8], t: &mut Scan, len: usize, w: u32, fast: u16, Ghost(cs): Ghost<Seq<u32>>, Ghost(out): Ghost<Seq<u8>>, compose: bool, compat: bool)
    requires
        scan_inv(s@, cs, compose, compat, *old(t), out),
        fast == fast_flag(compose, compat),
        old(t).i <= s@.len(),
        old(t).ki@ == old(t).kd@,
        old(t).i < s@.len() ==> old(t).ki@ < cs.len() && len == utf8_encode(cs[old(t).ki@]).len() && w == tword(
            cs[old(t).ki@],
        ),
    ensures
        scan_inv(s@, cs, compose, compat, *final(t), out),
        old(t).i <= final(t).i <= s@.len(),
{
    if t.i < s.len() && (w >> 16) as u16 & fast != 0 {
        reveal(scan_inv);
        let ghost ki = t.ki@;
        proof {
            axiom_fast(cs[ki], compose, compat);
            lemma_enc_char(s@, cs, ki);
        }
        t.kp = Ghost(ki);
        t.ki = Ghost(ki + 1);
        t.prev = t.i;
        t.lastcc = 0;
        t.i = t.i + len;
        proof {
            assert(passable(cs, ki, ki, compose, compat));
        }
    }
}

/// When decomposing, a segment of one character `c` (character `ki`, its
/// trie word `w`, ending at byte `e1`) normalizes to its decomposition.
/// Returns whether the segment is a single character, and if so the length
/// and trie word of the character after it.
fn seg_single(
    s: &[u8],
    c: u32,
    w: u32,
    e1: usize,
    bbf: u16,
    compat: bool,
    out: &mut Vec<u8>,
    Ghost(cs): Ghost<Seq<u32>>,
    Ghost(ki): Ghost<int>,
    Ghost(o0): Ghost<Seq<u8>>,
) -> (r: (bool, usize, u32))
    requires
        s@ == enc(cs),
        scalars(cs),
        0 <= ki < cs.len(),
        c == cs[ki],
        w == tword(c),
        e1 == enc(cs.take(ki + 1)).len(),
        bbf == bb_flag(false, compat),
        ki == 0 || boundary(c, false, compat),
        old(out)@ == o0 + enc(nf(cs.take(ki), false, compat)),
    ensures
        r.0 ==> final(out)@ == o0 + enc(nf(cs.take(ki + 1), false, compat)),
        r.0 ==> (e1 < s@.len() ==> ki + 1 < cs.len() && boundary(cs[ki + 1], false, compat) && r.1 == utf8_encode(
            cs[ki + 1],
        ).len() && r.2 == tword(cs[ki + 1])),
        r.0 ==> (e1 >= s@.len() ==> ki + 1 == cs.len()),
        !r.0 ==> final(out)@ == old(out)@,
{
    let n = s.len();
    proof {
        lemma_enc_whole(cs, ki + 1);
        lemma_tword(c);
    }
    let mut nlen: usize = 0;
    let mut nw: u32 = 0;
    if e1 < n {
        proof {
            if ki + 1 == cs.len() {
                assert(cs.take(ki + 1) =~= cs);
            }
            lemma_enc_char(s@, cs, ki + 1);
        }
        let (nc, l) = decode(s, e1, Ghost(cs[ki + 1]));
        nlen = l;
        nw = word_of(nc);
        if (nw >> 16) as u16 & bbf == 0 {
            return (false, 0, 0);
        }
        proof {
            axiom_bb(nc, false, compat);
        }
    } else {
        proof {
            lemma_enc_len_full(cs, ki + 1);
        }
    }
    emit_decomp(out, c, w, compat);
    proof {
        axiom_decomp_ordered(c, compat);
        lemma_decomp_all_one(c, compat);
        assert(cs.subrange(ki, ki + 1) =~= seq![c]);
        lemma_join(cs, ki, ki + 1, false, compat);
        assert(out@ =~= o0 + enc(nf(cs.take(ki + 1), false, compat)));
    }
    (true, nlen, nw)
}

/// Normalizes the segment from `st` (character `kst`, decoded as `c0`,
/// `len0`, `w0`) through at least character `ki` (which ends at byte `e1`)
/// up to the next boundary. Returns where it stopped, with the length and
/// trie word of the character there.
fn seg_general(
    s: &[u8],
    st: usize,
    c0: u32,
    len0: usize,
    w0: u32,
    e1: usize,
    bbf: u16,
    compose: bool,
    compat: bool,
    buf: &mut Buf,
    cb: &mut Buf,
    out: &mut Vec<u8>,
    Ghost(cs): Ghost<Seq<u32>>,
    Ghost(kst): Ghost<int>,
    Ghost(ki): Ghost<int>,
    Ghost(o0): Ghost<Seq<u8>>,
) -> (r: (usize, Ghost<int>, usize, u32))
    requires
        s@ == enc(cs),
        scalars(cs),
        0 <= kst <= ki < cs.len(),
        st == enc(cs.take(kst)).len(),
        e1 == enc(cs.take(ki + 1)).len(),
        c0 == cs[kst],
        len0 == utf8_encode(c0).len(),
        w0 == tword(c0),
        bbf == bb_flag(compose, compat),
        kst == 0 || boundary(cs[kst], compose, compat),
        old(out)@ == o0 + enc(nf(cs.take(kst), compose, compat)),
        old(buf).wf(),
        old(cb).wf(),
    ensures
        final(buf).wf(),
        final(cb).wf(),
        ki < r.1@ <= cs.len(),
        r.0 == enc(cs.take(r.1@)).len(),
        r.1@ < cs.len() ==> boundary(cs[r.1@], compose, compat) && r.2 == utf8_encode(cs[r.1@]).len() && r.3 == tword(
            cs[r.1@],
        ),
        final(out)@ == o0 + enc(nf(cs.take(r.1@), compose, compat)),
{
    let (e, Ghost(ke), blen, bw) = decompose_seg(s, st, c0, len0, w0, e1, bbf, compat, buf, Ghost(cs), Ghost(kst), Ghost(ki + 1));
    proof {
        lemma_seg_scalars(cs, kst, ke);
        if ke < cs.len() {
            axiom_bb(cs[ke], compose, compat);
        }
    }
    finish(compose, compat, buf, cb, out, Ghost(cs.subrange(kst, ke)));
    proof {
        lemma_join(cs, kst, ke, compose, compat);
        assert(out@ =~= o0 + enc(nf(cs.take(ke), compose, compat)));
    }
    (e, Ghost(ke), blen, bw)
}

/// Handles the characters at `t.i`: steps over fast ones, and normalizes
/// the segment around the first one that is not.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn step_char(
    s: &[u8],
    t: &mut Scan,
    fast: u16,
    bbf: u16,
    compose: bool,
    compat: bool,
    buf: &mut Buf,
    cb: &mut Buf,
    out: &mut Vec<u8>,
    Ghost(cs): Ghost<Seq<u32>>,
    Ghost(o0): Ghost<Seq<u8>>,
)
    requires
        scan_inv(s@, cs, compose, compat, *old(t), old(out)@.skip(o0.len() as int)),
        o0.len() <= old(out)@.len(),
        old(out)@.take(o0.len() as int) == o0,
        old(t).i < s@.len(),
        fast == fast_flag(compose, compat),
        bbf == bb_flag(compose, compat),
        old(buf).wf(),
        old(cb).wf(),
    ensures
        scan_inv(s@, cs, compose, compat, *final(t), final(out)@.skip(o0.len() as int)),
        o0.len() <= final(out)@.len(),
        final(out)@.take(o0.len() as int) == o0,
        old(t).i < final(t).i <= s@.len(),
        final(buf).wf(),
        final(cb).wf(),
{
    let ghost out1 = out@;
    proof {
        assert(out1 =~= o0 + out1.skip(o0.len() as int));
    }
    let (c, len, w) = skip_fast(s, t, fast, Ghost(cs), Ghost(out1.skip(o0.len() as int)), compose, compat);
    let n = s.len();
    if t.i >= n {
        return;
    }
    reveal(scan_inv);
    let ghost (kd, ki, kp) = (t.kd@, t.ki@, t.kp@);
    proof {
        lemma_enc_char(s@, cs, ki);
        lemma_utf8_bytes_len(cs[ki]);
    }
    let i = t.i;
    let done = t.done;
    let f = (w >> 16) as u16;
    let back = !(i == done || f & bbf != 0);
    let ghost kst: int = if back { kp } else { ki };
    let st = if back { t.prev } else { i };
    proof {
        if f & bbf != 0 {
            axiom_bb(c, compose, compat);
        }
        if i == done && ki != kd {
            lemma_enc_range(s@, cs, kd, ki);
            assert(cs.subrange(kd, ki).len() > 0);
            lemma_enc_empty(cs.subrange(kd, ki));
        }
        assert(kst == 0 || boundary(cs[kst], compose, compat));
        lemma_commit(s@, cs, kd, kst, compose, compat);
    }
    // The fast characters before the segment are their own normal form.
    extend(out, slice_subrange(s, done, st));
    proof {
        assert(out@ =~= o0 + enc(nf(cs.take(kst), compose, compat)));
    }
    let e1 = i + len;
    let mut e = e1;
    let ghost mut ke = ki + 1;
    let mut blen: usize = 0;
    let mut bw: u32 = 0;
    let mut handled = false;
    if !compose && !back {
        let (h, l, ww) = seg_single(s, c, w, e1, bbf, compat, out, Ghost(cs), Ghost(ki), Ghost(o0));
        handled = h;
        blen = l;
        bw = ww;
    }
    if !handled {
        let (c0, len0, w0) = if back {
            proof {
                lemma_enc_char(s@, cs, kp);
            }
            let (c0, l0) = decode(s, st, Ghost(cs[kp]));
            (c0, l0, word_of(c0))
        } else {
            (c, len, w)
        };
        let (e2, Ghost(ke2), l, ww) = seg_general(s, st, c0, len0, w0, e1, bbf, compose, compat, buf, cb, out, Ghost(cs), Ghost(kst), Ghost(ki), Ghost(o0));
        e = e2;
        proof {
            ke = ke2;
        }
        blen = l;
        bw = ww;
    }
    proof {
        assert(out@.skip(o0.len() as int) =~= enc(nf(cs.take(ke), compose, compat)));
        assert(out@.take(o0.len() as int) =~= o0);
        lemma_enc_whole(cs, ke);
        lemma_enc_strict(cs, ki, ke);
        if e < n && ke == cs.len() {
            assert(cs.take(ke) =~= cs);
        }
    }
    t.kd = Ghost(ke);
    t.ki = Ghost(ke);
    t.done = e;
    t.i = e;
    absorb(s, t, blen, bw, fast, Ghost(cs), Ghost(out@.skip(o0.len() as int)), compose, compat);
}

/// Appends the normal form of `s`, the UTF-8 encoding of `cs`, to `out`.
pub fn normalize_into(s: &[u8], compose: bool, compat: bool, out: &mut Vec<u8>, Ghost(cs): Ghost<Seq<u32>>)
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        final(out)@ == old(out)@ + enc(nf(cs, compose, compat)),
{
    let n = s.len();
    let fast = fast_flag_of(compose, compat);
    let bbf = bb_flag_of(compose, compat);
    let mut buf = Buf::new();
    let mut cb = Buf::new();
    let ghost o0 = out@;
    let mut t = Scan { done: 0, i: 0, prev: 0, lastcc: 0, kd: Ghost(0), ki: Ghost(0), kp: Ghost(0) };
    proof {
        reveal(scan_inv);
        assert(cs.take(0) =~= Seq::<u32>::empty());
        reveal_with_fuel(decomp_all, 1);
        reveal_with_fuel(reorder_from, 1);
        assert(nf(Seq::<u32>::empty(), compose, compat) =~= Seq::<u32>::empty());
        assert(out@.skip(o0.len() as int) =~= Seq::<u8>::empty());
        assert(out@.take(o0.len() as int) =~= o0);
    }
    while t.i < n
        invariant
            n == s@.len(),
            fast == fast_flag(compose, compat),
            bbf == bb_flag(compose, compat),
            scan_inv(s@, cs, compose, compat, t, out@.skip(o0.len() as int)),
            o0.len() <= out@.len(),
            out@.take(o0.len() as int) == o0,
            buf.wf(),
            cb.wf(),
        decreases n - t.i,
    {
        if !step_ascii(s, &mut t, Ghost(cs), Ghost(out@.skip(o0.len() as int)), compose, compat) {
            step_char(s, &mut t, fast, bbf, compose, compat, &mut buf, &mut cb, out, Ghost(cs), Ghost(o0));
        }
    }
    proof {
        reveal(scan_inv);
        let (kd, ki) = (t.kd@, t.ki@);
        lemma_enc_whole(cs, ki);
        lemma_enc_empty(cs.skip(ki));
        assert(cs.take(ki) =~= cs);
        lemma_commit(s@, cs, kd, ki, compose, compat);
        assert(out@ =~= o0 + out@.skip(o0.len() as int));
    }
    extend(out, slice_subrange(s, t.done, n));
    proof {
        assert(out@ =~= o0 + enc(nf(cs, compose, compat)));
    }
}

/// Whether the scan alone shows `s` is in normal form: every character is
/// fast or, when decomposing, copied through. `false` means "not known".
pub fn quick_check(s: &[u8], compose: bool, compat: bool, Ghost(cs): Ghost<Seq<u32>>) -> (r: bool)
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        r ==> nf(cs, compose, compat) == cs,
{
    let fast = fast_flag_of(compose, compat);
    let mut t = Scan { done: 0, i: 0, prev: 0, lastcc: 0, kd: Ghost(0), ki: Ghost(0), kp: Ghost(0) };
    proof {
        reveal(scan_inv);
        assert(cs.take(0) =~= Seq::<u32>::empty());
        reveal_with_fuel(decomp_all, 1);
        reveal_with_fuel(reorder_from, 1);
        assert(nf(Seq::<u32>::empty(), compose, compat) =~= Seq::<u32>::empty());
    }
    let ghost o = enc(nf(Seq::<u32>::empty(), compose, compat));
    let _ = skip_fast(s, &mut t, fast, Ghost(cs), Ghost(o), compose, compat);
    if t.i < s.len() {
        return false;
    }
    proof {
        reveal(scan_inv);
        let ki = t.ki@;
        lemma_enc_whole(cs, ki);
        lemma_enc_empty(cs.skip(ki));
        assert(cs.take(ki) =~= cs);
        lemma_nf_pass_run(cs, 0, ki, compose, compat);
        assert(cs.subrange(0, ki) =~= cs);
        assert(nf(cs.take(0), compose, compat) + cs =~= cs);
    }
    true
}

/// The same, without the fast path: the whole input is one segment. The
/// tests check `axiom_fast` against this.
pub fn normalize_slow(s: &[u8], compose: bool, compat: bool, out: &mut Vec<u8>, Ghost(cs): Ghost<Seq<u32>>)
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        final(out)@ == old(out)@ + enc(nf(cs, compose, compat)),
{
    let mut buf = Buf::new();
    let mut cb = Buf::new();
    proof {
        assert(cs.take(0) =~= Seq::<u32>::empty());
        assert(enc(Seq::<u32>::empty()).len() == 0);
    }
    if s.len() == 0 {
        proof {
            lemma_enc_empty(cs);
            assert(cs =~= Seq::<u32>::empty());
            reveal_with_fuel(decomp_all, 1);
            reveal_with_fuel(reorder_from, 1);
            reveal_with_fuel(compose_from, 1);
            assert(out@ =~= old(out)@ + enc(nf(cs, compose, compat)));
        }
        return;
    }
    proof {
        lemma_enc_empty(cs);
        lemma_enc_char(s@, cs, 0);
        lemma_enc_whole(cs, cs.len() as int);
        assert(cs.take(cs.len() as int) =~= cs);
    }
    let (c0, len0) = decode(s, 0, Ghost(cs[0]));
    let w0 = word_of(c0);
    let (_e, Ghost(ke), _l, _w) = decompose_seg(s, 0, c0, len0, w0, s.len(), 0, compat, &mut buf, Ghost(cs), Ghost(0), Ghost(cs.len() as int));
    proof {
        assert(cs.subrange(0, ke) =~= cs);
    }
    finish(compose, compat, &buf, &mut cb, out, Ghost(cs));
}

// ---------------------------------------------------------------------------
// Normal forms are scalars
// ---------------------------------------------------------------------------

proof fn lemma_decomp_all_scalars(cs: Seq<u32>, compat: bool)
    requires
        scalars(cs),
    ensures
        scalars(decomp_all(cs, compat)),
    decreases cs.len(),
{
    if cs.len() > 0 {
        lemma_decomp_all_scalars(cs.drop_last(), compat);
        axiom_decomp_scalar(cs.last(), compat);
        let a = decomp_all(cs.drop_last(), compat);
        let b = decomp(cs.last(), compat);
        assert forall|i: int| 0 <= i < (a + b).len() implies is_scalar(#[trigger] (a + b)[i]) by {
            if i >= a.len() {
                assert((a + b)[i] == b[i - a.len()]);
            }
        }
    }
}

proof fn lemma_insert_pos_bound(o: Seq<u32>, k: u8, p: int)
    requires
        0 <= p <= o.len(),
    ensures
        0 <= insert_pos(o, k, p) <= p,
    decreases p,
{
    if p > 0 && ccc(o[p - 1]) > k {
        lemma_insert_pos_bound(o, k, p - 1);
    }
}

proof fn lemma_reorder_scalars(o: Seq<u32>, d: Seq<u32>)
    requires
        scalars(o),
        scalars(d),
    ensures
        scalars(reorder_from(o, d)),
    decreases d.len(),
{
    if d.len() > 0 {
        lemma_reorder_scalars(o, d.drop_last());
        let q = reorder_from(o, d.drop_last());
        let c = d.last();
        assert(is_scalar(d[d.len() - 1]));
        if ccc(c) != 0 {
            lemma_insert_pos_bound(q, ccc(c), q.len() as int);
            let p = insert_pos(q, ccc(c), q.len() as int);
            assert forall|i: int| 0 <= i < q.insert(p, c).len() implies is_scalar(#[trigger] q.insert(p, c)[i]) by {
                if i > p {
                    assert(q.insert(p, c)[i] == q[i - 1]);
                } else if i < p {
                    assert(q.insert(p, c)[i] == q[i]);
                }
            }
        } else {
            assert forall|i: int| 0 <= i < q.push(c).len() implies is_scalar(#[trigger] q.push(c)[i]) by {
                if i < q.len() {
                    assert(q.push(c)[i] == q[i]);
                }
            }
        }
    }
}

proof fn lemma_last_starter_bound(o: Seq<u32>, p: int)
    requires
        0 <= p <= o.len(),
    ensures
        -1 <= last_starter(o, p) < p,
        last_starter(o, p) >= 0 ==> p >= 1,
    decreases p,
{
    if p > 0 && ccc(o[p - 1]) != 0 {
        lemma_last_starter_bound(o, p - 1);
    }
}

proof fn lemma_compose_scalars(o: Seq<u32>, d: Seq<u32>)
    requires
        scalars(o),
        scalars(d),
    ensures
        scalars(compose_from(o, d)),
    decreases d.len(),
{
    if d.len() > 0 {
        lemma_compose_scalars(o, d.drop_last());
        let q = compose_from(o, d.drop_last());
        let c = d.last();
        assert(is_scalar(d[d.len() - 1]));
        lemma_last_starter_bound(q, q.len() as int);
        let l = last_starter(q, q.len() as int);
        if l >= 0 && !blocked(q, l, c) && comp(q[l], c) is Some {
            axiom_comp(q[l], c);
            let r = comp(q[l], c)->0;
            assert forall|i: int| 0 <= i < q.len() implies is_scalar(#[trigger] q.update(l, r)[i]) by {
                if i != l {
                    assert(q.update(l, r)[i] == q[i]);
                }
            }
        } else {
            assert forall|i: int| 0 <= i < q.push(c).len() implies is_scalar(#[trigger] q.push(c)[i]) by {
                if i < q.len() {
                    assert(q.push(c)[i] == q[i]);
                }
            }
        }
    }
}

pub proof fn lemma_nf_scalars(cs: Seq<u32>, compose: bool, compat: bool)
    requires
        scalars(cs),
    ensures
        scalars(nf(cs, compose, compat)),
{
    lemma_decomp_all_scalars(cs, compat);
    lemma_reorder_scalars(seq![], decomp_all(cs, compat));
    if compose {
        lemma_compose_scalars(seq![], reorder_from(seq![], decomp_all(cs, compat)));
    }
}

} // verus!

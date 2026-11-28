//! Byte-class tests over a byte string, eight bytes at a time (SWAR): is
//! some byte an ASCII uppercase letter, and is some byte NUL, CR or LF.
//! These are the per-field checks HTTP/2 and HTTP/3 make on every header
//! name and value (RFC 9113 §8.2.1, RFC 9114 §4.2), most of them short.
//!
//! Each word test is proven, by bit-vector reasoning, to say whether one of
//! the word's eight bytes is in the class. The slice tests read the string
//! as words (the last one overlapping the one before it) and are proven
//! equal to the plain byte-by-byte statement. A string shorter than eight
//! bytes is built into one word in registers from at most two 4-byte or
//! three 1-byte loads, never through a copy to the stack (which stalls
//! store forwarding).
use crate::prims::{get, load_u64_le};
#[cfg(verus_only)]
use crate::prims::{le_bytes, le_word};
use vstd::prelude::*;

verus! {

/// An ASCII uppercase letter, `A` to `Z`.
pub open spec fn upper(c: u8) -> bool {
    0x41 <= c <= 0x5a
}

/// NUL, CR or LF: the bytes no HTTP/2 or HTTP/3 field value may hold.
pub open spec fn nul_cr_lf(c: u8) -> bool {
    c == 0 || c == 0x0d || c == 0x0a
}

/// Some byte of `s` is an uppercase letter.
pub open spec fn any_upper_spec(s: Seq<u8>) -> bool {
    exists|j: int| 0 <= j < s.len() && upper(#[trigger] s[j])
}

/// Some byte of `s` is NUL, CR or LF.
pub open spec fn any_nul_cr_lf_spec(s: Seq<u8>) -> bool {
    exists|j: int| 0 <= j < s.len() && nul_cr_lf(#[trigger] s[j])
}

/// Byte `k` of `w`, least significant first.
pub open spec fn wb(w: u64, k: int) -> u8 {
    if k == 0 {
        w as u8
    } else if k == 1 {
        (w >> 8u64) as u8
    } else if k == 2 {
        (w >> 16u64) as u8
    } else if k == 3 {
        (w >> 24u64) as u8
    } else if k == 4 {
        (w >> 32u64) as u8
    } else if k == 5 {
        (w >> 40u64) as u8
    } else if k == 6 {
        (w >> 48u64) as u8
    } else {
        (w >> 56u64) as u8
    }
}

const LO: u64 = 0x0101_0101_0101_0101;
const HI: u64 = 0x8080_8080_8080_8080;
const LOW7: u64 = 0x7f7f_7f7f_7f7f_7f7f;

/// Whether some byte of `x` is zero. Each byte's low seven bits plus 0x7f
/// set its top bit unless they are all zero, with no carry into the next
/// byte; or-ing in `x` sets it for a byte whose own top bit is set.
#[inline(always)]
pub fn zero_byte(x: u64) -> (r: bool)
    ensures
        r == exists|k: int| 0 <= k < 8 && wb(x, k) == 0,
{
    assert(x & 0x7f7f_7f7f_7f7f_7f7fu64 <= 0x7f7f_7f7f_7f7f_7f7fu64) by (bit_vector);
    let t = ((x & LOW7) + LOW7) | x;
    let r = t & HI != HI;
    assert(r == ((x as u8 == 0) || ((x >> 8u64) as u8 == 0) || ((x >> 16u64) as u8 == 0) || ((x
        >> 24u64) as u8 == 0) || ((x >> 32u64) as u8 == 0) || ((x >> 40u64) as u8 == 0) || ((x
        >> 48u64) as u8 == 0) || ((x >> 56u64) as u8 == 0))) by (bit_vector)
        requires
            t == (((x & 0x7f7f_7f7f_7f7f_7f7fu64) + 0x7f7f_7f7f_7f7f_7f7fu64) as u64) | x,
            r == (t & 0x8080_8080_8080_8080u64 != 0x8080_8080_8080_8080u64),
    ;
    proof {
        lemma_exists8(x, |c: u8| c == 0);
    }
    r
}

/// `exists k < 8. p(wb(w, k))` is the eight-way disjunction.
proof fn lemma_exists8(w: u64, p: spec_fn(u8) -> bool)
    ensures
        (exists|k: int| 0 <= k < 8 && p(#[trigger] wb(w, k))) == (p(w as u8) || p((w >> 8u64) as u8)
            || p((w >> 16u64) as u8) || p((w >> 24u64) as u8) || p((w >> 32u64) as u8) || p((w
            >> 40u64) as u8) || p((w >> 48u64) as u8) || p((w >> 56u64) as u8)),
{
    assert(wb(w, 0) == w as u8);
    assert(wb(w, 1) == (w >> 8u64) as u8);
    assert(wb(w, 2) == (w >> 16u64) as u8);
    assert(wb(w, 3) == (w >> 24u64) as u8);
    assert(wb(w, 4) == (w >> 32u64) as u8);
    assert(wb(w, 5) == (w >> 40u64) as u8);
    assert(wb(w, 6) == (w >> 48u64) as u8);
    assert(wb(w, 7) == (w >> 56u64) as u8);
}

/// Whether some byte of `w` is NUL, CR or LF.
#[inline(always)]
pub fn word_nul_cr_lf(w: u64) -> (r: bool)
    ensures
        r == exists|k: int| 0 <= k < 8 && nul_cr_lf(#[trigger] wb(w, k)),
{
    let a = zero_byte(w);
    let b = zero_byte(w ^ (LO * 0x0d));
    let c = zero_byte(w ^ (LO * 0x0a));
    proof {
        let cr = w ^ 0x0d0d_0d0d_0d0d_0d0du64;
        let lf = w ^ 0x0a0a_0a0a_0a0a_0a0au64;
        assert(LO * 0x0d == 0x0d0d_0d0d_0d0d_0d0du64);
        assert(LO * 0x0a == 0x0a0a_0a0a_0a0a_0a0au64);
        assert forall|k: int| 0 <= k < 8 implies (wb(cr, k) == 0) == (wb(w, k) == 0x0d) && (wb(lf, k)
            == 0) == (wb(w, k) == 0x0a) by {
            lemma_xor_byte(w, k);
        }
        if a || b || c {
            if a {
                let k = choose|k: int| 0 <= k < 8 && wb(w, k) == 0;
                assert(nul_cr_lf(wb(w, k)));
            } else if b {
                let k = choose|k: int| 0 <= k < 8 && wb(cr, k) == 0;
                assert(nul_cr_lf(wb(w, k)));
            } else {
                let k = choose|k: int| 0 <= k < 8 && wb(lf, k) == 0;
                assert(nul_cr_lf(wb(w, k)));
            }
        } else {
            assert forall|k: int| 0 <= k < 8 implies !nul_cr_lf(#[trigger] wb(w, k)) by {
                assert(wb(w, k) != 0);
                assert(wb(cr, k) != 0);
                assert(wb(lf, k) != 0);
            }
        }
    }
    a || b || c
}

/// Byte `k` of `w` xor a repeated byte is byte `k` of `w` xor that byte.
proof fn lemma_xor_byte(w: u64, k: int)
    requires
        0 <= k < 8,
    ensures
        (wb(w ^ 0x0d0d_0d0d_0d0d_0d0du64, k) == 0) == (wb(w, k) == 0x0d),
        (wb(w ^ 0x0a0a_0a0a_0a0a_0a0au64, k) == 0) == (wb(w, k) == 0x0a),
{
    let cr = w ^ 0x0d0d_0d0d_0d0d_0d0du64;
    let lf = w ^ 0x0a0a_0a0a_0a0a_0a0au64;
    assert(((cr as u8 == 0) == (w as u8 == 0x0d)) && (((cr >> 8u64) as u8 == 0) == ((w >> 8u64) as u8
        == 0x0d)) && (((cr >> 16u64) as u8 == 0) == ((w >> 16u64) as u8 == 0x0d)) && (((cr
        >> 24u64) as u8 == 0) == ((w >> 24u64) as u8 == 0x0d)) && (((cr >> 32u64) as u8 == 0) == ((w
        >> 32u64) as u8 == 0x0d)) && (((cr >> 40u64) as u8 == 0) == ((w >> 40u64) as u8 == 0x0d))
        && (((cr >> 48u64) as u8 == 0) == ((w >> 48u64) as u8 == 0x0d)) && (((cr >> 56u64) as u8
        == 0) == ((w >> 56u64) as u8 == 0x0d))) by (bit_vector)
        requires
            cr == w ^ 0x0d0d_0d0d_0d0d_0d0du64,
    ;
    assert(((lf as u8 == 0) == (w as u8 == 0x0a)) && (((lf >> 8u64) as u8 == 0) == ((w >> 8u64) as u8
        == 0x0a)) && (((lf >> 16u64) as u8 == 0) == ((w >> 16u64) as u8 == 0x0a)) && (((lf
        >> 24u64) as u8 == 0) == ((w >> 24u64) as u8 == 0x0a)) && (((lf >> 32u64) as u8 == 0) == ((w
        >> 32u64) as u8 == 0x0a)) && (((lf >> 40u64) as u8 == 0) == ((w >> 40u64) as u8 == 0x0a))
        && (((lf >> 48u64) as u8 == 0) == ((w >> 48u64) as u8 == 0x0a)) && (((lf >> 56u64) as u8
        == 0) == ((w >> 56u64) as u8 == 0x0a))) by (bit_vector)
        requires
            lf == w ^ 0x0a0a_0a0a_0a0a_0a0au64,
    ;
}

/// Whether some byte of `w` is an ASCII uppercase letter. With the top bit
/// of each byte cleared (so no addition carries into the next byte), a byte
/// is in `A..=Z` exactly when adding `0x80 - b'A'` sets its top bit and
/// adding `0x80 - b'Z' - 1` does not; bytes of 0x80 and above are excluded.
#[inline(always)]
pub fn word_upper(w: u64) -> (r: bool)
    ensures
        r == exists|k: int| 0 <= k < 8 && upper(#[trigger] wb(w, k)),
{
    let y = w & !HI;
    assert(w & !0x8080_8080_8080_8080u64 <= 0x7f7f_7f7f_7f7f_7f7fu64) by (bit_vector);
    let ge_a = y + 0x3f3f_3f3f_3f3f_3f3f;
    let gt_z = y + 0x2525_2525_2525_2525;
    let r = ge_a & !gt_z & !w & HI != 0;
    assert(r == ((0x41 <= w as u8 && w as u8 <= 0x5a) || (0x41 <= (w >> 8u64) as u8 && (w >> 8u64)
        as u8 <= 0x5a) || (0x41 <= (w >> 16u64) as u8 && (w >> 16u64) as u8 <= 0x5a) || (0x41 <= (w
        >> 24u64) as u8 && (w >> 24u64) as u8 <= 0x5a) || (0x41 <= (w >> 32u64) as u8 && (w
        >> 32u64) as u8 <= 0x5a) || (0x41 <= (w >> 40u64) as u8 && (w >> 40u64) as u8 <= 0x5a) || (
    0x41 <= (w >> 48u64) as u8 && (w >> 48u64) as u8 <= 0x5a) || (0x41 <= (w >> 56u64) as u8 && (w
        >> 56u64) as u8 <= 0x5a))) by (bit_vector)
        requires
            y == w & !0x8080_8080_8080_8080u64,
            ge_a == (y + 0x3f3f_3f3f_3f3f_3f3fu64) as u64,
            gt_z == (y + 0x2525_2525_2525_2525u64) as u64,
            r == (ge_a & !gt_z & !w & 0x8080_8080_8080_8080u64 != 0),
    ;
    proof {
        lemma_exists8(w, |c: u8| upper(c));
    }
    r
}

/// The bytes of the little-endian word of `b[i..i + 8]` are `b[i..i + 8]`.
proof fn lemma_word_bytes(b: Seq<u8>, i: int, w: u64)
    requires
        0 <= i,
        i + 8 <= b.len(),
        w as nat == le_word(b, i),
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] wb(w, k) == b[i + k],
{
    reveal_with_fuel(le_bytes, 9);
    let (b0, b1, b2, b3) = (b[i] as u64, b[i + 1] as u64, b[i + 2] as u64, b[i + 3] as u64);
    let (b4, b5, b6, b7) = (b[i + 4] as u64, b[i + 5] as u64, b[i + 6] as u64, b[i + 7] as u64);
    assert(w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (
    b6 << 48u64) | (b7 << 56u64)) by {
        lemma_le8(w, b0, b1, b2, b3, b4, b5, b6, b7);
    }
    assert(w as u8 == b0 && (w >> 8u64) as u8 == b1 && (w >> 16u64) as u8 == b2 && (w >> 24u64) as u8
        == b3 && (w >> 32u64) as u8 == b4 && (w >> 40u64) as u8 == b5 && (w >> 48u64) as u8 == b6 && (w
        >> 56u64) as u8 == b7) by (bit_vector)
        requires
            b0 < 256 && b1 < 256 && b2 < 256 && b3 < 256 && b4 < 256 && b5 < 256 && b6 < 256 && b7
                < 256,
            w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64)
                | (b6 << 48u64) | (b7 << 56u64),
    ;
}

/// The arithmetic little-endian value of eight bytes is the or of the
/// shifted bytes.
proof fn lemma_le8(w: u64, b0: u64, b1: u64, b2: u64, b3: u64, b4: u64, b5: u64, b6: u64, b7: u64)
    requires
        b0 < 256 && b1 < 256 && b2 < 256 && b3 < 256 && b4 < 256 && b5 < 256 && b6 < 256 && b7 < 256,
        w as nat == b0 as nat + 256 * (b1 as nat + 256 * (b2 as nat + 256 * (b3 as nat + 256 * (
        b4 as nat + 256 * (b5 as nat + 256 * (b6 as nat + 256 * (b7 as nat + 256 * 0))))))),
    ensures
        w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (
        b6 << 48u64) | (b7 << 56u64),
{
    // Build it up from the top byte: each step is `x * 256 + b == (x << 8) | b`.
    let x7 = b7;
    let x6 = (x7 * 256 + b6) as u64;
    let x5 = (x6 * 256 + b5) as u64;
    let x4 = (x5 * 256 + b4) as u64;
    let x3 = (x4 * 256 + b3) as u64;
    let x2 = (x3 * 256 + b2) as u64;
    let x1 = (x2 * 256 + b1) as u64;
    assert(x6 < 0x1_0000) by (nonlinear_arith) requires x6 == x7 * 256 + b6, x7 < 256, b6 < 256;
    assert(x5 < 0x100_0000) by (nonlinear_arith) requires x5 == x6 * 256 + b5, x6 < 0x1_0000, b5 < 256;
    assert(x4 < 0x1_0000_0000) by (nonlinear_arith) requires x4 == x5 * 256 + b4, x5 < 0x100_0000, b4 < 256;
    assert(x3 < 0x100_0000_0000) by (nonlinear_arith) requires x3 == x4 * 256 + b3, x4 < 0x1_0000_0000, b3 < 256;
    assert(x2 < 0x1_0000_0000_0000) by (nonlinear_arith) requires x2 == x3 * 256 + b2, x3 < 0x100_0000_0000, b2 < 256;
    assert(x1 < 0x100_0000_0000_0000) by (nonlinear_arith) requires x1 == x2 * 256 + b1, x2 < 0x1_0000_0000_0000, b1 < 256;
    assert(w == x1 * 256 + b0) by (nonlinear_arith)
        requires
            w as nat == b0 as nat + 256 * (b1 as nat + 256 * (b2 as nat + 256 * (b3 as nat + 256 * (
            b4 as nat + 256 * (b5 as nat + 256 * (b6 as nat + 256 * (b7 as nat + 256 * 0))))))),
            x1 == x2 * 256 + b1, x2 == x3 * 256 + b2, x3 == x4 * 256 + b3, x4 == x5 * 256 + b4,
            x5 == x6 * 256 + b5, x6 == x7 * 256 + b6, x7 == b7,
    ;
    assert(w == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (
    b6 << 48u64) | (b7 << 56u64)) by (bit_vector)
        requires
            b0 < 256 && b1 < 256 && b2 < 256 && b3 < 256 && b4 < 256 && b5 < 256 && b6 < 256 && b7
                < 256,
            x6 == (x7 * 256 + b6) as u64, x5 == (x6 * 256 + b5) as u64, x4 == (x5 * 256 + b4) as u64,
            x3 == (x4 * 256 + b3) as u64, x2 == (x3 * 256 + b2) as u64, x1 == (x2 * 256 + b1) as u64,
            x7 == b7, w == (x1 * 256 + b0) as u64,
            x1 < 0x100_0000_0000_0000,
    ;
}

/// The four bytes at `b[i..i + 4]`, little-endian, as one 32-bit load.
#[inline(always)]
fn word4(b: &[u8], i: usize) -> (r: u64)
    requires
        i + 4 <= b@.len(),
    ensures
        r == (b@[i as int] as u64) | ((b@[i + 1] as u64) << 8u64) | ((b@[i + 2] as u64) << 16u64) | ((
        b@[i + 3] as u64) << 24u64),
{
    let n = b.len();
    let b0 = get(b, i) as u64;
    let b1 = get(b, i + 1) as u64;
    let b2 = get(b, i + 2) as u64;
    let b3 = get(b, i + 3) as u64;
    // The form the compiler turns into one load.
    let r = b0 + 256 * (b1 + 256 * (b2 + 256 * b3));
    assert(r == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)) by (bit_vector)
        requires
            b0 < 256 && b1 < 256 && b2 < 256 && b3 < 256,
            r == (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) as u64,
    ;
    r
}

/// Which class a scan looks for.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Class {
    /// `upper`.
    Upper,
    /// `nul_cr_lf`.
    NulCrLf,
}

/// Whether `c` is in class `k`.
pub open spec fn in_class(k: Class, c: u8) -> bool {
    match k {
        Class::Upper => upper(c),
        Class::NulCrLf => nul_cr_lf(c),
    }
}

/// Some byte of `s` is in class `k`.
pub open spec fn any_in(k: Class, s: Seq<u8>) -> bool {
    exists|j: int| 0 <= j < s.len() && in_class(k, #[trigger] s[j])
}

#[inline(always)]
fn word_test(k: Class, w: u64) -> (r: bool)
    ensures
        r == exists|j: int| 0 <= j < 8 && in_class(k, #[trigger] wb(w, j)),
{
    match k {
        Class::Upper => {
            let r = word_upper(w);
            proof {
                if r {
                    let j = choose|j: int| 0 <= j < 8 && upper(#[trigger] wb(w, j));
                    assert(in_class(k, wb(w, j)));
                }
            }
            r
        },
        Class::NulCrLf => {
            let r = word_nul_cr_lf(w);
            proof {
                if r {
                    let j = choose|j: int| 0 <= j < 8 && nul_cr_lf(#[trigger] wb(w, j));
                    assert(in_class(k, wb(w, j)));
                }
            }
            r
        },
    }
}

/// Five bytes of `a`, which is in neither class, at bytes 3 to 7.
const PAD3: u64 = 0x6161_6161_6100_0000;

/// Whether some byte of `b` is in class `k`, eight bytes at a time.
#[inline(always)]
pub fn any(k: Class, b: &[u8]) -> (r: bool)
    ensures
        r == any_in(k, b@),
{
    let n = b.len();
    if n < 8 {
        if n == 0 {
            return false;
        }
        let w = if n >= 4 {
            // The first four bytes and the last four, which overlap
            // unless `n` is 8: together every byte.
            let lo = word4(b, 0);
            let hi = word4(b, n - 4);
            let w = lo | (hi << 32u64);
            proof {
                let s = b@;
                let (b0, b1, b2, b3) = (s[0] as u64, s[1] as u64, s[2] as u64, s[3] as u64);
                let m = n - 4;
                let (c0, c1, c2, c3) = (s[m as int] as u64, s[m + 1] as u64, s[m + 2] as u64, s[m + 3] as u64);
                assert(w as u8 == b0 && (w >> 8u64) as u8 == b1 && (w >> 16u64) as u8 == b2 && (w
                    >> 24u64) as u8 == b3 && (w >> 32u64) as u8 == c0 && (w >> 40u64) as u8 == c1 && (w
                    >> 48u64) as u8 == c2 && (w >> 56u64) as u8 == c3) by (bit_vector)
                    requires
                        b0 < 256 && b1 < 256 && b2 < 256 && b3 < 256 && c0 < 256 && c1 < 256 && c2
                            < 256 && c3 < 256,
                        lo == b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64),
                        hi == c0 | (c1 << 8u64) | (c2 << 16u64) | (c3 << 24u64),
                        w == lo | (hi << 32u64),
                ;
                assert forall|j: int| 0 <= j < 8 implies #[trigger] wb(w, j) == (if j < 4 {
                    s[j]
                } else {
                    s[m + j - 4]
                }) by {}
                let pos = |j: int| if j < 4 { j } else { m + j - 4 };
                let inv = |i: int| if i < 4 { i } else { i - m + 4 };
                lemma_cover(k, s, w, pos, inv);
            }
            w
        } else {
            // One to three bytes: the first, the middle and the last are
            // every byte, then padding.
            let b0 = get(b, 0) as u64;
            let bm = get(b, n / 2) as u64;
            let bl = get(b, n - 1) as u64;
            let w = b0 | (bm << 8u64) | (bl << 16u64) | PAD3;
            proof {
                let s = b@;
                assert(w as u8 == b0 && (w >> 8u64) as u8 == bm && (w >> 16u64) as u8 == bl && (w
                    >> 24u64) as u8 == 0x61 && (w >> 32u64) as u8 == 0x61 && (w >> 40u64) as u8 == 0x61
                    && (w >> 48u64) as u8 == 0x61 && (w >> 56u64) as u8 == 0x61) by (bit_vector)
                    requires
                        b0 < 256 && bm < 256 && bl < 256,
                        w == b0 | (bm << 8u64) | (bl << 16u64) | 0x6161_6161_6100_0000u64,
                ;
                let mid = (n / 2) as int;
                let last = (n - 1) as int;
                assert forall|j: int| 0 <= j < 3 implies #[trigger] wb(w, j) == s[if j == 0 {
                    0
                } else if j == 1 {
                    mid
                } else {
                    last
                }] by {}
                assert forall|j: int| 3 <= j < 8 implies #[trigger] wb(w, j) == 0x61 by {}
                if any_in(k, s) {
                    let j = choose|j: int| 0 <= j < s.len() && in_class(k, #[trigger] s[j]);
                    // Every byte of `s` is one of the three.
                    assert(j == 0 || j == mid || j == last);
                    let q = if j == 0 { 0int } else if j == mid { 1int } else { 2int };
                    assert(wb(w, q) == s[j]);
                }
                if exists|j: int| 0 <= j < 8 && in_class(k, #[trigger] wb(w, j)) {
                    let j = choose|j: int| 0 <= j < 8 && in_class(k, #[trigger] wb(w, j));
                    assert(j < 3);
                    assert(in_class(k, s[if j == 0 { 0 } else if j == 1 { mid } else { last }]));
                }
            }
            w
        };
        return word_test(k, w);
    }
    let mut i: usize = 0;
    while i < n - 8
        invariant
            n == b@.len(),
            8 <= n,
            i <= n,
            !any_in(k, b@.subrange(0, i as int)),
        decreases n - i,
    {
        let w = load_u64_le(b, i);
        proof {
            lemma_word_bytes(b@, i as int, w);
        }
        if word_test(k, w) {
            proof {
                let j = choose|j: int| 0 <= j < 8 && in_class(k, #[trigger] wb(w, j));
                assert(b@[i + j] == wb(w, j));
            }
            return true;
        }
        proof {
            lemma_extend(k, b@, i as int, w);
        }
        i = i + 8;
    }
    let w = load_u64_le(b, n - 8);
    proof {
        lemma_word_bytes(b@, n - 8, w);
    }
    let r = word_test(k, w);
    proof {
        if r {
            let j = choose|j: int| 0 <= j < 8 && in_class(k, #[trigger] wb(w, j));
            assert(b@[n - 8 + j] == wb(w, j));
        } else {
            assert forall|j: int| 0 <= j < n implies !in_class(k, #[trigger] b@[j]) by {
                if j < i {
                    assert(b@.subrange(0, i as int)[j] == b@[j]);
                } else {
                    assert(wb(w, j - (n - 8)) == b@[j]);
                }
            }
        }
    }
    r
}

/// A word whose bytes are bytes of `s` at `pos(j)`, covering all of `s`,
/// has a byte in class `k` exactly when `s` does.
proof fn lemma_cover(k: Class, s: Seq<u8>, w: u64, pos: spec_fn(int) -> int, inv: spec_fn(int) -> int)
    requires
        4 <= s.len() < 8,
        forall|j: int| 0 <= j < 8 ==> 0 <= #[trigger] pos(j) < s.len() && wb(w, j) == s[pos(j)],
        forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] inv(i) < 8 && pos(inv(i)) == i,
    ensures
        (exists|j: int| 0 <= j < 8 && in_class(k, #[trigger] wb(w, j))) == any_in(k, s),
{
    if any_in(k, s) {
        let i = choose|i: int| 0 <= i < s.len() && in_class(k, #[trigger] s[i]);
        let j = inv(i);
        assert(in_class(k, wb(w, j)));
    }
    if exists|j: int| 0 <= j < 8 && in_class(k, #[trigger] wb(w, j)) {
        let j = choose|j: int| 0 <= j < 8 && in_class(k, #[trigger] wb(w, j));
        assert(in_class(k, s[pos(j)]));
    }
}

/// No byte of `b[..i]` nor of the word at `i` is in class `k`: none of
/// `b[..i + 8]` is.
proof fn lemma_extend(k: Class, b: Seq<u8>, i: int, w: u64)
    requires
        0 <= i,
        i + 8 <= b.len(),
        !any_in(k, b.subrange(0, i)),
        forall|j: int| 0 <= j < 8 ==> #[trigger] wb(w, j) == b[i + j],
        !exists|j: int| 0 <= j < 8 && in_class(k, #[trigger] wb(w, j)),
    ensures
        !any_in(k, b.subrange(0, i + 8)),
{
    assert forall|j: int| 0 <= j < i + 8 implies !in_class(k, #[trigger] b.subrange(0, i + 8)[j]) by {
        if j < i {
            assert(b.subrange(0, i)[j] == b[j]);
        } else {
            assert(wb(w, j - i) == b[j]);
        }
    }
}

/// Some byte of `b` is an ASCII uppercase letter.
#[inline(always)]
pub fn any_upper(b: &[u8]) -> (r: bool)
    ensures
        r == any_upper_spec(b@),
{
    let r = any(Class::Upper, b);
    proof {
        if r {
            let j = choose|j: int| 0 <= j < b@.len() && in_class(Class::Upper, #[trigger] b@[j]);
            assert(upper(b@[j]));
        }
        if any_upper_spec(b@) {
            let j = choose|j: int| 0 <= j < b@.len() && upper(#[trigger] b@[j]);
            assert(in_class(Class::Upper, b@[j]));
        }
    }
    r
}

/// Some byte of `b` is NUL, CR or LF.
#[inline(always)]
pub fn any_nul_cr_lf(b: &[u8]) -> (r: bool)
    ensures
        r == any_nul_cr_lf_spec(b@),
{
    let r = any(Class::NulCrLf, b);
    proof {
        if r {
            let j = choose|j: int| 0 <= j < b@.len() && in_class(Class::NulCrLf, #[trigger] b@[j]);
            assert(nul_cr_lf(b@[j]));
        }
        if any_nul_cr_lf_spec(b@) {
            let j = choose|j: int| 0 <= j < b@.len() && nul_cr_lf(#[trigger] b@[j]);
            assert(in_class(Class::NulCrLf, b@[j]));
        }
    }
    r
}

} // verus!

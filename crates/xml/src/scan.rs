//! Sixteen-byte scanners for the long runs: character data, attribute
//! values, comments, CDATA sections, processing instructions, and the
//! check that every character is a `Char`.
//!
//! Each `*_run16` returns how many of the next sixteen bytes it may skip:
//! bytes outside its stop set, which the caller's lemma shows the spec
//! passes over the same way. A stop set may hold more than the bytes that
//! matter, since the caller's scalar step handles whatever byte comes
//! next. On x86-64 each is a few SSE2 instructions, verified against
//! verilith-simd's specifications (`lanes.rs`). Elsewhere it skips
//! nothing, and the scalar step does all the work.
use crate::chars::*;
#[allow(unused_imports)]
use crate::lanes::*;
use vstd::prelude::*;

verus! {

/// May end a run of character data: `<`, `&`, `]` (of `]]>`) or a
/// carriage return.
pub open spec fn text_stop(c: u8) -> bool {
    c == 0x3C || c == 0x26 || c == 0x5D || c == 0x0D
}

/// May end, or change the normalized value of, an attribute value run
/// quoted by `q`: the quote, `<`, `&`, or a byte up to 0x0D (tab, line
/// feed and carriage return among them).
pub open spec fn att_stop(c: u8, q: u8) -> bool {
    c == q || c == 0x3C || c == 0x26 || c <= 0x0D
}

/// Not a one-byte `Char`: a byte from 0x80 up, or a C0 control other
/// than tab, line feed and carriage return.
pub open spec fn char_stop(c: u8) -> bool {
    c >= 0x80 || bad_byte(c)
}

/// May end a CDATA section or need line-end normalization: `]` or a
/// carriage return.
pub open spec fn cdata_stop(c: u8) -> bool {
    c == 0x5D || c == 0x0D
}

} // verus!

#[cfg(target_arch = "x86_64")]
verus! {

use verilith_simd::arch::__m128i;

/// The skip given by a mask whose bit `k` says whether `s[i + k]` stops.
#[inline(always)]
#[allow(unused_variables)]
fn run_of_mask(s: &[u8], i: usize, m: u32, Ghost(f): Ghost<spec_fn(u8) -> bool>) -> (r: usize)
    requires
        i + 16 <= s@.len(),
        m < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(m, k) == f(s@[i + k]),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> !f(#[trigger] s@[q]),
{
    let r = first_set16(m);
    proof {
        assert forall|q: int| i <= q < i + r implies !f(#[trigger] s@[q]) by {
            assert(!bit(m, (q - i) as u32));
            assert(s@[i + (q - i) as u32] == s@[q]);
        }
    }
    r
}

/// Lanes equal to `c` have their top bit set, the others not.
#[inline(always)]
fn eqc(v: __m128i, c: u8) -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 16 ==> (#[trigger] b16(r)[k] >= 0x80) == (b16(v)[k] == c),
{
    eq16(v, splat16(c))
}

/// Lanes at most `c` have their top bit set, the others not.
#[inline(always)]
fn lec(v: __m128i, c: u8) -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 16 ==> (#[trigger] b16(r)[k] >= 0x80) == (b16(v)[k] <= c),
{
    eq16(min16(v, splat16(c)), v)
}

/// Top bits of `a | b`, lane by lane.
#[inline(always)]
fn or2(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 16 ==> (#[trigger] b16(r)[k] >= 0x80) == (b16(a)[k] >= 0x80 || b16(b)[k] >= 0x80),
{
    let r = or16(a, b);
    proof {
        assert forall|k: int| 0 <= k < 16 implies (#[trigger] b16(r)[k] >= 0x80) == (b16(a)[k] >= 0x80 || b16(b)[k]
            >= 0x80) by {
            lemma_top_or(b16(a)[k], b16(b)[k]);
        }
    }
    r
}

/// Bit `k` of the movemask of `x` is set exactly where `f` holds of
/// `s[i + k]`.
#[inline(always)]
#[allow(unused_variables)]
fn mask_of(x: __m128i, s: &[u8], i: usize, Ghost(f): Ghost<spec_fn(u8) -> bool>) -> (m: u32)
    requires
        i + 16 <= s@.len(),
        forall|k: int| 0 <= k < 16 ==> (#[trigger] b16(x)[k] >= 0x80) == f(s@[i + k]),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(m, k) == f(s@[i + k]),
{
    let m = movemask16(x);
    proof {
        assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == f(s@[i + k]) by {
            assert((b16(x)[k as int] >= 0x80) == f(s@[i + k as int]));
        }
    }
    m
}

#[inline(always)]
pub fn text_run16(s: &[u8], i: usize) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> !text_stop(#[trigger] s@[q]),
{
    let v = load16(s, i);
    let x = or2(or2(eqc(v, 0x3C), eqc(v, 0x26)), or2(eqc(v, 0x5D), eqc(v, 0x0D)));
    let ghost f = |c: u8| text_stop(c);
    proof {
        assert forall|k: int| 0 <= k < 16 implies (#[trigger] b16(x)[k] >= 0x80) == f(s@[i + k]) by {
            assert(b16(v)[k] == s@[i + k]);
        }
    }
    let m = mask_of(x, s, i, Ghost(f));
    run_of_mask(s, i, m, Ghost(f))
}

#[inline(always)]
pub fn att_run16(s: &[u8], i: usize, q: u8) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|p: int| i <= p < i + r ==> !att_stop(#[trigger] s@[p], q),
{
    let v = load16(s, i);
    let x = or2(or2(eqc(v, q), eqc(v, 0x3C)), or2(eqc(v, 0x26), lec(v, 0x0D)));
    let ghost f = |c: u8| att_stop(c, q);
    proof {
        assert forall|k: int| 0 <= k < 16 implies (#[trigger] b16(x)[k] >= 0x80) == f(s@[i + k]) by {
            assert(b16(v)[k] == s@[i + k]);
        }
    }
    let m = mask_of(x, s, i, Ghost(f));
    run_of_mask(s, i, m, Ghost(f))
}

#[inline(always)]
pub fn char_run16(s: &[u8], i: usize) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> !char_stop(#[trigger] s@[q]),
{
    let v = load16(s, i);
    let ghost f = |c: u8| char_stop(c);
    let hi = movemask16(v);
    let lo = movemask16(lec(v, 0x1F));
    let ok = movemask16(or2(or2(eqc(v, 0x09), eqc(v, 0x0A)), eqc(v, 0x0D)));
    let m = hi | (lo & !ok);
    proof {
        assert(hi | (lo & !ok) < 0x10000) by (bit_vector)
            requires
                hi < 0x10000 && lo < 0x10000,
        ;
        assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == f(s@[i + k]) by {
            assert(b16(v)[k as int] == s@[i + k]);
            lemma_andnot_bit(lo, ok, k);
            lemma_andnot_bit(hi, lo & !ok, k);
        }
    }
    run_of_mask(s, i, m, Ghost(f))
}

/// ASCII bytes.
#[inline(always)]
pub fn ascii_run16(s: &[u8], i: usize) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> #[trigger] s@[q] < 0x80,
{
    let v = load16(s, i);
    let ghost f = |b: u8| b >= 0x80;
    proof {
        assert forall|k: int| 0 <= k < 16 implies (#[trigger] b16(v)[k] >= 0x80) == f(s@[i + k]) by {
            assert(b16(v)[k] == s@[i + k]);
        }
    }
    let m = mask_of(v, s, i, Ghost(f));
    run_of_mask(s, i, m, Ghost(f))
}

/// Bytes other than `c`.
#[inline(always)]
pub fn byte_run16(s: &[u8], i: usize, c: u8) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> #[trigger] s@[q] != c,
{
    let v = load16(s, i);
    let x = eqc(v, c);
    let ghost f = |b: u8| b == c;
    proof {
        assert forall|k: int| 0 <= k < 16 implies (#[trigger] b16(x)[k] >= 0x80) == f(s@[i + k]) by {
            assert(b16(v)[k] == s@[i + k]);
        }
    }
    let m = mask_of(x, s, i, Ghost(f));
    run_of_mask(s, i, m, Ghost(f))
}

#[inline(always)]
pub fn cdata_run16(s: &[u8], i: usize) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> !cdata_stop(#[trigger] s@[q]),
{
    let v = load16(s, i);
    let x = or2(eqc(v, 0x5D), eqc(v, 0x0D));
    let ghost f = |c: u8| cdata_stop(c);
    proof {
        assert forall|k: int| 0 <= k < 16 implies (#[trigger] b16(x)[k] >= 0x80) == f(s@[i + k]) by {
            assert(b16(v)[k] == s@[i + k]);
        }
    }
    let m = mask_of(x, s, i, Ghost(f));
    run_of_mask(s, i, m, Ghost(f))
}

} // verus!

#[cfg(not(target_arch = "x86_64"))]
verus! {

#[inline(always)]
pub fn text_run16(s: &[u8], i: usize) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> !text_stop(#[trigger] s@[q]),
{
    0
}

#[inline(always)]
pub fn att_run16(s: &[u8], i: usize, q: u8) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|p: int| i <= p < i + r ==> !att_stop(#[trigger] s@[p], q),
{
    0
}

#[inline(always)]
pub fn char_run16(s: &[u8], i: usize) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> !char_stop(#[trigger] s@[q]),
{
    0
}

#[inline(always)]
pub fn byte_run16(s: &[u8], i: usize, c: u8) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> #[trigger] s@[q] != c,
{
    0
}

#[inline(always)]
pub fn ascii_run16(s: &[u8], i: usize) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> #[trigger] s@[q] < 0x80,
{
    0
}

#[inline(always)]
pub fn cdata_run16(s: &[u8], i: usize) -> (r: usize)
    requires
        i + 16 <= s@.len(),
    ensures
        r <= 16,
        forall|q: int| i <= q < i + r ==> !cdata_stop(#[trigger] s@[q]),
{
    0
}

} // verus!

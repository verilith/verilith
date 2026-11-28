//! Normalization of UTF-16, verified against `spec::nf`.
//!
//! The scan of `norm.rs`, over UTF-16 code units instead of UTF-8 bytes, so
//! that UTF-16 text is normalized without converting it. A unit below
//! `fast_below` is a whole character that is fast for the form, which makes
//! the skip loop one comparison per unit. Any other character is one unit
//! or a surrogate pair. The folds over a segment (`Buf`, `insert_exec`,
//! `compose_step_exec`, `insert_decomp`) are the ones `norm.rs` uses.
//!
//! `normalize16_into` and `quick_check16` take well-formed UTF-16: the
//! encoding `enc16s(cs)` of scalars `cs`. `valid16_prefix` finds the
//! longest well-formed prefix of any UTF-16 text, with its scalars, so a
//! caller can split text at unpaired surrogates.
use super::data::*;
use super::norm::{compose_step_exec, insert_decomp, Buf, Scan};
#[cfg(verus_only)]
use super::norm::{lemma_nf_scalars, lemma_seg_scalars};
use super::spec::*;
use super::tables::REC_CCC_LEN;
use crate::utf::conv::get16;
#[cfg(verus_only)]
use crate::utf::conv::simd_ok;
use verilith_simd::cpu::*;
use verilith_simd::neon::has_neon;
#[cfg(verus_only)]
use verilith_simd::neon::neon;
#[cfg(verus_only)]
use crate::utf::spec::{dec16_at, enc16, is_hi, is_lo, is_sur, utf16_len};
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

// ---------------------------------------------------------------------------
// UTF-16
// ---------------------------------------------------------------------------

/// UTF-16 encoding of a sequence of scalars.
pub open spec fn enc16s(cs: Seq<u32>) -> Seq<u16>
    decreases cs.len(),
{
    if cs.len() == 0 {
        seq![]
    } else {
        enc16s(cs.drop_last()) + enc16(cs.last())
    }
}

pub proof fn lemma_e_append(a: Seq<u32>, b: Seq<u32>)
    ensures
        enc16s(a + b) == enc16s(a) + enc16s(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(enc16s(a) + seq![] =~= enc16s(a));
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_e_append(a, b.drop_last());
        assert(enc16s(a) + enc16s(b.drop_last()) + enc16(b.last()) =~= enc16s(a) + (enc16s(b.drop_last()) + enc16(
            b.last())));
    }
}

pub proof fn lemma_e_one(c: u32)
    ensures
        enc16s(seq![c]) == enc16(c),
{
    reveal_with_fuel(enc16s, 2);
    assert(seq![c].drop_last() =~= Seq::<u32>::empty());
    assert(Seq::<u16>::empty() + enc16(c) =~= enc16(c));
}

/// The units of a scalar: one unit outside the surrogates, or a pair.
proof fn lemma_unit(c: u32)
    requires
        is_scalar(c),
    ensures
        ({
            let e = enc16(c);
            &&& e.len() >= 1
            &&& c < 0x10000 ==> e.len() == 1 && e[0] as u32 == c && !is_sur(e[0])
            &&& c >= 0x10000 ==> e.len() == 2 && is_hi(e[0]) && is_lo(e[1]) && 0x10000 + (e[0] as u32 - 0xD800) * 1024
                + (e[1] as u32 - 0xDC00) == c
        }),
{
    if c >= 0x10000 {
        let d = c as int - 0x10000;
        assert(d == (d / 1024) * 1024 + d % 1024 && 0 <= d / 1024 < 1024 && 0 <= d % 1024 < 1024) by (nonlinear_arith)
            requires
                0 <= d < 0x100000,
        ;
    }
}

/// `c`, the character at `s[i..]`, whose first unit `u` is already read.
#[inline(always)]
fn decode16_u(s: &[u16], i: usize, u: u16, Ghost(c): Ghost<u32>) -> (r: (u32, usize))
    requires
        is_scalar(c),
        i + enc16(c).len() <= s@.len(),
        s@.subrange(i as int, i + enc16(c).len()) == enc16(c),
        s@[i as int] == u,
    ensures
        r.0 == c,
        r.1 == enc16(c).len(),
{
    proof {
        lemma_unit(c);
        let e = enc16(c);
        assert forall|k: int| 0 <= k < e.len() implies s@[i + k] == e[k] by {
            assert(s@.subrange(i as int, i + e.len())[k] == s@[i + k]);
        }
        assert(s@[i as int] == e[0]);
    }
    if u < 0xD800 || u > 0xDFFF {
        (u as u32, 1)
    } else {
        assert(c >= 0x10000);
        let _n = s.len();
        let lo = get16(s, i + 1);
        (0x10000 + (u as u32 - 0xD800) * 1024 + (lo as u32 - 0xDC00), 2)
    }
}

#[inline(always)]
fn decode16(s: &[u16], i: usize, Ghost(c): Ghost<u32>) -> (r: (u32, usize))
    requires
        is_scalar(c),
        i + enc16(c).len() <= s@.len(),
        s@.subrange(i as int, i + enc16(c).len()) == enc16(c),
    ensures
        r.0 == c,
        r.1 == enc16(c).len(),
{
    proof {
        lemma_unit(c);
    }
    let u = get16(s, i);
    decode16_u(s, i, u, Ghost(c))
}

/// Appends scalar `c` to `out` in UTF-16 (one unit, or a surrogate pair).
#[inline(always)]
pub fn push16(out: &mut Vec<u16>, c: u32)
    requires
        is_scalar(c),
    ensures
        final(out)@ == old(out)@ + enc16(c),
{
    if c < 0x10000 {
        out.push(c as u16);
        assert(out@ =~= old(out)@ + enc16(c));
    } else {
        let d = c - 0x10000;
        out.push((0xD800 + d / 1024) as u16);
        out.push((0xDC00 + d % 1024) as u16);
        assert(out@ =~= old(out)@ + enc16(c));
    }
}

/// Appends `s` to `v`.
#[inline]
pub fn extend16(v: &mut Vec<u16>, s: &[u16])
    ensures
        final(v)@ == old(v)@ + s@,
{
    v.extend_from_slice(s);
    proof {
        assert forall|i: int| 0 <= i < final(v)@.len() implies #[trigger] final(v)@[i] == (old(v)@ + s@)[i] by {
            if i >= old(v)@.len() {
                assert(cloned::<u16>(s@[i - old(v)@.len()], final(v)@[i]));
            }
        }
        assert(final(v)@ =~= old(v)@ + s@);
    }
}

/// `enc16s(cs)` splits at character `k`.
proof fn lemma_e_at(cs: Seq<u32>, k: int)
    requires
        0 <= k < cs.len(),
    ensures
        enc16s(cs.skip(k)) == enc16(cs[k]) + enc16s(cs.skip(k + 1)),
        enc16s(cs.take(k + 1)) == enc16s(cs.take(k)) + enc16(cs[k]),
{
    assert(cs.skip(k) =~= seq![cs[k]] + cs.skip(k + 1));
    lemma_e_append(seq![cs[k]], cs.skip(k + 1));
    lemma_e_one(cs[k]);
    assert(cs.take(k + 1).drop_last() =~= cs.take(k));
}

proof fn lemma_e_whole(cs: Seq<u32>, k: int)
    requires
        0 <= k <= cs.len(),
    ensures
        enc16s(cs) == enc16s(cs.take(k)) + enc16s(cs.skip(k)),
{
    assert(cs =~= cs.take(k) + cs.skip(k));
    lemma_e_append(cs.take(k), cs.skip(k));
}

proof fn lemma_e_empty(cs: Seq<u32>)
    ensures
        enc16s(cs).len() == 0 <==> cs.len() == 0,
{
    if cs.len() > 0 {
        assert(cs =~= cs.drop_last() + seq![cs.last()]);
        lemma_e_append(cs.drop_last(), seq![cs.last()]);
        lemma_e_one(cs.last());
    }
}

/// The units of characters `a..b` of `cs`.
proof fn lemma_e_range(s: Seq<u16>, cs: Seq<u32>, a: int, b: int)
    requires
        s == enc16s(cs),
        0 <= a <= b <= cs.len(),
    ensures
        enc16s(cs.take(a)).len() <= enc16s(cs.take(b)).len() <= s.len(),
        s.subrange(enc16s(cs.take(a)).len() as int, enc16s(cs.take(b)).len() as int) == enc16s(cs.subrange(a, b)),
{
    assert(cs.take(b) =~= cs.take(a) + cs.subrange(a, b));
    lemma_e_append(cs.take(a), cs.subrange(a, b));
    lemma_e_whole(cs, b);
    assert(s.subrange(enc16s(cs.take(a)).len() as int, enc16s(cs.take(b)).len() as int) =~= enc16s(cs.subrange(a, b)));
}

/// Character `k` of `cs` is at unit `enc16s(cs.take(k)).len()` of `s`.
proof fn lemma_e_char(s: Seq<u16>, cs: Seq<u32>, k: int)
    requires
        s == enc16s(cs),
        0 <= k < cs.len(),
    ensures
        enc16s(cs.take(k)).len() + enc16(cs[k]).len() == enc16s(cs.take(k + 1)).len() <= s.len(),
        s.subrange(enc16s(cs.take(k)).len() as int, enc16s(cs.take(k + 1)).len() as int) == enc16(cs[k]),
{
    lemma_e_range(s, cs, k, k + 1);
    lemma_e_at(cs, k);
    assert(cs.subrange(k, k + 1) =~= seq![cs[k]]);
    lemma_e_one(cs[k]);
}

proof fn lemma_e_strict(cs: Seq<u32>, a: int, b: int)
    requires
        0 <= a < b <= cs.len(),
    ensures
        enc16s(cs.take(a)).len() < enc16s(cs.take(b)).len(),
{
    assert(cs.take(b) =~= cs.take(a) + cs.subrange(a, b));
    lemma_e_append(cs.take(a), cs.subrange(a, b));
    lemma_e_empty(cs.subrange(a, b));
}

proof fn lemma_e_len_full(cs: Seq<u32>, k: int)
    requires
        0 <= k <= cs.len(),
        enc16s(cs.take(k)).len() == enc16s(cs).len(),
    ensures
        k == cs.len(),
{
    lemma_e_whole(cs, k);
    lemma_e_empty(cs.skip(k));
}

/// Where a character starts before the end, there is a character.
proof fn lemma_e_more(s: Seq<u16>, cs: Seq<u32>, k: int)
    requires
        s == enc16s(cs),
        0 <= k <= cs.len(),
        enc16s(cs.take(k)).len() < s.len(),
    ensures
        k < cs.len(),
        enc16s(cs.take(k)).len() + enc16(cs[k]).len() == enc16s(cs.take(k + 1)).len() <= s.len(),
        s.subrange(enc16s(cs.take(k)).len() as int, enc16s(cs.take(k + 1)).len() as int) == enc16(cs[k]),
{
    if k == cs.len() {
        assert(cs.take(k) =~= cs);
    }
    lemma_e_char(s, cs, k);
}

/// A unit below U+D800 where a character starts is that character.
proof fn lemma_e_bmp(s: Seq<u16>, cs: Seq<u32>, k: int)
    requires
        s == enc16s(cs),
        scalars(cs),
        0 <= k <= cs.len(),
        enc16s(cs.take(k)).len() < s.len(),
        s[enc16s(cs.take(k)).len() as int] < 0xD800,
    ensures
        k < cs.len(),
        cs[k] == s[enc16s(cs.take(k)).len() as int] as u32,
        enc16s(cs.take(k + 1)).len() == enc16s(cs.take(k)).len() + 1,
{
    lemma_e_more(s, cs, k);
    lemma_unit(cs[k]);
    let i = enc16s(cs.take(k)).len() as int;
    assert(s.subrange(i, enc16s(cs.take(k + 1)).len() as int)[0] == s[i]);
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

/// A high and a low surrogate are the encoding of their scalar.
proof fn lemma_pair(u: u16, lo: u16)
    requires
        is_hi(u),
        is_lo(lo),
    ensures
        ({
            let c = (0x10000 + (u as u32 - 0xD800) * 1024 + (lo as u32 - 0xDC00)) as u32;
            &&& is_scalar(c)
            &&& c >= 0x10000
            &&& enc16(c) == seq![u, lo]
        }),
{
    let c = (0x10000 + (u as u32 - 0xD800) * 1024 + (lo as u32 - 0xDC00)) as u32;
    let d = c as int - 0x10000;
    assert(d == (u as int - 0xD800) * 1024 + (lo as int - 0xDC00));
    assert((u as int - 0xD800) == d / 1024 && (lo as int - 0xDC00) == d % 1024) by (nonlinear_arith)
        requires
            d == (u as int - 0xD800) * 1024 + (lo as int - 0xDC00),
            0 <= u as int - 0xD800 < 1024,
            0 <= lo as int - 0xDC00 < 1024,
    ;
    assert(enc16(c) =~= seq![u, lo]);
}

/// Appending a character to text and to its scalars.
proof fn lemma_push16(s: Seq<u16>, cs: Seq<u32>, i: int, c: u32)
    requires
        0 <= i,
        i + enc16(c).len() <= s.len(),
        s.take(i) == enc16s(cs),
        s.subrange(i, i + enc16(c).len()) == enc16(c),
    ensures
        s.take(i + enc16(c).len()) == enc16s(cs.push(c)),
{
    assert(cs.push(c).drop_last() =~= cs);
    assert(s.take(i + enc16(c).len()) =~= s.take(i) + s.subrange(i, i + enc16(c).len()));
}

proof fn lemma_sur_mask(x: u16)
    ensures
        ((x & 0xF800u16) == 0xD800u16) == is_sur(x),
{
    assert(((x & 0xF800u16) == 0xD800u16) == (0xD800u16 <= x && x <= 0xDFFFu16)) by (bit_vector);
}

/// None of the 8 units at `i` is a surrogate.
#[inline(always)]
fn clean8(s: &[u16], i: usize) -> (r: bool)
    requires
        i + 8 <= s@.len(),
    ensures
        r ==> forall|k: int| i <= k < i + 8 ==> !is_sur(#[trigger] s@[k]),
{
    let _n = s.len();
    let (a0, a1, a2, a3) = (get16(s, i), get16(s, i + 1), get16(s, i + 2), get16(s, i + 3));
    let (a4, a5, a6, a7) = (get16(s, i + 4), get16(s, i + 5), get16(s, i + 6), get16(s, i + 7));
    let m = ((a0 & 0xF800) == 0xD800) | ((a1 & 0xF800) == 0xD800) | ((a2 & 0xF800) == 0xD800) | ((a3 & 0xF800)
        == 0xD800) | ((a4 & 0xF800) == 0xD800) | ((a5 & 0xF800) == 0xD800) | ((a6 & 0xF800) == 0xD800) | ((a7
        & 0xF800) == 0xD800);
    proof {
        lemma_sur_mask(a0);
        lemma_sur_mask(a1);
        lemma_sur_mask(a2);
        lemma_sur_mask(a3);
        lemma_sur_mask(a4);
        lemma_sur_mask(a5);
        lemma_sur_mask(a6);
        lemma_sur_mask(a7);
        if !m {
            assert forall|k: int| i <= k < i + 8 implies !is_sur(#[trigger] s@[k]) by {
                let d = k - i;
                assert(d == 0 || d == 1 || d == 2 || d == 3 || d == 4 || d == 5 || d == 6 || d == 7);
            }
        }
    }
    !m
}

/// The scalars of `m` units outside the surrogates.
pub open spec fn bmp(s: Seq<u16>, i: int, m: int) -> Seq<u32> {
    Seq::new(m as nat, |k: int| s[i + k] as u32)
}

/// A run of units outside the surrogates is that many characters.
proof fn lemma_bmp_run(s: Seq<u16>, cs: Seq<u32>, i: int, m: int)
    requires
        0 <= i,
        0 <= m,
        i + m <= s.len(),
        s.take(i) == enc16s(cs),
        scalars(cs),
        forall|k: int| i <= k < i + m ==> !is_sur(#[trigger] s[k]),
    ensures
        s.take(i + m) == enc16s(cs + bmp(s, i, m)),
        scalars(cs + bmp(s, i, m)),
    decreases m,
{
    if m == 0 {
        assert(cs + bmp(s, i, m) =~= cs);
    } else {
        lemma_bmp_run(s, cs, i, m - 1);
        let c = s[i + m - 1] as u32;
        assert(!is_sur(s[i + m - 1]));
        assert(enc16(c) =~= s.subrange(i + m - 1, i + m));
        lemma_push16(s, cs + bmp(s, i, m - 1), i + m - 1, c);
        assert((cs + bmp(s, i, m - 1)).push(c) =~= cs + bmp(s, i, m));
    }
}

/// [`valid16_prefix`], 32 units at a time with AVX2 or NEON when `avx`
/// is set, 8 at a time otherwise.
#[inline(always)]
fn valid16_prefix_impl<const NEON: bool>(avx: bool, s: &[u16]) -> (r: (usize, Ghost<Seq<u32>>))
    requires
        avx ==> simd_ok(NEON),
    ensures
        r.0 <= s@.len(),
        scalars(r.1@),
        s@.take(r.0 as int) == enc16s(r.1@),
        r.0 < s@.len() ==> utf16_len(s@, r.0 as int) is None,
{
    let n = s.len();
    let mut i = 0;
    let mut gap: usize = 32;
    let ghost mut cs = Seq::<u32>::empty();
    proof {
        assert(s@.take(0) =~= enc16s(cs));
    }
    while i < n
        invariant
            avx ==> simd_ok(NEON),
            i <= n == s@.len(),
            32 <= gap <= 2048,
            scalars(cs),
            s@.take(i as int) == enc16s(cs),
        decreases n - i,
    {
        // 32 units at a time while no block has a surrogate. After one
        // that has, the next `gap` units go the scalar way below, and
        // `gap` doubles while blocks keep failing, so text dense in
        // surrogate pairs rarely retests.
        let mut lim = n;
        if avx && n - i >= 32 {
            if no_sur32_v::<NEON>(s, i) {
                proof {
                    lemma_bmp_run(s@, cs, i as int, 32);
                    cs = cs + bmp(s@, i as int, 32);
                }
                i += 32;
                gap = 32;
                continue;
            }
            lim = if n - i > gap { i + gap } else { n };
            if gap < 1024 {
                gap = gap * 2;
            }
        }
        let ghost i0 = i;
        assert(i0 < lim);
        while i < lim
            invariant
                i0 <= i <= n == s@.len(),
                i0 < lim <= n,
                scalars(cs),
                s@.take(i as int) == enc16s(cs),
            decreases n - i,
        {
            if n - i >= 8 && clean8(s, i) {
                proof {
                    lemma_bmp_run(s@, cs, i as int, 8);
                    cs = cs + bmp(s@, i as int, 8);
                }
                i += 8;
                continue;
            }
            let u = get16(s, i);
            if u < 0xD800 || u > 0xDFFF {
                proof {
                    assert(enc16(u as u32) =~= s@.subrange(i as int, i + 1));
                    lemma_push16(s@, cs, i as int, u as u32);
                    cs = cs.push(u as u32);
                }
                i += 1;
            } else if u <= 0xDBFF && i + 1 < n {
                let lo = get16(s, i + 1);
                if lo < 0xDC00 || lo > 0xDFFF {
                    return (i, Ghost(cs));
                }
                let c = 0x10000 + (u as u32 - 0xD800) * 1024 + (lo as u32 - 0xDC00);
                proof {
                    lemma_pair(u, lo);
                    assert(enc16(c) =~= s@.subrange(i as int, i + 2));
                    lemma_push16(s@, cs, i as int, c);
                    cs = cs.push(c);
                }
                i += 2;
            } else {
                return (i, Ghost(cs));
            }
        }
    }
    proof {
        assert(s@.take(n as int) =~= s@);
    }
    (i, Ghost(cs))
}

/// Trusted: `crate::utf::avx2::no_sur32` compiled with `avx2` enabled,
/// through `tf::no_sur32_avx2`, out of line, so that the scan around it is
/// compiled without AVX2 (whose code for the scalar steps is slower); the
/// contract is `no_sur32`'s, which is verified.
#[verifier::external_body]
fn no_sur32_avx2(s: &[u16], i: usize) -> (r: bool)
    requires
        avx2(),
        i + 32 <= s.len(),
    ensures
        r ==> forall|k: int| i <= k < i + 32 ==> !(0xD800u16 <= #[trigger] s@[k] && s@[k] <= 0xDFFFu16),
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::no_sur32_avx2(s, i) };
    #[cfg(not(target_arch = "x86_64"))]
    return crate::utf::avx2::no_sur32(s, i);
}

/// No unit of `s[i..i + 32]` is a surrogate (when true): NEON inline, or
/// the AVX2 test out of line.
#[inline(always)]
fn no_sur32_v<const NEON: bool>(s: &[u16], i: usize) -> (r: bool)
    requires
        simd_ok(NEON),
        i + 32 <= s.len(),
    ensures
        r ==> forall|k: int| i <= k < i + 32 ==> !is_sur(#[trigger] s@[k]),
{
    if NEON {
        crate::utf::neon::no_sur32_neon(s, i)
    } else {
        no_sur32_avx2(s, i)
    }
}

/// The longest well-formed prefix of `s`, and its scalars. When it stops
/// before the end, the unit there is an unpaired surrogate.
pub fn valid16_prefix(s: &[u16]) -> (r: (usize, Ghost<Seq<u32>>))
    ensures
        r.0 <= s@.len(),
        scalars(r.1@),
        s@.take(r.0 as int) == enc16s(r.1@),
        r.0 < s@.len() ==> utf16_len(s@, r.0 as int) is None,
{
    if has_avx2() {
        valid16_prefix_impl::<false>(true, s)
    } else if has_neon() {
        valid16_prefix_impl::<true>(true, s)
    } else {
        valid16_prefix_impl::<false>(false, s)
    }
}

/// A sequence of stable characters is its own normal form.
proof fn lemma_stable_nf(cs: Seq<u32>, compose: bool, compat: bool)
    requires
        forall|k: int| 0 <= k < cs.len() ==> stable(#[trigger] cs[k], compose, compat),
    ensures
        nf(cs, compose, compat) == cs,
{
    lemma_nf_stable_run(seq![], cs, compose, compat);
    assert(Seq::<u32>::empty() + cs =~= cs);
    reveal_with_fuel(decomp_all, 1);
    reveal_with_fuel(reorder_from, 1);
    reveal_with_fuel(compose_from, 1);
    assert(nf(Seq::<u32>::empty(), compose, compat) =~= Seq::<u32>::empty());
    assert(Seq::<u32>::empty() + cs =~= cs);
}

/// The prefix of `s` that is its own normal form because every character
/// in it is fast, cut so that the text after it starts with a boundary or
/// an unpaired surrogate: `nf(s)` is the prefix followed by the normal form
/// of the rest. The whole of `s` when it is all fast characters.
pub fn fast_prefix16(s: &[u16], compose: bool, compat: bool) -> (r: (usize, Ghost<Seq<u32>>))
    ensures
        r.0 <= s@.len(),
        scalars(r.1@),
        s@.take(r.0 as int) == enc16s(r.1@),
        nf(r.1@, compose, compat) == r.1@,
        0 < r.0 < s@.len() ==> match utf16_len(s@, r.0 as int) {
            Some(l) => boundary(dec16_at(s@, r.0 as int, l), compose, compat),
            None => true,
        },
{
    let n = s.len();
    let fast = fast_flag_of(compose, compat);
    let bbf = bb_flag_of(compose, compat);
    let fb = fast_below_of(compose, compat);
    let fbu = fb as u16;
    assert(fbu as u32 == fb) by (bit_vector)
        requires
            fb == 0xA0 || fb == 0x300 || fb == 0xC0,
            fbu == fb as u16;
    let mut i: usize = 0;
    let mut prev: usize = 0;
    let ghost mut cs = Seq::<u32>::empty();
    proof {
        assert(s@.take(0) =~= enc16s(cs));
    }
    while i < n
        invariant
            i <= n == s@.len(),
            fast == fast_flag(compose, compat),
            bbf == bb_flag(compose, compat),
            fb == fast_below(compose, compat),
            fbu as u32 == fb,
            scalars(cs),
            s@.take(i as int) == enc16s(cs),
            forall|k: int| 0 <= k < cs.len() ==> stable(#[trigger] cs[k], compose, compat),
            cs.len() > 0 ==> prev < i && utf16_len(s@, prev as int) == Some(i - prev) && dec16_at(
                s@,
                prev as int,
                i - prev,
            ) == cs.last() && prev + enc16(cs.last()).len() == i,
            cs.len() == 0 <==> i == 0,
        decreases n - i,
    {
        let u = get16(s, i);
        if u < fbu {
            // A unit below `fast_below` is a fast character.
            proof {
                let c = u as u32;
                assert(enc16(c) =~= s@.subrange(i as int, i + 1));
                axiom_fast_below(c, compose, compat);
                axiom_fast(c, compose, compat);
                lemma_push16(s@, cs, i as int, c);
                cs = cs.push(c);
            }
            prev = i;
            i += 1;
            continue;
        }
        let (c, len) = if u < 0xD800 || u > 0xDFFF {
            proof {
                assert(enc16(u as u32) =~= s@.subrange(i as int, i + 1));
            }
            (u as u32, 1)
        } else if u <= 0xDBFF && i + 1 < n {
            let lo = get16(s, i + 1);
            if lo < 0xDC00 || lo > 0xDFFF {
                proof {
                    lemma_stable_nf(cs, compose, compat);
                }
                return (i, Ghost(cs));
            }
            proof {
                lemma_pair(u, lo);
                assert(enc16((0x10000 + (u as u32 - 0xD800) * 1024 + (lo as u32 - 0xDC00)) as u32) =~= s@.subrange(
                    i as int,
                    i + 2,
                ));
            }
            (0x10000 + (u as u32 - 0xD800) * 1024 + (lo as u32 - 0xDC00), 2)
        } else {
            proof {
                lemma_stable_nf(cs, compose, compat);
            }
            return (i, Ghost(cs));
        };
        proof {
            lemma_unit(c);
        }
        {
            let w = word_of(c);
            let f = (w >> 16) as u16;
            if f & fast == 0 {
                proof {
                    lemma_stable_nf(cs, compose, compat);
                }
                if i == 0 || f & bbf != 0 {
                    proof {
                        if f & bbf != 0 {
                            axiom_bb(c, compose, compat);
                        }
                    }
                    return (i, Ghost(cs));
                }
                // The last fast character is stable, so a boundary.
                let ghost dl = cs.drop_last();
                proof {
                    assert(cs =~= dl.push(cs.last()));
                    assert(enc16s(cs) == enc16s(dl) + enc16(cs.last()));
                    assert(s@.take(prev as int) =~= s@.take(i as int).take(prev as int));
                    assert(s@.take(prev as int) =~= enc16s(dl));
                    assert(stable(cs[cs.len() - 1], compose, compat));
                    assert forall|k: int| 0 <= k < dl.len() implies stable(#[trigger] dl[k], compose, compat) by {
                        assert(dl[k] == cs[k]);
                    }
                    assert(scalars(dl)) by {
                        assert forall|k: int| 0 <= k < dl.len() implies is_scalar(#[trigger] dl[k]) by {
                            assert(dl[k] == cs[k]);
                        }
                    }
                    lemma_stable_nf(dl, compose, compat);
                }
                return (prev, Ghost(dl));
            }
        }
        proof {
            axiom_fast(c, compose, compat);
            lemma_push16(s@, cs, i as int, c);
            cs = cs.push(c);
        }
        prev = i;
        i += len;
    }
    proof {
        assert(s@.take(n as int) =~= s@);
        lemma_stable_nf(cs, compose, compat);
    }
    (n, Ghost(cs))
}

// ---------------------------------------------------------------------------
// Emitting
// ---------------------------------------------------------------------------

/// Appends the encoding of `decomp(c, compat)`; `w` is `tword(c)`.
#[inline(always)]
fn emit_decomp16(out: &mut Vec<u16>, c: u32, w: u32, compat: bool)
    requires
        is_scalar(c),
        w == tword(c),
        (w & 0xFFFF) < REC_CCC_LEN,
    ensures
        final(out)@ == old(out)@ + enc16s(decomp(c, compat)),
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
            out@ == old(out)@ + enc16s(dc.take(m as int)),
        decreases d.len - m,
    {
        let (x, _kx) = decomp_elem(c, kc, compat, &d, m);
        push16(out, x);
        proof {
            lemma_e_at(dc, m as int);
            assert(old(out)@ + enc16s(dc.take(m as int)) + enc16(x) =~= old(out)@ + (enc16s(dc.take(m as int))
                + enc16(x)));
        }
        m += 1;
    }
    proof {
        assert(dc.take(m as int) =~= dc);
    }
}

/// Appends the encoding of `v`, the normal form of `seg`.
fn emit16(v: &Vec<u32>, out: &mut Vec<u16>, Ghost(seg): Ghost<Seq<u32>>, compose: bool, compat: bool)
    requires
        scalars(seg),
        v@ == nf(seg, compose, compat),
    ensures
        final(out)@ == old(out)@ + enc16s(nf(seg, compose, compat)),
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
            out@ == old(out)@ + enc16s(v@.take(k as int)),
        decreases n - k,
    {
        push16(out, v[k]);
        proof {
            lemma_e_at(v@, k as int);
            assert(old(out)@ + enc16s(v@.take(k as int)) + enc16(v@[k as int]) =~= old(out)@ + (enc16s(v@.take(k as int))
                + enc16(v@[k as int])));
        }
        k += 1;
    }
    proof {
        assert(v@.take(k as int) =~= v@);
    }
}

/// Composes (if `compose`) the canonically ordered decomposition of `seg`
/// in `buf`, and appends the encoding of the result.
fn finish16(compose: bool, compat: bool, buf: &Buf, cb: &mut Buf, out: &mut Vec<u16>, Ghost(seg): Ghost<Seq<u32>>)
    requires
        buf.wf(),
        old(cb).wf(),
        scalars(seg),
        buf@ == reorder_from(seq![], decomp_all(seg, compat)),
    ensures
        final(cb).wf(),
        final(out)@ == old(out)@ + enc16s(nf(seg, compose, compat)),
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
        emit16(&cb.cp, out, Ghost(seg), compose, compat);
    } else {
        emit16(&buf.cp, out, Ghost(seg), compose, compat);
    }
}

// ---------------------------------------------------------------------------
// Segments
// ---------------------------------------------------------------------------

/// Decomposes characters from `st` (character `kst`, already decoded as
/// `c0`, `len0`, `w0`) into `buf`, in canonical order: at least up to
/// character `kmin`, then up to the next character with flag `bbf`, or
/// the end. Returns where it stopped, with the length and trie word of the
/// character there.
fn decompose_seg16(
    s: &[u16],
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
        s@ == enc16s(cs),
        scalars(cs),
        0 <= kst < kmin <= cs.len(),
        st == enc16s(cs.take(kst)).len(),
        imin == enc16s(cs.take(kmin)).len(),
        c0 == cs[kst],
        len0 == enc16(c0).len(),
        w0 == tword(c0),
    ensures
        final(buf).wf(),
        kmin <= r.1@ <= cs.len(),
        r.0 == enc16s(cs.take(r.1@)).len(),
        r.1@ < cs.len() ==> has_flag(cs[r.1@], bbf) && r.2 == enc16(cs[r.1@]).len() && r.3 == tword(cs[r.1@]),
        final(buf)@ == reorder_from(seq![], decomp_all(cs.subrange(kst, r.1@), compat)),
{
    let n = s.len();
    buf.clear();
    proof {
        lemma_e_char(s@, cs, kst);
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
            s@ == enc16s(cs),
            scalars(cs),
            0 <= kst < k <= cs.len(),
            kst < kmin <= cs.len(),
            imin == enc16s(cs.take(kmin)).len(),
            i == enc16s(cs.take(k)).len(),
            buf.wf(),
            buf@ == reorder_from(seq![], decomp_all(cs.subrange(kst, k), compat)),
        decreases n - i,
    {
        proof {
            lemma_e_whole(cs, k);
        }
        if i >= n {
            proof {
                lemma_e_len_full(cs, k);
            }
            return (i, Ghost(k), 0, 0);
        }
        proof {
            lemma_e_more(s@, cs, k);
        }
        let (c, len) = decode16(s, i, Ghost(cs[k]));
        let w = word_of(c);
        if i >= imin && (w >> 16) as u16 & bbf != 0 {
            proof {
                if k < kmin {
                    lemma_e_strict(cs, k, kmin);
                }
            }
            return (i, Ghost(k), len, w);
        }
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

// ---------------------------------------------------------------------------
// The scan
// ---------------------------------------------------------------------------

/// Characters `a..b` of `cs` are passable, so normalizing through them
/// appends their units.
proof fn lemma_commit16(s: Seq<u16>, cs: Seq<u32>, a: int, b: int, compose: bool, compat: bool)
    requires
        s == enc16s(cs),
        0 <= a <= b <= cs.len(),
        forall|k: int| a <= k < b ==> #[trigger] passable(cs, a, k, compose, compat),
    ensures
        enc16s(cs.take(a)).len() <= enc16s(cs.take(b)).len() <= s.len(),
        enc16s(nf(cs.take(a), compose, compat)) + s.subrange(
            enc16s(cs.take(a)).len() as int,
            enc16s(cs.take(b)).len() as int,
        ) == enc16s(nf(cs.take(b), compose, compat)),
{
    lemma_e_range(s, cs, a, b);
    lemma_nf_pass_run(cs, a, b, compose, compat);
    lemma_e_append(nf(cs.take(a), compose, compat), cs.subrange(a, b));
}

/// Normalizing through a segment that starts at a boundary (or at the
/// start) appends the segment's normal form.
proof fn lemma_join16(cs: Seq<u32>, a: int, b: int, compose: bool, compat: bool)
    requires
        0 <= a < b <= cs.len(),
        a == 0 || boundary(cs[a], compose, compat),
    ensures
        enc16s(nf(cs.take(b), compose, compat)) == enc16s(nf(cs.take(a), compose, compat)) + enc16s(
            nf(cs.subrange(a, b), compose, compat),
        ),
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
    lemma_e_append(nf(cs.take(a), compose, compat), nf(seg, compose, compat));
}

/// `scan_inv` of `norm.rs`, over units: `out` holds the normal form of the
/// characters before `done` (character `kd`), the characters from `done`
/// to `i` (character `ki`) are passable, and `prev` is where the last
/// stable one starts.
#[verifier::opaque]
pub open spec fn scan16_inv(s: Seq<u16>, cs: Seq<u32>, compose: bool, compat: bool, t: Scan, out: Seq<u16>) -> bool {
    let (kd, ki, kp) = (t.kd@, t.ki@, t.kp@);
    &&& s == enc16s(cs)
    &&& scalars(cs)
    &&& 0 <= kd <= ki <= cs.len()
    &&& t.done == enc16s(cs.take(kd)).len()
    &&& t.i == enc16s(cs.take(ki)).len()
    &&& out == enc16s(nf(cs.take(kd), compose, compat))
    &&& forall|k: int| kd <= k < ki ==> #[trigger] passable(cs, kd, k, compose, compat)
    &&& kd == 0 || kd == cs.len() || boundary(cs[kd], compose, compat)
    &&& ki > kd ==> kd <= kp < ki && stable(cs[kp], compose, compat) && t.prev == enc16s(cs.take(kp)).len()
        && t.lastcc == ccc(cs[ki - 1])
}

/// Steps over fast characters from `t.i` up to the first character that
/// is not fast, or the end.
#[inline(always)]
fn skip_fast16(
    s: &[u16],
    t: &mut Scan,
    fast: u16,
    Ghost(cs): Ghost<Seq<u32>>,
    Ghost(out): Ghost<Seq<u16>>,
    compose: bool,
    compat: bool,
) -> (r: (u32, usize, u32))
    requires
        scan16_inv(s@, cs, compose, compat, *old(t), out),
        fast == fast_flag(compose, compat),
    ensures
        scan16_inv(s@, cs, compose, compat, *final(t), out),
        final(t).done == old(t).done,
        final(t).kd == old(t).kd,
        old(t).i <= final(t).i <= s@.len(),
        final(t).i < s@.len() ==> final(t).ki@ < cs.len() && !has_flag(cs[final(t).ki@], fast) && r.0
            == cs[final(t).ki@] && r.1 == enc16(r.0).len() && r.2 == tword(r.0),
{
    reveal(scan16_inv);
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
    let fbu = fb as u16;
    proof {
        lemma_e_whole(cs, ki);
    }
    while i < n
        invariant
            n == s@.len(),
            s@ == enc16s(cs),
            scalars(cs),
            fast == fast_flag(compose, compat),
            fb == fast_below(compose, compat),
            fbu as u32 == fb,
            0 <= kd <= ki <= cs.len(),
            done == enc16s(cs.take(kd)).len(),
            i == enc16s(cs.take(ki)).len(),
            forall|k: int| kd <= k < ki ==> #[trigger] passable(cs, kd, k, compose, compat),
            ki > kd ==> kd <= kp < ki && stable(cs[kp], compose, compat) && prev == enc16s(cs.take(kp)).len() && lastcc
                == ccc(cs[ki - 1]),
            ki == old(t).ki@ ==> kp == old(t).kp@ && prev == old(t).prev && lastcc == old(t).lastcc,
            old(t).ki@ <= ki,
            old(t).i <= i <= n,
        ensures
            i <= n,
            i < n ==> ki < cs.len() && !has_flag(cs[ki], fast) && res.0 == cs[ki] && res.1 == enc16(res.0).len()
                && res.2 == tword(res.0),
        decreases n - i,
    {
        let u = get16(s, i);
        if u < fbu {
            proof {
                lemma_e_bmp(s@, cs, ki);
                axiom_fast_below(cs[ki], compose, compat);
                axiom_fast(cs[ki], compose, compat);
                kp = ki;
                ki = ki + 1;
                assert(passable(cs, kd, ki - 1, compose, compat));
            }
            prev = i;
            lastcc = 0;
            i += 1;
        } else {
            proof {
                lemma_e_more(s@, cs, ki);
                lemma_tword(cs[ki]);
            }
            let (c, len) = decode16_u(s, i, u, Ghost(cs[ki]));
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
fn absorb16(
    s: &[u16],
    t: &mut Scan,
    len: usize,
    w: u32,
    fast: u16,
    Ghost(cs): Ghost<Seq<u32>>,
    Ghost(out): Ghost<Seq<u16>>,
    compose: bool,
    compat: bool,
)
    requires
        scan16_inv(s@, cs, compose, compat, *old(t), out),
        fast == fast_flag(compose, compat),
        old(t).i <= s@.len(),
        old(t).ki@ == old(t).kd@,
        old(t).i < s@.len() ==> old(t).ki@ < cs.len() && len == enc16(cs[old(t).ki@]).len() && w == tword(
            cs[old(t).ki@],
        ),
    ensures
        scan16_inv(s@, cs, compose, compat, *final(t), out),
        old(t).i <= final(t).i <= s@.len(),
{
    if t.i < s.len() && (w >> 16) as u16 & fast != 0 {
        reveal(scan16_inv);
        let ghost ki = t.ki@;
        proof {
            axiom_fast(cs[ki], compose, compat);
            lemma_e_char(s@, cs, ki);
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
/// trie word `w`, ending at unit `e1`) normalizes to its decomposition.
/// Returns whether the segment is a single character, and if so the length
/// and trie word of the character after it.
fn seg_single16(
    s: &[u16],
    c: u32,
    w: u32,
    e1: usize,
    bbf: u16,
    compat: bool,
    out: &mut Vec<u16>,
    Ghost(cs): Ghost<Seq<u32>>,
    Ghost(ki): Ghost<int>,
    Ghost(o0): Ghost<Seq<u16>>,
) -> (r: (bool, usize, u32))
    requires
        s@ == enc16s(cs),
        scalars(cs),
        0 <= ki < cs.len(),
        c == cs[ki],
        w == tword(c),
        e1 == enc16s(cs.take(ki + 1)).len(),
        bbf == bb_flag(false, compat),
        ki == 0 || boundary(c, false, compat),
        old(out)@ == o0 + enc16s(nf(cs.take(ki), false, compat)),
    ensures
        r.0 ==> final(out)@ == o0 + enc16s(nf(cs.take(ki + 1), false, compat)),
        r.0 ==> (e1 < s@.len() ==> ki + 1 < cs.len() && boundary(cs[ki + 1], false, compat) && r.1 == enc16(
            cs[ki + 1],
        ).len() && r.2 == tword(cs[ki + 1])),
        r.0 ==> (e1 >= s@.len() ==> ki + 1 == cs.len()),
        !r.0 ==> final(out)@ == old(out)@,
{
    let n = s.len();
    proof {
        lemma_e_whole(cs, ki + 1);
        lemma_tword(c);
    }
    let mut nlen: usize = 0;
    let mut nw: u32 = 0;
    if e1 < n {
        proof {
            lemma_e_more(s@, cs, ki + 1);
        }
        let (nc, l) = decode16(s, e1, Ghost(cs[ki + 1]));
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
            lemma_e_len_full(cs, ki + 1);
        }
    }
    emit_decomp16(out, c, w, compat);
    proof {
        axiom_decomp_ordered(c, compat);
        lemma_decomp_all_one(c, compat);
        assert(cs.subrange(ki, ki + 1) =~= seq![c]);
        lemma_join16(cs, ki, ki + 1, false, compat);
        assert(out@ =~= o0 + enc16s(nf(cs.take(ki + 1), false, compat)));
    }
    (true, nlen, nw)
}

/// Normalizes the segment from `st` (character `kst`, decoded as `c0`,
/// `len0`, `w0`) through at least character `ki` (which ends at unit `e1`)
/// up to the next boundary. Returns where it stopped, with the length and
/// trie word of the character there.
fn seg_general16(
    s: &[u16],
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
    out: &mut Vec<u16>,
    Ghost(cs): Ghost<Seq<u32>>,
    Ghost(kst): Ghost<int>,
    Ghost(ki): Ghost<int>,
    Ghost(o0): Ghost<Seq<u16>>,
) -> (r: (usize, Ghost<int>, usize, u32))
    requires
        s@ == enc16s(cs),
        scalars(cs),
        0 <= kst <= ki < cs.len(),
        st == enc16s(cs.take(kst)).len(),
        e1 == enc16s(cs.take(ki + 1)).len(),
        c0 == cs[kst],
        len0 == enc16(c0).len(),
        w0 == tword(c0),
        bbf == bb_flag(compose, compat),
        kst == 0 || boundary(cs[kst], compose, compat),
        old(out)@ == o0 + enc16s(nf(cs.take(kst), compose, compat)),
        old(buf).wf(),
        old(cb).wf(),
    ensures
        final(buf).wf(),
        final(cb).wf(),
        ki < r.1@ <= cs.len(),
        r.0 == enc16s(cs.take(r.1@)).len(),
        r.1@ < cs.len() ==> boundary(cs[r.1@], compose, compat) && r.2 == enc16(cs[r.1@]).len() && r.3 == tword(
            cs[r.1@],
        ),
        final(out)@ == o0 + enc16s(nf(cs.take(r.1@), compose, compat)),
{
    let (e, Ghost(ke), blen, bw) = decompose_seg16(
        s,
        st,
        c0,
        len0,
        w0,
        e1,
        bbf,
        compat,
        buf,
        Ghost(cs),
        Ghost(kst),
        Ghost(ki + 1),
    );
    proof {
        lemma_seg_scalars(cs, kst, ke);
        if ke < cs.len() {
            axiom_bb(cs[ke], compose, compat);
        }
    }
    finish16(compose, compat, buf, cb, out, Ghost(cs.subrange(kst, ke)));
    proof {
        lemma_join16(cs, kst, ke, compose, compat);
        assert(out@ =~= o0 + enc16s(nf(cs.take(ke), compose, compat)));
    }
    (e, Ghost(ke), blen, bw)
}

/// Handles the characters at `t.i`: steps over fast ones, and normalizes
/// the segment around the first one that is not.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn step_char16(
    s: &[u16],
    t: &mut Scan,
    fast: u16,
    bbf: u16,
    compose: bool,
    compat: bool,
    buf: &mut Buf,
    cb: &mut Buf,
    out: &mut Vec<u16>,
    Ghost(cs): Ghost<Seq<u32>>,
    Ghost(o0): Ghost<Seq<u16>>,
)
    requires
        scan16_inv(s@, cs, compose, compat, *old(t), old(out)@.skip(o0.len() as int)),
        o0.len() <= old(out)@.len(),
        old(out)@.take(o0.len() as int) == o0,
        old(t).i < s@.len(),
        fast == fast_flag(compose, compat),
        bbf == bb_flag(compose, compat),
        old(buf).wf(),
        old(cb).wf(),
    ensures
        scan16_inv(s@, cs, compose, compat, *final(t), final(out)@.skip(o0.len() as int)),
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
    let (c, len, w) = skip_fast16(s, t, fast, Ghost(cs), Ghost(out1.skip(o0.len() as int)), compose, compat);
    let n = s.len();
    if t.i >= n {
        return;
    }
    reveal(scan16_inv);
    let ghost (kd, ki, kp) = (t.kd@, t.ki@, t.kp@);
    proof {
        lemma_e_char(s@, cs, ki);
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
            lemma_e_range(s@, cs, kd, ki);
            assert(cs.subrange(kd, ki).len() > 0);
            lemma_e_empty(cs.subrange(kd, ki));
        }
        assert(kst == 0 || boundary(cs[kst], compose, compat));
        lemma_commit16(s@, cs, kd, kst, compose, compat);
    }
    // The passable characters before the segment are their own normal form.
    extend16(out, slice_subrange(s, done, st));
    proof {
        assert(out@ =~= o0 + enc16s(nf(cs.take(kst), compose, compat)));
    }
    let e1 = i + len;
    let mut e = e1;
    let ghost mut ke = ki + 1;
    let mut blen: usize = 0;
    let mut bw: u32 = 0;
    let mut handled = false;
    if !compose && !back {
        let (h, l, ww) = seg_single16(s, c, w, e1, bbf, compat, out, Ghost(cs), Ghost(ki), Ghost(o0));
        handled = h;
        blen = l;
        bw = ww;
    }
    if !handled {
        let (c0, len0, w0) = if back {
            proof {
                lemma_e_char(s@, cs, kp);
            }
            let (c0, l0) = decode16(s, st, Ghost(cs[kp]));
            (c0, l0, word_of(c0))
        } else {
            (c, len, w)
        };
        let (e2, Ghost(ke2), l, ww) = seg_general16(
            s,
            st,
            c0,
            len0,
            w0,
            e1,
            bbf,
            compose,
            compat,
            buf,
            cb,
            out,
            Ghost(cs),
            Ghost(kst),
            Ghost(ki),
            Ghost(o0),
        );
        e = e2;
        proof {
            ke = ke2;
        }
        blen = l;
        bw = ww;
    }
    proof {
        assert(out@.skip(o0.len() as int) =~= enc16s(nf(cs.take(ke), compose, compat)));
        assert(out@.take(o0.len() as int) =~= o0);
        lemma_e_whole(cs, ke);
        lemma_e_strict(cs, ki, ke);
        if e < n && ke == cs.len() {
            assert(cs.take(ke) =~= cs);
        }
    }
    t.kd = Ghost(ke);
    t.ki = Ghost(ke);
    t.done = e;
    t.i = e;
    absorb16(s, t, blen, bw, fast, Ghost(cs), Ghost(out@.skip(o0.len() as int)), compose, compat);
}

/// Appends the normal form of `s`, the UTF-16 encoding of `cs`, to `out`.
pub fn normalize16_into(s: &[u16], compose: bool, compat: bool, out: &mut Vec<u16>, Ghost(cs): Ghost<Seq<u32>>)
    requires
        scalars(cs),
        s@ == enc16s(cs),
    ensures
        final(out)@ == old(out)@ + enc16s(nf(cs, compose, compat)),
{
    let n = s.len();
    let fast = fast_flag_of(compose, compat);
    let bbf = bb_flag_of(compose, compat);
    let mut buf = Buf::new();
    let mut cb = Buf::new();
    let ghost o0 = out@;
    let mut t = Scan { done: 0, i: 0, prev: 0, lastcc: 0, kd: Ghost(0), ki: Ghost(0), kp: Ghost(0) };
    proof {
        reveal(scan16_inv);
        assert(cs.take(0) =~= Seq::<u32>::empty());
        reveal_with_fuel(decomp_all, 1);
        reveal_with_fuel(reorder_from, 1);
        assert(nf(Seq::<u32>::empty(), compose, compat) =~= Seq::<u32>::empty());
        assert(out@.skip(o0.len() as int) =~= Seq::<u16>::empty());
        assert(out@.take(o0.len() as int) =~= o0);
    }
    while t.i < n
        invariant
            n == s@.len(),
            fast == fast_flag(compose, compat),
            bbf == bb_flag(compose, compat),
            scan16_inv(s@, cs, compose, compat, t, out@.skip(o0.len() as int)),
            o0.len() <= out@.len(),
            out@.take(o0.len() as int) == o0,
            buf.wf(),
            cb.wf(),
        decreases n - t.i,
    {
        step_char16(s, &mut t, fast, bbf, compose, compat, &mut buf, &mut cb, out, Ghost(cs), Ghost(o0));
    }
    proof {
        reveal(scan16_inv);
        let (kd, ki) = (t.kd@, t.ki@);
        lemma_e_whole(cs, ki);
        lemma_e_empty(cs.skip(ki));
        assert(cs.take(ki) =~= cs);
        lemma_commit16(s@, cs, kd, ki, compose, compat);
        assert(out@ =~= o0 + out@.skip(o0.len() as int));
    }
    extend16(out, slice_subrange(s, t.done, n));
    proof {
        assert(out@ =~= o0 + enc16s(nf(cs, compose, compat)));
    }
}

/// Whether the scan alone shows `s` is in normal form: every character is
/// fast or, when decomposing, copied through. `false` means "not known".
pub fn quick_check16(s: &[u16], compose: bool, compat: bool, Ghost(cs): Ghost<Seq<u32>>) -> (r: bool)
    requires
        scalars(cs),
        s@ == enc16s(cs),
    ensures
        r ==> nf(cs, compose, compat) == cs,
{
    let fast = fast_flag_of(compose, compat);
    let mut t = Scan { done: 0, i: 0, prev: 0, lastcc: 0, kd: Ghost(0), ki: Ghost(0), kp: Ghost(0) };
    proof {
        reveal(scan16_inv);
        assert(cs.take(0) =~= Seq::<u32>::empty());
        reveal_with_fuel(decomp_all, 1);
        reveal_with_fuel(reorder_from, 1);
        assert(nf(Seq::<u32>::empty(), compose, compat) =~= Seq::<u32>::empty());
    }
    let ghost o = enc16s(nf(Seq::<u32>::empty(), compose, compat));
    let _ = skip_fast16(s, &mut t, fast, Ghost(cs), Ghost(o), compose, compat);
    if t.i < s.len() {
        return false;
    }
    proof {
        reveal(scan16_inv);
        let ki = t.ki@;
        lemma_e_whole(cs, ki);
        lemma_e_empty(cs.skip(ki));
        assert(cs.take(ki) =~= cs);
        lemma_nf_pass_run(cs, 0, ki, compose, compat);
        assert(cs.subrange(0, ki) =~= cs);
        assert(nf(cs.take(0), compose, compat) + cs =~= cs);
    }
    true
}

} // verus!

/// The trampoline that compiles `no_sur32` with AVX2, out of line (see
/// `crate::utf::conv`'s trampolines, which this follows).
#[cfg(target_arch = "x86_64")]
mod tf {
    #[target_feature(enable = "avx2")]
    #[inline(never)]
    pub(super) unsafe fn no_sur32_avx2(s: &[u16], i: usize) -> bool {
        crate::utf::avx2::no_sur32(s, i)
    }
}

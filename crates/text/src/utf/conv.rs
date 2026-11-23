//! The verified transcoders: validation, conversion between UTF-8, UTF-16
//! and Latin-1, and the output sizes callers allocate by.
//!
//! Each converter is written once, with a flag for AVX2, and inlined into a
//! scalar and an AVX2 entry point. With AVX2, runs of 32 ASCII bytes or
//! units move in one step (`avx2::widen32`, `avx2::narrow32`); everything
//! else goes a character at a time. The loop invariant is the same either
//! way: what is written, followed by the spec's output for the text not yet
//! read, is the spec's output for the whole text.
use super::avx2::*;
use super::neon::*;
use verilith_simd::neon::*;
use super::spec::*;
use verilith_core::prims::{copy_in, get, set};
#[allow(unused_imports)]
use verilith_core::utf8::*;
use verilith_simd::cpu::*;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::cpu::group_cpu, verilith_simd::neon::group_neon};


#[inline(always)]
pub fn get16(b: &[u16], i: usize) -> (r: u16)
    requires
        i < b@.len(),
    ensures
        r == b@[i as int],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked(i) }
}

#[inline(always)]
pub fn set16(b: &mut [u16], i: usize, v: u16)
    requires
        i < old(b)@.len(),
    ensures
        final(b)@ == old(b)@.update(i as int, v),
{
    // SAFETY: in bounds by the precondition.
    unsafe { *b.get_unchecked_mut(i) = v }
}

/// Appending one element after `o` written elements.
proof fn lemma_push<T>(before: Seq<T>, after: Seq<T>, o: int, x: T)
    requires
        0 <= o < before.len(),
        after == before.update(o, x),
    ensures
        after.subrange(0, o + 1) == before.subrange(0, o) + seq![x],
{
    assert(after.subrange(0, o + 1) =~= before.subrange(0, o) + seq![x]);
}

// ---------------------------------------------------------------------------
// The 32-wide kernels, AVX2 or NEON
// ---------------------------------------------------------------------------

/// The CPU feature the kernels of one instantiation need.
pub open spec fn simd_ok(neon_k: bool) -> bool {
    if neon_k {
        neon()
    } else {
        avx2()
    }
}

#[inline(always)]
fn v_ascii32<const NEON: bool>(s: &[u8], i: usize) -> (r: bool)
    requires
        simd_ok(NEON),
        i + 32 <= s.len(),
    ensures
        r == ascii(s@, i as int, i + 32),
{
    if NEON {
        ascii32_neon(s, i)
    } else {
        // The CPU has AVX2.
        ascii32(s, i)
    }
}

#[inline(always)]
fn v_ascii64<const NEON: bool>(s: &[u8], i: usize) -> (r: bool)
    requires
        simd_ok(NEON),
        i + 64 <= s.len(),
    ensures
        r ==> ascii(s@, i as int, i + 64),
{
    if NEON {
        ascii64_neon(s, i)
    } else {
        // The CPU has AVX2.
        ascii64(s, i)
    }
}

#[inline(always)]
fn v_widen32<const NEON: bool>(s: &[u8], i: usize, out: &mut [u16], o: usize)
    requires
        simd_ok(NEON),
        i + 32 <= s.len(),
        o + 32 <= old(out).len(),
    ensures
        final(out).len() == old(out).len(),
        forall|k: int|
            0 <= k < final(out).len() ==> #[trigger] final(out)@[k] == if o <= k < o + 32 {
                s@[i + k - o] as u16
            } else {
                old(out)@[k]
            },
{
    if NEON {
        widen32_neon(s, i, out, o)
    } else {
        // The CPU has AVX2.
        widen32(s, i, out, o)
    }
}

#[inline(always)]
fn v_narrow32<const NEON: bool>(s: &[u16], i: usize, out: &mut [u8], o: usize)
    requires
        simd_ok(NEON),
        i + 32 <= s.len(),
        o + 32 <= old(out).len(),
        forall|k: int| i <= k < i + 32 ==> #[trigger] s@[k] <= 0xFF,
    ensures
        final(out).len() == old(out).len(),
        forall|k: int|
            0 <= k < final(out).len() ==> #[trigger] final(out)@[k] == if o <= k < o + 32 {
                s@[i + k - o] as u8
            } else {
                old(out)@[k]
            },
{
    if NEON {
        narrow32_neon(s, i, out, o)
    } else {
        // The CPU has AVX2.
        narrow32(s, i, out, o)
    }
}

#[inline(always)]
fn v_below32<const NEON: bool>(s: &[u16], i: usize, ascii_only: bool) -> (r: bool)
    requires
        simd_ok(NEON),
        i + 32 <= s.len(),
    ensures
        r ==> forall|k: int| i <= k < i + 32 ==> #[trigger] s@[k] < (if ascii_only { 0x80u16 } else { 0x100u16 }),
{
    if NEON {
        below32_neon(s, i, ascii_only)
    } else {
        // The CPU has AVX2.
        below32(s, i, ascii_only)
    }
}

// ---------------------------------------------------------------------------
// ASCII
// ---------------------------------------------------------------------------

#[inline(always)]
fn ascii_prefix_impl<const NEON: bool>(avx: bool, s: &[u8]) -> (r: usize)
    requires
        avx ==> simd_ok(NEON),
    ensures
        r <= s.len(),
        ascii(s@, 0, r as int),
        r < s.len() ==> s@[r as int] >= 0x80,
{
    let n = s.len();
    let mut i: usize = 0;
    if avx {
        while n - i >= 64
            invariant
                simd_ok(NEON),
                n == s.len(),
                i <= n,
                ascii(s@, 0, i as int),
            decreases n - i,
        {
            if !v_ascii64::<NEON>(s, i) {
                break;
            }
            i = i + 64;
        }
        while n - i >= 32
            invariant
                simd_ok(NEON),
                n == s.len(),
                i <= n,
                ascii(s@, 0, i as int),
            decreases n - i,
        {
            if !v_ascii32::<NEON>(s, i) {
                break;
            }
            i = i + 32;
        }
    }
    while i < n
        invariant
            n == s.len(),
            i <= n,
            ascii(s@, 0, i as int),
        decreases n - i,
    {
        if get(s, i) >= 0x80 {
            return i;
        }
        i = i + 1;
    }
    i
}

#[inline(always)]
fn ascii_prefix_avx2_body(s: &[u8]) -> (r: usize)
    requires
        avx2(),
    ensures
        r <= s.len(),
        ascii(s@, 0, r as int),
        r < s.len() ==> s@[r as int] >= 0x80,
{
    ascii_prefix_impl::<false>(true, s)
}

/// Trusted: `ascii_prefix_avx2_body` compiled with `avx2` enabled, through
/// `tf::ascii_prefix_avx2`; the contract is `ascii_prefix_avx2_body`'s, which is verified.
#[verifier::external_body]
fn ascii_prefix_avx2(s: &[u8]) -> (r: usize)
    requires
        avx2(),
    ensures
        r <= s.len(),
        ascii(s@, 0, r as int),
        r < s.len() ==> s@[r as int] >= 0x80,
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::ascii_prefix_avx2(s) };
    #[cfg(not(target_arch = "x86_64"))]
    return ascii_prefix_avx2_body(s);
}

/// The length of the longest ASCII prefix of `s`: the index of the first
/// byte at or above 0x80, or the length.
pub fn ascii_prefix(s: &[u8]) -> (r: usize)
    ensures
        r <= s.len(),
        ascii(s@, 0, r as int),
        r < s.len() ==> s@[r as int] >= 0x80,
{
    if has_avx2() {
        // The CPU has AVX2.
        ascii_prefix_avx2(s)
    } else if has_neon() {
        ascii_prefix_impl::<true>(true, s)
    } else {
        ascii_prefix_impl::<false>(false, s)
    }
}

// ---------------------------------------------------------------------------
// Latin-1 to UTF-8
// ---------------------------------------------------------------------------

#[inline(always)]
fn latin1_to_utf8_impl<const NEON: bool>(avx: bool, s: &[u8], out: &mut [u8]) -> (r: usize)
    requires
        avx ==> simd_ok(NEON),
        old(out).len() >= cnt_l1(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        r == cnt_l1(s@, 0),
        final(out)@.subrange(0, r as int) == l1to8(s@, 0),
{
    proof {
        lemma_l1_len(s@, 0);
    }
    let n = s.len();
    let mut i: usize = 0;
    let mut o: usize = 0;
    while i < n
        invariant
            avx ==> simd_ok(NEON),
            n == s.len(),
            i <= n,
            out.len() == old(out).len(),
            out.len() >= cnt_l1(s@, 0),
            l1to8(s@, 0).len() == cnt_l1(s@, 0),
            o <= out.len(),
            o + l1to8(s@, i as int).len() == l1to8(s@, 0).len(),
            out@.subrange(0, o as int) + l1to8(s@, i as int) == l1to8(s@, 0),
        decreases n - i,
    {
        let ghost before = out@;
        let ghost rest = l1to8(s@, i as int);
        proof {
            lemma_l1_len(s@, i as int);
            assert(o + rest.len() == l1to8(s@, 0).len());
        }
        // SAFETY: the CPU has AVX2 when `avx` is set.
        if avx && n - i >= 32 && v_ascii32::<NEON>(s, i) {
            proof {
                lemma_ascii_l1to8(s@, i as int, 32);
            }
            copy_in(out, o, s, i, 32);
            proof {
                assert(out@.subrange(0, o + 32) =~= before.subrange(0, o as int) + s@.subrange(i as int, i + 32));
                assert(out@.subrange(0, o + 32) + l1to8(s@, i + 32) =~= before.subrange(0, o as int) + rest);
            }
            i = i + 32;
            o = o + 32;
        } else {
            let b = get(s, i);
            let c = b as u32;
            if b < 0x80 {
                set(out, o, b);
                proof {
                    lemma_push(before, out@, o as int, b);
                    assert(utf8_encode(c) =~= seq![b]);
                    assert(out@.subrange(0, o + 1) + l1to8(s@, i + 1) =~= before.subrange(0, o as int) + rest);
                }
                o = o + 1;
            } else {
                let x = (0xC0 + c / 64) as u8;
                let y = (0x80 + c % 64) as u8;
                set(out, o, x);
                let ghost mid = out@;
                set(out, o + 1, y);
                proof {
                    lemma_push(before, mid, o as int, x);
                    lemma_push(mid, out@, o + 1, y);
                    assert(utf8_encode(c) =~= seq![x, y]);
                    assert(out@.subrange(0, o + 2) + l1to8(s@, i + 1) =~= before.subrange(0, o as int) + rest);
                }
                o = o + 2;
            }
            i = i + 1;
        }
    }
    proof {
        assert(out@.subrange(0, o as int) + l1to8(s@, n as int) =~= out@.subrange(0, o as int));
    }
    o
}

#[inline(always)]
fn latin1_to_utf8_avx2_body(s: &[u8], out: &mut [u8]) -> (r: usize)
    requires
        avx2(),
        old(out).len() >= cnt_l1(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        r == cnt_l1(s@, 0),
        final(out)@.subrange(0, r as int) == l1to8(s@, 0),
{
    latin1_to_utf8_impl::<false>(true, s, out)
}

/// Trusted: `latin1_to_utf8_avx2_body` compiled with `avx2` enabled, through
/// `tf::latin1_to_utf8_avx2`; the contract is `latin1_to_utf8_avx2_body`'s, which is verified.
#[verifier::external_body]
fn latin1_to_utf8_avx2(s: &[u8], out: &mut [u8]) -> (r: usize)
    requires
        avx2(),
        old(out).len() >= cnt_l1(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        r == cnt_l1(s@, 0),
        final(out)@.subrange(0, r as int) == l1to8(s@, 0),
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::latin1_to_utf8_avx2(s, out) };
    #[cfg(not(target_arch = "x86_64"))]
    return latin1_to_utf8_avx2_body(s, out);
}

/// Writes the UTF-8 of the Latin-1 text `s` at the front of `out`; returns
/// its length.
pub fn latin1_to_utf8(s: &[u8], out: &mut [u8]) -> (r: usize)
    requires
        old(out).len() >= cnt_l1(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        r == cnt_l1(s@, 0),
        final(out)@.subrange(0, r as int) == l1to8(s@, 0),
{
    if has_avx2() {
        // The CPU has AVX2.
        latin1_to_utf8_avx2(s, out)
    } else if has_neon() {
        latin1_to_utf8_impl::<true>(true, s, out)
    } else {
        latin1_to_utf8_impl::<false>(false, s, out)
    }
}

#[inline(always)]
fn latin1_to_utf8_safe_impl<const NEON: bool>(avx: bool, s: &[u8], out: &mut [u8]) -> (r: (usize, usize))
    requires
        avx ==> simd_ok(NEON),
    ensures
        final(out).len() == old(out).len(),
        r.0 <= s.len(),
        r.1 <= final(out).len(),
        final(out)@.subrange(0, r.1 as int) + l1to8(s@, r.0 as int) == l1to8(s@, 0),
        r.0 < s.len() ==> r.1 + utf8_encode(s@[r.0 as int] as u32).len() > final(out).len(),
{
    let n = s.len();
    let m = out.len();
    let mut i: usize = 0;
    let mut o: usize = 0;
    proof {
        assert(out@.subrange(0, 0) + l1to8(s@, 0) =~= l1to8(s@, 0));
    }
    while i < n
        invariant
            avx ==> simd_ok(NEON),
            n == s.len(),
            m == out.len(),
            i <= n,
            o <= m,
            out.len() == old(out).len(),
            o <= out.len(),
            o + l1to8(s@, i as int).len() == l1to8(s@, 0).len(),
            out@.subrange(0, o as int) + l1to8(s@, i as int) == l1to8(s@, 0),
        decreases n - i,
    {
        let ghost before = out@;
        let ghost rest = l1to8(s@, i as int);
        // SAFETY: the CPU has AVX2 when `avx` is set.
        if avx && n - i >= 32 && m - o >= 32 && v_ascii32::<NEON>(s, i) {
            proof {
                lemma_ascii_l1to8(s@, i as int, 32);
            }
            copy_in(out, o, s, i, 32);
            proof {
                assert(out@.subrange(0, o + 32) =~= before.subrange(0, o as int) + s@.subrange(i as int, i + 32));
                assert(out@.subrange(0, o + 32) + l1to8(s@, i + 32) =~= before.subrange(0, o as int) + rest);
            }
            i = i + 32;
            o = o + 32;
        } else {
            let b = get(s, i);
            let c = b as u32;
            if b < 0x80 {
                if m - o < 1 {
                    proof {
                        assert(utf8_encode(c).len() == 1);
                    }
                    return (i, o);
                }
                set(out, o, b);
                proof {
                    lemma_push(before, out@, o as int, b);
                    assert(utf8_encode(c) =~= seq![b]);
                    assert(out@.subrange(0, o + 1) + l1to8(s@, i + 1) =~= before.subrange(0, o as int) + rest);
                }
                o = o + 1;
            } else {
                if m - o < 2 {
                    proof {
                        assert(utf8_encode(c).len() == 2);
                    }
                    return (i, o);
                }
                let x = (0xC0 + c / 64) as u8;
                let y = (0x80 + c % 64) as u8;
                set(out, o, x);
                let ghost mid = out@;
                set(out, o + 1, y);
                proof {
                    lemma_push(before, mid, o as int, x);
                    lemma_push(mid, out@, o + 1, y);
                    assert(utf8_encode(c) =~= seq![x, y]);
                    assert(out@.subrange(0, o + 2) + l1to8(s@, i + 1) =~= before.subrange(0, o as int) + rest);
                }
                o = o + 2;
            }
            i = i + 1;
        }
    }
    (i, o)
}

#[inline(always)]
fn latin1_to_utf8_safe_avx2_body(s: &[u8], out: &mut [u8]) -> (r: (usize, usize))
    requires
        avx2(),
    ensures
        final(out).len() == old(out).len(),
        r.0 <= s.len(),
        r.1 <= final(out).len(),
        final(out)@.subrange(0, r.1 as int) + l1to8(s@, r.0 as int) == l1to8(s@, 0),
        r.0 < s.len() ==> r.1 + utf8_encode(s@[r.0 as int] as u32).len() > final(out).len(),
{
    latin1_to_utf8_safe_impl::<false>(true, s, out)
}

/// Trusted: `latin1_to_utf8_safe_avx2_body` compiled with `avx2` enabled, through
/// `tf::latin1_to_utf8_safe_avx2`; the contract is `latin1_to_utf8_safe_avx2_body`'s, which is verified.
#[verifier::external_body]
fn latin1_to_utf8_safe_avx2(s: &[u8], out: &mut [u8]) -> (r: (usize, usize))
    requires
        avx2(),
    ensures
        final(out).len() == old(out).len(),
        r.0 <= s.len(),
        r.1 <= final(out).len(),
        final(out)@.subrange(0, r.1 as int) + l1to8(s@, r.0 as int) == l1to8(s@, 0),
        r.0 < s.len() ==> r.1 + utf8_encode(s@[r.0 as int] as u32).len() > final(out).len(),
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::latin1_to_utf8_safe_avx2(s, out) };
    #[cfg(not(target_arch = "x86_64"))]
    return latin1_to_utf8_safe_avx2_body(s, out);
}

/// Converts as much of the Latin-1 text `s` as fits in `out`, a whole
/// character at a time; returns how much was read and written. What is
/// written is the UTF-8 of what was read, and the next character, if any,
/// does not fit.
pub fn latin1_to_utf8_safe(s: &[u8], out: &mut [u8]) -> (r: (usize, usize))
    ensures
        final(out).len() == old(out).len(),
        r.0 <= s.len(),
        r.1 <= final(out).len(),
        final(out)@.subrange(0, r.1 as int) + l1to8(s@, r.0 as int) == l1to8(s@, 0),
        r.0 < s.len() ==> r.1 + utf8_encode(s@[r.0 as int] as u32).len() > final(out).len(),
{
    if has_avx2() {
        // The CPU has AVX2.
        latin1_to_utf8_safe_avx2(s, out)
    } else if has_neon() {
        latin1_to_utf8_safe_impl::<true>(true, s, out)
    } else {
        latin1_to_utf8_safe_impl::<false>(false, s, out)
    }
}

// ---------------------------------------------------------------------------
// Latin-1 to UTF-16, UTF-16 to Latin-1
// ---------------------------------------------------------------------------

#[inline(always)]
fn latin1_to_utf16_impl<const NEON: bool>(avx: bool, s: &[u8], out: &mut [u16])
    requires
        avx ==> simd_ok(NEON),
        old(out).len() >= s.len(),
    ensures
        final(out).len() == old(out).len(),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] final(out)@[k] == s@[k] as u16,
{
    let n = s.len();
    let mut i: usize = 0;
    while i < n
        invariant
            avx ==> simd_ok(NEON),
            n == s.len(),
            i <= n,
            out.len() == old(out).len(),
            out.len() >= n,
            forall|k: int| 0 <= k < i ==> #[trigger] out@[k] == s@[k] as u16,
        decreases n - i,
    {
        if avx && n - i >= 32 {
            let ghost before = out@;
            v_widen32::<NEON>(s, i, out, i);
            proof {
                assert forall|k: int| 0 <= k < i + 32 implies #[trigger] out@[k] == s@[k] as u16 by {
                    if k < i {
                        assert(out@[k] == before[k]);
                    }
                }
            }
            i = i + 32;
        } else {
            set16(out, i, get(s, i) as u16);
            i = i + 1;
        }
    }
}

#[inline(always)]
fn latin1_to_utf16_avx2_body(s: &[u8], out: &mut [u16])
    requires
        avx2(),
        old(out).len() >= s.len(),
    ensures
        final(out).len() == old(out).len(),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] final(out)@[k] == s@[k] as u16,
{
    latin1_to_utf16_impl::<false>(true, s, out)
}

/// Trusted: `latin1_to_utf16_avx2_body` compiled with `avx2` enabled, through
/// `tf::latin1_to_utf16_avx2`; the contract is `latin1_to_utf16_avx2_body`'s, which is verified.
#[verifier::external_body]
fn latin1_to_utf16_avx2(s: &[u8], out: &mut [u16])
    requires
        avx2(),
        old(out).len() >= s.len(),
    ensures
        final(out).len() == old(out).len(),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] final(out)@[k] == s@[k] as u16,
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::latin1_to_utf16_avx2(s, out) };
    #[cfg(not(target_arch = "x86_64"))]
    return latin1_to_utf16_avx2_body(s, out);
}

/// Widens the Latin-1 text `s` to UTF-16 at the front of `out`.
pub fn latin1_to_utf16(s: &[u8], out: &mut [u16])
    requires
        old(out).len() >= s.len(),
    ensures
        final(out).len() == old(out).len(),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] final(out)@[k] == s@[k] as u16,
{
    if has_avx2() {
        // The CPU has AVX2.
        latin1_to_utf16_avx2(s, out)
    } else if has_neon() {
        latin1_to_utf16_impl::<true>(true, s, out)
    } else {
        latin1_to_utf16_impl::<false>(false, s, out)
    }
}

#[inline(always)]
fn utf16_to_latin1_impl<const NEON: bool>(avx: bool, s: &[u16], out: &mut [u8]) -> (r: bool)
    requires
        avx ==> simd_ok(NEON),
        old(out).len() >= s.len(),
    ensures
        final(out).len() == old(out).len(),
        r == latin1_units(s@),
        r ==> forall|k: int| 0 <= k < s.len() ==> #[trigger] final(out)@[k] == s@[k] as u8,
{
    let n = s.len();
    let mut i: usize = 0;
    while i < n
        invariant
            avx ==> simd_ok(NEON),
            n == s.len(),
            i <= n,
            out.len() == old(out).len(),
            out.len() >= n,
            forall|k: int| 0 <= k < i ==> #[trigger] s@[k] <= 0xFF,
            forall|k: int| 0 <= k < i ==> #[trigger] out@[k] == s@[k] as u8,
        decreases n - i,
    {
        // SAFETY: the CPU has AVX2 when `avx` is set.
        if avx && n - i >= 32 && v_below32::<NEON>(s, i, false) {
            let ghost before = out@;
            v_narrow32::<NEON>(s, i, out, i);
            proof {
                assert forall|k: int| 0 <= k < i + 32 implies #[trigger] out@[k] == s@[k] as u8 by {
                    if k < i {
                        assert(out@[k] == before[k]);
                    }
                }
            }
            i = i + 32;
        } else {
            let u = get16(s, i);
            if u > 0xFF {
                return false;
            }
            set(out, i, u as u8);
            i = i + 1;
        }
    }
    true
}

#[inline(always)]
fn utf16_to_latin1_avx2_body(s: &[u16], out: &mut [u8]) -> (r: bool)
    requires
        avx2(),
        old(out).len() >= s.len(),
    ensures
        final(out).len() == old(out).len(),
        r == latin1_units(s@),
        r ==> forall|k: int| 0 <= k < s.len() ==> #[trigger] final(out)@[k] == s@[k] as u8,
{
    utf16_to_latin1_impl::<false>(true, s, out)
}

/// Trusted: `utf16_to_latin1_avx2_body` compiled with `avx2` enabled, through
/// `tf::utf16_to_latin1_avx2`; the contract is `utf16_to_latin1_avx2_body`'s, which is verified.
#[verifier::external_body]
fn utf16_to_latin1_avx2(s: &[u16], out: &mut [u8]) -> (r: bool)
    requires
        avx2(),
        old(out).len() >= s.len(),
    ensures
        final(out).len() == old(out).len(),
        r == latin1_units(s@),
        r ==> forall|k: int| 0 <= k < s.len() ==> #[trigger] final(out)@[k] == s@[k] as u8,
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::utf16_to_latin1_avx2(s, out) };
    #[cfg(not(target_arch = "x86_64"))]
    return utf16_to_latin1_avx2_body(s, out);
}

/// Narrows the UTF-16 text `s` to Latin-1 at the front of `out`; false if a
/// unit is above 0xFF.
pub fn utf16_to_latin1(s: &[u16], out: &mut [u8]) -> (r: bool)
    requires
        old(out).len() >= s.len(),
    ensures
        final(out).len() == old(out).len(),
        r == latin1_units(s@),
        r ==> forall|k: int| 0 <= k < s.len() ==> #[trigger] final(out)@[k] == s@[k] as u8,
{
    if has_avx2() {
        // The CPU has AVX2.
        utf16_to_latin1_avx2(s, out)
    } else if has_neon() {
        utf16_to_latin1_impl::<true>(true, s, out)
    } else {
        utf16_to_latin1_impl::<false>(false, s, out)
    }
}

// ---------------------------------------------------------------------------
// UTF-8 to UTF-16 and to Latin-1
// ---------------------------------------------------------------------------

/// The character at `i` of a well-formed text: its length and scalar.
#[inline(always)]
fn decode8(s: &[u8], i: usize) -> (r: (usize, u32))
    requires
        i < s.len(),
        utf8_len(s@, i as int) is Some,
    ensures
        r.0 as int == utf8_len(s@, i as int)->0,
        r.1 == dec8_at(s@, i as int, r.0 as int),
        i + r.0 <= s.len(),
{
    proof {
        lemma_dec8_roundtrip(s@, i as int);
    }
    let b0 = get(s, i);
    if b0 < 0x80 {
        (1, b0 as u32)
    } else if b0 < 0xE0 {
        let b1 = get(s, i + 1);
        (2, (((b0 & 0x1F) as u32) << 6u32) | ((b1 & 0x3F) as u32))
    } else if b0 < 0xF0 {
        let b1 = get(s, i + 1);
        let b2 = get(s, i + 2);
        (3, (((b0 & 0x0F) as u32) << 12u32) | (((b1 & 0x3F) as u32) << 6u32) | ((b2 & 0x3F) as u32))
    } else {
        let b1 = get(s, i + 1);
        let b2 = get(s, i + 2);
        let b3 = get(s, i + 3);
        (4, (((b0 & 0x07) as u32) << 18u32) | (((b1 & 0x3F) as u32) << 12u32) | (((b2 & 0x3F) as u32) << 6u32) | ((b3
            & 0x3F) as u32))
    }
}

#[inline(always)]
fn utf8_to_utf16_impl<const NEON: bool>(avx: bool, s: &[u8], out: &mut [u16]) -> (r: usize)
    requires
        avx ==> simd_ok(NEON),
        utf8_from(s@, 0),
        old(out).len() >= cnt8(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        r == cnt8(s@, 0),
        final(out)@.subrange(0, r as int) == u8to16(s@, 0),
{
    proof {
        lemma_u8to16_len(s@, 0);
    }
    let n = s.len();
    let mut i: usize = 0;
    let mut o: usize = 0;
    while i < n
        invariant
            avx ==> simd_ok(NEON),
            n == s.len(),
            i <= n,
            utf8_from(s@, i as int),
            out.len() == old(out).len(),
            out.len() >= cnt8(s@, 0),
            u8to16(s@, 0).len() == cnt8(s@, 0),
            o <= out.len(),
            o + u8to16(s@, i as int).len() == u8to16(s@, 0).len(),
            out@.subrange(0, o as int) + u8to16(s@, i as int) == u8to16(s@, 0),
        decreases n - i,
    {
        let ghost before = out@;
        let ghost rest = u8to16(s@, i as int);
        proof {
            assert(o + rest.len() == u8to16(s@, 0).len());
        }
        // SAFETY: the CPU has AVX2 when `avx` is set.
        if avx && n - i >= 32 && v_ascii32::<NEON>(s, i) {
            proof {
                lemma_ascii_u8to16(s@, i as int, 32);
            }
            v_widen32::<NEON>(s, i, out, o);
            proof {
                let w = Seq::new(32, |t: int| s@[i + t] as u16);
                assert(out@.subrange(0, o + 32) =~= before.subrange(0, o as int) + w);
                assert(out@.subrange(0, o + 32) + u8to16(s@, i + 32) =~= before.subrange(0, o as int) + rest);
            }
            i = i + 32;
            o = o + 32;
        } else {
            let (l, c) = decode8(s, i);
            proof {
                lemma_dec8_roundtrip(s@, i as int);
                assert(rest == enc16(c) + u8to16(s@, i + l));
            }
            if c < 0x10000 {
                set16(out, o, c as u16);
                proof {
                    lemma_push(before, out@, o as int, c as u16);
                    assert(out@.subrange(0, o + 1) + u8to16(s@, i + l) =~= before.subrange(0, o as int) + rest);
                }
                o = o + 1;
            } else {
                let d = c - 0x10000;
                proof {
                    assert(d <= 0xFFFFF ==> d >> 10u32 <= 0x3FF && d & 0x3FF <= 0x3FF) by (bit_vector);
                }
                let x = (0xD800 + (d >> 10u32)) as u16;
                let y = (0xDC00 + (d & 0x3FF)) as u16;
                proof {
                    assert(d >> 10u32 == d / 1024 && d & 0x3FF == d % 1024) by (bit_vector);
                    assert(enc16(c) =~= seq![x, y]);
                }
                set16(out, o, x);
                let ghost mid = out@;
                set16(out, o + 1, y);
                proof {
                    lemma_push(before, mid, o as int, x);
                    lemma_push(mid, out@, o + 1, y);
                    assert(out@.subrange(0, o + 2) + u8to16(s@, i + l) =~= before.subrange(0, o as int) + rest);
                }
                o = o + 2;
            }
            i = i + l;
        }
    }
    proof {
        assert(out@.subrange(0, o as int) + u8to16(s@, n as int) =~= out@.subrange(0, o as int));
    }
    o
}

#[inline(always)]
fn utf8_to_utf16_avx2_body(s: &[u8], out: &mut [u16]) -> (r: usize)
    requires
        avx2(),
        utf8_from(s@, 0),
        old(out).len() >= cnt8(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        r == cnt8(s@, 0),
        final(out)@.subrange(0, r as int) == u8to16(s@, 0),
{
    utf8_to_utf16_impl::<false>(true, s, out)
}

/// Trusted: `utf8_to_utf16_avx2_body` compiled with `avx2` enabled, through
/// `tf::utf8_to_utf16_avx2`; the contract is `utf8_to_utf16_avx2_body`'s, which is verified.
#[verifier::external_body]
fn utf8_to_utf16_avx2(s: &[u8], out: &mut [u16]) -> (r: usize)
    requires
        avx2(),
        utf8_from(s@, 0),
        old(out).len() >= cnt8(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        r == cnt8(s@, 0),
        final(out)@.subrange(0, r as int) == u8to16(s@, 0),
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::utf8_to_utf16_avx2(s, out) };
    #[cfg(not(target_arch = "x86_64"))]
    return utf8_to_utf16_avx2_body(s, out);
}

/// Converts the UTF-8 text `s` to UTF-16 at the front of `out`; `None` if
/// `s` is not well-formed. `out` needs `cnt8(s)` units
/// (`utf16_length_from_utf8`), which is the length of the result.
pub fn utf8_to_utf16(s: &[u8], out: &mut [u16]) -> (r: Option<usize>)
    requires
        old(out).len() >= cnt8(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        (r is Some) == utf8_from(s@, 0),
        r matches Some(n) ==> n == cnt8(s@, 0) && final(out)@.subrange(0, n as int) == u8to16(s@, 0),
{
    if !super::valid8::utf8_valid(s) {
        return None;
    }
    if has_avx2() {
        // The CPU has AVX2.
        Some(utf8_to_utf16_avx2(s, out))
    } else if has_neon() {
        Some(utf8_to_utf16_impl::<true>(true, s, out))
    } else {
        Some(utf8_to_utf16_impl::<false>(false, s, out))
    }
}

#[inline(always)]
fn utf8_to_latin1_impl<const NEON: bool>(avx: bool, s: &[u8], out: &mut [u8]) -> (r: Option<usize>)
    requires
        avx ==> simd_ok(NEON),
        utf8_from(s@, 0),
        old(out).len() >= cnt8l1(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        (r is Some) == latin1_from(s@, 0),
        r matches Some(n) ==> n == cnt8l1(s@, 0) && final(out)@.subrange(0, n as int) == u8tol1(s@, 0),
{
    proof {
        lemma_u8tol1_len(s@, 0);
    }
    let n = s.len();
    let mut i: usize = 0;
    let mut o: usize = 0;
    while i < n
        invariant
            avx ==> simd_ok(NEON),
            n == s.len(),
            i <= n,
            utf8_from(s@, i as int),
            latin1_from(s@, 0) == latin1_from(s@, i as int),
            out.len() == old(out).len(),
            out.len() >= cnt8l1(s@, 0),
            u8tol1(s@, 0).len() == cnt8l1(s@, 0),
            o <= out.len(),
            o + u8tol1(s@, i as int).len() == u8tol1(s@, 0).len(),
            out@.subrange(0, o as int) + u8tol1(s@, i as int) == u8tol1(s@, 0),
        decreases n - i,
    {
        let ghost before = out@;
        let ghost rest = u8tol1(s@, i as int);
        proof {
            assert(o + rest.len() == u8tol1(s@, 0).len());
        }
        // SAFETY: the CPU has AVX2 when `avx` is set.
        if avx && n - i >= 32 && v_ascii32::<NEON>(s, i) {
            proof {
                lemma_ascii_u8to16(s@, i as int, 32);
            }
            copy_in(out, o, s, i, 32);
            proof {
                assert(out@.subrange(0, o + 32) =~= before.subrange(0, o as int) + s@.subrange(i as int, i + 32));
                assert(out@.subrange(0, o + 32) + u8tol1(s@, i + 32) =~= before.subrange(0, o as int) + rest);
            }
            i = i + 32;
            o = o + 32;
        } else {
            let (l, c) = decode8(s, i);
            if c >= 0x100 {
                return None;
            }
            set(out, o, c as u8);
            proof {
                lemma_push(before, out@, o as int, c as u8);
                assert(out@.subrange(0, o + 1) + u8tol1(s@, i + l) =~= before.subrange(0, o as int) + rest);
            }
            o = o + 1;
            i = i + l;
        }
    }
    proof {
        assert(out@.subrange(0, o as int) + u8tol1(s@, n as int) =~= out@.subrange(0, o as int));
    }
    Some(o)
}

#[inline(always)]
fn utf8_to_latin1_avx2_body(s: &[u8], out: &mut [u8]) -> (r: Option<usize>)
    requires
        avx2(),
        utf8_from(s@, 0),
        old(out).len() >= cnt8l1(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        (r is Some) == latin1_from(s@, 0),
        r matches Some(n) ==> n == cnt8l1(s@, 0) && final(out)@.subrange(0, n as int) == u8tol1(s@, 0),
{
    utf8_to_latin1_impl::<false>(true, s, out)
}

/// Trusted: `utf8_to_latin1_avx2_body` compiled with `avx2` enabled, through
/// `tf::utf8_to_latin1_avx2`; the contract is `utf8_to_latin1_avx2_body`'s, which is verified.
#[verifier::external_body]
fn utf8_to_latin1_avx2(s: &[u8], out: &mut [u8]) -> (r: Option<usize>)
    requires
        avx2(),
        utf8_from(s@, 0),
        old(out).len() >= cnt8l1(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        (r is Some) == latin1_from(s@, 0),
        r matches Some(n) ==> n == cnt8l1(s@, 0) && final(out)@.subrange(0, n as int) == u8tol1(s@, 0),
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::utf8_to_latin1_avx2(s, out) };
    #[cfg(not(target_arch = "x86_64"))]
    return utf8_to_latin1_avx2_body(s, out);
}

proof fn lemma_latin1_from_valid(s: Seq<u8>, i: int)
    requires
        0 <= i,
        latin1_from(s, i),
    ensures
        utf8_from(s, i),
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_latin1_from_valid(s, i + utf8_len(s, i)->0);
    }
}

/// Converts the UTF-8 text `s` to Latin-1 at the front of `out`; `None` if
/// it is not well-formed or has a character above U+00FF.
pub fn utf8_to_latin1(s: &[u8], out: &mut [u8]) -> (r: Option<usize>)
    requires
        old(out).len() >= cnt8l1(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        (r is Some) == latin1_from(s@, 0),
        r matches Some(n) ==> n == cnt8l1(s@, 0) && final(out)@.subrange(0, n as int) == u8tol1(s@, 0),
{
    if !super::valid8::utf8_valid(s) {
        proof {
            if latin1_from(s@, 0) {
                lemma_latin1_from_valid(s@, 0);
            }
        }
        return None;
    }
    if has_avx2() {
        // The CPU has AVX2.
        utf8_to_latin1_avx2(s, out)
    } else if has_neon() {
        utf8_to_latin1_impl::<true>(true, s, out)
    } else {
        utf8_to_latin1_impl::<false>(false, s, out)
    }
}

// ---------------------------------------------------------------------------
// UTF-16 to UTF-8
// ---------------------------------------------------------------------------

#[inline(always)]
#[verifier::rlimit(40)]
fn utf16_to_utf8_impl<const NEON: bool>(avx: bool, s: &[u16], out: &mut [u8]) -> (r: Option<usize>)
    requires
        avx ==> simd_ok(NEON),
        old(out).len() >= cnt16(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        (r is Some) == utf16_from(s@, 0),
        r matches Some(n) ==> n == cnt16(s@, 0) && final(out)@.subrange(0, n as int) == u16to8(s@, 0),
{
    proof {
        lemma_u16to8_len(s@, 0);
    }
    let n = s.len();
    let mut i: usize = 0;
    let mut o: usize = 0;
    while i < n
        invariant
            avx ==> simd_ok(NEON),
            n == s.len(),
            i <= n,
            utf16_from(s@, 0) == utf16_from(s@, i as int),
            out.len() == old(out).len(),
            out.len() >= u16to8(s@, 0).len(),
            utf16_from(s@, 0) ==> u16to8(s@, 0).len() == cnt16(s@, 0),
            o <= out.len(),
            o + u16to8(s@, i as int).len() == u16to8(s@, 0).len(),
            out@.subrange(0, o as int) + u16to8(s@, i as int) == u16to8(s@, 0),
        decreases n - i,
    {
        let ghost before = out@;
        let ghost rest = u16to8(s@, i as int);
        proof {
            assert(o + rest.len() == u16to8(s@, 0).len());
        }
        // SAFETY: the CPU has AVX2 when `avx` is set.
        if avx && n - i >= 32 && v_below32::<NEON>(s, i, true) {
            proof {
                lemma_ascii_u16to8(s@, i as int, 32);
            }
            v_narrow32::<NEON>(s, i, out, o);
            proof {
                let w = Seq::new(32, |t: int| s@[i + t] as u8);
                assert(out@.subrange(0, o + 32) =~= before.subrange(0, o as int) + w);
                assert(out@.subrange(0, o + 32) + u16to8(s@, i + 32) =~= before.subrange(0, o as int) + rest);
            }
            i = i + 32;
            o = o + 32;
        } else {
            let u = get16(s, i);
            if u < 0x80 {
                set(out, o, u as u8);
                proof {
                    lemma_push(before, out@, o as int, u as u8);
                    assert(utf8_encode(u as u32) =~= seq![u as u8]);
                    assert(out@.subrange(0, o + 1) + u16to8(s@, i + 1) =~= before.subrange(0, o as int) + rest);
                }
                o = o + 1;
                i = i + 1;
            } else if u < 0x800 {
                let c = u as u32;
                let x = (0xC0 + c / 64) as u8;
                let y = (0x80 + c % 64) as u8;
                set(out, o, x);
                let ghost m1 = out@;
                set(out, o + 1, y);
                proof {
                    lemma_push(before, m1, o as int, x);
                    lemma_push(m1, out@, o + 1, y);
                    assert(utf8_encode(c) =~= seq![x, y]);
                    assert(out@.subrange(0, o + 2) + u16to8(s@, i + 1) =~= before.subrange(0, o as int) + rest);
                }
                o = o + 2;
                i = i + 1;
            } else if u < 0xD800 || u > 0xDFFF {
                let c = u as u32;
                let x = (0xE0 + c / 4096) as u8;
                let y = (0x80 + (c / 64) % 64) as u8;
                let z = (0x80 + c % 64) as u8;
                set(out, o, x);
                let ghost m1 = out@;
                set(out, o + 1, y);
                let ghost m2 = out@;
                set(out, o + 2, z);
                proof {
                    lemma_push(before, m1, o as int, x);
                    lemma_push(m1, m2, o + 1, y);
                    lemma_push(m2, out@, o + 2, z);
                    assert(utf8_encode(c) =~= seq![x, y, z]);
                    assert(out@.subrange(0, o + 3) + u16to8(s@, i + 1) =~= before.subrange(0, o as int) + rest);
                }
                o = o + 3;
                i = i + 1;
            } else if u <= 0xDBFF && n - i >= 2 && 0xDC00 <= get16(s, i + 1) && get16(s, i + 1) <= 0xDFFF {
                let v = get16(s, i + 1);
                let c = (0x10000 + (u as u32 - 0xD800) * 1024 + (v as u32 - 0xDC00)) as u32;
                let x = (0xF0 + c / 262144) as u8;
                let y = (0x80 + (c / 4096) % 64) as u8;
                let z = (0x80 + (c / 64) % 64) as u8;
                let w = (0x80 + c % 64) as u8;
                proof {
                    assert(c == dec16_at(s@, i as int, 2));
                    assert(c >= 0x10000);
                }
                set(out, o, x);
                let ghost m1 = out@;
                set(out, o + 1, y);
                let ghost m2 = out@;
                set(out, o + 2, z);
                let ghost m3 = out@;
                set(out, o + 3, w);
                proof {
                    lemma_push(before, m1, o as int, x);
                    lemma_push(m1, m2, o + 1, y);
                    lemma_push(m2, m3, o + 2, z);
                    lemma_push(m3, out@, o + 3, w);
                    assert(utf8_encode(c) =~= seq![x, y, z, w]);
                    assert(out@.subrange(0, o + 4) + u16to8(s@, i + 2) =~= before.subrange(0, o as int) + rest);
                }
                o = o + 4;
                i = i + 2;
            } else {
                proof {
                    assert(utf16_len(s@, i as int) is None);
                }
                return None;
            }
        }
    }
    proof {
        assert(out@.subrange(0, o as int) + u16to8(s@, n as int) =~= out@.subrange(0, o as int));
    }
    Some(o)
}

#[inline(always)]
fn utf16_to_utf8_avx2_body(s: &[u16], out: &mut [u8]) -> (r: Option<usize>)
    requires
        avx2(),
        old(out).len() >= cnt16(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        (r is Some) == utf16_from(s@, 0),
        r matches Some(n) ==> n == cnt16(s@, 0) && final(out)@.subrange(0, n as int) == u16to8(s@, 0),
{
    utf16_to_utf8_impl::<false>(true, s, out)
}

/// Trusted: `utf16_to_utf8_avx2_body` compiled with `avx2` enabled, through
/// `tf::utf16_to_utf8_avx2`; the contract is `utf16_to_utf8_avx2_body`'s, which is verified.
#[verifier::external_body]
fn utf16_to_utf8_avx2(s: &[u16], out: &mut [u8]) -> (r: Option<usize>)
    requires
        avx2(),
        old(out).len() >= cnt16(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        (r is Some) == utf16_from(s@, 0),
        r matches Some(n) ==> n == cnt16(s@, 0) && final(out)@.subrange(0, n as int) == u16to8(s@, 0),
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::utf16_to_utf8_avx2(s, out) };
    #[cfg(not(target_arch = "x86_64"))]
    return utf16_to_utf8_avx2_body(s, out);
}

/// Converts the UTF-16 text `s` to UTF-8 at the front of `out`; `None` if
/// it is not well-formed. `out` needs `cnt16(s)` bytes
/// (`utf8_length_from_utf16`), which is the length of the result.
pub fn utf16_to_utf8(s: &[u16], out: &mut [u8]) -> (r: Option<usize>)
    requires
        old(out).len() >= cnt16(s@, 0),
    ensures
        final(out).len() == old(out).len(),
        (r is Some) == utf16_from(s@, 0),
        r matches Some(n) ==> n == cnt16(s@, 0) && final(out)@.subrange(0, n as int) == u16to8(s@, 0),
{
    if has_avx2() {
        // The CPU has AVX2.
        utf16_to_utf8_avx2(s, out)
    } else if has_neon() {
        utf16_to_utf8_impl::<true>(true, s, out)
    } else {
        utf16_to_utf8_impl::<false>(false, s, out)
    }
}

// ---------------------------------------------------------------------------
// Output sizes
// ---------------------------------------------------------------------------

/// Inputs this long or longer are refused by the counters (their counts
/// could overflow): an eighth of the address space, 2^61 on 64-bit targets
/// and 2^29 on 32-bit ones (wasm32).
pub const MAX_LEN: usize = usize::MAX / 8 + 1;

#[inline(always)]
fn count_latin1_utf8_impl<const NEON: bool>(avx: bool, s: &[u8]) -> (r: usize)
    requires
        avx ==> simd_ok(NEON),
        s.len() < MAX_LEN,
    ensures
        r == cnt_l1(s@, 0),
{
    let n = s.len();
    let mut i: usize = 0;
    let mut c: usize = 0;
    while i < n
        invariant
            avx ==> simd_ok(NEON),
            n == s.len(),
            n < MAX_LEN,
            i <= n,
            c <= 2 * i,
            c + cnt_l1(s@, i as int) == cnt_l1(s@, 0),
        decreases n - i,
    {
        // SAFETY: the CPU has AVX2 when `avx` is set.
        if avx && n - i >= 32 && v_ascii32::<NEON>(s, i) {
            proof {
                lemma_ascii_l1to8(s@, i as int, 32);
            }
            c = c + 32;
            i = i + 32;
        } else {
            c = c + if get(s, i) >= 0x80 { 2 } else { 1 };
            i = i + 1;
        }
    }
    c
}

#[inline(always)]
fn count_latin1_utf8_avx2_body(s: &[u8]) -> (r: usize)
    requires
        avx2(),
        s.len() < MAX_LEN,
    ensures
        r == cnt_l1(s@, 0),
{
    count_latin1_utf8_impl::<false>(true, s)
}

/// Trusted: `count_latin1_utf8_avx2_body` compiled with `avx2` enabled, through
/// `tf::count_latin1_utf8_avx2`; the contract is `count_latin1_utf8_avx2_body`'s, which is verified.
#[verifier::external_body]
fn count_latin1_utf8_avx2(s: &[u8]) -> (r: usize)
    requires
        avx2(),
        s.len() < MAX_LEN,
    ensures
        r == cnt_l1(s@, 0),
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::count_latin1_utf8_avx2(s) };
    #[cfg(not(target_arch = "x86_64"))]
    return count_latin1_utf8_avx2_body(s);
}

/// `utf8_length_from_latin1`.
pub fn count_latin1_utf8(s: &[u8]) -> (r: usize)
    requires
        s.len() < MAX_LEN,
    ensures
        r == cnt_l1(s@, 0),
{
    if has_avx2() {
        // The CPU has AVX2.
        count_latin1_utf8_avx2(s)
    } else if has_neon() {
        count_latin1_utf8_impl::<true>(true, s)
    } else {
        count_latin1_utf8_impl::<false>(false, s)
    }
}

#[inline(always)]
fn count_utf8_impl<const NEON: bool>(avx: bool, s: &[u8], latin1: bool) -> (r: usize)
    requires
        avx ==> simd_ok(NEON),
        s.len() < MAX_LEN,
    ensures
        r == if latin1 { cnt8l1(s@, 0) } else { cnt8(s@, 0) },
{
    let n = s.len();
    let mut i: usize = 0;
    let mut c: usize = 0;
    while i < n
        invariant
            avx ==> simd_ok(NEON),
            n == s.len(),
            n < MAX_LEN,
            i <= n,
            c <= 2 * i,
            c + (if latin1 { cnt8l1(s@, i as int) } else { cnt8(s@, i as int) }) == if latin1 {
                cnt8l1(s@, 0)
            } else {
                cnt8(s@, 0)
            },
        decreases n - i,
    {
        // SAFETY: the CPU has AVX2 when `avx` is set.
        if avx && n - i >= 32 && v_ascii32::<NEON>(s, i) {
            proof {
                lemma_ascii_u8to16(s@, i as int, 32);
            }
            c = c + 32;
            i = i + 32;
        } else {
            let b = get(s, i);
            let lead: usize = if 0x80 <= b && b <= 0xBF { 0 } else { 1 };
            let four: usize = if !latin1 && b >= 0xF0 { 1 } else { 0 };
            c = c + lead + four;
            i = i + 1;
        }
    }
    c
}

#[inline(always)]
fn count_utf8_avx2_body(s: &[u8], latin1: bool) -> (r: usize)
    requires
        avx2(),
        s.len() < MAX_LEN,
    ensures
        r == if latin1 { cnt8l1(s@, 0) } else { cnt8(s@, 0) },
{
    count_utf8_impl::<false>(true, s, latin1)
}

/// Trusted: `count_utf8_avx2_body` compiled with `avx2` enabled, through
/// `tf::count_utf8_avx2`; the contract is `count_utf8_avx2_body`'s, which is verified.
#[verifier::external_body]
fn count_utf8_avx2(s: &[u8], latin1: bool) -> (r: usize)
    requires
        avx2(),
        s.len() < MAX_LEN,
    ensures
        r == if latin1 { cnt8l1(s@, 0) } else { cnt8(s@, 0) },
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::count_utf8_avx2(s, latin1) };
    #[cfg(not(target_arch = "x86_64"))]
    return count_utf8_avx2_body(s, latin1);
}

/// `utf16_length_from_utf8`, or with `latin1`, `latin1_length_from_utf8`.
pub fn count_utf8(s: &[u8], latin1: bool) -> (r: usize)
    requires
        s.len() < MAX_LEN,
    ensures
        r == if latin1 { cnt8l1(s@, 0) } else { cnt8(s@, 0) },
{
    if has_avx2() {
        // The CPU has AVX2.
        count_utf8_avx2(s, latin1)
    } else if has_neon() {
        count_utf8_impl::<true>(true, s, latin1)
    } else {
        count_utf8_impl::<false>(false, s, latin1)
    }
}

#[inline(always)]
fn count_utf16_impl<const NEON: bool>(avx: bool, s: &[u16]) -> (r: usize)
    requires
        avx ==> simd_ok(NEON),
        s.len() < MAX_LEN,
    ensures
        r == cnt16(s@, 0),
{
    let n = s.len();
    let mut i: usize = 0;
    let mut c: usize = 0;
    while i < n
        invariant
            avx ==> simd_ok(NEON),
            n == s.len(),
            n < MAX_LEN,
            i <= n,
            c <= 3 * i,
            c + cnt16(s@, i as int) == cnt16(s@, 0),
        decreases n - i,
    {
        // SAFETY: the CPU has AVX2 when `avx` is set.
        if avx && n - i >= 32 && v_below32::<NEON>(s, i, true) {
            proof {
                lemma_ascii_u16to8(s@, i as int, 32);
            }
            c = c + 32;
            i = i + 32;
        } else {
            let u = get16(s, i);
            c = c + if u <= 0x7F {
                1
            } else if u <= 0x7FF || (0xD800 <= u && u <= 0xDFFF) {
                2
            } else {
                3
            };
            i = i + 1;
        }
    }
    c
}

#[inline(always)]
fn count_utf16_avx2_body(s: &[u16]) -> (r: usize)
    requires
        avx2(),
        s.len() < MAX_LEN,
    ensures
        r == cnt16(s@, 0),
{
    count_utf16_impl::<false>(true, s)
}

/// Trusted: `count_utf16_avx2_body` compiled with `avx2` enabled, through
/// `tf::count_utf16_avx2`; the contract is `count_utf16_avx2_body`'s, which is verified.
#[verifier::external_body]
fn count_utf16_avx2(s: &[u16]) -> (r: usize)
    requires
        avx2(),
        s.len() < MAX_LEN,
    ensures
        r == cnt16(s@, 0),
{
    // SAFETY: the contract requires the CPU feature (checked by the caller).
    #[cfg(target_arch = "x86_64")]
    return unsafe { tf::count_utf16_avx2(s) };
    #[cfg(not(target_arch = "x86_64"))]
    return count_utf16_avx2_body(s);
}

/// `utf8_length_from_utf16`.
pub fn count_utf16(s: &[u16]) -> (r: usize)
    requires
        s.len() < MAX_LEN,
    ensures
        r == cnt16(s@, 0),
{
    if has_avx2() {
        // The CPU has AVX2.
        count_utf16_avx2(s)
    } else if has_neon() {
        count_utf16_impl::<true>(true, s)
    } else {
        count_utf16_impl::<false>(false, s)
    }
}

} // verus!

/// Trampolines that compile a verified `*_body` function with the target
/// features its kernel needs. Each is one call; `#[target_feature]` only
/// changes code generation. Verus rejects the attribute on verified code
/// (verus-lang/verus#3362), so it lives outside `verus!`.
#[cfg(target_arch = "x86_64")]
mod tf {
    #[allow(unused_imports)]
    use super::*;

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn ascii_prefix_avx2(s: &[u8]) -> usize {
        ascii_prefix_avx2_body(s)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn count_latin1_utf8_avx2(s: &[u8]) -> usize {
        count_latin1_utf8_avx2_body(s)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn count_utf16_avx2(s: &[u16]) -> usize {
        count_utf16_avx2_body(s)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn count_utf8_avx2(s: &[u8], latin1: bool) -> usize {
        count_utf8_avx2_body(s, latin1)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn latin1_to_utf16_avx2(s: &[u8], out: &mut [u16]) {
        latin1_to_utf16_avx2_body(s, out)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn latin1_to_utf8_avx2(s: &[u8], out: &mut [u8]) -> usize {
        latin1_to_utf8_avx2_body(s, out)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn latin1_to_utf8_safe_avx2(s: &[u8], out: &mut [u8]) -> (usize, usize) {
        latin1_to_utf8_safe_avx2_body(s, out)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn utf16_to_latin1_avx2(s: &[u16], out: &mut [u8]) -> bool {
        utf16_to_latin1_avx2_body(s, out)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn utf16_to_utf8_avx2(s: &[u16], out: &mut [u8]) -> Option<usize> {
        utf16_to_utf8_avx2_body(s, out)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn utf8_to_latin1_avx2(s: &[u8], out: &mut [u8]) -> Option<usize> {
        utf8_to_latin1_avx2_body(s, out)
    }

    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn utf8_to_utf16_avx2(s: &[u8], out: &mut [u16]) -> usize {
        utf8_to_utf16_avx2_body(s, out)
    }
}

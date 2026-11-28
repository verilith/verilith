//! Unaligned vector loads and stores on slices (TRUSTED).
//!
//! Each is a one-line wrapper over `_mm*_loadu_si*` / `_mm*_storeu_si*`
//! (or, for the 8-byte forms, `_mm_loadl_epi64` / `_mm_storel_epi64`, and
//! `_mm_storeu_si32` for the 4-byte store)
//! taking a slice and an index instead of a raw pointer. The `requires`
//! clause is the bounds check, proven by Verus at each call site; without
//! verification a `debug_assert!` keeps it.
use crate::cpu::*;
use crate::lanes::*;
use crate::ops::*;
use crate::arch::*;
use vstd::prelude::*;

verus! {

/// The 16 bytes at `s[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn load128_u8(s: &[u8], i: usize) -> (r: __m128i)
    requires
        i + 16 <= s@.len(),
    ensures
        b128(r) == s@.subrange(i as int, i + 16),
{
    debug_assert!(i + 16 <= s.len());
    unsafe { _mm_loadu_si128(s.as_ptr().add(i) as *const __m128i) }
}

/// The 32 bytes at `s[i..i + 32]`.
#[verifier::external_body]
#[inline(always)]
pub fn load256_u8(s: &[u8], i: usize) -> (r: __m256i)
    requires
        avx2(),
        i + 32 <= s@.len(),
    ensures
        b256(r) == s@.subrange(i as int, i + 32),
{
    debug_assert!(i + 32 <= s.len());
    unsafe { _mm256_loadu_si256(s.as_ptr().add(i) as *const __m256i) }
}

/// The four 32-bit values at `s[i..i + 4]`.
#[verifier::external_body]
#[inline(always)]
pub fn load128_u32(s: &[u32], i: usize) -> (r: __m128i)
    requires
        i + 4 <= s@.len(),
    ensures
        u32x4(r) == s@.subrange(i as int, i + 4),
{
    debug_assert!(i + 4 <= s.len());
    unsafe { _mm_loadu_si128(s.as_ptr().add(i) as *const __m128i) }
}

/// The eight 32-bit values at `s[i..i + 8]`.
#[verifier::external_body]
#[inline(always)]
pub fn load256_u32(s: &[u32], i: usize) -> (r: __m256i)
    requires
        avx2(),
        i + 8 <= s@.len(),
    ensures
        u32x8(r) == s@.subrange(i as int, i + 8),
{
    debug_assert!(i + 8 <= s.len());
    unsafe { _mm256_loadu_si256(s.as_ptr().add(i) as *const __m256i) }
}

/// Stores the 128-bit vector `v` as the 16 bytes at `s[i..i + 16]`:
///
/// ```text
/// requires i + 16 <= old(s)@.len()
/// ensures  final(s)@ == old(s)@.subrange(0, i as int) + b128(v) + old(s)@.subrange(i + 16, old(s)@.len() as int)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn store128_u8(s: &mut [u8], i: usize, v: __m128i)
    requires
        i + 16 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + b128(v) + old(s)@.subrange(i + 16, old(s)@.len() as int),
{
    debug_assert!(i + 16 <= s.len());
    unsafe { _mm_storeu_si128(s.as_mut_ptr().add(i) as *mut __m128i, v) }
}

/// Stores the 256-bit vector `v` as the 32 bytes at `s[i..i + 32]`:
///
/// ```text
/// requires avx2()
///          i + 32 <= old(s)@.len()
/// ensures  final(s)@ == old(s)@.subrange(0, i as int) + b256(v) + old(s)@.subrange(i + 32, old(s)@.len() as int)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn store256_u8(s: &mut [u8], i: usize, v: __m256i)
    requires
        avx2(),
        i + 32 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + b256(v) + old(s)@.subrange(i + 32, old(s)@.len() as int),
{
    debug_assert!(i + 32 <= s.len());
    unsafe { _mm256_storeu_si256(s.as_mut_ptr().add(i) as *mut __m256i, v) }
}

/// Stores the 128-bit vector `v` as the 4 32-bit values at `s[i..i + 4]`:
///
/// ```text
/// requires i + 4 <= old(s)@.len()
/// ensures  final(s)@ == old(s)@.subrange(0, i as int) + u32x4(v) + old(s)@.subrange(i + 4, old(s)@.len() as int)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn store128_u32(s: &mut [u32], i: usize, v: __m128i)
    requires
        i + 4 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u32x4(v) + old(s)@.subrange(i + 4, old(s)@.len() as int),
{
    debug_assert!(i + 4 <= s.len());
    unsafe { _mm_storeu_si128(s.as_mut_ptr().add(i) as *mut __m128i, v) }
}

/// Stores the 256-bit vector `v` as the 8 32-bit values at `s[i..i + 8]`:
///
/// ```text
/// requires avx2()
///          i + 8 <= old(s)@.len()
/// ensures  final(s)@ == old(s)@.subrange(0, i as int) + u32x8(v) + old(s)@.subrange(i + 8, old(s)@.len() as int)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn store256_u32(s: &mut [u32], i: usize, v: __m256i)
    requires
        avx2(),
        i + 8 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u32x8(v) + old(s)@.subrange(i + 8, old(s)@.len() as int),
{
    debug_assert!(i + 8 <= s.len());
    unsafe { _mm256_storeu_si256(s.as_mut_ptr().add(i) as *mut __m256i, v) }
}

/// The two 64-bit values at `s[i..i + 2]`.
/// The two 64-bit values at `s[i..i + 2]`.
#[verifier::external_body]
#[inline(always)]
pub fn load128_u64(s: &[u64], i: usize) -> (r: __m128i)
    requires
        i + 2 <= s@.len(),
    ensures
        u64x2(r) == s@.subrange(i as int, i + 2),
{
    debug_assert!(i + 2 <= s.len());
    unsafe { _mm_loadu_si128(s.as_ptr().add(i) as *const __m128i) }
}

/// Stores `v` at `s[i..i + 2]`.
#[verifier::external_body]
#[inline(always)]
pub fn store128_u64(s: &mut [u64], i: usize, v: __m128i)
    requires
        i + 2 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u64x2(v) + old(s)@.subrange(i + 2, old(s)@.len() as int),
{
    debug_assert!(i + 2 <= s.len());
    unsafe { _mm_storeu_si128(s.as_mut_ptr().add(i) as *mut __m128i, v) }
}

/// The sixteen 16-bit values at `s[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn load256_u16(s: &[u16], i: usize) -> (r: __m256i)
    requires
        avx2(),
        i + 16 <= s@.len(),
    ensures
        u16x16(r) == s@.subrange(i as int, i + 16),
{
    debug_assert!(i + 16 <= s.len());
    unsafe { _mm256_loadu_si256(s.as_ptr().add(i) as *const __m256i) }
}

/// Stores the 256-bit vector `v` as the 16 16-bit values at `s[i..i + 16]`:
///
/// ```text
/// requires avx2()
///          i + 16 <= old(s)@.len()
/// ensures  final(s)@ == old(s)@.subrange(0, i as int) + u16x16(v) + old(s)@.subrange(i + 16, old(s)@.len() as int)
/// ```
#[verifier::external_body]
#[inline(always)]
pub fn store256_u16(s: &mut [u16], i: usize, v: __m256i)
    requires
        avx2(),
        i + 16 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u16x16(v) + old(s)@.subrange(i + 16, old(s)@.len() as int),
{
    debug_assert!(i + 16 <= s.len());
    unsafe { _mm256_storeu_si256(s.as_mut_ptr().add(i) as *mut __m256i, v) }
}

/// The eight 16-bit values at `s[i..i + 8]`, as their bits.
#[verifier::external_body]
#[inline(always)]
pub fn load128_i16(s: &[i16], i: usize) -> (r: __m128i)
    requires
        i + 8 <= s@.len(),
    ensures
        u16x8(r) == s@.subrange(i as int, i + 8).map_values(|x: i16| x as u16),
{
    debug_assert!(i + 8 <= s.len());
    unsafe { _mm_loadu_si128(s.as_ptr().add(i) as *const __m128i) }
}

/// The sixteen 16-bit values at `s[i..i + 16]`, as their bits.
#[verifier::external_body]
#[inline(always)]
pub fn load256_i16(s: &[i16], i: usize) -> (r: __m256i)
    requires
        avx2(),
        i + 16 <= s@.len(),
    ensures
        u16x16(r) == s@.subrange(i as int, i + 16).map_values(|x: i16| x as u16),
{
    debug_assert!(i + 16 <= s.len());
    unsafe { _mm256_loadu_si256(s.as_ptr().add(i) as *const __m256i) }
}

/// Stores `v` as eight 16-bit values at `s[i..i + 8]`.
#[verifier::external_body]
#[inline(always)]
pub fn store128_i16(s: &mut [i16], i: usize, v: __m128i)
    requires
        i + 8 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u16x8(v).map_values(|x: u16| x as i16)
            + old(s)@.subrange(i + 8, old(s)@.len() as int),
{
    debug_assert!(i + 8 <= s.len());
    unsafe { _mm_storeu_si128(s.as_mut_ptr().add(i) as *mut __m128i, v) }
}

/// Stores `v` as sixteen 16-bit values at `s[i..i + 16]`.
#[verifier::external_body]
#[inline(always)]
pub fn store256_i16(s: &mut [i16], i: usize, v: __m256i)
    requires
        avx2(),
        i + 16 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + u16x16(v).map_values(|x: u16| x as i16)
            + old(s)@.subrange(i + 16, old(s)@.len() as int),
{
    debug_assert!(i + 16 <= s.len());
    unsafe { _mm256_storeu_si256(s.as_mut_ptr().add(i) as *mut __m256i, v) }
}

/// The 8 bytes at `s[i..i + 8]` in the low half of the vector, zeros in the
/// high half (`_mm_loadl_epi64`). Reads only those 8 bytes.
#[verifier::external_body]
#[inline(always)]
pub fn loadl64_u8(s: &[u8], i: usize) -> (r: __m128i)
    requires
        i + 8 <= s@.len(),
    ensures
        b128(r) == s@.subrange(i as int, i + 8) + splat8(0u8, 8),
{
    debug_assert!(i + 8 <= s.len());
    unsafe { _mm_loadl_epi64(s.as_ptr().add(i) as *const __m128i) }
}

/// Stores the low 8 bytes of `v` at `s[i..i + 8]` (`_mm_storel_epi64`).
/// Writes only those 8 bytes.
#[verifier::external_body]
#[inline(always)]
pub fn storel64_u8(s: &mut [u8], i: usize, v: __m128i)
    requires
        i + 8 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + b128(v).subrange(0, 8) + old(s)@.subrange(i + 8, old(s)@.len() as int),
{
    debug_assert!(i + 8 <= s.len());
    unsafe { _mm_storel_epi64(s.as_mut_ptr().add(i) as *mut __m128i, v) }
}

/// Stores the low 4 bytes of `v` at `s[i..i + 4]` (`_mm_storeu_si32`,
/// `movd`). Writes only those 4 bytes.
#[verifier::external_body]
#[inline(always)]
pub fn storel32_u8(s: &mut [u8], i: usize, v: __m128i)
    requires
        i + 4 <= old(s)@.len(),
    ensures
        final(s)@ == old(s)@.subrange(0, i as int) + b128(v).subrange(0, 4) + old(s)@.subrange(i + 4, old(s)@.len() as int),
{
    debug_assert!(i + 4 <= s.len());
    unsafe { _mm_storeu_si32(s.as_mut_ptr().add(i), v) }
}

} // verus!

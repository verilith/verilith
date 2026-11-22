//! Portable emulation of the x86 intrinsics that `crate::x86` specifies.
//!
//! On x86-64, `crate::arch` is `core::arch::x86_64`. On every other target
//! it is this module, so code written against vsimd's x86 specifications
//! still compiles there. Verified code reaches an intrinsic beyond SSE2 only
//! after run-time detection (`has_avx2` and friends), which is always false
//! off x86, so those paths never run; the SSE2 ones, which x86-64 code may
//! call unconditionally, do run, and compute what the CPU would.
//!
//! This module is not verified. It is compiled on x86-64 too, where
//! `tests/emu.rs` compares every function with the CPU instruction.
#![allow(non_camel_case_types, clippy::missing_safety_doc, clippy::needless_range_loop)]

/// A 128-bit vector: its bytes in memory order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(16))]
pub struct __m128i(pub [u8; 16]);

/// A 256-bit vector: its bytes in memory order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(32))]
pub struct __m256i(pub [u8; 32]);

// ---------------------------------------------------------------------------
// Lane access
// ---------------------------------------------------------------------------

#[inline]
fn g16(b: &[u8], i: usize) -> u16 {
    u16::from_le_bytes([b[2 * i], b[2 * i + 1]])
}
#[inline]
fn s16(b: &mut [u8], i: usize, x: u16) {
    b[2 * i..2 * i + 2].copy_from_slice(&x.to_le_bytes());
}
#[inline]
fn g32(b: &[u8], i: usize) -> u32 {
    u32::from_le_bytes(b[4 * i..4 * i + 4].try_into().unwrap())
}
#[inline]
fn s32(b: &mut [u8], i: usize, x: u32) {
    b[4 * i..4 * i + 4].copy_from_slice(&x.to_le_bytes());
}
#[inline]
fn g64(b: &[u8], i: usize) -> u64 {
    u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap())
}
#[inline]
fn s64(b: &mut [u8], i: usize, x: u64) {
    b[8 * i..8 * i + 8].copy_from_slice(&x.to_le_bytes());
}

fn map8<const N: usize>(a: [u8; N], b: [u8; N], f: impl Fn(u8, u8) -> u8) -> [u8; N] {
    let mut r = [0u8; N];
    for i in 0..N {
        r[i] = f(a[i], b[i]);
    }
    r
}
fn map16<const N: usize>(a: [u8; N], b: [u8; N], f: impl Fn(u16, u16) -> u16) -> [u8; N] {
    let mut r = [0u8; N];
    for i in 0..N / 2 {
        s16(&mut r, i, f(g16(&a, i), g16(&b, i)));
    }
    r
}
fn map32<const N: usize>(a: [u8; N], b: [u8; N], f: impl Fn(u32, u32) -> u32) -> [u8; N] {
    let mut r = [0u8; N];
    for i in 0..N / 4 {
        s32(&mut r, i, f(g32(&a, i), g32(&b, i)));
    }
    r
}
fn map64<const N: usize>(a: [u8; N], b: [u8; N], f: impl Fn(u64, u64) -> u64) -> [u8; N] {
    let mut r = [0u8; N];
    for i in 0..N / 8 {
        s64(&mut r, i, f(g64(&a, i), g64(&b, i)));
    }
    r
}

fn sat_u8(x: i16) -> u8 {
    x.clamp(0, 255) as u8
}

// Per-lane (16-byte) operations, applied to each lane of a vector.
fn unpacklo8(a: &[u8], b: &[u8], r: &mut [u8]) {
    for k in 0..8 {
        r[2 * k] = a[k];
        r[2 * k + 1] = b[k];
    }
}
fn unpackhi8(a: &[u8], b: &[u8], r: &mut [u8]) {
    for k in 0..8 {
        r[2 * k] = a[8 + k];
        r[2 * k + 1] = b[8 + k];
    }
}
fn unpacklo16(a: &[u8], b: &[u8], r: &mut [u8]) {
    for k in 0..4 {
        s16(r, 2 * k, g16(a, k));
        s16(r, 2 * k + 1, g16(b, k));
    }
}
fn unpackhi16(a: &[u8], b: &[u8], r: &mut [u8]) {
    for k in 0..4 {
        s16(r, 2 * k, g16(a, 4 + k));
        s16(r, 2 * k + 1, g16(b, 4 + k));
    }
}
fn unpackhi64(a: &[u8], b: &[u8], r: &mut [u8]) {
    s64(r, 0, g64(a, 1));
    s64(r, 1, g64(b, 1));
}
fn unpacklo32(a: &[u8], b: &[u8], r: &mut [u8]) {
    s32(r, 0, g32(a, 0));
    s32(r, 1, g32(b, 0));
    s32(r, 2, g32(a, 1));
    s32(r, 3, g32(b, 1));
}
fn unpackhi32(a: &[u8], b: &[u8], r: &mut [u8]) {
    s32(r, 0, g32(a, 2));
    s32(r, 1, g32(b, 2));
    s32(r, 2, g32(a, 3));
    s32(r, 3, g32(b, 3));
}
fn unpacklo64(a: &[u8], b: &[u8], r: &mut [u8]) {
    s64(r, 0, g64(a, 0));
    s64(r, 1, g64(b, 0));
}
fn packus16(a: &[u8], b: &[u8], r: &mut [u8]) {
    for k in 0..8 {
        r[k] = sat_u8(g16(a, k) as i16);
        r[8 + k] = sat_u8(g16(b, k) as i16);
    }
}
fn packs16(a: &[u8], b: &[u8], r: &mut [u8]) {
    for k in 0..8 {
        r[k] = (g16(a, k) as i16).clamp(-0x80, 0x7f) as i8 as u8;
        r[8 + k] = (g16(b, k) as i16).clamp(-0x80, 0x7f) as i8 as u8;
    }
}
fn packs32(a: &[u8], b: &[u8], r: &mut [u8]) {
    for k in 0..4 {
        s16(r, k, (g32(a, k) as i32).clamp(-0x8000, 0x7fff) as i16 as u16);
        s16(r, 4 + k, (g32(b, k) as i32).clamp(-0x8000, 0x7fff) as i16 as u16);
    }
}
fn shuffle8(a: &[u8], b: &[u8], r: &mut [u8]) {
    for k in 0..16 {
        r[k] = if b[k] >= 128 { 0 } else { a[(b[k] % 16) as usize] };
    }
}
fn bslli(a: &[u8], n: usize, r: &mut [u8]) {
    for k in 0..16 {
        r[k] = if k >= n { a[k - n] } else { 0 };
    }
}
fn bsrli(a: &[u8], n: usize, r: &mut [u8]) {
    for k in 0..16 {
        r[k] = if k + n < 16 { a[k + n] } else { 0 };
    }
}
fn alignr(hi: &[u8], lo: &[u8], n: usize, r: &mut [u8]) {
    for k in 0..16 {
        r[k] = if k + n < 16 {
            lo[k + n]
        } else if k + n < 32 {
            hi[k + n - 16]
        } else {
            0
        };
    }
}
fn shuffle32(a: &[u8], imm: i32, r: &mut [u8]) {
    for k in 0..4 {
        s32(r, k, g32(a, ((imm >> (2 * k)) & 3) as usize));
    }
}

fn lanes2<const N: usize>(a: [u8; N], b: [u8; N], f: impl Fn(&[u8], &[u8], &mut [u8])) -> [u8; N] {
    let mut r = [0u8; N];
    for l in 0..N / 16 {
        f(&a[16 * l..16 * l + 16], &b[16 * l..16 * l + 16], &mut r[16 * l..16 * l + 16]);
    }
    r
}

macro_rules! both {
    ($n128:ident, $n256:ident, |$a:ident, $b:ident| $e:expr) => {
        #[inline]
        pub fn $n128(a: __m128i, b: __m128i) -> __m128i {
            let ($a, $b) = (a.0, b.0);
            __m128i($e)
        }
        #[inline]
        pub fn $n256(a: __m256i, b: __m256i) -> __m256i {
            let ($a, $b) = (a.0, b.0);
            __m256i($e)
        }
    };
}

both!(_mm_add_epi8, _mm256_add_epi8, |a, b| map8(a, b, u8::wrapping_add));
both!(_mm_sub_epi8, _mm256_sub_epi8, |a, b| map8(a, b, u8::wrapping_sub));
both!(_mm_adds_epu8, _mm256_adds_epu8, |a, b| map8(a, b, u8::saturating_add));
both!(_mm_subs_epu8, _mm256_subs_epu8, |a, b| map8(a, b, u8::saturating_sub));
both!(_mm_adds_epi8, _mm256_adds_epi8, |a, b| map8(a, b, |x, y| (x as i8).saturating_add(y as i8) as u8));
both!(_mm_subs_epi8, _mm256_subs_epi8, |a, b| map8(a, b, |x, y| (x as i8).saturating_sub(y as i8) as u8));
both!(_mm_subs_epu16, _mm256_subs_epu16, |a, b| map16(a, b, u16::saturating_sub));
both!(_mm_min_epu8, _mm256_min_epu8, |a, b| map8(a, b, u8::min));
both!(_mm_max_epu8, _mm256_max_epu8, |a, b| map8(a, b, u8::max));
both!(_mm_avg_epu8, _mm256_avg_epu8, |a, b| map8(a, b, |x, y| ((x as u16 + y as u16 + 1) / 2) as u8));
both!(_mm_cmpeq_epi8, _mm256_cmpeq_epi8, |a, b| map8(a, b, |x, y| if x == y { 0xff } else { 0 }));
both!(_mm_cmpgt_epi8, _mm256_cmpgt_epi8, |a, b| map8(a, b, |x, y| if (x as i8) > (y as i8) { 0xff } else { 0 }));
both!(_mm_add_epi16, _mm256_add_epi16, |a, b| map16(a, b, u16::wrapping_add));
both!(_mm_sub_epi16, _mm256_sub_epi16, |a, b| map16(a, b, u16::wrapping_sub));
both!(_mm_mullo_epi16, _mm256_mullo_epi16, |a, b| map16(a, b, u16::wrapping_mul));
both!(_mm_mulhi_epi16, _mm256_mulhi_epi16, |a, b| map16(a, b, |x, y| ((x as i16 as i32 * y as i16 as i32) >> 16) as u16));
both!(_mm_mulhi_epu16, _mm256_mulhi_epu16, |a, b| map16(a, b, |x, y| ((x as u32 * y as u32) >> 16) as u16));
both!(_mm_cmpeq_epi16, _mm256_cmpeq_epi16, |a, b| map16(a, b, |x, y| if x == y { 0xffff } else { 0 }));
both!(_mm_add_epi32, _mm256_add_epi32, |a, b| map32(a, b, u32::wrapping_add));
both!(_mm_sub_epi32, _mm256_sub_epi32, |a, b| map32(a, b, u32::wrapping_sub));
both!(_mm_cmpeq_epi32, _mm256_cmpeq_epi32, |a, b| map32(a, b, |x, y| if x == y { !0 } else { 0 }));
both!(_mm_cmpgt_epi32, _mm256_cmpgt_epi32, |a, b| map32(a, b, |x, y| if (x as i32) > (y as i32) { !0 } else { 0 }));
both!(_mm_add_epi64, _mm256_add_epi64, |a, b| map64(a, b, u64::wrapping_add));
both!(_mm_unpacklo_epi8, _mm256_unpacklo_epi8, |a, b| lanes2(a, b, unpacklo8));
both!(_mm_unpackhi_epi8, _mm256_unpackhi_epi8, |a, b| lanes2(a, b, unpackhi8));
both!(_mm_unpacklo_epi16, _mm256_unpacklo_epi16, |a, b| lanes2(a, b, unpacklo16));
both!(_mm_unpackhi_epi16, _mm256_unpackhi_epi16, |a, b| lanes2(a, b, unpackhi16));
both!(_mm_unpacklo_epi32, _mm256_unpacklo_epi32, |a, b| lanes2(a, b, unpacklo32));
both!(_mm_unpackhi_epi32, _mm256_unpackhi_epi32, |a, b| lanes2(a, b, unpackhi32));
both!(_mm_unpacklo_epi64, _mm256_unpacklo_epi64, |a, b| lanes2(a, b, unpacklo64));
both!(_mm_unpackhi_epi64, _mm256_unpackhi_epi64, |a, b| lanes2(a, b, unpackhi64));
both!(_mm_packus_epi16, _mm256_packus_epi16, |a, b| lanes2(a, b, packus16));
both!(_mm_packs_epi16, _mm256_packs_epi16, |a, b| lanes2(a, b, packs16));
both!(_mm_packs_epi32, _mm256_packs_epi32, |a, b| lanes2(a, b, packs32));
both!(_mm_shuffle_epi8, _mm256_shuffle_epi8, |a, b| lanes2(a, b, shuffle8));
both!(_mm_and_si128, _mm256_and_si256, |a, b| map8(a, b, |x, y| x & y));
both!(_mm_or_si128, _mm256_or_si256, |a, b| map8(a, b, |x, y| x | y));
both!(_mm_xor_si128, _mm256_xor_si256, |a, b| map8(a, b, |x, y| x ^ y));
both!(_mm_andnot_si128, _mm256_andnot_si256, |a, b| map8(a, b, |x, y| !x & y));
both!(_mm_madd_epi16, _mm256_madd_epi16, |a, b| {
    let mut r = a;
    r.fill(0);
    for i in 0..a.len() / 4 {
        let p = |k: usize| g16(&a, k) as i16 as i32 * g16(&b, k) as i16 as i32;
        s32(&mut r, i, p(2 * i).wrapping_add(p(2 * i + 1)) as u32);
    }
    r
});
both!(_mm_maddubs_epi16, _mm256_maddubs_epi16, |a, b| {
    let mut r = a;
    r.fill(0);
    for i in 0..a.len() / 2 {
        let p = |k: usize| a[k] as i32 * b[k] as i8 as i32;
        s16(&mut r, i, (p(2 * i) + p(2 * i + 1)).clamp(-0x8000, 0x7fff) as i16 as u16);
    }
    r
});
both!(_mm_sad_epu8, _mm256_sad_epu8, |a, b| {
    let mut r = a;
    r.fill(0);
    for j in 0..a.len() / 8 {
        let s: u64 = (0..8).map(|k| a[8 * j + k].abs_diff(b[8 * j + k]) as u64).sum();
        s64(&mut r, j, s);
    }
    r
});

#[inline]
pub fn _mm_blendv_epi8(a: __m128i, b: __m128i, m: __m128i) -> __m128i {
    let mut r = a.0;
    for i in 0..16 {
        if m.0[i] >= 128 {
            r[i] = b.0[i];
        }
    }
    __m128i(r)
}
#[inline]
pub fn _mm256_blendv_epi8(a: __m256i, b: __m256i, m: __m256i) -> __m256i {
    let mut r = a.0;
    for i in 0..32 {
        if m.0[i] >= 128 {
            r[i] = b.0[i];
        }
    }
    __m256i(r)
}

fn movemask(a: &[u8]) -> i32 {
    let mut m = 0u32;
    for (i, &x) in a.iter().enumerate() {
        m |= ((x >> 7) as u32) << i;
    }
    m as i32
}
#[inline]
pub fn _mm_movemask_epi8(a: __m128i) -> i32 {
    movemask(&a.0)
}
#[inline]
pub fn _mm256_movemask_epi8(a: __m256i) -> i32 {
    movemask(&a.0)
}

// ---------------------------------------------------------------------------
// Immediate shifts and shuffles
// ---------------------------------------------------------------------------

macro_rules! imm1 {
    ($n128:ident, $n256:ident, |$a:ident, $k:ident| $e:expr) => {
        #[inline]
        pub fn $n128<const IMM8: i32>(a: __m128i) -> __m128i {
            let ($a, $k) = (a.0, IMM8);
            __m128i($e)
        }
        #[inline]
        pub fn $n256<const IMM8: i32>(a: __m256i) -> __m256i {
            let ($a, $k) = (a.0, IMM8);
            __m256i($e)
        }
    };
}

fn each16<const N: usize>(a: [u8; N], f: impl Fn(u16) -> u16) -> [u8; N] {
    map16(a, a, |x, _| f(x))
}
fn each32<const N: usize>(a: [u8; N], f: impl Fn(u32) -> u32) -> [u8; N] {
    map32(a, a, |x, _| f(x))
}
fn lanes1<const N: usize>(a: [u8; N], f: impl Fn(&[u8], &mut [u8])) -> [u8; N] {
    lanes2(a, a, |x, _, r| f(x, r))
}

imm1!(_mm_srli_epi16, _mm256_srli_epi16, |a, k| each16(a, |x| if !(0..=15).contains(&k) { 0 } else { x >> k }));
imm1!(_mm_slli_epi16, _mm256_slli_epi16, |a, k| each16(a, |x| if !(0..=15).contains(&k) { 0 } else { x << k }));
imm1!(_mm_srai_epi16, _mm256_srai_epi16, |a, k| each16(a, |x| ((x as i16) >> (k as u32).min(15)) as u16));
imm1!(_mm_srli_epi32, _mm256_srli_epi32, |a, k| each32(a, |x| if !(0..=31).contains(&k) { 0 } else { x >> k }));
imm1!(_mm_slli_epi32, _mm256_slli_epi32, |a, k| each32(a, |x| if !(0..=31).contains(&k) { 0 } else { x << k }));
imm1!(_mm_shuffle_epi32, _mm256_shuffle_epi32, |a, k| lanes1(a, |x, r| shuffle32(x, k, r)));
imm1!(_mm_slli_si128, _mm256_bslli_epi128, |a, k| lanes1(a, |x, r| bslli(x, (k & 0xff) as usize, r)));
imm1!(_mm_srli_si128, _mm256_bsrli_epi128, |a, k| lanes1(a, |x, r| bsrli(x, (k & 0xff) as usize, r)));

#[inline]
pub fn _mm_alignr_epi8<const IMM8: i32>(a: __m128i, b: __m128i) -> __m128i {
    __m128i(lanes2(a.0, b.0, |x, y, r| alignr(x, y, (IMM8 & 0xff) as usize, r)))
}
#[inline]
pub fn _mm256_alignr_epi8<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    __m256i(lanes2(a.0, b.0, |x, y, r| alignr(x, y, (IMM8 & 0xff) as usize, r)))
}

#[inline]
pub fn _mm256_extracti128_si256<const IMM1: i32>(a: __m256i) -> __m128i {
    let o = 16 * (IMM1 & 1) as usize;
    __m128i(a.0[o..o + 16].try_into().unwrap())
}

#[inline]
pub fn _mm256_permute2x128_si256<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    let pick = |c: i32| -> [u8; 16] {
        if c & 8 != 0 {
            return [0; 16];
        }
        let src = if c & 2 == 0 { &a.0 } else { &b.0 };
        let o = 16 * (c & 1) as usize;
        src[o..o + 16].try_into().unwrap()
    };
    let mut r = [0u8; 32];
    r[..16].copy_from_slice(&pick(IMM8 & 0xf));
    r[16..].copy_from_slice(&pick((IMM8 >> 4) & 0xf));
    __m256i(r)
}

#[inline]
pub fn _mm256_permutevar8x32_epi32(a: __m256i, idx: __m256i) -> __m256i {
    let mut r = [0u8; 32];
    for i in 0..8 {
        s32(&mut r, i, g32(&a.0, (g32(&idx.0, i) % 8) as usize));
    }
    __m256i(r)
}

// ---------------------------------------------------------------------------
// Constructors and conversions
// ---------------------------------------------------------------------------

#[inline]
pub fn _mm_setzero_si128() -> __m128i {
    __m128i([0; 16])
}
#[inline]
pub fn _mm256_setzero_si256() -> __m256i {
    __m256i([0; 32])
}

fn splat<const N: usize, const W: usize>(x: [u8; W]) -> [u8; N] {
    let mut r = [0u8; N];
    for i in 0..N {
        r[i] = x[i % W];
    }
    r
}
#[inline]
pub fn _mm_set1_epi8(x: i8) -> __m128i {
    __m128i(splat(x.to_le_bytes()))
}
#[inline]
pub fn _mm_set1_epi16(x: i16) -> __m128i {
    __m128i(splat(x.to_le_bytes()))
}
#[inline]
pub fn _mm_set1_epi32(x: i32) -> __m128i {
    __m128i(splat(x.to_le_bytes()))
}
#[inline]
pub fn _mm_set1_epi64x(x: i64) -> __m128i {
    __m128i(splat(x.to_le_bytes()))
}
#[inline]
pub fn _mm256_set1_epi8(x: i8) -> __m256i {
    __m256i(splat(x.to_le_bytes()))
}
#[inline]
pub fn _mm256_set1_epi16(x: i16) -> __m256i {
    __m256i(splat(x.to_le_bytes()))
}
#[inline]
pub fn _mm256_set1_epi32(x: i32) -> __m256i {
    __m256i(splat(x.to_le_bytes()))
}
#[inline]
pub fn _mm256_set1_epi64x(x: i64) -> __m256i {
    __m256i(splat(x.to_le_bytes()))
}

#[inline]
pub fn _mm_setr_epi32(e0: i32, e1: i32, e2: i32, e3: i32) -> __m128i {
    let mut r = [0u8; 16];
    for (i, e) in [e0, e1, e2, e3].into_iter().enumerate() {
        s32(&mut r, i, e as u32);
    }
    __m128i(r)
}
#[allow(clippy::too_many_arguments)]
#[inline]
pub fn _mm256_setr_epi32(e0: i32, e1: i32, e2: i32, e3: i32, e4: i32, e5: i32, e6: i32, e7: i32) -> __m256i {
    let mut r = [0u8; 32];
    for (i, e) in [e0, e1, e2, e3, e4, e5, e6, e7].into_iter().enumerate() {
        s32(&mut r, i, e as u32);
    }
    __m256i(r)
}
#[allow(clippy::too_many_arguments)]
#[inline]
pub fn _mm_setr_epi8(
    e0: i8, e1: i8, e2: i8, e3: i8, e4: i8, e5: i8, e6: i8, e7: i8,
    e8: i8, e9: i8, e10: i8, e11: i8, e12: i8, e13: i8, e14: i8, e15: i8,
) -> __m128i {
    __m128i([e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15].map(|x| x as u8))
}
#[allow(clippy::too_many_arguments)]
#[inline]
pub fn _mm256_setr_epi8(
    e0: i8, e1: i8, e2: i8, e3: i8, e4: i8, e5: i8, e6: i8, e7: i8,
    e8: i8, e9: i8, e10: i8, e11: i8, e12: i8, e13: i8, e14: i8, e15: i8,
    e16: i8, e17: i8, e18: i8, e19: i8, e20: i8, e21: i8, e22: i8, e23: i8,
    e24: i8, e25: i8, e26: i8, e27: i8, e28: i8, e29: i8, e30: i8, e31: i8,
) -> __m256i {
    __m256i(
        [
            e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21,
            e22, e23, e24, e25, e26, e27, e28, e29, e30, e31,
        ]
        .map(|x| x as u8),
    )
}

#[inline]
pub fn _mm_cvtsi32_si128(x: i32) -> __m128i {
    let mut r = [0u8; 16];
    s32(&mut r, 0, x as u32);
    __m128i(r)
}
#[inline]
pub fn _mm_cvtsi128_si32(a: __m128i) -> i32 {
    g32(&a.0, 0) as i32
}
#[inline]
pub fn _mm_cvtsi64_si128(x: i64) -> __m128i {
    let mut r = [0u8; 16];
    s64(&mut r, 0, x as u64);
    __m128i(r)
}
#[inline]
pub fn _mm_cvtsi128_si64(a: __m128i) -> i64 {
    g64(&a.0, 0) as i64
}
#[inline]
pub fn _mm256_castsi256_si128(a: __m256i) -> __m128i {
    __m128i(a.0[..16].try_into().unwrap())
}
#[inline]
pub fn _mm256_set_m128i(hi: __m128i, lo: __m128i) -> __m256i {
    let mut r = [0u8; 32];
    r[..16].copy_from_slice(&lo.0);
    r[16..].copy_from_slice(&hi.0);
    __m256i(r)
}

#[allow(clippy::too_many_arguments)]
#[inline]
pub fn _mm_setr_epi16(e0: i16, e1: i16, e2: i16, e3: i16, e4: i16, e5: i16, e6: i16, e7: i16) -> __m128i {
    let mut r = [0u8; 16];
    for (i, e) in [e0, e1, e2, e3, e4, e5, e6, e7].into_iter().enumerate() {
        s16(&mut r, i, e as u16);
    }
    __m128i(r)
}
#[inline]
pub fn _mm256_broadcastsi128_si256(a: __m128i) -> __m256i {
    _mm256_set_m128i(a, a)
}
/// `vptest`'s ZF: 1 when `a & b` is all zero.
#[inline]
pub fn _mm256_testz_si256(a: __m256i, b: __m256i) -> i32 {
    (0..32).all(|k| a.0[k] & b.0[k] == 0) as i32
}
/// `pclmulqdq`: the 128-bit carry-less product of the quadwords `IMM8`
/// selects (bit 0: of `a`, bit 4: of `b`).
#[inline]
pub fn _mm_clmulepi64_si128<const IMM8: i32>(a: __m128i, b: __m128i) -> __m128i {
    let x = g64(&a.0, (IMM8 & 1) as usize);
    let y = g64(&b.0, ((IMM8 >> 4) & 1) as usize);
    let mut p: u128 = 0;
    for i in 0..64 {
        if (y >> i) & 1 == 1 {
            p ^= (x as u128) << i;
        }
    }
    __m128i(p.to_le_bytes())
}

// ---------------------------------------------------------------------------
// Unaligned loads and stores
// ---------------------------------------------------------------------------

#[inline]
pub unsafe fn _mm_loadu_si128(p: *const __m128i) -> __m128i {
    core::ptr::read_unaligned(p)
}
/// Reads 8 bytes; the high half is zero.
#[inline]
pub unsafe fn _mm_loadl_epi64(p: *const __m128i) -> __m128i {
    let mut r = [0u8; 16];
    core::ptr::copy_nonoverlapping(p as *const u8, r.as_mut_ptr(), 8);
    __m128i(r)
}
/// Writes the low 8 bytes.
#[inline]
pub unsafe fn _mm_storel_epi64(p: *mut __m128i, v: __m128i) {
    core::ptr::copy_nonoverlapping(v.0.as_ptr(), p as *mut u8, 8);
}
/// Writes the low 4 bytes.
#[inline]
pub unsafe fn _mm_storeu_si32(p: *mut u8, v: __m128i) {
    core::ptr::copy_nonoverlapping(v.0.as_ptr(), p, 4);
}
#[inline]
pub unsafe fn _mm256_loadu_si256(p: *const __m256i) -> __m256i {
    core::ptr::read_unaligned(p)
}
#[inline]
pub unsafe fn _mm_storeu_si128(p: *mut __m128i, v: __m128i) {
    core::ptr::write_unaligned(p, v)
}
#[inline]
pub unsafe fn _mm256_storeu_si256(p: *mut __m256i, v: __m256i) {
    core::ptr::write_unaligned(p, v)
}

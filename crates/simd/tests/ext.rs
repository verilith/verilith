//! Differential test of the trusted specifications in `verilith_simd::avx512` and
//! `verilith_simd::scalar`, and of the specifications in `src/x86.rs` that
//! `tests/difftest.rs` does not generate (`packs_epi32`, `setr_epi16`,
//! `testz_si256`, `broadcastsi128_si256`, `clmulepi64_si128`), an
//! exhaustive check of the signed saturating byte operations, and the
//! 8-byte load and store of `verilith_simd::mem`.
//!
//! Random and edge-biased inputs are run through the CPU and through the
//! verified reference implementation of each specification
//! (`verilith_simd::refs`); any difference fails the test. `VSIMD_ITERS` sets the
//! number of inputs per function (default 200,000). The AVX-512 tests are
//! skipped, with a message, on a CPU without AVX-512BW and VBMI2.
#![cfg(target_arch = "x86_64")]
#![allow(unused_unsafe)]
use core::arch::x86_64::*;
use core::mem::transmute;
use verilith_simd::refs::*;

fn iters() -> usize {
    std::env::var("VSIMD_ITERS").ok().and_then(|s| s.parse().ok()).unwrap_or(200_000)
}

struct Rng(u64);
impl Rng {
    fn new(s: u64) -> Rng {
        Rng(s.wrapping_mul(0x9E3779B97F4A7C15) | 1)
    }
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn byte(&mut self) -> u8 {
        let r = self.next();
        if r % 4 == 0 { [0u8, 1, 2, 0x0f, 0x10, 0x7e, 0x7f, 0x80, 0x81, 0xfe, 0xff][(r >> 8) as usize % 11] } else { (r >> 16) as u8 }
    }
    fn bytes<const N: usize>(&mut self) -> [u8; N] {
        let mut b = [0u8; N];
        let mode = self.next() % 8;
        for x in b.iter_mut() {
            *x = if mode == 0 { (self.next() >> 20) as u8 } else { self.byte() };
        }
        b
    }
    /// `a` with a few bytes changed, or `a`, or a fresh value.
    fn rel<const N: usize>(&mut self, a: [u8; N]) -> [u8; N] {
        match self.next() % 5 {
            0 => a,
            1 => {
                let mut b = a;
                for _ in 0..(self.next() % 4) {
                    let i = self.next() as usize % N;
                    b[i] = b[i].wrapping_add((self.next() % 3) as u8).wrapping_sub(1);
                }
                b
            }
            _ => self.bytes(),
        }
    }
    /// A mask: uniform, sparse, dense or an edge value.
    fn mask(&mut self) -> u64 {
        match self.next() % 6 {
            0 => [0, !0, 1, 1 << 63, 0x5555_5555_5555_5555, 0xffff_ffff, !0 << 32][(self.next() % 7) as usize],
            1 => self.next() & self.next() & self.next(),
            2 => self.next() | self.next() | self.next(),
            _ => self.next(),
        }
    }
}

fn u16s(b: &[u8]) -> Vec<u16> {
    b.chunks(2).map(|c| u16::from_le_bytes([c[0], c[1]])).collect()
}
fn u32s(b: &[u8]) -> Vec<u32> {
    b.chunks(4).map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]])).collect()
}
fn u64s(b: &[u8]) -> Vec<u64> {
    b.chunks(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect()
}
fn b128(v: __m128i) -> [u8; 16] {
    unsafe { transmute(v) }
}
fn b256(v: __m256i) -> [u8; 32] {
    unsafe { transmute(v) }
}
fn b512(v: __m512i) -> [u8; 64] {
    unsafe { transmute(v) }
}
fn v128(b: [u8; 16]) -> __m128i {
    unsafe { transmute(b) }
}
fn v256(b: [u8; 32]) -> __m256i {
    unsafe { transmute(b) }
}
fn v512(b: [u8; 64]) -> __m512i {
    unsafe { transmute(b) }
}

#[test]
fn popcnt() {
    let mut r = Rng::new(1);
    for _ in 0..iters() {
        let m = r.mask();
        assert_eq!(verilith_simd::scalar::popcnt64(m), ref_popcount64(m), "popcnt64({m:#x})");
    }
}

#[test]
fn sse2_extras() {
    let mut r = Rng::new(2);
    for _ in 0..iters() {
        let a = r.bytes::<16>();
        let b = r.rel(a);
        let got = u16s(&b128(unsafe { _mm_packs_epi32(v128(a), v128(b)) }));
        assert_eq!(got, ref_packs32_lanes(&u32s(&a), &u32s(&b)), "_mm_packs_epi32 {a:02x?} {b:02x?}");
        let w = u16s(&a);
        let e = |k: usize| w[k] as i16;
        let got = u16s(&b128(unsafe { _mm_setr_epi16(e(0), e(1), e(2), e(3), e(4), e(5), e(6), e(7)) }));
        assert_eq!(got, w, "_mm_setr_epi16");
    }
}

/// `adds_epi8` and `subs_epi8` on every pair of bytes, and `packs_epi16`
/// on every 16-bit value, in every lane position: the saturation bounds
/// and the lane order, exhaustively.
#[test]
fn signed_saturation_exhaustive() {
    for x in 0..=255u8 {
        for y0 in (0..=255u8).step_by(16) {
            let mut a = [x; 16];
            let mut b = [0u8; 16];
            for k in 0..16 {
                b[k] = y0 + k as u8;
            }
            // A second arrangement, so every pair meets every lane.
            a.rotate_left((x % 16) as usize);
            let got = b128(unsafe { _mm_adds_epi8(v128(a), v128(b)) });
            assert_eq!(got.to_vec(), ref_adds_s8(&a, &b), "_mm_adds_epi8 {a:02x?} {b:02x?}");
            for k in 0..16 {
                assert_eq!(got[k] as i8, (a[k] as i8).saturating_add(b[k] as i8));
            }
            let got = b128(unsafe { _mm_subs_epi8(v128(a), v128(b)) });
            assert_eq!(got.to_vec(), ref_subs_s8(&a, &b), "_mm_subs_epi8 {a:02x?} {b:02x?}");
            for k in 0..16 {
                assert_eq!(got[k] as i8, (a[k] as i8).saturating_sub(b[k] as i8));
            }
        }
    }
    for base in (0..=0xffffu32).step_by(16) {
        let mut a = [0u8; 16];
        let mut b = [0u8; 16];
        for k in 0..8 {
            let va = (base + k as u32) as u16;
            let vb = (base + 8 + k as u32) as u16;
            a[2 * k..2 * k + 2].copy_from_slice(&va.to_le_bytes());
            b[2 * k..2 * k + 2].copy_from_slice(&vb.to_le_bytes());
        }
        let got = b128(unsafe { _mm_packs_epi16(v128(a), v128(b)) });
        assert_eq!(got.to_vec(), ref_packs16_lanes(&u16s(&a), &u16s(&b)), "_mm_packs_epi16 {a:02x?} {b:02x?}");
        for k in 0..8 {
            // `a`'s eight lanes first, then `b`'s.
            assert_eq!(got[k] as i8, ((base + k as u32) as u16 as i16).clamp(-128, 127) as i8);
            assert_eq!(got[8 + k] as i8, ((base + 8 + k as u32) as u16 as i16).clamp(-128, 127) as i8);
        }
    }
}

/// A build that is compiled for SSSE3 runs on a CPU that has it.
#[test]
fn compiled_features_are_present() {
    if verilith_simd::cpu::compiled_with_ssse3() {
        assert!(std::is_x86_feature_detected!("ssse3"));
        assert!(cfg!(target_feature = "ssse3"));
    } else {
        assert!(!cfg!(target_feature = "ssse3"));
    }
}

/// The 8-byte load and store in `verilith_simd::mem`: the bytes their
/// specifications state, and no others read or written.
#[test]
fn mem_low_halves() {
    let mut r = Rng::new(0x10ad_8);
    for _ in 0..iters() {
        let src: [u8; 32] = r.bytes();
        let i = r.next() as usize % 25;
        // Exactly 8 readable bytes when `i == len - 8`.
        let v = b128(verilith_simd::mem::loadl64_u8(&src[..i + 8], i));
        let mut want = [0u8; 16];
        want[..8].copy_from_slice(&src[i..i + 8]);
        assert_eq!(v, want, "loadl64_u8 at {i}");
        let a: [u8; 16] = r.bytes();
        let mut dst: [u8; 32] = r.bytes();
        let old = dst;
        verilith_simd::mem::storel64_u8(&mut dst[..i + 8], i, v128(a));
        let mut want = old;
        want[i..i + 8].copy_from_slice(&a[..8]);
        assert_eq!(dst, want, "storel64_u8 at {i}");
        // Exactly 4 writable bytes when `j == len - 4`.
        let j = r.next() as usize % 29;
        let mut dst = old;
        verilith_simd::mem::storel32_u8(&mut dst[..j + 4], j, v128(a));
        let mut want = old;
        want[j..j + 4].copy_from_slice(&a[..4]);
        assert_eq!(dst, want, "storel32_u8 at {j}");
    }
}

#[test]
fn clmul() {
    if !std::is_x86_feature_detected!("pclmulqdq") {
        eprintln!("skipping: no PCLMULQDQ");
        return;
    }
    #[target_feature(enable = "pclmulqdq")]
    fn go(a: __m128i, b: __m128i) -> __m128i {
        _mm_clmulepi64_si128::<0>(a, b)
    }
    let mut r = Rng::new(3);
    for _ in 0..iters() {
        let a = r.bytes::<16>();
        let b = r.rel(a);
        let got = u64s(&b128(unsafe { go(v128(a), v128(b)) }))[0];
        let want = ref_clmul_lo(u64s(&a)[0], u64s(&b)[0]);
        assert_eq!(got, want, "_mm_clmulepi64_si128::<0> {a:02x?} {b:02x?}");
    }
    // The use it is specified for: a prefix XOR.
    for _ in 0..iters() / 4 {
        let m = r.mask();
        let got = u64s(&b128(unsafe { go(_mm_set_epi64x(0, m as i64), _mm_set1_epi8(-1)) }))[0];
        assert_eq!(got, ref_clmul_lo(m, !0));
    }
}

#[test]
fn avx2_extras() {
    if !std::is_x86_feature_detected!("avx2") {
        eprintln!("skipping: no AVX2");
        return;
    }
    #[target_feature(enable = "avx2")]
    fn body(n: usize) {
        let mut r = Rng::new(4);
        for it in 0..n {
            let a = r.bytes::<32>();
            let mut b = r.rel(a);
            let got = u16s(&b256(_mm256_packs_epi32(v256(a), v256(b))));
            assert_eq!(got, ref_packs32_lanes(&u32s(&a), &u32s(&b)), "_mm256_packs_epi32 {a:02x?} {b:02x?}");
            // testz: disjoint operands half the time, some with one shared bit.
            if it % 2 == 0 {
                for k in 0..32 {
                    b[k] &= !a[k];
                }
                if it % 4 == 0 {
                    let k = r.next() as usize % 32;
                    b[k] |= a[k] & (1 << (r.next() % 8));
                }
            }
            let got = _mm256_testz_si256(v256(a), v256(b));
            let zero = ref_and8(&a, &b).iter().all(|&x| x == 0);
            assert!(got == 0 || got == 1);
            assert_eq!(got == 1, zero, "_mm256_testz_si256 {a:02x?} {b:02x?}");
            let h = r.bytes::<16>();
            let got = b256(_mm256_broadcastsi128_si256(v128(h)));
            assert_eq!(got.to_vec(), [h, h].concat(), "_mm256_broadcastsi128_si256");
        }
    }
    unsafe { body(iters()) }
}

fn need_avx512() -> bool {
    if !(std::is_x86_feature_detected!("avx512f") && std::is_x86_feature_detected!("avx512bw") && std::is_x86_feature_detected!("avx512vbmi2")) {
        eprintln!("skipping: no AVX-512BW with VBMI2");
        return false;
    }
    true
}

#[test]
fn avx512_lanes() {
    if !need_avx512() {
        return;
    }
    #[target_feature(enable = "avx512f,avx512bw")]
    fn body(n: usize) {
        let mut r = Rng::new(5);
        for _ in 0..n {
            let a = r.bytes::<64>();
            let b = r.rel(a);
            let (x, y) = (v512(a), v512(b));
            assert_eq!(b512(_mm512_and_si512(x, y)).to_vec(), ref_and8(&a, &b), "_mm512_and_si512");
            assert_eq!(b512(_mm512_or_si512(x, y)).to_vec(), ref_or8(&a, &b), "_mm512_or_si512");
            assert_eq!(b512(_mm512_xor_si512(x, y)).to_vec(), ref_xor8(&a, &b), "_mm512_xor_si512");
            assert_eq!(b512(_mm512_subs_epu8(x, y)).to_vec(), ref_subs_u8(&a, &b), "_mm512_subs_epu8");
            assert_eq!(b512(_mm512_shuffle_epi8(x, y)).to_vec(), ref_shuffle8_lanes(&a, &b), "_mm512_shuffle_epi8 {a:02x?} {b:02x?}");
            assert_eq!(u32s(&b512(_mm512_add_epi32(x, y))), ref_add32(&u32s(&a), &u32s(&b)), "_mm512_add_epi32");
            let c = r.byte();
            assert_eq!(b512(_mm512_set1_epi8(c as i8)), [c; 64], "_mm512_set1_epi8");
            let w = r.next() as u32;
            assert_eq!(u32s(&b512(_mm512_set1_epi32(w as i32))), vec![w; 16], "_mm512_set1_epi32");
            let h: [u8; 16] = a[..16].try_into().unwrap();
            assert_eq!(b512(_mm512_broadcast_i32x4(v128(h))).to_vec(), [h, h, h, h].concat(), "_mm512_broadcast_i32x4");
            assert_eq!(u32s(&b512(_mm512_cvtepu8_epi32(v128(h)))), ref_zext8_32(&h), "_mm512_cvtepu8_epi32");
            assert_eq!(b128(_mm512_castsi512_si128(x)), a[..16], "_mm512_castsi512_si128");
            assert_eq!(b128(_mm512_extracti32x4_epi32::<0>(x)), a[..16], "_mm512_extracti32x4_epi32::<0>");
            assert_eq!(b128(_mm512_extracti32x4_epi32::<1>(x)), a[16..32], "_mm512_extracti32x4_epi32::<1>");
            assert_eq!(b128(_mm512_extracti32x4_epi32::<2>(x)), a[32..48], "_mm512_extracti32x4_epi32::<2>");
            assert_eq!(b128(_mm512_extracti32x4_epi32::<3>(x)), a[48..], "_mm512_extracti32x4_epi32::<3>");
            // Memory, through the wrappers.
            let mut buf = [0u8; 200];
            let o = r.next() as usize % 137;
            buf[o..o + 64].copy_from_slice(&a);
            assert_eq!(b512(unsafe { _mm512_loadu_si512(buf.as_ptr().add(o) as *const __m512i) }), a, "_mm512_loadu_si512");
            let mut q = [7u32; 40];
            let o = r.next() as usize % 25;
            unsafe { _mm512_storeu_si512(q.as_mut_ptr().add(o) as *mut __m512i, x) };
            assert_eq!(&q[o..o + 16], &u32s(&a)[..], "_mm512_storeu_si512");
            assert!(q[..o].iter().chain(&q[o + 16..]).all(|&v| v == 7));
        }
        macro_rules! srl {
            ($($k:literal),*) => {$(
                for _ in 0..n / 16 {
                    let a = r.bytes::<64>();
                    assert_eq!(u16s(&b512(_mm512_srli_epi16::<$k>(v512(a)))), ref_srli16(&u16s(&a), $k), "_mm512_srli_epi16::<{}>", $k);
                }
            )*};
        }
        srl!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 31, 32, 33, 63, 64, 127, 128, 255);
    }
    unsafe { body(iters()) }
}

#[test]
fn avx512_masks() {
    if !need_avx512() {
        return;
    }
    #[target_feature(enable = "avx512f,avx512bw,avx512vbmi2")]
    fn body(n: usize) {
        let mut r = Rng::new(6);
        for it in 0..n {
            let a = r.bytes::<64>();
            let mut b = r.rel(a);
            let (x, y) = (v512(a), v512(b));
            assert_eq!(_mm512_cmpeq_epi8_mask(x, y), ref_movemask(&ref_cmpeq8(&a, &b)), "_mm512_cmpeq_epi8_mask {a:02x?} {b:02x?}");
            assert_eq!(_mm512_cmple_epu8_mask(x, y), ref_movemask(&ref_cmple_u8(&a, &b)), "_mm512_cmple_epu8_mask {a:02x?} {b:02x?}");
            if it % 2 == 0 {
                for k in 0..64 {
                    b[k] &= !a[k];
                }
                for _ in 0..r.next() % 3 {
                    let k = r.next() as usize % 64;
                    b[k] |= a[k] & (1 << (r.next() % 8));
                }
            }
            assert_eq!(_mm512_test_epi8_mask(x, v512(b)), ref_movemask(&ref_testm8(&a, &b)), "_mm512_test_epi8_mask {a:02x?} {b:02x?}");
            let m = r.mask();
            assert_eq!(b512(_mm512_maskz_compress_epi8(m, x)).to_vec(), ref_compress8(m, &a), "_mm512_maskz_compress_epi8 {m:#x} {a:02x?}");
        }
    }
    unsafe { body(iters()) }
}

/// The wrappers themselves (the functions verified code calls), once each,
/// so a wrapper that named the wrong intrinsic would fail.
#[test]
fn avx512_wrappers() {
    if !need_avx512() {
        return;
    }
    use verilith_simd::avx512 as w;
    #[target_feature(enable = "avx512f,avx512bw,avx512vbmi2")]
    fn body(n: usize) {
        let mut r = Rng::new(7);
        for _ in 0..n / 8 {
            let a = r.bytes::<64>();
            let b = r.rel(a);
            let (x, y) = (v512(a), v512(b));
            let h: [u8; 16] = a[..16].try_into().unwrap();
            let m = r.mask();
            let c = r.byte() as i8;
            let d = r.next() as i32;
            unsafe {
                assert_eq!(b512(w::_mm512_and_si512(x, y)), b512(_mm512_and_si512(x, y)));
                assert_eq!(b512(w::_mm512_or_si512(x, y)), b512(_mm512_or_si512(x, y)));
                assert_eq!(b512(w::_mm512_xor_si512(x, y)), b512(_mm512_xor_si512(x, y)));
                assert_eq!(b512(w::_mm512_subs_epu8(x, y)), b512(_mm512_subs_epu8(x, y)));
                assert_eq!(b512(w::_mm512_shuffle_epi8(x, y)), b512(_mm512_shuffle_epi8(x, y)));
                assert_eq!(b512(w::_mm512_add_epi32(x, y)), b512(_mm512_add_epi32(x, y)));
                assert_eq!(b512(w::_mm512_srli_epi16::<4>(x)), b512(_mm512_srli_epi16::<4>(x)));
                assert_eq!(b512(w::_mm512_set1_epi8(c)), b512(_mm512_set1_epi8(c)));
                assert_eq!(b512(w::_mm512_set1_epi32(d)), b512(_mm512_set1_epi32(d)));
                assert_eq!(b512(w::_mm512_broadcast_i32x4(v128(h))), b512(_mm512_broadcast_i32x4(v128(h))));
                assert_eq!(b512(w::_mm512_cvtepu8_epi32(v128(h))), b512(_mm512_cvtepu8_epi32(v128(h))));
                assert_eq!(b128(w::_mm512_castsi512_si128(x)), b128(_mm512_castsi512_si128(x)));
                assert_eq!(b128(w::_mm512_extracti32x4_epi32::<2>(x)), b128(_mm512_extracti32x4_epi32::<2>(x)));
                assert_eq!(w::_mm512_cmpeq_epi8_mask(x, y), _mm512_cmpeq_epi8_mask(x, y));
                assert_eq!(w::_mm512_cmple_epu8_mask(x, y), _mm512_cmple_epu8_mask(x, y));
                assert_eq!(w::_mm512_test_epi8_mask(x, y), _mm512_test_epi8_mask(x, y));
                assert_eq!(b512(w::_mm512_maskz_compress_epi8(m, x)), b512(_mm512_maskz_compress_epi8(m, x)));
                let mut buf = vec![0u8; 100];
                buf[9..73].copy_from_slice(&a);
                assert_eq!(b512(w::load512_u8(&buf, 9)), a);
                let mut q = vec![7u32; 40];
                w::store512_u32(&mut q, 5, x);
                assert_eq!(&q[5..21], &u32s(&a)[..]);
                assert!(q[..5].iter().chain(&q[21..]).all(|&v| v == 7));
            }
        }
    }
    unsafe { body(iters()) }
}

//! The portable emulation (`verilith_simd::emu`) against the CPU, on x86-64: every
//! function on random and edge-biased inputs, every immediate value.
#![cfg(target_arch = "x86_64")]
#![allow(non_snake_case)]
use core::arch::x86_64 as x;
use core::mem::transmute;
use verilith_simd::emu as e;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn byte(&mut self) -> u8 {
        let r = self.next();
        if r % 4 == 0 { [0u8, 1, 0x7f, 0x80, 0x81, 0xff][(r >> 8) as usize % 6] } else { (r >> 16) as u8 }
    }
    fn b16(&mut self) -> [u8; 16] {
        core::array::from_fn(|_| self.byte())
    }
    fn b32(&mut self) -> [u8; 32] {
        core::array::from_fn(|_| self.byte())
    }
}

const N: usize = 20_000;

fn c128(v: x::__m128i) -> [u8; 16] {
    unsafe { transmute(v) }
}
fn c256(v: x::__m256i) -> [u8; 32] {
    unsafe { transmute(v) }
}
fn x128(b: [u8; 16]) -> x::__m128i {
    unsafe { transmute(b) }
}
fn x256(b: [u8; 32]) -> x::__m256i {
    unsafe { transmute(b) }
}

macro_rules! bin {
    ($r:ident, $($f:ident),*) => {$(
        for _ in 0..N {
            let (a, b) = ($r.b16(), $r.b16());
            let want = c128(unsafe { x::$f(x128(a), x128(b)) });
            assert_eq!(e::$f(e::__m128i(a), e::__m128i(b)).0, want, stringify!($f));
        }
    )*};
}
macro_rules! bin256 {
    ($r:ident, $($f:ident),*) => {$(
        for _ in 0..N {
            let (a, b) = ($r.b32(), $r.b32());
            let want = c256(unsafe { x::$f(x256(a), x256(b)) });
            assert_eq!(e::$f(e::__m256i(a), e::__m256i(b)).0, want, stringify!($f));
        }
    )*};
}
macro_rules! imm {
    ($r:ident, $f:ident, $($k:literal),*) => {$(
        for _ in 0..N / 16 {
            let a = $r.b16();
            assert_eq!(e::$f::<$k>(e::__m128i(a)).0, c128(unsafe { x::$f::<$k>(x128(a)) }), "{} {}", stringify!($f), $k);
        }
    )*};
}
macro_rules! imm256 {
    ($r:ident, $f:ident, $($k:literal),*) => {$(
        for _ in 0..N / 16 {
            let a = $r.b32();
            assert_eq!(e::$f::<$k>(e::__m256i(a)).0, c256(unsafe { x::$f::<$k>(x256(a)) }), "{} {}", stringify!($f), $k);
        }
    )*};
}
macro_rules! imm2 {
    ($r:ident, $f:ident, $($k:literal),*) => {$(
        for _ in 0..N / 16 {
            let (a, b) = ($r.b16(), $r.b16());
            assert_eq!(e::$f::<$k>(e::__m128i(a), e::__m128i(b)).0, c128(unsafe { x::$f::<$k>(x128(a), x128(b)) }), "{} {}", stringify!($f), $k);
        }
    )*};
}
macro_rules! imm2_256 {
    ($r:ident, $f:ident, $($k:literal),*) => {$(
        for _ in 0..N / 16 {
            let (a, b) = ($r.b32(), $r.b32());
            assert_eq!(e::$f::<$k>(e::__m256i(a), e::__m256i(b)).0, c256(unsafe { x::$f::<$k>(x256(a), x256(b)) }), "{} {}", stringify!($f), $k);
        }
    )*};
}

#[test]
fn sse2_and_ssse3() {
    let mut r = Rng(0x1234_5678_9abc_def1);
    bin!(r, _mm_add_epi8, _mm_sub_epi8, _mm_adds_epu8, _mm_subs_epu8, _mm_adds_epi8, _mm_subs_epi8, _mm_packs_epi16, _mm_min_epu8, _mm_max_epu8, _mm_avg_epu8,
        _mm_cmpeq_epi8, _mm_cmpgt_epi8, _mm_add_epi16, _mm_sub_epi16, _mm_mullo_epi16, _mm_mulhi_epi16,
        _mm_cmpeq_epi16, _mm_madd_epi16, _mm_add_epi32, _mm_sub_epi32, _mm_cmpeq_epi32, _mm_cmpgt_epi32,
        _mm_add_epi64, _mm_sad_epu8, _mm_unpacklo_epi8, _mm_unpackhi_epi8, _mm_unpacklo_epi32,
        _mm_unpackhi_epi32, _mm_unpacklo_epi64, _mm_packus_epi16, _mm_shuffle_epi8, _mm_maddubs_epi16,
        _mm_and_si128, _mm_or_si128, _mm_xor_si128, _mm_andnot_si128);
    imm!(r, _mm_srli_epi16, 0, 1, 7, 15, 16, 255);
    imm!(r, _mm_slli_epi16, 0, 1, 7, 15, 16, 255);
    imm!(r, _mm_srai_epi16, 0, 1, 7, 15, 16, 255);
    imm!(r, _mm_srli_epi32, 0, 1, 13, 31, 32, 255);
    imm!(r, _mm_slli_epi32, 0, 1, 13, 31, 32, 255);
    imm!(r, _mm_shuffle_epi32, 0, 0x1b, 0x4e, 0xb1, 0xff, 0x93);
    imm!(r, _mm_slli_si128, 0, 1, 4, 8, 15, 16, 255);
    imm!(r, _mm_srli_si128, 0, 1, 4, 8, 15, 16, 255);
    imm2!(r, _mm_alignr_epi8, 0, 1, 8, 15, 16, 17, 31, 32, 255);
    for _ in 0..N {
        let (a, b, m) = (r.b16(), r.b16(), r.b16());
        assert_eq!(e::_mm_blendv_epi8(e::__m128i(a), e::__m128i(b), e::__m128i(m)).0,
            c128(unsafe { x::_mm_blendv_epi8(x128(a), x128(b), x128(m)) }));
        assert_eq!(e::_mm_movemask_epi8(e::__m128i(a)), unsafe { x::_mm_movemask_epi8(x128(a)) });
        let w = r.next();
        assert_eq!(e::_mm_set1_epi8(w as i8).0, c128(unsafe { x::_mm_set1_epi8(w as i8) }));
        assert_eq!(e::_mm_set1_epi16(w as i16).0, c128(unsafe { x::_mm_set1_epi16(w as i16) }));
        assert_eq!(e::_mm_set1_epi32(w as i32).0, c128(unsafe { x::_mm_set1_epi32(w as i32) }));
        assert_eq!(e::_mm_set1_epi64x(w as i64).0, c128(unsafe { x::_mm_set1_epi64x(w as i64) }));
        let q = |k: u32| (w >> k) as i32;
        assert_eq!(e::_mm_setr_epi32(q(0), q(8), q(16), q(32)).0, c128(unsafe { x::_mm_setr_epi32(q(0), q(8), q(16), q(32)) }));
        let b8 = |k: u32| (w >> (4 * k)) as i8;
        assert_eq!(
            e::_mm_setr_epi8(b8(0), b8(1), b8(2), b8(3), b8(4), b8(5), b8(6), b8(7), b8(8), b8(9), b8(10), b8(11), b8(12), b8(13), b8(14), b8(15)).0,
            c128(unsafe { x::_mm_setr_epi8(b8(0), b8(1), b8(2), b8(3), b8(4), b8(5), b8(6), b8(7), b8(8), b8(9), b8(10), b8(11), b8(12), b8(13), b8(14), b8(15)) })
        );
        assert_eq!(e::_mm_cvtsi32_si128(w as i32).0, c128(unsafe { x::_mm_cvtsi32_si128(w as i32) }));
        assert_eq!(e::_mm_cvtsi64_si128(w as i64).0, c128(unsafe { x::_mm_cvtsi64_si128(w as i64) }));
        assert_eq!(e::_mm_cvtsi128_si32(e::__m128i(a)), unsafe { x::_mm_cvtsi128_si32(x128(a)) });
        assert_eq!(e::_mm_cvtsi128_si64(e::__m128i(a)), unsafe { x::_mm_cvtsi128_si64(x128(a)) });
        let mut buf = [0u8; 40];
        let o = (w % 24) as usize;
        unsafe { e::_mm_storeu_si128(buf.as_mut_ptr().add(o) as *mut e::__m128i, e::__m128i(a)) };
        assert_eq!(&buf[o..o + 16], &a);
        assert_eq!(unsafe { e::_mm_loadu_si128(buf.as_ptr().add(o) as *const e::__m128i) }.0, a);
        // The 8-byte forms: only 8 bytes are read and written.
        let mut small = [0xa5u8; 24];
        let o8 = (w % 17) as usize;
        unsafe { e::_mm_storel_epi64(small.as_mut_ptr().add(o8) as *mut e::__m128i, e::__m128i(a)) };
        let mut want = [0xa5u8; 24];
        want[o8..o8 + 8].copy_from_slice(&a[..8]);
        assert_eq!(small, want);
        let mut xs = [0xa5u8; 24];
        unsafe { x::_mm_storel_epi64(xs.as_mut_ptr().add(o8) as *mut x::__m128i, x128(a)) };
        assert_eq!(small, xs);
        assert_eq!(unsafe { e::_mm_loadl_epi64(small.as_ptr().add(o8) as *const e::__m128i) }.0,
            c128(unsafe { x::_mm_loadl_epi64(small.as_ptr().add(o8) as *const x::__m128i) }));
        // The 4-byte store: only 4 bytes are written.
        let mut small = [0xa5u8; 24];
        let o4 = (w % 21) as usize;
        unsafe { e::_mm_storeu_si32(small.as_mut_ptr().add(o4), e::__m128i(a)) };
        let mut want = [0xa5u8; 24];
        want[o4..o4 + 4].copy_from_slice(&a[..4]);
        assert_eq!(small, want);
        let mut xs = [0xa5u8; 24];
        unsafe { x::_mm_storeu_si32(xs.as_mut_ptr().add(o4), x128(a)) };
        assert_eq!(small, xs);
    }
    assert_eq!(e::_mm_setzero_si128().0, [0; 16]);
}

#[test]
fn extras() {
    let mut r = Rng(0x51ed_270b_9f3c_1a47);
    bin!(r, _mm_packs_epi32);
    for _ in 0..N {
        let w: [i16; 8] = core::array::from_fn(|_| r.next() as i16);
        assert_eq!(
            e::_mm_setr_epi16(w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]).0,
            c128(unsafe { x::_mm_setr_epi16(w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]) })
        );
    }
    if std::is_x86_feature_detected!("pclmulqdq") {
        #[target_feature(enable = "pclmulqdq")]
        fn go<const K: i32>(a: x::__m128i, b: x::__m128i) -> x::__m128i {
            x::_mm_clmulepi64_si128::<K>(a, b)
        }
        for _ in 0..N {
            let (a, b) = (r.b16(), r.b16());
            assert_eq!(e::_mm_clmulepi64_si128::<0>(e::__m128i(a), e::__m128i(b)).0, c128(unsafe { go::<0>(x128(a), x128(b)) }));
            assert_eq!(e::_mm_clmulepi64_si128::<1>(e::__m128i(a), e::__m128i(b)).0, c128(unsafe { go::<1>(x128(a), x128(b)) }));
            assert_eq!(e::_mm_clmulepi64_si128::<16>(e::__m128i(a), e::__m128i(b)).0, c128(unsafe { go::<16>(x128(a), x128(b)) }));
            assert_eq!(e::_mm_clmulepi64_si128::<17>(e::__m128i(a), e::__m128i(b)).0, c128(unsafe { go::<17>(x128(a), x128(b)) }));
        }
    }
    if std::is_x86_feature_detected!("avx2") {
        #[target_feature(enable = "avx2")]
        fn go(r: &mut Rng) {
            bin256!(r, _mm256_packs_epi32);
            for it in 0..N {
                let a = r.b32();
                let mut b = r.b32();
                if it % 2 == 0 {
                    for k in 0..32 {
                        b[k] &= !a[k];
                    }
                    if it % 4 == 0 {
                        b[(r.next() % 32) as usize] |= a[(r.next() % 32) as usize];
                    }
                }
                assert_eq!(
                    e::_mm256_testz_si256(e::__m256i(a), e::__m256i(b)),
                    x::_mm256_testz_si256(x256(a), x256(b))
                );
                let h = r.b16();
                assert_eq!(e::_mm256_broadcastsi128_si256(e::__m128i(h)).0, c256(x::_mm256_broadcastsi128_si256(x128(h))));
            }
        }
        unsafe { go(&mut r) }
    }
}

#[test]
fn avx2() {
    if !std::is_x86_feature_detected!("avx2") {
        return;
    }
    let mut r = Rng(0x0f1e_2d3c_4b5a_6978);
    bin256!(r, _mm256_add_epi8, _mm256_sub_epi8, _mm256_adds_epu8, _mm256_subs_epu8, _mm256_adds_epi8,
        _mm256_subs_epi8, _mm256_packs_epi16, _mm256_min_epu8,
        _mm256_max_epu8, _mm256_avg_epu8, _mm256_cmpeq_epi8, _mm256_cmpgt_epi8, _mm256_add_epi16,
        _mm256_sub_epi16, _mm256_mullo_epi16, _mm256_mulhi_epi16, _mm256_cmpeq_epi16, _mm256_madd_epi16,
        _mm256_add_epi32, _mm256_sub_epi32, _mm256_cmpeq_epi32, _mm256_cmpgt_epi32, _mm256_add_epi64,
        _mm256_sad_epu8, _mm256_unpacklo_epi8, _mm256_unpackhi_epi8, _mm256_unpacklo_epi32,
        _mm256_unpackhi_epi32, _mm256_unpacklo_epi64, _mm256_packus_epi16, _mm256_shuffle_epi8,
        _mm256_maddubs_epi16, _mm256_and_si256, _mm256_or_si256, _mm256_xor_si256, _mm256_andnot_si256,
        _mm256_permutevar8x32_epi32);
    imm256!(r, _mm256_srli_epi16, 0, 1, 7, 15, 16, 255);
    imm256!(r, _mm256_slli_epi16, 0, 1, 7, 15, 16, 255);
    imm256!(r, _mm256_srai_epi16, 0, 1, 7, 15, 16, 255);
    imm256!(r, _mm256_srli_epi32, 0, 1, 13, 31, 32, 255);
    imm256!(r, _mm256_slli_epi32, 0, 1, 13, 31, 32, 255);
    imm256!(r, _mm256_shuffle_epi32, 0, 0x1b, 0x4e, 0xb1, 0xff, 0x93);
    imm256!(r, _mm256_bslli_epi128, 0, 1, 4, 8, 15, 16, 255);
    imm256!(r, _mm256_bsrli_epi128, 0, 1, 4, 8, 15, 16, 255);
    imm2_256!(r, _mm256_alignr_epi8, 0, 1, 8, 15, 16, 17, 31, 32, 255);
    imm2_256!(r, _mm256_permute2x128_si256, 0x00, 0x01, 0x02, 0x03, 0x08, 0x20, 0x21, 0x30, 0x31, 0x80, 0x13, 0x88, 0xff);
    for _ in 0..N {
        let (a, b, m) = (r.b32(), r.b32(), r.b32());
        assert_eq!(e::_mm256_blendv_epi8(e::__m256i(a), e::__m256i(b), e::__m256i(m)).0,
            c256(unsafe { x::_mm256_blendv_epi8(x256(a), x256(b), x256(m)) }));
        assert_eq!(e::_mm256_movemask_epi8(e::__m256i(a)), unsafe { x::_mm256_movemask_epi8(x256(a)) });
        assert_eq!(e::_mm256_extracti128_si256::<0>(e::__m256i(a)).0, c128(unsafe { x::_mm256_extracti128_si256::<0>(x256(a)) }));
        assert_eq!(e::_mm256_extracti128_si256::<1>(e::__m256i(a)).0, c128(unsafe { x::_mm256_extracti128_si256::<1>(x256(a)) }));
        assert_eq!(e::_mm256_castsi256_si128(e::__m256i(a)).0, c128(unsafe { x::_mm256_castsi256_si128(x256(a)) }));
        let (h, l) = (r.b16(), r.b16());
        assert_eq!(e::_mm256_set_m128i(e::__m128i(h), e::__m128i(l)).0, c256(unsafe { x::_mm256_set_m128i(x128(h), x128(l)) }));
        let w = r.next();
        assert_eq!(e::_mm256_set1_epi8(w as i8).0, c256(unsafe { x::_mm256_set1_epi8(w as i8) }));
        assert_eq!(e::_mm256_set1_epi16(w as i16).0, c256(unsafe { x::_mm256_set1_epi16(w as i16) }));
        assert_eq!(e::_mm256_set1_epi32(w as i32).0, c256(unsafe { x::_mm256_set1_epi32(w as i32) }));
        assert_eq!(e::_mm256_set1_epi64x(w as i64).0, c256(unsafe { x::_mm256_set1_epi64x(w as i64) }));
        let q = |k: u32| (w >> k) as i32;
        assert_eq!(
            e::_mm256_setr_epi32(q(0), q(4), q(8), q(12), q(16), q(20), q(24), q(32)).0,
            c256(unsafe { x::_mm256_setr_epi32(q(0), q(4), q(8), q(12), q(16), q(20), q(24), q(32)) })
        );
        let v: [i8; 32] = core::array::from_fn(|k| (w >> (2 * k)) as i8);
        assert_eq!(
            e::_mm256_setr_epi8(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15], v[16], v[17], v[18], v[19], v[20], v[21], v[22], v[23], v[24], v[25], v[26], v[27], v[28], v[29], v[30], v[31]).0,
            c256(unsafe { x::_mm256_setr_epi8(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13], v[14], v[15], v[16], v[17], v[18], v[19], v[20], v[21], v[22], v[23], v[24], v[25], v[26], v[27], v[28], v[29], v[30], v[31]) })
        );
        let mut buf = [0u8; 64];
        let o = (w % 32) as usize;
        unsafe { e::_mm256_storeu_si256(buf.as_mut_ptr().add(o) as *mut e::__m256i, e::__m256i(a)) };
        assert_eq!(&buf[o..o + 32], &a);
        assert_eq!(unsafe { e::_mm256_loadu_si256(buf.as_ptr().add(o) as *const e::__m256i) }.0, a);
    }
    assert_eq!(e::_mm256_setzero_si256().0, [0; 32]);
}

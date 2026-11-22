// Unverified prototypes of the AVX2 kernels, to check the design's speed.
use core::arch::x86_64::*;

const ENC_SHUF: [u8; 32] = [1,0,2,1, 4,3,5,4, 7,6,8,7, 10,9,11,10, 1,0,2,1, 4,3,5,4, 7,6,8,7, 10,9,11,10];
const LUT_STD: [i8; 32] = [-65+97-26-0+0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];

#[target_feature(enable = "avx2")]
pub unsafe fn enc(x: &[u8], out: &mut [u8]) -> usize {
    let shuf = _mm256_loadu_si256(ENC_SHUF.as_ptr() as *const _);
    let mut lut = [0i8; 32];
    for l in 0..2 {
        lut[16*l] = (b'a' as i8).wrapping_sub(26);
        for k in 1..11 { lut[16*l+k] = (b'0' as i8).wrapping_sub(52); }
        lut[16*l+11] = (b'+' as i8).wrapping_sub(62);
        lut[16*l+12] = (b'/' as i8).wrapping_sub(63);
        lut[16*l+13] = b'A' as i8;
    }
    let _ = LUT_STD;
    let lut = _mm256_loadu_si256(lut.as_ptr() as *const _);
    let mut i = 0; let mut o = 0;
    while i + 28 <= x.len() {
        let lo = _mm_loadu_si128(x.as_ptr().add(i) as *const _);
        let hi = _mm_loadu_si128(x.as_ptr().add(i + 12) as *const _);
        let v = _mm256_set_m128i(hi, lo);
        let s = _mm256_shuffle_epi8(v, shuf);
        let t0 = _mm256_and_si256(_mm256_srli_epi32(s, 10), _mm256_set1_epi32(0x3f));
        let t1 = _mm256_and_si256(_mm256_slli_epi32(s, 4), _mm256_set1_epi32(0x3f00));
        let t2 = _mm256_and_si256(_mm256_srli_epi32(s, 6), _mm256_set1_epi32(0x3f0000));
        let t3 = _mm256_and_si256(_mm256_slli_epi32(s, 8), _mm256_set1_epi32(0x3f000000));
        let idx = _mm256_or_si256(_mm256_or_si256(t0, t1), _mm256_or_si256(t2, t3));
        let mut r = _mm256_subs_epu8(idx, _mm256_set1_epi8(51));
        let less = _mm256_cmpgt_epi8(_mm256_set1_epi8(26), idx);
        r = _mm256_or_si256(r, _mm256_and_si256(less, _mm256_set1_epi8(13)));
        r = _mm256_shuffle_epi8(lut, r);
        r = _mm256_add_epi8(r, idx);
        _mm256_storeu_si256(out.as_mut_ptr().add(o) as *mut _, r);
        i += 24; o += 32;
    }
    i
}

const VL: [u8; 16] = [11, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 21, 23, 23, 23, 21];
const VH: [u8; 16] = [1, 1, 2, 4, 8, 16, 8, 16, 1, 1, 1, 1, 1, 1, 1, 1];
const ROLL: [i8; 16] = [0, 16, 19, 4, -65, -65, -71, -71, 0,0,0,0,0,0,0,0];
const PACK: [i8; 32] = [2,1,0,6,5,4,10,9,8,14,13,12,-1,-1,-1,-1, 2,1,0,6,5,4,10,9,8,14,13,12,-1,-1,-1,-1];

#[target_feature(enable = "avx2")]
pub unsafe fn dec(s: &[u8], out: &mut [u8]) -> Option<usize> {
    let d = |a: &[u8;16]| { let mut b=[0u8;32]; b[..16].copy_from_slice(a); b[16..].copy_from_slice(a); _mm256_loadu_si256(b.as_ptr() as *const _) };
    let vl = d(&VL); let vh = d(&VH);
    let roll = { let mut b=[0i8;32]; b[..16].copy_from_slice(&ROLL); b[16..].copy_from_slice(&ROLL); _mm256_loadu_si256(b.as_ptr() as *const _) };
    let pack = _mm256_loadu_si256(PACK.as_ptr() as *const _);
    let perm = _mm256_setr_epi32(0,1,2,4,5,6,3,7);
    let m0f = _mm256_set1_epi8(0x0f);
    let mut err = _mm256_setzero_si256();
    let mut j = 0; let mut o = 0;
    while j + 44 <= s.len() {
        let v = _mm256_loadu_si256(s.as_ptr().add(j) as *const _);
        let hi = _mm256_and_si256(_mm256_srli_epi32(v, 4), m0f);
        let lo = _mm256_and_si256(v, m0f);
        let l = _mm256_shuffle_epi8(vl, lo);
        let h = _mm256_shuffle_epi8(vh, hi);
        err = _mm256_or_si256(err, _mm256_and_si256(l, h));
        let eq = _mm256_cmpeq_epi8(v, _mm256_set1_epi8(0x2F));
        let key = _mm256_add_epi8(hi, _mm256_and_si256(eq, _mm256_set1_epi8(-1)));
        let vals = _mm256_add_epi8(v, _mm256_shuffle_epi8(roll, key));
        let m = _mm256_maddubs_epi16(vals, _mm256_set1_epi32(0x01400140));
        let w = _mm256_madd_epi16(m, _mm256_set1_epi32(0x00011000));
        let p = _mm256_shuffle_epi8(w, pack);
        let p = _mm256_permutevar8x32_epi32(p, perm);
        _mm256_storeu_si256(out.as_mut_ptr().add(o) as *mut _, p);
        j += 32; o += 24;
    }
    if _mm256_movemask_epi8(_mm256_cmpeq_epi8(err, _mm256_setzero_si256())) != -1 { return None; }
    Some(j)
}

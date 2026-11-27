//! Differential test of every NEON wrapper in `verilith_simd::neon` against the
//! verified reference implementation of its spec. On AArch64 this checks
//! the real instructions (the trusted specs). On `wasm32-wasip1` built
//! with `simd128`, run under a WebAssembly engine, it checks the
//! SIMD128 instructions (`verilith_simd::wasm`) through the verified
//! `verilith_simd::wasm_neon`. On x86-64 it checks the same path, with
//! the SIMD128 instructions run as the SSE code of `verilith_simd::wasm_x86`
//! where there is some (which needs a CPU with SSE4.1 and SSSE3).
//! Elsewhere it checks the emulation the wrappers call there.
//!
//! `VSIMD_ITERS` sets the number of random inputs per wrapper (default
//! 200,000).
use verilith_simd::neon::*;
use verilith_simd::refs::*;
use verilith_simd::refs_neon::*;

fn iters() -> usize {
    std::env::var("VSIMD_ITERS").ok().and_then(|s| s.parse().ok()).unwrap_or(200_000)
}

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
        if r % 4 == 0 { [0u8, 1, 0x0f, 0x10, 0x7f, 0x80, 0x81, 0xfe, 0xff][(r >> 8) as usize % 9] } else { (r >> 16) as u8 }
    }
    fn b16(&mut self) -> [u8; 16] {
        let mode = self.next() % 4;
        core::array::from_fn(|_| if mode == 0 { (self.next() >> 30) as u8 % 20 } else { self.byte() })
    }
}

fn v(b: [u8; 16]) -> uint8x16_t {
    vld1q_u8_at(&b, 0)
}
fn bytes(x: uint8x16_t) -> [u8; 16] {
    let mut b = [0u8; 16];
    vst1q_u8_at(&mut b, 0, x);
    b
}
fn u32s(b: &[u8; 16]) -> Vec<u32> {
    b.chunks(4).map(|c| u32::from_le_bytes(c.try_into().unwrap())).collect()
}

fn u64s(b: &[u8; 16]) -> Vec<u64> {
    b.chunks(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect()
}

fn u16s(b: &[u8; 16]) -> Vec<u16> {
    (0..8).map(|i| u16::from_le_bytes([b[2 * i], b[2 * i + 1]])).collect()
}

#[test]
fn binary_ops() {
    let mut r = Rng(0x5eed_0001_dead_beef);
    for _ in 0..iters() {
        let (a, b) = (r.b16(), r.b16());
        let (va, vb) = (v(a), v(b));
        assert_eq!(bytes(vandq_u8(va, vb)).to_vec(), ref_and8(&a, &b), "and");
        assert_eq!(bytes(vorrq_u8(va, vb)).to_vec(), ref_or8(&a, &b), "orr");
        assert_eq!(bytes(veorq_u8(va, vb)).to_vec(), ref_xor8(&a, &b), "eor");
        assert_eq!(bytes(vaddq_u8(va, vb)).to_vec(), ref_add8(&a, &b), "add");
        assert_eq!(bytes(vqsubq_u8(va, vb)).to_vec(), ref_subs_u8(&a, &b), "uqsub");
        assert_eq!(bytes(vceqq_u8(va, vb)).to_vec(), ref_cmpeq8(&a, &b), "cmeq");
        assert_eq!(bytes(vqtbl1q_u8(va, vb)).to_vec(), ref_tbl1(&a, &b), "tbl");
        assert_eq!(bytes(vzip1q_u8(va, vb)).to_vec(), ref_unpacklo8_lanes(&a, &b), "zip1");
        assert_eq!(bytes(vzip2q_u8(va, vb)).to_vec(), ref_unpackhi8_lanes(&a, &b), "zip2");
        assert_eq!(u16s(&bytes(vzip1q_u16(va, vb))), ref_unpacklo16_lanes(&u16s(&a), &u16s(&b)), "zip1 u16");
        assert_eq!(u16s(&bytes(vzip2q_u16(va, vb))), ref_unpackhi16_lanes(&u16s(&a), &u16s(&b)), "zip2 u16");
        assert_eq!(u32s(&bytes(vzip1q_u32(va, vb))), ref_unpacklo32_lanes(&u32s(&a), &u32s(&b)), "zip1 u32");
        assert_eq!(u32s(&bytes(vzip2q_u32(va, vb))), ref_unpackhi32_lanes(&u32s(&a), &u32s(&b)), "zip2 u32");
        assert_eq!(u64s(&bytes(vzip1q_u64(va, vb))), ref_unpacklo64_lanes(&u64s(&a), &u64s(&b)), "zip1 u64");
        assert_eq!(u64s(&bytes(vzip2q_u64(va, vb))), ref_unpackhi64_lanes(&u64s(&a), &u64s(&b)), "zip2 u64");
        assert_eq!(bytes(vuzp1q_u8(va, vb)).to_vec(), ref_uzp1_8(&a, &b), "uzp1");
        assert_eq!(u16s(&bytes(vaddq_s16(va, vb))), ref_add16(&u16s(&a), &u16s(&b)), "add s16");
        assert_eq!(u16s(&bytes(vsubq_s16(va, vb))), ref_sub16(&u16s(&a), &u16s(&b)), "sub s16");
        assert_eq!(u16s(&bytes(vqdmulhq_s16(va, vb))), ref_qdmulh_s16(&u16s(&a), &u16s(&b)), "sqdmulh");
        assert_eq!(bytes(vpaddq_u8(va, vb)).to_vec(), ref_padd8(&a, &b), "addp");
        assert_eq!(bytes(vrhaddq_u8(va, vb)).to_vec(), ref_avg_u8(&a, &b), "urhadd");
        assert_eq!(bytes(vsubq_u8(va, vb)).to_vec(), ref_sub8(&a, &b), "sub");
        assert_eq!(u16s(&bytes(vqsubq_u16(va, vb))), ref_subs_u16(&u16s(&a), &u16s(&b)), "uqsub u16");
        assert_eq!(bytes(vmaxq_u8(va, vb)).to_vec(), ref_max_u8(&a, &b), "umax");
        assert_eq!(bytes(vabdq_u8(va, vb)).to_vec(), ref_abd_u8(&a, &b), "uabd");
        assert_eq!(bytes(vcleq_u8(va, vb)).to_vec(), ref_cmple_u8(&a, &b), "cmhs (le)");
        assert_eq!(bytes(vqaddq_u8(va, vb)).to_vec(), ref_adds_u8(&a, &b), "uqadd");
        assert_eq!(bytes(vbicq_u8(va, vb)).to_vec(), ref_andnot8(&b, &a), "bic");
        assert_eq!(bytes(vqaddq_s8(va, vb)).to_vec(), ref_adds_s8(&a, &b), "sqadd");
        assert_eq!(bytes(vqsubq_s8(va, vb)).to_vec(), ref_subs_s8(&a, &b), "sqsub");
        assert_eq!(bytes(vmulq_u8(va, vb)).to_vec(), ref_mullo8(&a, &b), "mul.16b");
        assert_eq!(u16s(&bytes(vmulq_u16(va, vb))), ref_mullo16(&u16s(&a), &u16s(&b)), "mul.8h");
        assert_eq!(u32s(&bytes(vmulq_u32(va, vb))), ref_mullo32(&u32s(&a), &u32s(&b)), "mul.4s");
        assert_eq!(u16s(&bytes(vpaddlq_u8(va))), ref_paddl8(&a), "uaddlp.16b");
        assert_eq!(u32s(&bytes(vpaddlq_u16(va))), ref_paddl16(&u16s(&a)), "uaddlp.8h");
        assert_eq!(u64s(&bytes(vpaddlq_u32(va))), ref_paddl32(&u32s(&a)), "uaddlp.4s");
    }
}

/// The loop filter's byte operations on every pair of bytes, against the
/// references and against plain statements of each.
#[test]
fn filter_byte_pairs() {
    for x in 0..=255u8 {
        let a = [x; 16];
        for o in 0..16u8 {
            let b: [u8; 16] = core::array::from_fn(|i| (i as u8).wrapping_mul(16).wrapping_add(o));
            let (va, vb) = (v(a), v(b));
            let got = [
                bytes(vmaxq_u8(va, vb)),
                bytes(vabdq_u8(va, vb)),
                bytes(vcleq_u8(va, vb)),
                bytes(vqaddq_u8(va, vb)),
                bytes(vbicq_u8(va, vb)),
                bytes(vqaddq_s8(va, vb)),
                bytes(vqsubq_s8(va, vb)),
            ];
            assert_eq!(got[0].to_vec(), ref_max_u8(&a, &b), "umax {x}");
            assert_eq!(got[1].to_vec(), ref_abd_u8(&a, &b), "uabd {x}");
            assert_eq!(got[2].to_vec(), ref_cmple_u8(&a, &b), "cmhs {x}");
            assert_eq!(got[3].to_vec(), ref_adds_u8(&a, &b), "uqadd {x}");
            assert_eq!(got[4].to_vec(), ref_andnot8(&b, &a), "bic {x}");
            assert_eq!(got[5].to_vec(), ref_adds_s8(&a, &b), "sqadd {x}");
            assert_eq!(got[6].to_vec(), ref_subs_s8(&a, &b), "sqsub {x}");
            for i in 0..16 {
                let (p, q) = (a[i], b[i]);
                assert_eq!(got[0][i], p.max(q));
                assert_eq!(got[1][i], p.abs_diff(q));
                assert_eq!(got[2][i], if p <= q { 0xff } else { 0 });
                assert_eq!(got[3][i], p.saturating_add(q));
                assert_eq!(got[4][i], p & !q);
                assert_eq!(got[5][i], (p as i8).saturating_add(q as i8) as u8);
                assert_eq!(got[6][i], (p as i8).saturating_sub(q as i8) as u8);
            }
        }
    }
}

macro_rules! ext {
    ($r:ident, $($k:literal),*) => {$(
        for _ in 0..iters() / 16 {
            let (a, b) = ($r.b16(), $r.b16());
            assert_eq!(bytes(vextq_u8::<$k>(v(a), v(b))).to_vec(), ref_alignr_lanes(&b, &a, $k), "ext {}", $k);
        }
    )*};
}
macro_rules! shr {
    ($r:ident, $($k:literal),*) => {$(
        for _ in 0..iters() / 8 {
            let a = $r.b16();
            assert_eq!(bytes(vshrq_n_u8::<$k>(v(a))).to_vec(), ref_shr8(&a, $k), "ushr {}", $k);
        }
    )*};
}

macro_rules! sshr16 {
    ($r:ident, $($k:literal),*) => {$(
        for _ in 0..iters() / 8 {
            let a = $r.b16();
            assert_eq!(u16s(&bytes(vshrq_n_s16::<$k>(v(a)))), ref_srai16(&u16s(&a), $k), "sshr {}", $k);
        }
    )*};
}

macro_rules! sshr8 {
    ($r:ident, $($k:literal),*) => {$(
        for _ in 0..iters() / 8 {
            let a = $r.b16();
            assert_eq!(bytes(vshrq_n_s8::<$k>(v(a))).to_vec(), ref_sra8(&a, $k), "sshr.16b {}", $k);
        }
        // Every byte value.
        for x in 0..=255u8 {
            let a: [u8; 16] = core::array::from_fn(|i| x.wrapping_add(i as u8));
            let got = bytes(vshrq_n_s8::<$k>(v(a)));
            assert_eq!(got.to_vec(), ref_sra8(&a, $k), "sshr.16b {} {x}", $k);
            for i in 0..16 {
                assert_eq!(got[i], ((a[i] as i8) >> ($k as u32).min(7)) as u8);
            }
        }
    )*};
}

/// The spec of the signed saturating narrowing shift, and a plain
/// statement of it.
fn want_sqshrn(a: &[u8; 16], b: &[u8; 16], n: u32) -> Vec<u8> {
    ref_packs16_lanes(&ref_srai16(&u16s(a), n), &ref_srai16(&u16s(b), n))
}
fn plain_sqshrn(a: &[u8; 16], b: &[u8; 16], n: u32) -> Vec<u8> {
    u16s(a).iter().chain(u16s(b).iter()).map(|&x| ((x as i16) >> n).clamp(-128, 127) as i8 as u8).collect()
}
macro_rules! narrow_s {
    ($r:ident, $($k:literal),*) => {$(
        for _ in 0..iters() / 8 {
            let (a, b) = ($r.b16(), $r.b16());
            let s = bytes(vqshrn2_n_s16::<$k>(v(a), v(b))).to_vec();
            assert_eq!(s, want_sqshrn(&a, &b, $k), "sqshrn {}", $k);
            assert_eq!(s, plain_sqshrn(&a, &b, $k), "sqshrn {} (plain)", $k);
        }
        // Every 16-bit value in every lane position.
        for x in 0..=0xffffu16 {
            let y = x.wrapping_mul(0x9e37).wrapping_add(0x79b9);
            let (mut a, mut b) = ([0u8; 16], [0u8; 16]);
            for i in 0..8 {
                a[2 * i..2 * i + 2].copy_from_slice(&x.wrapping_add(i as u16).to_le_bytes());
                b[2 * i..2 * i + 2].copy_from_slice(&y.wrapping_sub(i as u16).to_le_bytes());
            }
            assert_eq!(bytes(vqshrn2_n_s16::<$k>(v(a), v(b))).to_vec(), want_sqshrn(&a, &b, $k), "sqshrn {} {x:#x}", $k);
            assert_eq!(want_sqshrn(&a, &b, $k), plain_sqshrn(&a, &b, $k));
        }
    )*};
}

/// The specs of the widening shifts, on the vector `a`: its low (or high)
/// bytes interleaved with zeros, as 16-bit lanes, shifted left.
fn want_shll(a: &[u8; 16], high: bool, n: u32) -> Vec<u16> {
    let z = [0u8; 16];
    let w: [u8; 16] =
        if high { ref_unpackhi8_lanes(a, &z) } else { ref_unpacklo8_lanes(a, &z) }.try_into().unwrap();
    ref_slli16(&u16s(&w), n)
}
/// The specs of the two saturating narrowing shifts.
fn want_sqshrun(a: &[u8; 16], b: &[u8; 16], n: u32) -> Vec<u8> {
    ref_packus16_lanes(&ref_srai16(&u16s(a), n), &ref_srai16(&u16s(b), n))
}
fn want_uqshrn(a: &[u8; 16], b: &[u8; 16], n: u32) -> Vec<u8> {
    ref_packus16_lanes(&ref_srli16(&u16s(a), n), &ref_srli16(&u16s(b), n))
}
/// Plain statements of the same three operations, to check the specs'
/// wording as well as the instructions.
fn plain_shll(a: &[u8; 16], high: bool, n: u32) -> Vec<u16> {
    (0..8).map(|i| (a[i + if high { 8 } else { 0 }] as u16) << n).collect()
}
fn plain_sqshrun(a: &[u8; 16], b: &[u8; 16], n: u32) -> Vec<u8> {
    u16s(a).iter().chain(u16s(b).iter()).map(|&x| ((x as i16) >> n).clamp(0, 255) as u8).collect()
}
fn plain_uqshrn(a: &[u8; 16], b: &[u8; 16], n: u32) -> Vec<u8> {
    u16s(a).iter().chain(u16s(b).iter()).map(|&x| (x >> n).min(255) as u8).collect()
}

macro_rules! shll {
    ($r:ident, $($k:literal),*) => {$(
        for _ in 0..iters() / 8 {
            let a = $r.b16();
            let lo = u16s(&bytes(vshll_low_n_u8::<$k>(v(a))));
            let hi = u16s(&bytes(vshll_high_n_u8::<$k>(v(a))));
            assert_eq!(lo, want_shll(&a, false, $k), "ushll {}", $k);
            assert_eq!(hi, want_shll(&a, true, $k), "ushll2 {}", $k);
            assert_eq!(lo, plain_shll(&a, false, $k), "ushll {} (plain)", $k);
            assert_eq!(hi, plain_shll(&a, true, $k), "ushll2 {} (plain)", $k);
        }
    )*};
}
macro_rules! narrow {
    ($r:ident, $($k:literal),*) => {$(
        for _ in 0..iters() / 8 {
            let (a, b) = ($r.b16(), $r.b16());
            let s = bytes(vqshrun2_n_s16::<$k>(v(a), v(b))).to_vec();
            let u = bytes(vqshrn2_n_u16::<$k>(v(a), v(b))).to_vec();
            assert_eq!(s, want_sqshrun(&a, &b, $k), "sqshrun {}", $k);
            assert_eq!(u, want_uqshrn(&a, &b, $k), "uqshrn {}", $k);
            assert_eq!(s, plain_sqshrun(&a, &b, $k), "sqshrun {} (plain)", $k);
            assert_eq!(u, plain_uqshrn(&a, &b, $k), "uqshrn {} (plain)", $k);
        }
        // Every 16-bit value in every lane position, with a different one
        // in the other vector: all the saturation edges.
        for x in 0..=0xffffu16 {
            let y = x.wrapping_mul(0x9e37).wrapping_add(0x79b9);
            let (mut a, mut b) = ([0u8; 16], [0u8; 16]);
            for i in 0..8 {
                a[2 * i..2 * i + 2].copy_from_slice(&x.wrapping_add(i as u16).to_le_bytes());
                b[2 * i..2 * i + 2].copy_from_slice(&y.wrapping_sub(i as u16).to_le_bytes());
            }
            assert_eq!(bytes(vqshrun2_n_s16::<$k>(v(a), v(b))).to_vec(), want_sqshrun(&a, &b, $k), "sqshrun {} {x:#x}", $k);
            assert_eq!(bytes(vqshrn2_n_u16::<$k>(v(a), v(b))).to_vec(), want_uqshrn(&a, &b, $k), "uqshrn {} {x:#x}", $k);
            assert_eq!(want_sqshrun(&a, &b, $k), plain_sqshrun(&a, &b, $k));
            assert_eq!(want_uqshrn(&a, &b, $k), plain_uqshrn(&a, &b, $k));
        }
    )*};
}

/// `urhadd`, `sub` and the widening shifts on every pair of bytes, and
/// `uqsub` on 16-bit lanes around the point where it saturates.
#[test]
fn byte_pairs_and_u16_edges() {
    for x in 0..=255u8 {
        let a = [x; 16];
        let b: [u8; 16] = core::array::from_fn(|i| (i as u8).wrapping_mul(16));
        for o in 0..16u8 {
            let b = b.map(|y| y.wrapping_add(o));
            assert_eq!(bytes(vrhaddq_u8(v(a), v(b))).to_vec(), ref_avg_u8(&a, &b), "urhadd {x}");
            assert_eq!(bytes(vsubq_u8(v(a), v(b))).to_vec(), ref_sub8(&a, &b), "sub {x}");
            for i in 0..16 {
                assert_eq!(bytes(vrhaddq_u8(v(a), v(b)))[i], ((a[i] as u16 + b[i] as u16 + 1) >> 1) as u8);
                assert_eq!(bytes(vsubq_u8(v(a), v(b)))[i], a[i].wrapping_sub(b[i]));
            }
        }
    }
    let edge = [0u16, 1, 2, 0x7ffe, 0x7fff, 0x8000, 0x8001, 0xfffe, 0xffff, 17685, 17684, 17686];
    for &x in &edge {
        for &y in &edge {
            let (mut a, mut b) = ([0u8; 16], [0u8; 16]);
            for i in 0..8 {
                a[2 * i..2 * i + 2].copy_from_slice(&x.wrapping_add(i as u16 % 2).to_le_bytes());
                b[2 * i..2 * i + 2].copy_from_slice(&y.to_le_bytes());
            }
            let got = u16s(&bytes(vqsubq_u16(v(a), v(b))));
            assert_eq!(got, ref_subs_u16(&u16s(&a), &u16s(&b)), "uqsub {x:#x} {y:#x}");
            for i in 0..8 {
                assert_eq!(got[i], u16s(&a)[i].saturating_sub(u16s(&b)[i]));
            }
        }
    }
}

/// `sqdmulh` on the pairs that saturate or sit next to saturation, and
/// `dup` on every 16-bit value.
#[test]
fn s16_edges() {
    let edge = [0x8000u16, 0x8001, 0x7fff, 0xffff, 0, 1, 0x4000, 0xc000];
    for &x in &edge {
        for &y in &edge {
            let (mut a, mut b) = ([0u8; 16], [0u8; 16]);
            for i in 0..8 {
                a[2 * i..2 * i + 2].copy_from_slice(&x.to_le_bytes());
                b[2 * i..2 * i + 2].copy_from_slice(&y.to_le_bytes());
            }
            assert_eq!(u16s(&bytes(vqdmulhq_s16(v(a), v(b)))), ref_qdmulh_s16(&u16s(&a), &u16s(&b)), "sqdmulh {x:#x} {y:#x}");
        }
    }
    for x in 0..=0xffffu16 {
        assert_eq!(u16s(&bytes(vdupq_n_s16(x as i16))), vec![x; 8], "dup {x:#x}");
    }
}

#[test]
fn immediates() {
    let mut r = Rng(0x5eed_0002_0bad_cafe);
    ext!(r, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
    shr!(r, 1, 2, 3, 4, 5, 6, 7, 8);
    sshr16!(r, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
    shll!(r, 0, 1, 2, 3, 4, 5, 6, 7, 8);
    narrow!(r, 1, 2, 3, 4, 5, 6, 7, 8);
    sshr8!(r, 1, 2, 3, 4, 5, 6, 7, 8);
    narrow_s!(r, 1, 2, 3, 4, 5, 6, 7, 8);
}

#[test]
fn reductions_loads_and_stores() {
    let mut r = Rng(0x5eed_0003_feed_f00d);
    for _ in 0..iters() {
        let a = r.b16();
        let va = v(a);
        assert_eq!(vmaxvq_u8(va), ref_max8(&a), "umaxv.16b");
        assert_eq!(vmaxvq_u16(va), ref_max16(&u16s(&a)), "umaxv.8h");
        assert_eq!(vgetq_lane_u64_0(va), u64::from_le_bytes(a[..8].try_into().unwrap()), "mov d[0]");
        assert_eq!(vgetq_lane_u64_1(va), u64::from_le_bytes(a[8..].try_into().unwrap()), "mov d[1]");
        let n = vshrn4_u64(va);
        for k in 0..16u64 {
            let want = if k % 2 == 0 { a[k as usize] >> 4 } else { a[k as usize] & 15 } as u64;
            assert_eq!((n >> (4 * k)) & 15, want, "shrn #4 nibble {k}");
        }
        let x = r.byte();
        assert_eq!(bytes(vdupq_n_u8(x)), [x; 16], "dup");

        // Unaligned loads and stores at every offset.
        let buf: Vec<u8> = (0..48).map(|_| r.byte()).collect();
        let o = (r.next() % 32) as usize;
        assert_eq!(bytes(vld1q_u8_at(&buf, o)).as_slice(), &buf[o..o + 16], "ld1 u8");
        let mut out = buf.clone();
        vst1q_u8_at(&mut out, o, va);
        assert_eq!(&out[o..o + 16], &a, "st1 u8");
        assert_eq!(&out[..o], &buf[..o]);
        assert_eq!(&out[o + 16..], &buf[o + 16..]);

        // 8-byte loads (the high half zero) and stores (only 8 bytes
        // written) at every offset, to the last 8 bytes of the buffer.
        let o = (r.next() % 41) as usize;
        let l = bytes(vld1q_u8_low_at(&buf, o));
        assert_eq!(&l[..8], &buf[o..o + 8], "ldr d");
        assert_eq!(&l[8..], &[0u8; 8], "ldr d (high half)");
        let l = bytes(vld1q_u8_low_at(&buf[..o + 8], o));
        assert_eq!(&l[..8], &buf[o..o + 8], "ldr d at the end");
        let mut out = buf.clone();
        vst1q_u8_low_at(&mut out, o, va);
        assert_eq!(&out[o..o + 8], &a[..8], "str d");
        assert_eq!(&out[..o], &buf[..o]);
        assert_eq!(&out[o + 8..], &buf[o + 8..]);
        let mut out = buf[..o + 8].to_vec();
        vst1q_u8_low_at(&mut out, o, va);
        assert_eq!(&out[o..], &a[..8], "str d at the end");
        assert_eq!(&out[..o], &buf[..o]);

        // A vector from two 64-bit halves.
        let (lo, hi) = (r.next(), r.next() ^ u64::from_le_bytes(a[..8].try_into().unwrap()));
        assert_eq!(u64s(&bytes(vcombine_u64(lo, hi))), [lo, hi], "fmov d, mov d[1]");

        // 4-byte lane stores (only 4 bytes written) at every offset, to
        // the last 4 bytes of the buffer.
        let o = (r.next() % 45) as usize;
        let lane = |n: usize, out: &mut [u8]| match n {
            0 => vst1q_lane_u32_at::<0>(out, o, va),
            1 => vst1q_lane_u32_at::<1>(out, o, va),
            2 => vst1q_lane_u32_at::<2>(out, o, va),
            _ => vst1q_lane_u32_at::<3>(out, o, va),
        };
        for n in 0..4 {
            let mut out = buf.clone();
            lane(n, &mut out);
            assert_eq!(&out[o..o + 4], &a[4 * n..4 * n + 4], "st1 s[{n}]");
            assert_eq!(&out[..o], &buf[..o]);
            assert_eq!(&out[o + 4..], &buf[o + 4..]);
            let mut out = buf[..o + 4].to_vec();
            lane(n, &mut out);
            assert_eq!(&out[o..], &a[4 * n..4 * n + 4], "st1 s[{n}] at the end");
            assert_eq!(&out[..o], &buf[..o]);
        }

        let w: Vec<u16> = (0..24).map(|_| r.next() as u16).collect();
        let o = (r.next() % 16) as usize;
        assert_eq!(u16s(&bytes(vld1q_u16_at(&w, o))), &w[o..o + 8], "ld1 u16");
        let mut ow = w.clone();
        vst1q_u16_at(&mut ow, o, va);
        assert_eq!(&ow[o..o + 8], u16s(&a).as_slice(), "st1 u16");
        assert_eq!(&ow[..o], &w[..o]);
        assert_eq!(&ow[o + 8..], &w[o + 8..]);

        let w: Vec<i16> = (0..24).map(|_| r.next() as i16).collect();
        let o = (r.next() % 16) as usize;
        let wu: Vec<u16> = w.iter().map(|&x| x as u16).collect();
        assert_eq!(u16s(&bytes(vld1q_s16_at(&w, o))), &wu[o..o + 8], "ld1 s16");
        let mut ow = w.clone();
        vst1q_s16_at(&mut ow, o, va);
        let au: Vec<i16> = u16s(&a).iter().map(|&x| x as i16).collect();
        assert_eq!(&ow[o..o + 8], au.as_slice(), "st1 s16");
        assert_eq!(&ow[..o], &w[..o]);
        assert_eq!(&ow[o + 8..], &w[o + 8..]);

        let w: Vec<u32> = (0..12).map(|_| r.next() as u32).collect();
        let o = (r.next() % 8) as usize;
        assert_eq!(u32s(&bytes(vld1q_u32_at(&w, o))), &w[o..o + 4], "ld1 u32");
        let mut ow = w.clone();
        vst1q_u32_at(&mut ow, o, va);
        assert_eq!(&ow[o..o + 4], u32s(&a).as_slice(), "st1 u32");
        assert_eq!(&ow[..o], &w[..o]);
        assert_eq!(&ow[o + 4..], &w[o + 4..]);
        let x = r.next() as u32;
        assert_eq!(u32s(&bytes(vdupq_n_u32(x))), [x; 4], "dup .4s");
        assert_eq!(u32s(&bytes(vdupq_laneq_u32_3(va))), [u32s(&a)[3]; 4], "dup .4s[3]");
    }
}

#[test]
fn detection() {
    assert_eq!(has_neon(), cfg!(any(target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128"))));
}

#[test]
fn movemask64_packs_mask_bits() {
    let mut r = Rng(0x5eed_0004_1234_5678);
    for _ in 0..iters() / 4 {
        let m: [u8; 64] = core::array::from_fn(|_| if r.next() & 1 == 1 { 0xff } else { 0 });
        let vs: Vec<_> = (0..4).map(|i| v(m[16 * i..16 * i + 16].try_into().unwrap())).collect();
        let want = (0..64).fold(0u64, |acc, k| acc | (((m[k] == 0xff) as u64) << k));
        assert_eq!(verilith_simd::neon_mask::movemask64(vs[0], vs[1], vs[2], vs[3]), want);
    }
}

#[test]
fn movemask16_packs_mask_bits() {
    let mut r = Rng(0x5eed_0005_8765_4321);
    for _ in 0..iters() / 4 {
        let m: [u8; 16] = core::array::from_fn(|_| if r.next() & 1 == 1 { 0xff } else { 0 });
        let want = (0..16).fold(0u32, |acc, k| acc | (((m[k] == 0xff) as u32) << k));
        assert_eq!(verilith_simd::neon_mask::movemask16(v(m)), want);
    }
}

macro_rules! rshr32 {
    ($r:ident, $($k:literal),*) => {$(
        for _ in 0..iters() / 8 {
            let a = $r.b16();
            assert_eq!(u32s(&bytes(vrshrq_n_s32::<$k>(v(a)))), ref_rshr_s32(&u32s(&a), $k), "srshr {}", $k);
        }
    )*};
}

macro_rules! shl32 {
    ($r:ident, $($k:literal),*) => {$(
        for _ in 0..iters() / 8 {
            let a = $r.b16();
            assert_eq!(u32s(&bytes(vshlq_n_u32::<$k>(v(a)))), ref_slli32(&u32s(&a), $k), "shl.4s {}", $k);
        }
    )*};
}

/// The integer-transform wrappers: `abs`, `umax`, `smull`/`smull2`, 32-bit
/// add and subtract, `srshr`, `shl` and `uzp2`.
#[test]
fn transform_ops() {
    let mut r = Rng(0x5eed_0009_1dc7_0001);
    for _ in 0..iters() {
        let (a, b) = (r.b16(), r.b16());
        let (va, vb) = (v(a), v(b));
        let (a16, b16) = (u16s(&a), u16s(&b));
        let (a32, b32) = (u32s(&a), u32s(&b));
        assert_eq!(u16s(&bytes(vabsq_s16(va))), ref_abs16(&a16), "abs.8h");
        assert_eq!(u16s(&bytes(vmaxq_u16(va, vb))), ref_max_u16(&a16, &b16), "umax.8h");
        assert_eq!(u32s(&bytes(vmull_lo_s16(va, vb))), ref_mull_lo_s16(&a16, &b16), "smull");
        assert_eq!(u32s(&bytes(vmull_hi_s16(va, vb))), ref_mull_hi_s16(&a16, &b16), "smull2");
        assert_eq!(u32s(&bytes(vaddq_u32(va, vb))), ref_add32(&a32, &b32), "add.4s");
        assert_eq!(u32s(&bytes(vsubq_u32(va, vb))), ref_sub32(&a32, &b32), "sub.4s");
        assert_eq!(u16s(&bytes(vuzp2q_u16(va, vb))), ref_uzp2_16(&a16, &b16), "uzp2.8h");
    }
    // The 16-bit edges, in every lane pairing.
    let e: [u16; 8] = [0, 1, 0x7fff, 0x8000, 0x8001, 0xffff, 0x00ff, 0xff00];
    for s in 0..8 {
        let a: [u8; 16] = core::array::from_fn(|i| e[i / 2].to_le_bytes()[i % 2]);
        let b: [u8; 16] = core::array::from_fn(|i| e[(i / 2 + s) % 8].to_le_bytes()[i % 2]);
        let (a16, b16) = (u16s(&a), u16s(&b));
        assert_eq!(u16s(&bytes(vabsq_s16(v(a)))), ref_abs16(&a16), "abs.8h edges");
        assert_eq!(u32s(&bytes(vmull_lo_s16(v(a), v(b)))), ref_mull_lo_s16(&a16, &b16), "smull edges");
        assert_eq!(u32s(&bytes(vmull_hi_s16(v(a), v(b)))), ref_mull_hi_s16(&a16, &b16), "smull2 edges");
    }
    rshr32!(r, 1, 2, 7, 11, 16, 18, 30, 31);
    shl32!(r, 0, 1, 4, 13, 31);
    // The 32-bit edges for the rounding shift.
    let e32: [u32; 8] = [0, 1, 0x7fff_ffff, 0x8000_0000, 0x8000_0001, 0xffff_ffff, 0x3ff, 0x400];
    for h in 0..2 {
        let a: [u8; 16] = core::array::from_fn(|i| e32[4 * h + i / 4].to_le_bytes()[i % 4]);
        assert_eq!(u32s(&bytes(vrshrq_n_s32::<1>(v(a)))), ref_rshr_s32(&u32s(&a), 1), "srshr 1 edges");
        assert_eq!(u32s(&bytes(vrshrq_n_s32::<11>(v(a)))), ref_rshr_s32(&u32s(&a), 11), "srshr 11 edges");
        assert_eq!(u32s(&bytes(vrshrq_n_s32::<31>(v(a)))), ref_rshr_s32(&u32s(&a), 31), "srshr 31 edges");
    }
}

/// `st3`: the interleaved store writes its 48 bytes and no others.
#[test]
fn interleaved_store() {
    let mut r = Rng(0x5eed_000a_57e3_0001);
    for n in 0..iters() / 4 {
        let (a, b, c) = (r.b16(), r.b16(), r.b16());
        let off = n % 9;
        let mut buf = [0xa5u8; 64];
        vst3q_u8_at(&mut buf, off, v(a), v(b), v(c));
        assert_eq!(buf[off..off + 48].to_vec(), ref_interleave3(&a, &b, &c), "st3");
        assert!(buf[..off].iter().chain(&buf[off + 48..]).all(|&x| x == 0xa5), "st3 wrote outside its 48 bytes");
    }
}

macro_rules! lane16 {
    ($r:ident, $($l:literal),*) => {$(
        for _ in 0..iters() / 8 {
            let (a, c, acc) = ($r.b16(), $r.b16(), $r.b16());
            let (a16, c16, acc32) = (u16s(&a), u16s(&c), u32s(&acc));
            assert_eq!(u32s(&bytes(vmull_lo_laneq_s16::<$l>(v(a), v(c)))), ref_mull_lo_lane_s16(&a16, &c16, $l), "smull lane {}", $l);
            assert_eq!(u32s(&bytes(vmull_hi_laneq_s16::<$l>(v(a), v(c)))), ref_mull_hi_lane_s16(&a16, &c16, $l), "smull2 lane {}", $l);
            assert_eq!(
                u32s(&bytes(vmlal_lo_laneq_s16::<$l>(v(acc), v(a), v(c)))),
                ref_mlal_lo_lane_s16(&acc32, &a16, &c16, $l),
                "smlal lane {}", $l
            );
            assert_eq!(
                u32s(&bytes(vmlal_hi_laneq_s16::<$l>(v(acc), v(a), v(c)))),
                ref_mlal_hi_lane_s16(&acc32, &a16, &c16, $l),
                "smlal2 lane {}", $l
            );
        }
    )*};
}

fn want_rshrn(a: &[u8; 16], b: &[u8; 16], n: u32) -> Vec<u16> {
    let mut w = ref_rshrn_s32(&u32s(a), n);
    w.extend(ref_rshrn_s32(&u32s(b), n));
    w
}

macro_rules! rshrn32 {
    ($r:ident, $e:ident, $($k:literal),*) => {$(
        for _ in 0..iters() / 8 {
            let (a, b) = ($r.b16(), $r.b16());
            assert_eq!(u16s(&bytes(vrshrn2_n_s32::<$k>(v(a), v(b)))), want_rshrn(&a, &b, $k), "rshrn {}", $k);
            assert_eq!(u16s(&bytes(vrshrn_lo_n_s32::<$k>(v(a)))), want_rshrn(&a, &[0; 16], $k), "rshrn low {}", $k);
        }
        for h in 0..2 {
            let a: [u8; 16] = core::array::from_fn(|i| $e[4 * h + i / 4].to_le_bytes()[i % 4]);
            let b: [u8; 16] = core::array::from_fn(|i| $e[4 * (1 - h) + i / 4].to_le_bytes()[i % 4]);
            assert_eq!(u16s(&bytes(vrshrn2_n_s32::<$k>(v(a), v(b)))), want_rshrn(&a, &b, $k), "rshrn {} edges", $k);
            assert_eq!(u16s(&bytes(vrshrn_lo_n_s32::<$k>(v(a)))), want_rshrn(&a, &[0; 16], $k), "rshrn low {} edges", $k);
        }
    )*};
}

/// The wrappers for the 16-bit inverse DCT: `smull`/`smull2` and
/// `smlal`/`smlal2` by element, `rshrn`/`rshrn2`, `uqadd` and `uaddlv`.
#[test]
fn idct16_ops() {
    let mut r = Rng(0x5eed_000a_1dc7_0016);
    lane16!(r, 0, 1, 2, 3, 4, 5, 6, 7);
    // The 16-bit edges, in every lane pairing, against every 32-bit edge.
    let e: [u16; 8] = [0, 1, 0x7fff, 0x8000, 0x8001, 0xffff, 0x00ff, 0xff00];
    let e32: [u32; 8] = [0, 1, 0x7fff_ffff, 0x8000_0000, 0x8000_0001, 0xffff_ffff, 0x3fff_ffff, 0xc000_0000];
    for s in 0..8 {
        for t in 0..8 {
            let a: [u8; 16] = core::array::from_fn(|i| e[i / 2].to_le_bytes()[i % 2]);
            let c: [u8; 16] = core::array::from_fn(|i| e[(i / 2 + s) % 8].to_le_bytes()[i % 2]);
            let acc: [u8; 16] = core::array::from_fn(|i| e32[(i / 4 + t) % 8].to_le_bytes()[i % 4]);
            let (a16, c16, acc32) = (u16s(&a), u16s(&c), u32s(&acc));
            assert_eq!(u32s(&bytes(vmull_lo_laneq_s16::<0>(v(a), v(c)))), ref_mull_lo_lane_s16(&a16, &c16, 0), "smull lane edges");
            assert_eq!(u32s(&bytes(vmull_hi_laneq_s16::<3>(v(a), v(c)))), ref_mull_hi_lane_s16(&a16, &c16, 3), "smull2 lane edges");
            assert_eq!(
                u32s(&bytes(vmlal_lo_laneq_s16::<5>(v(acc), v(a), v(c)))),
                ref_mlal_lo_lane_s16(&acc32, &a16, &c16, 5),
                "smlal lane edges"
            );
            assert_eq!(
                u32s(&bytes(vmlal_hi_laneq_s16::<7>(v(acc), v(a), v(c)))),
                ref_mlal_hi_lane_s16(&acc32, &a16, &c16, 7),
                "smlal2 lane edges"
            );
        }
    }
    let r32: [u32; 8] = [0, 1, 0x7fff_ffff, 0x8000_0000, 0x8000_0001, 0xffff_ffff, 0x3ff, 0x400];
    rshrn32!(r, r32, 1, 2, 7, 11, 15, 16);
    for _ in 0..iters() {
        let (a, b) = (r.b16(), r.b16());
        let (a16, b16) = (u16s(&a), u16s(&b));
        assert_eq!(u16s(&bytes(vqaddq_u16(v(a), v(b)))), ref_adds_u16(&a16, &b16), "uqadd.8h");
        assert_eq!(vaddlvq_u16(v(a)) as u64, ref_sum_u16(&a16), "uaddlv.8h");
    }
    let ones = [0xffu8; 16];
    assert_eq!(vaddlvq_u16(v(ones)) as u64, ref_sum_u16(&u16s(&ones)), "uaddlv.8h all ones");
    assert_eq!(u16s(&bytes(vqaddq_u16(v(ones), v(ones)))), ref_adds_u16(&u16s(&ones), &u16s(&ones)), "uqadd.8h all ones");
}

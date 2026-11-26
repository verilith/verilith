//! The instruction specifications of `isa` against the CPU: each SHA
//! instruction wrapper (and the few other instructions the kernels specify
//! themselves) on random operands, against `isa_ref`, the verified
//! implementations of those specifications. On x86-64 this needs a CPU with
//! SHA-NI; the AArch64 ones run natively on AArch64 (or under qemu, as
//! `ci.sh` does). Elsewhere the AArch64 wrappers are `isa_ref` themselves,
//! so their tests only check that the emulated kernels agree with the
//! portable ones.
use verilith_sha2::{armv8, compress, compress512, isa_ref};

/// xorshift64*: reproducible operands.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    /// Mostly uniform words, with some all-zero, all-one and one-bit words,
    /// where carries and rotations are easiest to get wrong.
    fn word(&mut self) -> u64 {
        match self.next() % 8 {
            0 => 0,
            1 => u64::MAX,
            2 => 1 << (self.next() % 64),
            _ => self.next(),
        }
    }
    fn u32x4(&mut self) -> [u32; 4] {
        [self.word() as u32, self.word() as u32, self.word() as u32, self.word() as u32]
    }
    fn u64x2(&mut self) -> [u64; 2] {
        [self.word(), self.word()]
    }
    fn u8x16(&mut self) -> [u8; 16] {
        let mut b = [0u8; 16];
        for x in &mut b {
            *x = self.next() as u8;
        }
        b
    }
}

const N: usize = 200_000;

#[cfg(target_arch = "x86_64")]
mod x86 {
    use super::*;
    use core::arch::x86_64::__m128i;
    use verilith_sha2::shani;

    fn v(a: [u32; 4]) -> __m128i {
        unsafe { core::mem::transmute(a) }
    }
    fn a(v: __m128i) -> [u32; 4] {
        unsafe { core::mem::transmute(v) }
    }

    #[test]
    fn sha_ni_matches_spec() {
        if !shani::has_shani() {
            eprintln!("no SHA-NI: skipped");
            return;
        }
        let mut r = Rng(0x5a17_0001);
        for _ in 0..N {
            let (x, y, k) = (r.u32x4(), r.u32x4(), r.u32x4());
            assert_eq!(a(shani::sha256rnds2(v(x), v(y), v(k))), isa_ref::sha256rnds2(x, y, k), "sha256rnds2 {x:x?} {y:x?} {k:x?}");
            assert_eq!(a(shani::sha256msg1(v(x), v(y))), isa_ref::sha256msg1(x, y), "sha256msg1 {x:x?} {y:x?}");
            assert_eq!(a(shani::sha256msg2(v(x), v(y))), isa_ref::sha256msg2(x, y), "sha256msg2 {x:x?} {y:x?}");
        }
    }

    #[test]
    fn pblendw_matches_spec() {
        if !shani::has_shani() {
            eprintln!("no SSE4.1: skipped");
            return;
        }
        let mut r = Rng(0x5a17_0002);
        macro_rules! check {
            ($($imm:literal)*) => {$(
                for _ in 0..1000 {
                    let (x, y) = (r.u8x16(), r.u8x16());
                    let got: [u8; 16] = unsafe {
                        core::mem::transmute(shani::blend_epi16::<$imm>(core::mem::transmute(x), core::mem::transmute(y)))
                    };
                    assert_eq!(got, isa_ref::blend16(x, y, $imm), "pblendw {:#x}", $imm);
                }
            )*};
        }
        check!(0x00 0xf0 0x0f 0xff 0xaa 0x55 0x3c 0x81);
    }
}

#[cfg(target_arch = "aarch64")]
type V = core::arch::aarch64::uint8x16_t;
#[cfg(not(target_arch = "aarch64"))]
type V = verilith_simd::neon::uint8x16_t;

fn v8(b: [u8; 16]) -> V {
    unsafe { core::mem::transmute(b) }
}
fn v32(a: [u32; 4]) -> V {
    unsafe { core::mem::transmute(a) }
}
fn v64(a: [u64; 2]) -> V {
    unsafe { core::mem::transmute(a) }
}
fn a8(v: V) -> [u8; 16] {
    unsafe { core::mem::transmute(v) }
}
fn a32(v: V) -> [u32; 4] {
    unsafe { core::mem::transmute(v) }
}
fn a64(v: V) -> [u64; 2] {
    unsafe { core::mem::transmute(v) }
}

#[test]
fn armv8_sha2_matches_spec() {
    if cfg!(target_arch = "aarch64") && !armv8::has_sha2() {
        eprintln!("no SHA2 extension: skipped");
        return;
    }
    let mut r = Rng(0x5a17_0003);
    for _ in 0..N {
        let (x, y, k) = (r.u32x4(), r.u32x4(), r.u32x4());
        assert_eq!(a32(armv8::vsha256hq(v32(x), v32(y), v32(k))), isa_ref::sha256h(x, y, k), "sha256h {x:x?} {y:x?} {k:x?}");
        assert_eq!(a32(armv8::vsha256h2q(v32(x), v32(y), v32(k))), isa_ref::sha256h2(x, y, k), "sha256h2 {x:x?} {y:x?} {k:x?}");
        assert_eq!(a32(armv8::vsha256su0q(v32(x), v32(y))), isa_ref::sha256su0(x, y), "sha256su0 {x:x?} {y:x?}");
        assert_eq!(a32(armv8::vsha256su1q(v32(x), v32(y), v32(k))), isa_ref::sha256su1(x, y, k), "sha256su1 {x:x?} {y:x?} {k:x?}");
    }
}

#[test]
fn armv8_sha512_matches_spec() {
    if cfg!(target_arch = "aarch64") && !armv8::has_sha512() {
        eprintln!("no SHA-512 instructions: skipped");
        return;
    }
    let mut r = Rng(0x5a17_0004);
    for _ in 0..N {
        let (x, y, z) = (r.u64x2(), r.u64x2(), r.u64x2());
        assert_eq!(a64(armv8::vsha512hq(v64(x), v64(y), v64(z))), isa_ref::sha512h(x, y, z), "sha512h {x:x?} {y:x?} {z:x?}");
        assert_eq!(a64(armv8::vsha512h2q(v64(x), v64(y), v64(z))), isa_ref::sha512h2(x, y, z), "sha512h2 {x:x?} {y:x?} {z:x?}");
        assert_eq!(a64(armv8::vsha512su0q(v64(x), v64(y))), isa_ref::sha512su0(x, y), "sha512su0 {x:x?} {y:x?}");
        assert_eq!(a64(armv8::vsha512su1q(v64(x), v64(y), v64(z))), isa_ref::sha512su1(x, y, z), "sha512su1 {x:x?} {y:x?} {z:x?}");
    }
}

#[test]
fn armv8_neon_matches_spec() {
    let mut r = Rng(0x5a17_0005);
    for _ in 0..10_000 {
        let (b, x, y) = (r.u8x16(), r.u64x2(), r.u64x2());
        assert_eq!(a8(armv8::vrev32q_u8(v8(b))), isa_ref::rev32(b));
        assert_eq!(a8(armv8::vrev64q_u8(v8(b))), isa_ref::rev64(b));
        assert_eq!(a64(armv8::vaddq_u64(v64(x), v64(y))), isa_ref::add64x2(x, y));
        let s = [x[0], x[1], y[0], y[1]];
        assert_eq!(a64(armv8::vld1q_u64_at(&s, 1)), [x[1], y[0]]);
        let mut t = [0u64; 4];
        armv8::vst1q_u64_at(&mut t, 2, v64(x));
        assert_eq!(t, [0, 0, x[0], x[1]]);
    }
}

/// The AArch64 kernels, called directly (on other targets, over the
/// verified emulation of the instructions), against the portable ones.
#[test]
fn armv8_kernels_match_portable() {
    if cfg!(target_arch = "aarch64") && !(armv8::has_sha2() && armv8::has_sha512()) {
        eprintln!("no SHA2 or SHA-512 instructions: skipped");
        return;
    }
    let mut r = Rng(0x5a17_0006);
    for blocks in 0..12 {
        for _ in 0..4 {
            let p: Vec<u8> = (0..128 * blocks + (r.next() % 128) as usize).map(|_| r.next() as u8).collect();
            let st: [u32; 8] = core::array::from_fn(|_| r.next() as u32);
            let (mut a, mut b) = (st, st);
            armv8::compress_blocks(&mut a, &p);
            compress::compress_blocks(&mut b, &p);
            assert_eq!(a, b, "SHA-256, {} bytes", p.len());
            let st: [u64; 8] = core::array::from_fn(|_| r.next());
            let (mut a, mut b) = (st, st);
            armv8::compress512_blocks(&mut a, &p);
            compress512::compress_blocks(&mut b, &p);
            assert_eq!(a, b, "SHA-512, {} bytes", p.len());
        }
    }
}

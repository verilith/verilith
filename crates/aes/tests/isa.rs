//! The instruction wrappers against the CPU: each wrapper of `x86` (on
//! x86-64) or `neon` (on AArch64, natively or under qemu) on random
//! operands, against `isa_ref`, the verified implementations of the
//! specifications in their `ensures`. A wrapper whose intrinsic does not
//! compute what Verus is told it does fails here.
#![allow(unused_imports, dead_code)]
use verilith_aes::isa_ref::*;

/// xorshift64*: reproducible operands.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    /// Mostly uniform, with some all-zero, all-one and one-bit values.
    fn word(&mut self) -> u64 {
        match self.next() % 8 {
            0 => 0,
            1 => u64::MAX,
            2 => 1 << (self.next() % 64),
            _ => self.next(),
        }
    }
    fn u128(&mut self) -> u128 {
        (self.word() as u128) << 64 | self.word() as u128
    }
    /// A shuffle mask: indices, some with bit 7 set, some with other
    /// high bits set (which PSHUFB ignores).
    fn mask(&mut self) -> u128 {
        let mut m = 0u128;
        for k in 0..16 {
            let b = match self.next() % 4 {
                0 => 0x80 | (self.next() as u8 & 0x7f),
                1 => self.next() as u8 & 0x7f,
                _ => self.next() as u8 & 15,
            };
            m |= (b as u128) << (8 * k);
        }
        m
    }
}

const N: usize = 20_000;

fn le(b: [u8; 16]) -> u128 {
    u128::from_le_bytes(b)
}

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
mod x86 {
    use super::*;
    use verilith_aes::x86::*;

    fn ni() -> bool {
        std::is_x86_feature_detected!("aes")
            && std::is_x86_feature_detected!("pclmulqdq")
            && std::is_x86_feature_detected!("ssse3")
            && std::is_x86_feature_detected!("sse4.1")
    }

    #[test]
    fn x128() {
        if !ni() {
            eprintln!("skipped: no AES-NI");
            return;
        }
        let mut rng = Rng(1);
        for _ in 0..N {
            let (a, b, m) = (rng.u128(), rng.u128(), rng.mask());
            let (xa, xb, xm) = (x_set(a), x_set(b), x_set(m));
            assert_eq!(x_get(xa), a);
            assert_eq!(x_get(x_xor(xa, xb)), a ^ b);
            assert_eq!(le(bytes_of(x_get(x_aesenc(xa, xb)))), le(aesenc_ref(bytes_of(a), bytes_of(b))));
            assert_eq!(le(bytes_of(x_get(x_aesenclast(xa, xb)))), le(aesenclast_ref(bytes_of(a), bytes_of(b))));
            assert_eq!(x_get(x_clmul::<0x00>(xa, xb)), pclmul_ref(a, b, 0x00));
            assert_eq!(x_get(x_clmul::<0x01>(xa, xb)), pclmul_ref(a, b, 0x01));
            assert_eq!(x_get(x_clmul::<0x10>(xa, xb)), pclmul_ref(a, b, 0x10));
            assert_eq!(x_get(x_clmul::<0x11>(xa, xb)), pclmul_ref(a, b, 0x11));
            assert_eq!(le(bytes_of(x_get(x_pshufb(xa, xm)))), le(pshufb_ref(bytes_of(a), bytes_of(m))));
            assert_eq!(x_get(x_add32(xa, xb)), add32x4_ref(a, b));
            assert_eq!(x_get(x_sll64::<1>(xa)), sll64x2_ref(a, 1));
            assert_eq!(x_get(x_sll64::<57>(xa)), sll64x2_ref(a, 57));
            assert_eq!(x_get(x_sll64::<62>(xa)), sll64x2_ref(a, 62));
            assert_eq!(x_get(x_sll64::<63>(xa)), sll64x2_ref(a, 63));
            assert_eq!(x_get(x_srl64::<1>(xa)), srl64x2_ref(a, 1));
            assert_eq!(x_get(x_srl64::<2>(xa)), srl64x2_ref(a, 2));
            assert_eq!(x_get(x_srl64::<7>(xa)), srl64x2_ref(a, 7));
            assert_eq!(x_get(x_srl64::<63>(xa)), srl64x2_ref(a, 63));
            assert_eq!(x_get(x_bsll8(xa)), a << 64);
            assert_eq!(x_get(x_bsrl8(xa)), a >> 64);
            // Loads and stores, at an odd offset.
            let mut buf = [0u8; 40];
            buf[3..19].copy_from_slice(&a.to_le_bytes());
            assert_eq!(x_get(x_load(&buf, 3)), a);
            let mut out = [7u8; 40];
            x_store(&mut out, 5, xa);
            assert_eq!(&out[5..21], &a.to_le_bytes());
            assert!(out[..5].iter().chain(&out[21..]).all(|&x| x == 7));
            assert_eq!(x_get(x_load16(&a.to_le_bytes())), a);
            let mut t = [0u8; 16];
            x_store16(&mut t, xa);
            assert_eq!(t, a.to_le_bytes());
            assert_eq!(x_get(x_load_u128(&[b, a, b], 1)), a);
        }
    }

    #[test]
    fn z512() {
        if !(ni()
            && std::is_x86_feature_detected!("avx512f")
            && std::is_x86_feature_detected!("avx512bw")
            && std::is_x86_feature_detected!("avx512vl")
            && std::is_x86_feature_detected!("vaes")
            && std::is_x86_feature_detected!("vpclmulqdq"))
        {
            eprintln!("skipped: no VAES");
            return;
        }
        let mut rng = Rng(2);
        let lanes = |z| {
            let mut o = [0u128; 4];
            let mut b = [0u8; 64];
            z_store(&mut b, 0, z);
            for l in 0..4 {
                o[l] = u128::from_le_bytes(b[16 * l..16 * l + 16].try_into().unwrap());
            }
            o
        };
        for _ in 0..N / 4 {
            let a: [u128; 4] = core::array::from_fn(|_| rng.u128());
            let b: [u128; 4] = core::array::from_fn(|_| rng.u128());
            let c: [u128; 4] = core::array::from_fn(|_| rng.u128());
            let m: [u128; 4] = core::array::from_fn(|_| rng.mask());
            let (za, zb, zc, zm) = (z_load_u128(&a, 0), z_load_u128(&b, 0), z_load_u128(&c, 0), z_load_u128(&m, 0));
            assert_eq!(lanes(za), a);
            let mut bytes = [0u8; 70];
            for l in 0..4 {
                bytes[6 + 16 * l..22 + 16 * l].copy_from_slice(&a[l].to_le_bytes());
            }
            assert_eq!(lanes(z_load(&bytes, 6)), a);
            assert_eq!(lanes(z_bcast(&b, 2)), [b[2]; 4]);
            assert_eq!(lanes(z_bcast_x(x_set(c[1]))), [c[1]; 4]);
            assert_eq!(lanes(z_from_x(x_set(c[3]))), [c[3], 0, 0, 0]);
            assert_eq!(x_get(z_lane::<0>(za)), a[0]);
            assert_eq!(x_get(z_lane::<1>(za)), a[1]);
            assert_eq!(x_get(z_lane::<2>(za)), a[2]);
            assert_eq!(x_get(z_lane::<3>(za)), a[3]);
            let x = lanes(z_xor(za, zb));
            let x3 = lanes(z_xor3(za, zb, zc));
            let e = lanes(z_aesenc(za, zb));
            let el = lanes(z_aesenclast(za, zb));
            let c00 = lanes(z_clmul::<0x00>(za, zb));
            let c01 = lanes(z_clmul::<0x01>(za, zb));
            let c10 = lanes(z_clmul::<0x10>(za, zb));
            let c11 = lanes(z_clmul::<0x11>(za, zb));
            let s = lanes(z_pshufb(za, zm));
            let ad = lanes(z_add32(za, zb));
            for l in 0..4 {
                assert_eq!(x[l], a[l] ^ b[l]);
                assert_eq!(x3[l], a[l] ^ b[l] ^ c[l]);
                assert_eq!(e[l], le(aesenc_ref(bytes_of(a[l]), bytes_of(b[l]))));
                assert_eq!(el[l], le(aesenclast_ref(bytes_of(a[l]), bytes_of(b[l]))));
                assert_eq!(c00[l], pclmul_ref(a[l], b[l], 0x00));
                assert_eq!(c01[l], pclmul_ref(a[l], b[l], 0x01));
                assert_eq!(c10[l], pclmul_ref(a[l], b[l], 0x10));
                assert_eq!(c11[l], pclmul_ref(a[l], b[l], 0x11));
                assert_eq!(s[l], le(pshufb_ref(bytes_of(a[l]), bytes_of(m[l]))));
                assert_eq!(ad[l], add32x4_ref(a[l], b[l]));
            }
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_endian = "little"))]
mod arm {
    use super::*;
    use verilith_aes::neon::*;

    #[test]
    fn n128() {
        if !has_arm_aes() {
            eprintln!("skipped: no FEAT_AES/FEAT_PMULL");
            return;
        }
        let mut rng = Rng(3);
        for _ in 0..N {
            let (a, b, m) = (rng.u128(), rng.u128(), rng.mask());
            let (na, nb, nm) = (n_set(a), n_set(b), n_set(m));
            assert_eq!(n_get(na), a);
            assert_eq!(n_get(n_xor(na, nb)), a ^ b);
            assert_eq!(le(bytes_of(n_get(n_aese(na, nb)))), le(aese_ref(bytes_of(a), bytes_of(b))));
            assert_eq!(le(bytes_of(n_get(n_aesmc(na)))), le(aesmc_ref(bytes_of(a))));
            assert_eq!(n_get(n_clmul::<0x00>(na, nb)), pclmul_ref(a, b, 0x00));
            assert_eq!(n_get(n_clmul::<0x01>(na, nb)), pclmul_ref(a, b, 0x01));
            assert_eq!(n_get(n_clmul::<0x10>(na, nb)), pclmul_ref(a, b, 0x10));
            assert_eq!(n_get(n_clmul::<0x11>(na, nb)), pclmul_ref(a, b, 0x11));
            assert_eq!(le(bytes_of(n_get(n_tbl(na, nm)))), le(pshufb_ref(bytes_of(a), bytes_of(m))));
            assert_eq!(n_get(n_add32(na, nb)), add32x4_ref(a, b));
            assert_eq!(n_get(n_sll64::<1>(na)), sll64x2_ref(a, 1));
            assert_eq!(n_get(n_sll64::<57>(na)), sll64x2_ref(a, 57));
            assert_eq!(n_get(n_sll64::<62>(na)), sll64x2_ref(a, 62));
            assert_eq!(n_get(n_sll64::<63>(na)), sll64x2_ref(a, 63));
            assert_eq!(n_get(n_srl64::<1>(na)), srl64x2_ref(a, 1));
            assert_eq!(n_get(n_srl64::<2>(na)), srl64x2_ref(a, 2));
            assert_eq!(n_get(n_srl64::<7>(na)), srl64x2_ref(a, 7));
            assert_eq!(n_get(n_srl64::<63>(na)), srl64x2_ref(a, 63));
            assert_eq!(n_get(n_bsll8(na)), a << 64);
            assert_eq!(n_get(n_bsrl8(na)), a >> 64);
            let mut buf = [0u8; 40];
            buf[3..19].copy_from_slice(&a.to_le_bytes());
            assert_eq!(n_get(n_load(&buf, 3)), a);
            let mut out = [7u8; 40];
            n_store(&mut out, 5, na);
            assert_eq!(&out[5..21], &a.to_le_bytes());
            assert!(out[..5].iter().chain(&out[21..]).all(|&x| x == 7));
            assert_eq!(n_get(n_load16(&a.to_le_bytes())), a);
            let mut t = [0u8; 16];
            n_store16(&mut t, na);
            assert_eq!(t, a.to_le_bytes());
            assert_eq!(n_get(n_load_u128(&[b, a, b], 1)), a);
        }
    }
}

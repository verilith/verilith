//! The Arm implementation of the kernels, run on any host: off AArch64,
//! `neon`'s wrappers are the verified reference implementations of their
//! specifications, so this checks the Arm round structure and kernels
//! against RustCrypto everywhere CI runs. (On AArch64 it runs the
//! instructions themselves, as `rustcrypto.rs` does.)
#![cfg(target_endian = "little")]
use aes_gcm::aead::{AeadInPlace, KeyInit};
use verilith_aes::arm::Arm;
use verilith_aes::gcm::Gcm;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
}

#[test]
fn arm_gcm() {
    #[cfg(target_arch = "aarch64")]
    if !verilith_aes::neon::has_arm_aes() {
        return;
    }
    let mut rng = Rng(11);
    for klen in [16, 32] {
        for plen in (0..300).chain([1024, 4099]) {
            let key = rng.bytes(klen);
            let iv: [u8; 12] = rng.bytes(12).try_into().unwrap();
            let aad = rng.bytes(plen % 41);
            let pt = rng.bytes(plen);
            let mut want = pt.clone();
            let tag = if klen == 16 {
                aes_gcm::Aes128Gcm::new_from_slice(&key).unwrap().encrypt_in_place_detached((&iv).into(), &aad, &mut want)
            } else {
                aes_gcm::Aes256Gcm::new_from_slice(&key).unwrap().encrypt_in_place_detached((&iv).into(), &aad, &mut want)
            }
            .unwrap();
            let g = Gcm::new::<Arm>(&key);
            let mut buf = pt.clone();
            let mut t = [0u8; 16];
            g.seal::<Arm>(&iv, &aad, &mut buf, &mut t, false);
            assert_eq!(buf, want, "key {klen} text {plen}");
            assert_eq!(&t[..], &tag[..]);
            assert!(g.open::<Arm>(&iv, &aad, &mut buf, &t, false));
            assert_eq!(buf, pt);
            t[0] ^= 1;
            assert!(!g.open::<Arm>(&iv, &aad, &mut want, &t, false));
        }
    }
}

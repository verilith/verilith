//! The CPU kernels against the verified portable one, and the streaming
//! hashers against RustCrypto's sha2, an independent implementation.
use sha2::Digest;
use verilith_sha2::{compress, cpu, sha224, sha256, Sha224, Sha256};

/// xorshift64*: reproducible bytes.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| (self.next() >> 56) as u8).collect()
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

#[test]
fn cpu_kernel_matches_portable() {
    println!("kernel: {}", cpu::kernel());
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    let data = r.bytes(64 * 40 + 63);
    for start in 0..8 {
        let mut st0 = [0u32; 8];
        for w in st0.iter_mut() {
            *w = r.next() as u32;
        }
        // Every block count up to 40, and lengths that are not whole blocks.
        for end in start..data.len() {
            let p = &data[start..end];
            let (mut a, mut b) = (st0, st0);
            cpu::compress_blocks(&mut a, p);
            compress::compress_blocks(&mut b, p);
            assert_eq!(a, b, "start {start} len {}", p.len());
        }
    }
}

#[test]
fn bmi2_build_matches_portable() {
    let Some((k256, k512)) = cpu::bmi2_kernels() else {
        eprintln!("no BMI2: skipped");
        return;
    };
    let mut r = Rng(7);
    let data = r.bytes(128 * 12 + 127);
    let (mut a, mut b) = (verilith_sha2::spec::IV256, verilith_sha2::spec::IV256);
    let (mut c, mut d) = (verilith_sha2::spec512::IV512, verilith_sha2::spec512::IV512);
    for end in 0..data.len() {
        let p = &data[..end];
        k256(&mut a, p);
        compress::compress_blocks(&mut b, p);
        assert_eq!(a, b, "sha-256 len {end}");
        k512(&mut c, p);
        verilith_sha2::compress512::compress_blocks(&mut d, p);
        assert_eq!(c, d, "sha-512 len {end}");
    }
}

#[test]
fn every_length_against_rustcrypto() {
    let mut r = Rng(1);
    let data = r.bytes(4200);
    for n in 0..data.len() {
        let d = &data[..n];
        assert_eq!(sha256(d)[..], sha2::Sha256::digest(d)[..], "sha256 len {n}");
        assert_eq!(sha224(d)[..], sha2::Sha224::digest(d)[..], "sha224 len {n}");
    }
}

#[test]
fn every_split_against_one_shot() {
    // Two updates, split at every point, for every length up to 300: each
    // way the buffer can be part-filled, filled exactly, or skipped.
    let mut r = Rng(2);
    let data = r.bytes(300);
    for n in 0..=data.len() {
        let want = sha256(&data[..n]);
        for k in 0..=n {
            let mut h = Sha256::new();
            h.update(&data[..k]);
            h.update(&data[k..n]);
            assert_eq!(h.finalize(), want, "len {n} split {k}");
        }
    }
}

#[test]
fn random_pieces_against_rustcrypto() {
    let mut r = Rng(3);
    for _ in 0..2000 {
        let n = r.below(3000);
        let data = r.bytes(n);
        let (mut a, mut b) = (Sha256::new(), Sha224::new());
        let (mut x, mut y) = (sha2::Sha256::new(), sha2::Sha224::new());
        let mut i = 0;
        while i < n {
            let k = (i + r.below(200)).min(n);
            a.update(&data[i..k]);
            b.update(&data[i..k]);
            x.update(&data[i..k]);
            y.update(&data[i..k]);
            i = k;
        }
        assert_eq!(a.finalize()[..], x.finalize()[..]);
        assert_eq!(b.finalize()[..], y.finalize()[..]);
    }
}

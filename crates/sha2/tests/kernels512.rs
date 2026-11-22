//! The SHA-512 family: the CPU kernel against the verified portable one,
//! and the streaming hashers against RustCrypto's sha2.
use sha2::Digest;
use verilith_sha2::*;

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
    println!("kernel: {}", cpu::kernel512());
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    let data = r.bytes(128 * 24 + 127);
    for start in 0..4 {
        let mut st0 = [0u64; 8];
        for w in st0.iter_mut() {
            *w = r.next();
        }
        for end in start..data.len() {
            let p = &data[start..end];
            let (mut a, mut b) = (st0, st0);
            cpu::compress512_blocks(&mut a, p);
            compress512::compress_blocks(&mut b, p);
            assert_eq!(a, b, "start {start} len {}", p.len());
        }
    }
}

#[test]
fn every_length_against_rustcrypto() {
    let mut r = Rng(1);
    let data = r.bytes(2200);
    for n in 0..data.len() {
        let d = &data[..n];
        assert_eq!(sha512(d)[..], sha2::Sha512::digest(d)[..], "sha512 len {n}");
        assert_eq!(sha384(d)[..], sha2::Sha384::digest(d)[..], "sha384 len {n}");
        assert_eq!(sha512_224(d)[..], sha2::Sha512_224::digest(d)[..], "sha512/224 len {n}");
        assert_eq!(sha512_256(d)[..], sha2::Sha512_256::digest(d)[..], "sha512/256 len {n}");
    }
}

#[test]
fn every_split_against_one_shot() {
    let mut r = Rng(2);
    let data = r.bytes(400);
    for n in 0..=data.len() {
        let want = sha512(&data[..n]);
        for k in 0..=n {
            let mut h = Sha512::new();
            h.update(&data[..k]);
            h.update(&data[k..n]);
            assert_eq!(h.finalize(), want, "len {n} split {k}");
        }
    }
}

#[test]
fn random_pieces_against_rustcrypto() {
    let mut r = Rng(3);
    for _ in 0..1000 {
        let n = r.below(5000);
        let data = r.bytes(n);
        let (mut a, mut b) = (Sha512::new(), Sha384::new());
        let (mut x, mut y) = (sha2::Sha512::new(), sha2::Sha384::new());
        let mut i = 0;
        while i < n {
            let k = (i + r.below(300)).min(n);
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

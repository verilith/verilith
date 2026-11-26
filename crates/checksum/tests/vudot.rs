//! The trusted `udot` contracts (`vudot`) against a plain
//! reference, and the AArch64 Adler-32 kernel against the portable code,
//! on random inputs. On a CPU without the dot-product extension (and on
//! every non-AArch64 CPU) the wrappers are the plain-Rust stand-ins, so
//! this still checks the verified kernel's arithmetic, and says so.
use verilith_checksum::adlerv::udot::adler32_udot;
use verilith_checksum::adlerv::{DESC64, ONES64};
use verilith_simd::vudot::*;
use verilith_checksum::{adler32_update, cpu};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn byte(&mut self) -> u8 {
        match self.next() % 4 {
            0 => 0,
            1 => 255,
            _ => self.next() as u8,
        }
    }
}

fn note() {
    if !has_dotprod() {
        eprintln!("no dot-product extension: checking the plain-Rust stand-ins");
    }
}

fn dot_ref(acc: &[u32], x: &[u8], w: &[u8]) -> Vec<u32> {
    acc.iter()
        .enumerate()
        .map(|(j, &a)| a.wrapping_add((0..4).map(|k| x[4 * j + k] as u32 * w[4 * j + k] as u32).sum::<u32>()))
        .collect()
}

#[test]
fn wrappers() {
    note();
    let mut r = Rng(0x2545F4914F6CDD1D);
    let mut buf = [0u8; 256];
    for _ in 0..100_000 {
        for b in buf.iter_mut() {
            *b = r.byte();
        }
        // Any weights: `udot` is unsigned on both sides.
        let wv: Vec<u8> = (0..64).map(|_| r.byte()).collect();
        let i = (r.next() % 129) as usize;
        let x = nb_load(&buf, i);
        let w = nb_load(&wv, 0);
        let z = nd_zero();
        assert_eq!(nd_store(&z), [0u32; 16]);
        // Lanes with known values; fifteen doublings of up to 4 * 255^2 wrap.
        let seed: Vec<u8> = (0..64).map(|_| r.byte()).collect();
        let ff = [0xffu8; 64];
        let mut a = nd_dot(&z, &nb_load(&seed, 0), &nb_load(&ff, 0));
        let mut a0 = dot_ref(&[0; 16], &seed, &ff);
        for _ in 0..(r.next() % 16) {
            a = nd_add(&a, &a);
            a0 = a0.iter().map(|v| v.wrapping_add(*v)).collect();
        }
        assert_eq!(nd_store(&a).to_vec(), a0);
        let a1 = nd_add(&a, &a);
        let want: Vec<u32> = a0.iter().map(|v| v.wrapping_add(*v)).collect();
        assert_eq!(nd_store(&a1).to_vec(), want);
        let t = nd_dot(&a, &x, &w);
        assert_eq!(nd_store(&t).to_vec(), dot_ref(&a0, &buf[i..i + 64], &wv));
    }
}

#[test]
fn kernel_agrees() {
    note();
    let mut r = Rng(0xA0761D6478BD642F);
    let rand: Vec<u8> = (0..210_000).map(|_| r.next() as u8).collect();
    let ff = vec![0xffu8; 210_000];
    let mut lens: Vec<usize> = (0..1100).collect();
    lens.extend((0..200).map(|_| (r.next() % 200_000) as usize));
    lens.extend([65536, 65536 + 63, 131072]);
    for &n in &lens {
        for data in [&rand, &ff] {
            let o = (r.next() % 64) as usize;
            let d = &data[o..o + n];
            let (a, b) = ((r.next() % 65521) as u32, (r.next() % 65521) as u32);
            let want = adler32_update(a, b, d);
            assert_eq!(adler32_udot(a, b, d), want, "udot n={n}");
            assert_eq!(cpu::adler32_update(a, b, d), want, "dispatch n={n}");
        }
    }
    // The constants the kernel loads.
    assert!(ONES64.iter().all(|&v| v == 1));
    assert!(DESC64.iter().enumerate().all(|(k, &v)| v as usize == 64 - k));
}

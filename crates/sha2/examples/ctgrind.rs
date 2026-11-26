//! The constant-time check: run under Valgrind's memcheck by `./ci.sh ct`,
//! which fails if memcheck reports anything.
//!
//! The secret inputs (the message, the chaining state, the HMAC key and the
//! tag given to `verify`) are marked undefined with memcheck's client
//! requests, as in Adam Langley's ctgrind. Memcheck tracks undefinedness
//! through every instruction of the compiled code and reports a
//! conditional branch, or a memory address, that depends on an undefined
//! value: exactly a branch or an index that depends on a secret. Lengths
//! are public. Results are marked defined again before they are used.
//!
//! It covers the verified portable kernels (and their BMI2 and AVX2 builds
//! where the CPU Valgrind presents has those), the kernel the dispatch
//! picks, the six hashers over every length up to 300 in several splits,
//! and the six MACs: keys of every length up to 300, and `verify` on
//! right, wrong and wrong-length tags. `--control branch` and `--control
//! index` run code that leaks instead, which the check must report.
#![allow(clippy::needless_range_loop)]
use verilith_sha2::*;

#[cfg(not(target_arch = "x86_64"))]
fn main() {
    eprintln!("ctgrind: the Valgrind client requests here are written for x86-64");
    std::process::exit(2);
}

/// A Valgrind client request (`VALGRIND_DO_CLIENT_REQUEST` on amd64): a
/// no-op returning `default` when not run under Valgrind.
#[cfg(target_arch = "x86_64")]
fn request(default: usize, args: [usize; 6]) -> usize {
    let mut r = default;
    // SAFETY: the magic sequence rotates rdi by 128 bits in all, leaving it
    // as it was, and exchanges rbx with itself; Valgrind recognises it and
    // writes its answer to rdx.
    unsafe {
        core::arch::asm!(
            "rol rdi, 3", "rol rdi, 13", "rol rdi, 61", "rol rdi, 51", "xchg rbx, rbx",
            inout("rdx") r,
            in("rax") args.as_ptr(),
            inout("rdi") 0usize => _,
            options(nostack),
        );
    }
    r
}

#[cfg(target_arch = "x86_64")]
const MC: usize = (b'M' as usize) << 24 | (b'C' as usize) << 16;

/// Marks `s`'s bytes secret (undefined to memcheck).
#[cfg(target_arch = "x86_64")]
fn secret<T: ?Sized>(s: &T) {
    request(0, [MC + 1, s as *const T as *const u8 as usize, core::mem::size_of_val(s), 0, 0, 0]);
}

/// Marks `s`'s bytes public again (defined).
#[cfg(target_arch = "x86_64")]
fn public<T: ?Sized>(s: &T) {
    request(0, [MC + 2, s as *const T as *const u8 as usize, core::mem::size_of_val(s), 0, 0, 0]);
}

#[cfg(target_arch = "x86_64")]
fn bytes(seed: u64, n: usize) -> Vec<u8> {
    let mut x = seed | 1;
    (0..n)
        .map(|_| {
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            (x.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 56) as u8
        })
        .collect()
}

#[cfg(target_arch = "x86_64")]
fn kernels() {
    type K256 = fn(&mut [u32; 8], &[u8]);
    type K512 = fn(&mut [u64; 8], &[u8]);
    let mut k256: Vec<(&str, K256)> = vec![("portable", compress::compress_blocks), ("dispatch", cpu::compress_blocks)];
    let mut k512: Vec<(&str, K512)> = vec![("portable", compress512::compress_blocks), ("dispatch", cpu::compress512_blocks)];
    if let Some((a, b)) = cpu::bmi2_kernels() {
        k256.push(("bmi2", a));
        k512.push(("bmi2", b));
    }
    if let Some((a, b)) = cpu::avx2_kernels() {
        k256.push(("avx2", a));
        k512.push(("avx2", b));
    }
    eprintln!("ctgrind: SHA-256 dispatch picks {}, SHA-512 {}", cpu::kernel(), cpu::kernel512());
    for blocks in [1, 2, 3, 4, 5, 9] {
        let p = bytes(blocks as u64, 128 * blocks);
        for (name, k) in &k256 {
            let mut st = [0x6a09_e667u32; 8];
            secret(&st);
            secret(&p[..]);
            k(&mut st, &p[..64 * blocks]);
            public(&st);
            std::hint::black_box(st);
            eprintln!("ctgrind: SHA-256 {name}, {blocks} blocks");
        }
        for (name, k) in &k512 {
            let mut st = [0x6a09_e667_f3bc_c908u64; 8];
            secret(&st);
            secret(&p[..]);
            k(&mut st, &p);
            public(&st);
            std::hint::black_box(st);
            eprintln!("ctgrind: SHA-512 {name}, {blocks} blocks");
        }
    }
}

#[cfg(target_arch = "x86_64")]
macro_rules! hashers {
    ($($h:ident)*) => {$({
        for n in 0..=300usize {
            let m = bytes(n as u64 + 7, n);
            for cut in [0, n / 3, n / 2, n] {
                secret(&m[..]);
                let mut h = $h::new();
                h.update(&m[..cut]);
                h.update(&m[cut..]);
                let d = h.finalize();
                public(&d);
                std::hint::black_box(d);
            }
        }
        eprintln!(concat!("ctgrind: ", stringify!($h), ", every length to 300"));
    })*};
}

#[cfg(target_arch = "x86_64")]
macro_rules! macs {
    ($($m:ident)*) => {$({
        for n in 0..=300usize {
            let key = bytes(n as u64 + 11, n);
            let msg = bytes(n as u64 + 13, n % 150);
            secret(&key[..]);
            secret(&msg[..]);
            let mut m = $m::new(&key);
            m.update(&msg);
            let mut tag = m.finalize();
            let mut bad = tag;
            bad[n % bad.len()] ^= 1 << (n % 8);
            secret(&tag);
            secret(&bad);
            let ok = m.verify(&tag);
            let no = m.verify(&bad);
            let short = m.verify(&bad[1..]);
            public(&ok);
            public(&no);
            public(&short);
            assert!(ok && !no && !short);
            public(&tag);
            tag[0] ^= 0;
            std::hint::black_box(tag);
        }
        eprintln!(concat!("ctgrind: ", stringify!($m), ", every key length to 300, verify"));
    })*};
}

/// A comparison that returns at the first difference.
#[cfg(target_arch = "x86_64")]
#[inline(never)]
fn early_eq(a: &[u8], b: &[u8]) -> bool {
    for i in 0..a.len() {
        if a[i] != b[i] {
            return false;
        }
    }
    true
}

#[cfg(target_arch = "x86_64")]
fn main() {
    if request(0, [0x1001, 0, 0, 0, 0, 0]) == 0 {
        eprintln!("ctgrind: not running under Valgrind (use ./ci.sh ct)");
        std::process::exit(2);
    }
    // The controls: code that leaks, which memcheck must report, to show
    // that the check sees a leak. `--control branch` compares a tag byte by
    // byte and returns at the first difference; `--control index` looks a
    // table up at a secret index.
    let args: Vec<String> = std::env::args().collect();
    if let Some(i) = args.iter().position(|a| a == "--control") {
        let a = bytes(1, 32);
        let mut b = a.clone();
        b[31] ^= 1;
        secret(&a[..]);
        secret(&b[..]);
        let r = match args.get(i + 1).map(String::as_str) {
            Some("branch") => early_eq(&a, &b) as u8,
            Some("index") => {
                let t: [u8; 256] = std::hint::black_box(core::array::from_fn(|i| i as u8));
                t[a[0] as usize]
            }
            _ => {
                eprintln!("ctgrind: --control branch|index");
                std::process::exit(2);
            }
        };
        public(&r);
        std::hint::black_box(r);
        return;
    }
    kernels();
    hashers!(Sha224 Sha256 Sha384 Sha512 Sha512_224 Sha512_256);
    macs!(HmacSha224 HmacSha256 HmacSha384 HmacSha512 HmacSha512_224 HmacSha512_256);
}

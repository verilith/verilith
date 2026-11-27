//! The constant-time check: run under Valgrind's memcheck by `./ci.sh ct`,
//! which fails if memcheck reports anything.
//!
//! The secrets (the key, the plaintext, the additional data and the block
//! given to the block cipher) are marked undefined with memcheck's client
//! requests, as in Adam Langley's ctgrind. Memcheck then reports any
//! conditional branch or memory address that depends on them. Lengths are
//! public. It covers key expansion and H, GCM sealing at every length up
//! to 300 and some longer ones (the same CTR and GHASH code `open` runs),
//! and the block cipher. `open` itself is left out: it branches once, on
//! whether the tag matched, which its caller learns anyway, and memcheck
//! cannot be told that this one is public. Valgrind's CPU
//! has AES-NI and PCLMULQDQ but not AVX-512, so this is the 128-bit path.
//! `--control branch` and `--control index` run code that leaks instead,
//! which the check must report.
use verilith_aes::{Aes, AesGcm};

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
fn main() {
    let control = std::env::args().skip_while(|a| a != "--control").nth(1);
    let iv = [9u8; 12];
    let mut n = 0;
    for klen in [16usize, 32] {
        let key = bytes(klen as u64, klen);
        secret(&key[..]);
        let k = AesGcm::new(&key).expect("AES-NI");
        let b = Aes::new(&key).unwrap();
        for len in (0..300).chain([1024, 4096 + 7]) {
            let mut buf = bytes(len as u64 + 1, len);
            let aad = bytes(len as u64 + 2, len % 37);
            secret(&buf[..]);
            secret(&aad[..]);
            let mut tag = [0u8; 16];
            assert!(k.seal(&iv, &aad, &mut buf, &mut tag));
            // The ciphertext and tag are public.
            public(&buf[..]);
            public(&tag);
            n += 1;
        }
        let mut blk = [3u8; 16];
        secret(&blk);
        b.encrypt_block(&mut blk);
        public(&blk);
        // A leak memcheck must see: a branch, or an index, on a secret.
        match control.as_deref() {
            Some("branch") => {
                let mut blk = [5u8; 16];
                secret(&blk);
                b.encrypt_block(&mut blk);
                if blk[0] & 1 == 1 {
                    n += 1;
                }
            }
            Some("index") => {
                let t = std::hint::black_box(bytes(7, 256));
                let i = std::hint::black_box(key[0] as usize);
                std::hint::black_box(t[i]);
            }
            _ => {}
        }
    }
    eprintln!("ctgrind: {n} seals checked");
}

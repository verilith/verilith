//! The dynamic constant-time check of the key schedule: run under
//! Valgrind's memcheck by `./ci.sh ct` (built with the `ctgrind` feature),
//! which fails if memcheck reports anything.
//!
//! The secrets (PSKs, shared secrets, traffic secrets, transcript hashes,
//! the record IV) are marked undefined with memcheck's client requests, as
//! in Adam Langley's ctgrind, and memcheck reports any conditional branch
//! or memory address that depends on them. It runs HKDF-Extract and
//! HKDF-Expand-Label, Derive-Secret, every step of the schedule from the
//! early secret to the resumption master secret, the traffic keys and IVs,
//! the Finished MAC and its comparison, the record nonce, and the copies
//! into and out of `Secret`, for both hashes and every secret length the
//! protocol uses. These go through verilith-sha2's HMAC, so this covers the
//! SHA-2 kernel this CPU (Valgrind's, which has no SHA extensions) runs.
//! `--control compare` runs an early-exit compare instead, which must be
//! reported.
use verilith_tls::ct::{ct_eq, declassify};
use verilith_tls::keys::*;
use verilith_tls::spec_keys::HashAlg;
use vstd::prelude::Ghost;

#[cfg(not(target_arch = "x86_64"))]
fn main() {
    eprintln!("ctgrind: the Valgrind client requests here are written for x86-64");
    std::process::exit(2);
}

#[cfg(target_arch = "x86_64")]
fn request(default: usize, args: [usize; 6]) -> usize {
    let mut r = default;
    // SAFETY: Valgrind's client-request sequence (see src/ct.rs).
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

/// Marks `s`'s bytes public again.
#[cfg(target_arch = "x86_64")]
fn public<T: ?Sized>(s: &T) {
    request(0, [MC + 2, s as *const T as *const u8 as usize, core::mem::size_of_val(s), 0, 0, 0]);
}

fn g<T>() -> Ghost<T> {
    Ghost::assume_new()
}

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

/// A Secret whose bytes are marked secret (its length stays public).
#[cfg(target_arch = "x86_64")]
fn sec(seed: u64, n: usize) -> Secret {
    let b = bytes(seed, n);
    secret(&b[..]);
    let s = Secret::from_slice(&b, n);
    s
}

#[cfg(target_arch = "x86_64")]
fn main() {
    let control = std::env::args().skip_while(|a| a != "--control").nth(1);
    let mut n = 0;
    for a in [HashAlg::Sha256, HashAlg::Sha384] {
        let hl = hash_len_x(a);
        let psk = bytes(1, hl);
        let dhe = bytes(2, 48);
        secret(&psk[..]);
        secret(&dhe[..]);
        let th = sec(3, hl);
        let es = early_secret_x(a, &psk);
        let bk = binder_key_x(a, &psk);
        let et = early_traffic_x(a, &psk, &th, g());
        for dl in [32, 48] {
            let hs = handshake_secret_x(a, &psk, &dhe[..dl]);
            let chs = hs_traffic_x(a, &hs, &th, g(), g(), g());
            let ms = master_secret_x(a, &hs, g(), g());
            let ap = ap_traffic_x(a, &ms, &th, g(), g(), g());
            let rm = resumption_master_x(a, &ms, &th, g(), g(), g());
            let tp = ticket_psk_x(a, &rm, &[7u8; 8]);
            let nx = next_traffic_secret_x(a, &ap.0);
            for kl in [16, 32] {
                let (k, iv) = traffic_keys_x(a, &nx, kl);
                let (k2, iv2, hp) = quic_keys_x(a, &chs.0, kl);
                let mut ivb = [0u8; 12];
                ivb.copy_from_slice(iv.as_slice());
                let nonce = record_nonce_x(&ivb, n as u64);
                // Keys and nonces are secret, so what was computed from
                // them is not marked public; only their lengths are read.
                std::hint::black_box((k.len(), k2.len(), iv2.len(), hp.len(), nonce.len()));
            }
            let fin = verify_data_x(a, &chs.1, &th, g());
            let other = sec(9, fin.len());
            // The client's Finished: compared without branching, then the
            // one decision, which is public.
            let ok = declassify(ct_eq(fin.as_slice(), fin.as_slice()));
            let bad = declassify(ct_eq(fin.as_slice(), other.as_slice()));
            assert!(ok && !bad);
            std::hint::black_box((es.len(), bk.len(), et.len(), tp.len()));
            n += 1;
        }
        for l in 0..=48 {
            let k = bytes(l as u64 + 10, l);
            secret(&k[..]);
            let m = bytes(l as u64 + 11, 2 * l + 1);
            secret(&m[..]);
            let h = hmac_x(a, &k, &m);
            let e = expand_label_x(a, h.as_slice(), &L_KEY, &m[..l.min(hl)], l.clamp(1, hl));
            std::hint::black_box(e.len());
            n += 1;
        }
        let (c, s) = initial_secrets_x(&bytes(5, 8));
        std::hint::black_box((c.len(), s.len()));
        public(&psk[..]);
    }
    if control.as_deref() == Some("compare") {
        let a = bytes(20, 32);
        let b = bytes(20, 32);
        secret(&a[..]);
        if std::hint::black_box(&a[..]) == std::hint::black_box(&b[..]) {
            n += 1;
        }
    }
    eprintln!("ctgrind: {n} schedules and MACs checked");
}

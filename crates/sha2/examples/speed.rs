//! SHA-256 and SHA-512 throughput: verilith-sha2 (the kernel `cpu` picks, and the
//! verified portable kernel alone) against RustCrypto's sha2 and against
//! OpenSSL's libcrypto (loaded with dlopen, if there is one):
//! `cargo run --release --example speed`.
use sha2::Digest;
use std::ffi::{c_char, c_int, c_void, CString};
use std::time::Instant;
use verilith_sha2::{compress, cpu, sha256, sha512, Sha256};

extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
}

type OneShot = unsafe extern "C" fn(*const u8, usize, *mut u8) -> *mut u8;

fn openssl(name: &std::ffi::CStr) -> Option<OneShot> {
    let names = std::env::var("VSHA2_LIBCRYPTO").into_iter().chain(["libcrypto.so.3".into(), "libcrypto.3.dylib".into()]);
    for n in names {
        unsafe {
            let h = dlopen(CString::new(n).unwrap().as_ptr(), 2);
            if !h.is_null() {
                let f = dlsym(h, name.as_ptr());
                if !f.is_null() {
                    return Some(std::mem::transmute::<*mut c_void, OneShot>(f));
                }
            }
        }
    }
    None
}

/// Best of 15 runs, in MB/s.
fn best(mut f: impl FnMut() -> u8, bytes: usize) -> f64 {
    let mut best = f64::MAX;
    for _ in 0..15 {
        let reps = (32usize << 20) / bytes + 1;
        let t = Instant::now();
        for _ in 0..reps {
            std::hint::black_box(f());
        }
        best = best.min(t.elapsed().as_secs_f64() / reps as f64);
    }
    bytes as f64 / best / 1e6
}

fn main() {
    let ossl = openssl(c"SHA256");
    let ossl512 = openssl(c"SHA512");
    let data: Vec<u8> = (0..1usize << 20).map(|i| (i.wrapping_mul(2654435761) >> 13) as u8).collect();
    println!("kernel: {}  (MB/s, best of 15)", cpu::kernel());
    println!("{:>8}  {:>10}  {:>10}  {:>10}  {:>10}", "bytes", "verilith", "portable", "rustcrypto", "openssl");
    for n in [16usize, 64, 256, 1024, 8192, 65536, 1 << 20] {
        let d = &data[..n];
        let ours = best(|| sha256(std::hint::black_box(d))[0], n);
        // The verified portable kernel over the whole blocks (no padding).
        let whole = &d[..n / 64 * 64];
        let portable = if whole.is_empty() {
            f64::NAN
        } else {
            best(
                || {
                    let mut st = verilith_sha2::spec::IV256;
                    compress::compress_blocks(&mut st, std::hint::black_box(whole));
                    st[0] as u8
                },
                whole.len(),
            )
        };
        let rc = best(|| sha2::Sha256::digest(std::hint::black_box(d))[0], n);
        let os = match ossl {
            Some(f) => best(
                || {
                    let mut md = [0u8; 32];
                    unsafe { f(std::hint::black_box(d).as_ptr(), n, md.as_mut_ptr()) };
                    md[0]
                },
                n,
            ),
            None => f64::NAN,
        };
        assert_eq!(sha256(d)[..], sha2::Sha256::digest(d)[..]);
        println!("{n:>8}  {ours:>10.0}  {portable:>10.0}  {rc:>10.0}  {os:>10.0}");
    }
    // Streaming in small pieces, as a TLS record or HMAC caller would.
    let t = best(
        || {
            let mut h = Sha256::new();
            for c in data[..65536].chunks(37) {
                h.update(c);
            }
            h.finalize()[0]
        },
        65536,
    );
    println!("65536 in pieces of 37: {t:.0} MB/s");

    println!();
    println!("SHA-512 kernel: {}", cpu::kernel512());
    println!("{:>8}  {:>10}  {:>10}  {:>10}", "bytes", "verilith", "rustcrypto", "openssl");
    for n in [16usize, 128, 1024, 8192, 65536, 1 << 20] {
        let d = &data[..n];
        let ours = best(|| sha512(std::hint::black_box(d))[0], n);
        let rc = best(|| sha2::Sha512::digest(std::hint::black_box(d))[0], n);
        let os = match ossl512 {
            Some(f) => best(
                || {
                    let mut md = [0u8; 64];
                    unsafe { f(std::hint::black_box(d).as_ptr(), n, md.as_mut_ptr()) };
                    md[0]
                },
                n,
            ),
            None => f64::NAN,
        };
        assert_eq!(sha512(d)[..], sha2::Sha512::digest(d)[..]);
        println!("{n:>8}  {ours:>10.0}  {rc:>10.0}  {os:>10.0}");
    }
}

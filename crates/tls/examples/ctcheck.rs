//! The binary for `scripts/ctcheck.py`, the static constant-time check of
//! the compiled code (`./ci.sh ctstatic`): each `ctcheck_*` function is one
//! of verilith-tls's own operations on secrets, compiled as a user of the
//! crate gets it, with its arguments in registers (lengths and pointers:
//! public) and its secrets in memory. (The key schedule, which is HMAC, is
//! checked under Valgrind by `examples/ctgrind.rs`.) The check reads the code;
//! running this does nothing useful.
use std::hint::black_box;
use verilith_tls::keys::*;

/// The per-record nonce (§5.3): the IV, secret, XOR the sequence number.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_record_nonce(iv: &[u8; 12], seq: u64, out: &mut [u8; 12]) {
    *out = record_nonce_x(iv, seq);
}

/// Copying a secret in and out.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_secret_copy(src: &[u8; 48], l: usize, out: &mut [u8; 48]) {
    let s = Secret::from_slice(&src[..], l.min(48));
    out[..s.len()].copy_from_slice(s.as_slice());
}

/// Comparing a Finished or a binder with what it should be.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_ct_eq(a: &[u8; 48], b: &[u8; 48], l: usize) -> bool {
    verilith_tls::ct::declassify(verilith_tls::ct::ct_eq(&a[..l.min(48)], &b[..l.min(48)]))
}

/// A leak the check must report: an early-exit compare. (Written as a loop:
/// `a == b` on two 48-byte arrays is no control, since LLVM compiles it on
/// AArch64 to loads, XORs and ORs with no branch, which do not leak.)
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_leak_compare(a: &[u8; 48], b: &[u8; 48]) -> bool {
    for i in 0..48 {
        if black_box(a[i]) != b[i] {
            return false;
        }
    }
    true
}

fn main() {
    let mut n = [0u8; 12];
    let mut c = [0u8; 48];
    ctcheck_record_nonce(&[4; 12], 7, &mut n);
    ctcheck_secret_copy(&[5; 48], 32, &mut c);
    black_box(ctcheck_ct_eq(&[1; 48], &[1; 48], 32));
    black_box(ctcheck_leak_compare(&[1; 48], &[1; 48]));
    black_box((n, c));
    black_box([
        ctcheck_record_nonce as *const () as usize,
        ctcheck_secret_copy as *const () as usize,
        ctcheck_ct_eq as *const () as usize,
        ctcheck_leak_compare as *const () as usize,
    ]);
}

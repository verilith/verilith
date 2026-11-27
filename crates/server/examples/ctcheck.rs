//! The binary for `scripts/ctcheck.py`, the static constant-time check of
//! the compiled code (`./ci.sh ctstatic`): the one place this crate handles
//! a TLS secret itself, laying out the traffic key and IV for the kernel
//! when it hands record protection to kTLS (`sys::ktls_crypto_info`).
//! The check reads that function itself (on AArch64 it does not follow
//! calls). `ctcheck_leak_key` is the control: it writes at an offset taken
//! from a key byte, and the check must report it. The check reads the code; running this
//! does nothing useful.
#![cfg_attr(not(target_os = "linux"), allow(unused))]
use std::hint::black_box;

#[cfg(target_os = "linux")]
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_ktls_crypto_info(suite: u16, key: &[u8; 32], l: usize, iv: &[u8; 12], seq: u64, info: &mut [u8; 56]) -> usize {
    verilith_server::sys::ktls_crypto_info(suite, &key[..l.min(32)], iv, seq, info).unwrap_or(0)
}

#[cfg(target_os = "linux")]
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_leak_key(key: &[u8; 32], info: &mut [u8; 56]) {
    info[(key[0] & 31) as usize..][..16].copy_from_slice(&key[16..]);
}

fn main() {
    #[cfg(target_os = "linux")]
    {
        let mut info = [0u8; 56];
        black_box(ctcheck_ktls_crypto_info(0x1301, &[1; 32], 16, &[2; 12], 3, &mut info));
        ctcheck_leak_key(&[1; 32], &mut info);
        black_box((info, ctcheck_ktls_crypto_info as *const () as usize, ctcheck_leak_key as *const () as usize));
    }
}

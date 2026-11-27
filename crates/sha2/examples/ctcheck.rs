//! The binary for `scripts/ctcheck.py`, the static constant-time check of
//! the compiled code (`./ci.sh ctstatic`). It is not meant to be run for
//! its output: each `ctcheck_*` function is one entry point (a kernel or a
//! hasher), compiled as a user of the crate gets it, with its lengths and
//! pointers in registers (public) and the message and state in memory
//! (secret). The MACs are checked under Valgrind only (`examples/ctgrind.rs`):
//! the static check loses track of which bytes of a MAC's state are the
//! (public) buffered length and reports leaks that are not there. The kernels behind function pointers (the
//! BMI2 and AVX2 builds) and the AArch64 kernels are checked by their own
//! symbols, which `main` keeps linked.
//!
//! The `ctcheck_leak_*` functions are the controls: an early-exit compare
//! and a lookup at a secret index, which the check must report.
use core::slice::from_raw_parts as sl;
use std::hint::black_box;
use verilith_sha2::*;

macro_rules! kernel {
    ($name:ident, $w:ty, $f:path) => {
        #[unsafe(no_mangle)]
        #[inline(never)]
        pub unsafe extern "C" fn $name(st: &mut [$w; 8], p: *const u8, n: usize) {
            // SAFETY: the caller passes `n` readable bytes at `p`.
            $f(st, unsafe { sl(p, n) })
        }
    };
}
kernel!(ctcheck_dispatch256, u32, cpu::compress_blocks);
kernel!(ctcheck_dispatch512, u64, cpu::compress512_blocks);
kernel!(ctcheck_portable256, u32, compress::compress_blocks);
kernel!(ctcheck_portable512, u64, compress512::compress_blocks);

macro_rules! hasher {
    ($name:ident, $f:path, $l:literal) => {
        #[unsafe(no_mangle)]
        #[inline(never)]
        pub unsafe extern "C" fn $name(p: *const u8, n: usize, out: &mut [u8; $l]) {
            // SAFETY: the caller passes `n` readable bytes at `p`.
            *out = $f(unsafe { sl(p, n) })
        }
    };
}
hasher!(ctcheck_sha256, sha256, 32);
hasher!(ctcheck_sha512, sha512, 64);

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_leak_branch(a: &[u8; 32], b: &[u8; 32]) -> bool {
    for i in 0..32 {
        if black_box(a[i]) != b[i] {
            return false;
        }
    }
    true
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_leak_index(k: &[u8; 32], t: &[u8; 256]) -> u8 {
    t[k[3] as usize]
}

fn main() {
    let msg = black_box(vec![3u8; 300]);
    let mut s32 = [0u32; 8];
    let mut s64 = [0u64; 8];
    let (mut o32, mut o64) = ([0u8; 32], [0u8; 64]);
    // SAFETY: the lengths are those of the buffers.
    unsafe {
        ctcheck_dispatch256(&mut s32, msg.as_ptr(), 256);
        ctcheck_dispatch512(&mut s64, msg.as_ptr(), 256);
        ctcheck_portable256(&mut s32, msg.as_ptr(), 256);
        ctcheck_portable512(&mut s64, msg.as_ptr(), 256);
        ctcheck_sha256(msg.as_ptr(), 300, &mut o32);
        ctcheck_sha512(msg.as_ptr(), 300, &mut o64);
    }
    for (a, b) in cpu::bmi2_kernels().into_iter().chain(cpu::avx2_kernels()) {
        a(&mut s32, &msg[..256]);
        b(&mut s64, &msg[..256]);
    }
    #[cfg(target_arch = "aarch64")]
    if black_box(false) {
        armv8::compress_blocks(&mut s32, &msg[..256]);
        armv8::compress512_blocks(&mut s64, &msg[..256]);
    }
    black_box(ctcheck_leak_branch(&o32, &o32));
    black_box(ctcheck_leak_index(&o32, &[0; 256]));
    black_box([ctcheck_leak_branch as *const () as usize, ctcheck_leak_index as *const () as usize]);
    black_box((s32, s64, o32, o64));
}

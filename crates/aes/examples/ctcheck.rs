//! The binary for `tools/ctcheck.py`, the static constant-time check of
//! the compiled code (`./ci.sh ctstatic`). It is not meant to be run for
//! its output: it exists so that the linker keeps every entry point the
//! check reads (key expansion, H, the block cipher, and sealing and
//! opening on each path), compiled exactly as a user of the crate gets
//! them, and so that the check has code that does leak to find.
//!
//! `CTCHECK_NR_OFFSET` tells the check what it needs to know about `Gcm`:
//! the offset of `nr`, its one public field (the number of rounds, from the
//! key's length). The check reads it from the binary, so it is the layout
//! of the target the binary was built for.
//!
//! The `ctcheck_leak_*` functions are the controls: each leaks a secret in
//! one way (a branch, a memory index, a branch on a value moved out of a
//! vector register, a variable-time instruction, and a select written
//! without a branch that LLVM turns into one) and the check must report
//! it, or it is not seeing what it should. `ctcheck_clean` handles a
//! secret without leaking it and must pass.
use std::hint::black_box;
use verilith_aes::{Aes, AesGcm};

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_leak_branch(k: &[u8; 16], out: &mut u32) {
    if k[0] & 1 == 1 {
        // SAFETY: `out` is a valid reference.
        unsafe { core::ptr::write_volatile(out, 1) };
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_leak_index(k: &[u8; 16], t: &[u8; 256]) -> u8 {
    t[k[3] as usize]
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_leak_divide(k: &[u8; 16]) -> u32 {
    (k[0] as u32 | (k[1] as u32) << 8) / (k[2] as u32 | 1)
}

#[cfg(target_arch = "x86_64")]
#[unsafe(no_mangle)]
#[inline(never)]
#[target_feature(enable = "aes,sse4.1")]
pub unsafe extern "C" fn ctcheck_leak_vector(k: &[u8; 16], out: &mut u32) {
    use core::arch::x86_64::*;
    // SAFETY: 16 bytes are readable at `k`.
    let x = unsafe { _mm_loadu_si128(k.as_ptr().cast()) };
    let y = _mm_aesenc_si128(x, x);
    if _mm_extract_epi8::<5>(y) & 1 == 1 {
        // SAFETY: `out` is a valid reference.
        unsafe { core::ptr::write_volatile(out, 1) };
    }
}

#[cfg(target_arch = "aarch64")]
#[unsafe(no_mangle)]
#[inline(never)]
#[target_feature(enable = "neon,aes")]
pub unsafe extern "C" fn ctcheck_leak_vector(k: &[u8; 16], out: &mut u32) {
    use core::arch::aarch64::*;
    // SAFETY: 16 bytes are readable at `k`.
    let x = unsafe { vld1q_u8(k.as_ptr()) };
    let y = vaeseq_u8(x, x);
    if vgetq_lane_u8::<5>(y) & 1 == 1 {
        // SAFETY: `out` is a valid reference.
        unsafe { core::ptr::write_volatile(out, 1) };
    }
}

/// A select written without a branch, which LLVM compiles to one: the
/// reason the check reads the machine code and not the source.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_leak_select(k: &[u8; 16], out: &mut [u8; 16]) {
    let m = 0u8.wrapping_sub(k[0] & 1);
    for i in 0..16 {
        out[i] = (k[i] ^ 0x5c) & m | k[15 - i] & !m;
    }
}

/// Copies and mixes a secret without leaking it; must pass.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ctcheck_clean(k: &[u8; 16], out: &mut [u8; 16]) {
    for i in 0..16 {
        out[i] = k[i].rotate_left(3) ^ k[15 - i] ^ 0x5c;
    }
}

#[unsafe(no_mangle)]
#[used]
pub static CTCHECK_NR_OFFSET: u64 = verilith_aes::layout::NR_OFFSET as u64;

fn main() {
    // Reach every entry point, so that each is linked in; the check reads
    // the code, not what this does.
    let key = black_box([7u8; 32]);
    let iv = black_box([1u8; 12]);
    let mut buf = black_box(vec![0u8; 300]);
    let mut tag = [0u8; 16];
    for klen in [16, 32] {
        for k in [AesGcm::new(&key[..klen]), AesGcm::new_narrow(&key[..klen])].into_iter().flatten() {
            k.seal(&iv, b"aad", &mut buf, &mut tag);
            black_box(k.open(&iv, b"aad", &mut buf, &tag));
        }
        if let Some(b) = Aes::new(&key[..klen]) {
            let mut blk = [0u8; 16];
            b.encrypt_block(&mut blk);
            black_box(blk);
        }
    }
    let mut o = 0u32;
    let mut c = [0u8; 16];
    ctcheck_leak_branch(&key[..16].try_into().unwrap(), &mut o);
    black_box(ctcheck_leak_index(&key[..16].try_into().unwrap(), &[0u8; 256]));
    black_box(ctcheck_leak_divide(&key[..16].try_into().unwrap()));
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    // SAFETY: only reached for its symbol; the check never runs it, and
    // `main` never calls it on a CPU without the features.
    if black_box(false) {
        unsafe { ctcheck_leak_vector(&key[..16].try_into().unwrap(), &mut o) };
    }
    ctcheck_leak_select(&key[..16].try_into().unwrap(), &mut c);
    black_box(c);
    // Keep each control's own symbol, even where a call above was inlined.
    black_box([ctcheck_leak_select as *const () as usize, ctcheck_clean as *const () as usize, ctcheck_leak_branch as *const () as usize, ctcheck_leak_index as *const () as usize]);
    ctcheck_clean(&key[..16].try_into().unwrap(), &mut c);
    black_box((o, c, tag, buf));
}

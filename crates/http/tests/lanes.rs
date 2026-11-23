//! Checks the SSE2 wrappers `src/lanes.rs` re-exports from verilith-simd against their specs,
//! on every pair of byte values per lane.
#![cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;
use verilith_http::lanes::*;

fn lanes(v: __m128i) -> [u8; 16] {
    unsafe { std::mem::transmute(v) }
}

#[test]
fn load_splat() {
    let s: Vec<u8> = (0..=255u8).collect();
    for i in 0..=240 {
        assert_eq!(lanes(load16(&s, i)), s[i..i + 16]);
    }
    for c in 0..=255u8 {
        assert_eq!(lanes(splat16(c)), [c; 16]);
    }
}

#[test]
fn per_lane_ops() {
    for a in 0..=255u8 {
        let mut bs = [0u8; 256];
        for (i, b) in bs.iter_mut().enumerate() {
            *b = i as u8;
        }
        for chunk in bs.chunks(16) {
            let va = splat16(a);
            let vb = load16(chunk, 0);
            let eq = lanes(eq16(va, vb));
            let or = lanes(or16(va, vb));
            let mn = lanes(min16(va, vb));
            for k in 0..16 {
                let b = chunk[k];
                assert_eq!(eq[k], if a == b { 0xFF } else { 0 });
                assert_eq!(or[k], a | b);
                assert_eq!(mn[k], a.min(b));
            }
            let m = movemask16(vb);
            assert!(m < 0x10000);
            for k in 0..16 {
                assert_eq!((m >> k) & 1 == 1, chunk[k] >= 0x80);
            }
        }
    }
}

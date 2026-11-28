//! The CRC instruction wrappers against their definition, a bit at a time,
//! on random registers and bytes (on the CPUs that have the instructions;
//! elsewhere the portable loops, which are that definition).
use verilith_simd::crc::*;

fn bits(poly: u32, mut c: u32, d: &[u8]) -> u32 {
    for &x in d {
        c ^= x as u32;
        for _ in 0..8 {
            c = if c & 1 == 1 { (c >> 1) ^ poly } else { c >> 1 };
        }
    }
    c
}

#[test]
fn crc_instructions() {
    let mut x: u64 = 0x243f_6a88_85a3_08d3;
    let mut r = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    let c32c = has_crc32c();
    let arm = has_crc_arm();
    for _ in 0..200_000 {
        let c = r() as u32;
        let d = r().to_le_bytes();
        let pad: Vec<u8> = [&[r() as u8][..], &d[..]].concat();
        if c32c {
            assert_eq!(crc32c_u64(c as u64, &pad, 1), bits(0x82f6_3b78, c, &d) as u64);
            assert_eq!(crc32c_u8(c, d[0]), bits(0x82f6_3b78, c, &d[..1]));
        }
        if arm || !cfg!(target_arch = "aarch64") {
            assert_eq!(crc32_u64(c, &pad, 1), bits(0xedb8_8320, c, &d));
        }
    }
}

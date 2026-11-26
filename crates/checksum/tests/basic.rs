//! The dispatched kernels against the portable ones, and the three-lane CRC-32.
use verilith_checksum::{adler32, adler32_update, crc32, crc32_update};

#[test]
fn checksums() {
    assert_eq!(crc32(b""), 0);
    assert_eq!(crc32(b"123456789"), 0xcbf4_3926);
    assert_eq!(adler32(b"Wikipedia"), 0x11e6_0398);
    // The CPU kernels agree with the portable ones on every length up to
    // well past the PCLMULQDQ threshold.
    let data: Vec<u8> = (0..5000u32).map(|i| (i.wrapping_mul(2654435761u32) >> 13) as u8).collect();
    for n in 0..data.len() {
        let d = &data[..n];
        assert_eq!(verilith_checksum::cpu::crc32_update(0xffff_ffff, d), crc32_update(0xffff_ffff, d));
        assert_eq!(verilith_checksum::cpu::adler32_update(1, 0, d), adler32_update(1, 0, d));
    }
}

#[test]
fn crc32_lanes() {
    use verilith_checksum::lanes;
    let mut x = 0x9e37_79b9_7f4a_7c15u64;
    let data: Vec<u8> = (0..3 * 12288 + 5000)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            (x >> 32) as u8
        })
        .collect();
    let mut lens: Vec<usize> = (0..1000).collect();
    for b in [1536usize, 3072, 12288, 13824, 24576, 36864] {
        lens.extend(b - 20..b + 20);
    }
    lens.push(data.len());
    for &n in &lens {
        for (reg, off) in [(0xffff_ffffu32, 0usize), (0, 1), (0x1234_5678, 3), (1, 7)] {
            let d = &data[off..off + n.min(data.len() - off)];
            let want = crc32_update(reg, d);
            assert_eq!(lanes::crc32_update(reg, d), want, "lanes, len {n}");
            assert_eq!(verilith_checksum::cpu::crc32_update(reg, d), want, "cpu, len {n}");
        }
    }
    // The shift itself: stepping past 32, 128, 512 and 4096 zero bytes.
    for c in [1u32, 0x8000_0000, 0xdead_beef, 0xffff_ffff] {
        let g = vstd::prelude::Ghost::assume_new;
        assert_eq!(lanes::shift(&lanes::NIBS_32, c, g()), crc32_update(c, &[0u8; 32]));
        assert_eq!(lanes::shift(&lanes::NIBS_128, c, g()), crc32_update(c, &[0u8; 128]));
        assert_eq!(lanes::shift(&lanes::NIBS_256, c, g()), crc32_update(c, &[0u8; 256]));
        assert_eq!(lanes::shift(&lanes::NIBS_512, c, g()), crc32_update(c, &[0u8; 512]));
        assert_eq!(lanes::shift(&lanes::NIBS_4096, c, g()), crc32_update(c, &[0u8; 4096]));
    }
}

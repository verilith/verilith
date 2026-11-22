//! CRC-32C: published values, the table kernel against a bit-at-a-time
//! reference written from the definition, and the CPU's instruction
//! (`checksum::cpu`, unverified) against the table kernel.
use verilith_core::checksum::{cpu, crc32c, crc32c_update};

/// The register update one bit at a time (RFC 3720 appendix B.4).
fn reference(mut c: u32, d: &[u8]) -> u32 {
    for &x in d {
        c ^= x as u32;
        for _ in 0..8 {
            c = if c & 1 == 1 { (c >> 1) ^ 0x82f6_3b78 } else { c >> 1 };
        }
    }
    c
}

fn data(n: usize, mut x: u64) -> Vec<u8> {
    (0..n)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x as u8
        })
        .collect()
}

#[test]
fn published() {
    assert_eq!(crc32c(b""), 0);
    assert_eq!(crc32c(b"123456789"), 0xe306_9283);
    // RFC 3720 appendix B.4.
    assert_eq!(crc32c(&[0u8; 32]), 0x8a91_36aa);
    assert_eq!(crc32c(&[0xffu8; 32]), 0x62a8_ab43);
    let inc: Vec<u8> = (0..32).collect();
    assert_eq!(crc32c(&inc), 0x46dd_794e);
    let dec: Vec<u8> = (0..32).rev().collect();
    assert_eq!(crc32c(&dec), 0x113f_db5c);
}

#[test]
fn table_against_reference() {
    let d = data(2000, 0x2545_f491_4f6c_dd1d);
    for n in 0..=2000 {
        let reg = (n as u32).wrapping_mul(0x9e37_79b9);
        assert_eq!(crc32c_update(reg, &d[..n]), reference(reg, &d[..n]), "len {n}");
    }
}

#[test]
fn cpu_against_table() {
    let d = data(5000, 0x94d0_49bb_1331_11eb);
    for off in 0..8 {
        for n in 0..=(5000 - 8) {
            if n > 300 && n % 97 != 0 {
                continue;
            }
            let s = &d[off..off + n];
            let reg = (n as u32 ^ off as u32).wrapping_mul(0x85eb_ca77);
            assert_eq!(cpu::crc32c_update(reg, s), crc32c_update(reg, s), "offset {off}, len {n}");
        }
    }
}

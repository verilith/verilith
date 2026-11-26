//! CRC-32C: published values, the table kernel against a bit-at-a-time
//! reference written from the definition, the CPU's instruction (the
//! trusted `crc32c::crc32c_word`) against the table kernel on random
//! registers and words, and the verified instruction kernel
//! (`cpu`) against the table kernel.
use verilith_checksum::crc32c::{crc32c_word, has_crc32c};
use verilith_checksum::{cpu, crc32c, crc32c_update};

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

/// What `crc32c_word` is trusted for: on 1,000,000 random registers and
/// words (with zero, all-one and one-bit words mixed in), the instruction
/// gives what the verified table kernel gives over the same eight bytes.
#[test]
fn instruction_against_table() {
    if !has_crc32c() {
        eprintln!("skipped: this CPU has no CRC-32C instruction");
        return;
    }
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    for k in 0..1_000_000u32 {
        let reg = next() as u32;
        let w = match k % 8 {
            0 => 0,
            1 => u64::MAX,
            2 => 1u64 << (next() % 64),
            _ => next(),
        };
        let reg = if k % 16 == 3 { 0 } else if k % 16 == 5 { u32::MAX } else { reg };
        let b = w.to_le_bytes();
        let mut d = [0u8; 11];
        let i = (k % 4) as usize;
        d[i..i + 8].copy_from_slice(&b);
        assert_eq!(crc32c_word(reg as u64, &d, i), crc32c_update(reg, &b) as u64, "reg {reg:#x}, word {w:#x}");
    }
}

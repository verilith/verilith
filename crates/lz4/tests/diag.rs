//! Says why vlz4 rejects frames that liblz4 accepts, among mutated
//! frames (`cargo test --release --test diag -- --ignored --nocapture`).
mod common;
use common::*;

#[test]
#[ignore]
fn diag() {
    let Some(l) = Lz4f::load() else { return };
    let mut rng = Rng(0x452821e638d01377);
    for round in 0..30000 {
        let size = [0usize, 5, 20, 300, 5000, 70000][round % 6];
        let input = sample(&mut rng, size, round % KINDS);
        let mut p = Preferences::default();
        p.frame_info.block_size_id = 4 + (round % 4) as i32;
        p.frame_info.block_mode = (round / 4 % 2) as i32;
        p.frame_info.content_checksum = (round / 8 % 2) as i32;
        p.frame_info.block_checksum = (round / 16 % 2) as i32;
        p.frame_info.content_size = if round / 32 % 2 == 0 { input.len() as u64 } else { 0 };
        let mut c = l.compress(&input, &p);
        for _ in 0..1 + rng.below(2) {
            let at = rng.below(c.len());
            match rng.below(4) {
                0 => c[at] ^= 1 << rng.below(8),
                1 => c[at] = rng.next() as u8,
                2 => c.truncate(at),
                _ => c.insert(at, rng.next() as u8),
            }
            if c.is_empty() {
                break;
            }
        }
        let theirs = l.decompress(&c, usize::MAX).filter(|(_, used)| *used == c.len()).map(|(v, _)| v);
        let mut o = Vec::new();
        let ours = verilith_lz4::frame::decode_frame(&c, 0, &mut o, 1 << 30);
        if theirs.is_some() && !matches!(ours, Ok(j) if j == c.len()) {
            let h = verilith_lz4::frame::read_header(&c, 0);
            eprintln!("round {round}: ours {ours:?}, header {h:?}, len {}", c.len());
            if let Some(h) = h {
                let mut i = h.end;
                let mut total = 0;
                loop {
                    let w = u32::from_le_bytes(c[i..i + 4].try_into().unwrap());
                    let size = (w & 0x7fff_ffff) as usize;
                    if size == 0 {
                        eprintln!("  end mark at {i}");
                        break;
                    }
                    let data = &c[i + 4..i + 4 + size];
                    let mut buf = vec![0u8; total + (8 << 20)];
                    let r = if w >> 31 == 1 { Some(size) } else { verilith_lz4::block::decode_block(data, &mut buf, 0, total).map(|n| n - total) };
                    eprintln!("  block at {i}: size {size} raw {} -> {r:?}, zero offset {}", w >> 31, has_zero_offset(data));
                    match r {
                        Some(n) => total += n,
                        None => break,
                    }
                    i += 4 + size + if h.bsum { 4 } else { 0 };
                }
            }
        }
    }
}

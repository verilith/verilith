//! Frames that libzstd wrote (tests/data, by scripts/gen-test-frames.py),
//! decoded with no library at run time: the tests that do real work where
//! libzstd cannot be loaded (wasm32-wasip1 under wasmtime, in
//! scripts/wasm32.sh). The inputs are rebuilt here as the script built them.
use verilith_zstd::frame::decompress_exec;

const WORDS: [&[u8]; 16] = [
    b"the", b"quick", b"brown", b"fox", b"jumps", b"over", b"lazy", b"dog", b"zstd", b"frame", b"block", b"literal",
    b"sequence", b"offset", b"match", b"huffman",
];

fn sample(size: usize, kind: u32, seed: u64) -> Vec<u8> {
    let mut x = seed;
    let mut out = Vec::new();
    while out.len() < size {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let r = x >> 33;
        match kind {
            0 => out.push(r as u8),
            1 => {
                out.extend_from_slice(WORDS[(r % 16) as usize]);
                out.push(b' ');
            },
            _ => {
                if r % 3 == 0 {
                    out.extend(std::iter::repeat_n(r as u8, 1 + ((r >> 8) % 40) as usize));
                } else {
                    out.extend_from_slice(WORDS[(r % 16) as usize]);
                    out.push(b' ');
                }
            },
        }
    }
    out.truncate(size);
    out
}

#[test]
fn libzstd_frames() {
    let cases = [
        ("random-4k", 4096, 0),
        ("text-200k-l1", 200_000, 1),
        ("text-200k-l19", 200_000, 1),
        ("mixed-300k-l9", 300_000, 2),
        ("mixed-300k-w10", 300_000, 2),
        ("empty", 0, 1),
    ];
    for (name, size, kind) in cases {
        let path = format!("{}/tests/data/{name}.zst", env!("CARGO_MANIFEST_DIR"));
        let c = std::fs::read(&path).unwrap();
        let want = sample(size, kind, 0x9e3779b97f4a7c15 + size as u64);
        assert!(decompress_exec(&c, 1 << 30).ok() == Some(want), "{name}");
        // One byte less than the content is refused.
        if size > 0 {
            assert!(decompress_exec(&c, size - 1).is_err(), "{name}");
        }
        // A flipped bit in the last byte (the checksum, or the end of the
        // last block) is noticed: the frame no longer decodes to the input.
        let mut bad = c.clone();
        *bad.last_mut().unwrap() ^= 1;
        assert!(decompress_exec(&bad, 1 << 30).ok() != Some(sample(size, kind, 0x9e3779b97f4a7c15 + size as u64)), "{name}");
    }
}

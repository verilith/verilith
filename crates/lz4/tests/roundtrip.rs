//! Round trips through the proven compressors and decompressors alone,
//! with no reference library: the tests that run where liblz4 cannot be
//! loaded (wasm32-wasip1 under wasmtime, in scripts/wasm32.sh).
mod common;
use common::{sample, sizes, Rng, KINDS};
use verilith_lz4::{compress, compress_block, compress_bound, decompress, decompress_block, Prefs};

#[test]
fn blocks() {
    let mut rng = Rng(0x6a09_e667_f3bc_c908);
    for size in sizes() {
        for kind in 0..KINDS {
            let input = sample(&mut rng, size, kind);
            let mut c = vec![0u8; compress_bound(size)];
            let n = compress_block(&input, &mut c, 1).expect("compress_bound is enough");
            let mut out = vec![0u8; size];
            assert_eq!(decompress_block(&c[..n], &mut out), Some(size), "size {size} kind {kind}");
            assert!(out == input, "size {size} kind {kind}");
        }
    }
}

#[test]
fn frames() {
    let mut rng = Rng(0xbb67_ae85_84ca_a73b);
    for (i, size) in sizes().into_iter().enumerate() {
        for kind in 0..KINDS {
            let input = sample(&mut rng, size, kind);
            let prefs = Prefs { block_id: 4 + (i % 4) as u8, indep: i % 2 == 0, bsum: kind % 2 == 0, csum: true, csize: i % 3 == 0, accel: 1 };
            let c = compress(&input, &prefs);
            assert!(decompress(&c, usize::MAX).ok() == Some(input), "size {size} kind {kind}");
        }
    }
}

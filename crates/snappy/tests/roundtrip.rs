//! Round trips through the proven compressor and decompressor alone, with
//! no reference library: the tests that run where libsnappy cannot be
//! loaded (wasm32-wasip1 under wasmtime, in scripts/wasm32.sh).
mod common;
use common::{sample, sizes, Rng, KINDS};
use verilith_snappy::{compress, decompress, max_compressed_length, uncompressed_length, validate};

#[test]
fn raw() {
    let mut rng = Rng(0x3c6e_f372_fe94_f82b);
    for size in sizes() {
        for kind in 0..KINDS {
            let input = sample(&mut rng, size, kind);
            let c = compress(&input).expect("below 4 GiB");
            assert!(c.len() <= max_compressed_length(size), "size {size} kind {kind}");
            assert!(validate(&c), "size {size} kind {kind}");
            assert_eq!(uncompressed_length(&c), Some(size), "size {size} kind {kind}");
            assert!(decompress(&c, usize::MAX).ok() == Some(input), "size {size} kind {kind}");
        }
    }
}

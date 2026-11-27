//! Compresses arbitrary bytes through the compressor's C ABI, one-shot
//! and streamed in pieces, at every level, and checks that each frame
//! decodes back to the input. Under ASan (`cargo fuzz run compress`) this
//! checks the unverified adapter for memory errors. `tests/compress.rs`
//! runs the same checks without libFuzzer.
#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    verilith_zstd::ccapi::exercise(data);
});

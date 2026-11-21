//! Feeds arbitrary bytes, with arbitrary buffer sizes, to every
//! decompression entry point of the C ABI. Under ASan
//! (`cargo fuzz run c_abi_bytes`) this checks the adapter for memory
//! errors on hostile input. `tests/stress.rs` runs the same checks
//! without libFuzzer.
#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    verilith_zstd::capi::exercise(data);
});

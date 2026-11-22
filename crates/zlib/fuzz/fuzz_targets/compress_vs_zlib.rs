//! Compresses the fuzz input with vzlib's verified compressor (format and
//! level from the first byte) and decompresses it with zlib. The proof says
//! the output decompresses under vzlib's specification; this checks that
//! zlib, an independent decoder, agrees.
#![no_main]
use libfuzzer_sys::fuzz_target;

#[path = "../../tests/common/mod.rs"]
mod common;

fuzz_target!(|data: &[u8]| {
    if data.is_empty() {
        return;
    }
    let (opt, body) = data.split_at(1);
    let level = (opt[0] % 10) as u32;
    let (c, wbits) = match (opt[0] / 10) % 3 {
        0 => (verilith_zlib::deflate::compress_raw(body, level), -15),
        1 => (verilith_zlib::deflate::zlib_compress(body, level), 15),
        _ => (verilith_zlib::deflate::gzip_compress(body, level), 31),
    };
    let (out, used) = common::zinflate(&c, wbits).expect("zlib rejected vzlib's output");
    assert_eq!(out, body);
    assert_eq!(used, c.len());
});

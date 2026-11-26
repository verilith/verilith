#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// Verilith: formally verified (Verus) drop-in replacements for foundational
// libraries.
//
// This crate holds no code of its own. Each feature re-exports one library
// crate under a short name, and no feature is on by default:
//
// ```toml
// verilith = { version = "0.1", features = ["json", "zlib"] }
// ```
//
// gives `verilith::json` and `verilith::zlib`. Depending on `verilith-json`
// directly is the same code with a shorter dependency list.
#![no_std]

/// `verilith-archive`: zip and tar readers behind libarchive's read API.
#[cfg(feature = "archive")]
pub use verilith_archive as archive;
/// `verilith-brotli`: Brotli.
#[cfg(feature = "brotli")]
pub use verilith_brotli as brotli;
/// `verilith-core`: shared verified building blocks (bit readers, Huffman tables, CRC-32, UTF-8).
#[cfg(feature = "core")]
pub use verilith_core as core;
/// `verilith-dns`: DNS message parser and serializer.
#[cfg(feature = "dns")]
pub use verilith_dns as dns;
/// `verilith-font`: font sanitizer (OpenType, WOFF, WOFF2).
#[cfg(feature = "font")]
pub use verilith_font as font;
/// `verilith-gif`: GIF decoder.
#[cfg(feature = "gif")]
pub use verilith_gif as gif;
/// `verilith-hpack`: HPACK header compression.
#[cfg(feature = "hpack")]
pub use verilith_hpack as hpack;
/// `verilith-http`: HTTP/1 parser.
#[cfg(feature = "http")]
pub use verilith_http as http;
/// `verilith-jpeg`: JPEG decoder.
#[cfg(feature = "jpeg")]
pub use verilith_jpeg as jpeg;
/// `verilith-json`: JSON parser.
#[cfg(feature = "json")]
pub use verilith_json as json;
/// `verilith-lz4`: LZ4.
#[cfg(feature = "lz4")]
pub use verilith_lz4 as lz4;
/// `verilith-png`: PNG decoder.
#[cfg(feature = "png")]
pub use verilith_png as png;
/// `verilith-quic`: the QUIC wire format and transport state machines.
#[cfg(feature = "quic")]
pub use verilith_quic as quic;
/// `verilith-regex`: regular expressions.
#[cfg(feature = "regex")]
pub use verilith_regex as regex;
/// `verilith-sha2`: SHA-2 (SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/t).
#[cfg(feature = "sha2")]
pub use verilith_sha2 as sha2;
/// `verilith-simd`: verified SIMD kernels.
#[cfg(feature = "simd")]
pub use verilith_simd as simd;
/// `verilith-snappy`: Snappy.
#[cfg(feature = "snappy")]
pub use verilith_snappy as snappy;
/// `verilith-sync`: queues, channels and locks.
#[cfg(feature = "sync")]
pub use verilith_sync as sync;
/// `verilith-text`: UTF-8/16, base64, Unicode and IDNA.
#[cfg(feature = "text")]
pub use verilith_text as text;
/// `verilith-tiff`: TIFF decoder.
#[cfg(feature = "tiff")]
pub use verilith_tiff as tiff;
/// `verilith-url`: WHATWG URL parser.
#[cfg(feature = "url")]
pub use verilith_url as url;
/// `verilith-wasm`: WebAssembly interpreter.
#[cfg(feature = "wasm")]
pub use verilith_wasm as wasm;
/// `verilith-webp`: WebP decoder.
#[cfg(feature = "webp")]
pub use verilith_webp as webp;
/// `verilith-x509`: X.509 certificate parser.
#[cfg(feature = "x509")]
pub use verilith_x509 as x509;
/// `verilith-xml`: XML 1.0 parser.
#[cfg(feature = "xml")]
pub use verilith_xml as xml;
/// `verilith-xxhash`: XXH32 and XXH64.
#[cfg(feature = "xxhash")]
pub use verilith_xxhash as xxhash;
/// `verilith-zlib`: zlib, gzip and DEFLATE.
#[cfg(feature = "zlib")]
pub use verilith_zlib as zlib;
/// `verilith-zstd`: Zstandard decoder.
#[cfg(feature = "zstd")]
pub use verilith_zstd as zstd;

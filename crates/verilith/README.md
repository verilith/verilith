# verilith

One crate that re-exports every Verilith library behind a feature. It holds
no code of its own, and no feature is on by default.

```toml
[dependencies]
verilith = { version = "0.1", features = ["json", "zlib"] }
```

```rust,ignore
use verilith::json;
use verilith::zlib;
```

Each library is verified and versioned in its own crate. If you want the
shortest dependency list, depend on that crate directly.

| Feature | Module | Crate | What it is |
|---|---|---|---|
| `archive` | `verilith::archive` | [`verilith-archive`](https://github.com/verilith/verilith/tree/main/crates/archive) | zip and tar readers behind libarchive's read API |
| `brotli` | `verilith::brotli` | [`verilith-brotli`](https://github.com/verilith/verilith/tree/main/crates/brotli) | Brotli |
| `core` | `verilith::core` | [`verilith-core`](https://github.com/verilith/verilith/tree/main/crates/core) | shared verified building blocks (bit readers, Huffman tables, CRC-32, UTF-8) |
| `dns` | `verilith::dns` | [`verilith-dns`](https://github.com/verilith/verilith/tree/main/crates/dns) | DNS message parser and serializer |
| `font` | `verilith::font` | [`verilith-font`](https://github.com/verilith/verilith/tree/main/crates/font) | font sanitizer (OpenType, WOFF, WOFF2) |
| `gif` | `verilith::gif` | [`verilith-gif`](https://github.com/verilith/verilith/tree/main/crates/gif) | GIF decoder |
| `h2` | `verilith::h2` | [`verilith-h2`](https://github.com/verilith/verilith/tree/main/crates/h2) | HTTP/2 frames |
| `hpack` | `verilith::hpack` | [`verilith-hpack`](https://github.com/verilith/verilith/tree/main/crates/hpack) | HPACK header compression |
| `http` | `verilith::http` | [`verilith-http`](https://github.com/verilith/verilith/tree/main/crates/http) | HTTP/1 parser |
| `jpeg` | `verilith::jpeg` | [`verilith-jpeg`](https://github.com/verilith/verilith/tree/main/crates/jpeg) | JPEG decoder |
| `json` | `verilith::json` | [`verilith-json`](https://github.com/verilith/verilith/tree/main/crates/json) | JSON parser |
| `lz4` | `verilith::lz4` | [`verilith-lz4`](https://github.com/verilith/verilith/tree/main/crates/lz4) | LZ4 |
| `png` | `verilith::png` | [`verilith-png`](https://github.com/verilith/verilith/tree/main/crates/png) | PNG decoder |
| `regex` | `verilith::regex` | [`verilith-regex`](https://github.com/verilith/verilith/tree/main/crates/regex) | regular expressions |
| `sha2` | `verilith::sha2` | [`verilith-sha2`](https://github.com/verilith/verilith/tree/main/crates/sha2) | SHA-2: SHA-224 to SHA-512 |
| `simd` | `verilith::simd` | [`verilith-simd`](https://github.com/verilith/verilith/tree/main/crates/simd) | verified SIMD kernels |
| `snappy` | `verilith::snappy` | [`verilith-snappy`](https://github.com/verilith/verilith/tree/main/crates/snappy) | Snappy |
| `sync` | `verilith::sync` | [`verilith-sync`](https://github.com/verilith/verilith/tree/main/crates/sync) | queues, channels and locks |
| `text` | `verilith::text` | [`verilith-text`](https://github.com/verilith/verilith/tree/main/crates/text) | UTF-8/16, base64, Unicode and IDNA |
| `tiff` | `verilith::tiff` | [`verilith-tiff`](https://github.com/verilith/verilith/tree/main/crates/tiff) | TIFF decoder |
| `url` | `verilith::url` | [`verilith-url`](https://github.com/verilith/verilith/tree/main/crates/url) | WHATWG URL parser |
| `wasm` | `verilith::wasm` | [`verilith-wasm`](https://github.com/verilith/verilith/tree/main/crates/wasm) | WebAssembly interpreter |
| `webp` | `verilith::webp` | [`verilith-webp`](https://github.com/verilith/verilith/tree/main/crates/webp) | WebP decoder |
| `x509` | `verilith::x509` | [`verilith-x509`](https://github.com/verilith/verilith/tree/main/crates/x509) | X.509 certificate parser |
| `xxhash` | `verilith::xxhash` | [`verilith-xxhash`](https://github.com/verilith/verilith/tree/main/crates/xxhash) | XXH32 and XXH64 |
| `zlib` | `verilith::zlib` | [`verilith-zlib`](https://github.com/verilith/verilith/tree/main/crates/zlib) | zlib, gzip and DEFLATE |
| `zstd` | `verilith::zstd` | [`verilith-zstd`](https://github.com/verilith/verilith/tree/main/crates/zstd) | Zstandard decoder |

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/verilith/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/verilith/LICENSE-MIT), at your option.

# verilith

One crate that re-exports every Verilith library behind a feature. It holds
no code of its own, and no feature is on by default.

```toml
[dependencies]
verilith = { version = "0.1", features = ["json", "zlib"] }
```

```rust
use verilith::json;
use verilith::zlib;
```

Each library is verified and versioned in its own crate. If you want the
shortest dependency list, depend on that crate directly.

| Feature | Module | Crate | What it is |
|---|---|---|---|
| `archive` | `verilith::archive` | [`verilith-archive`](../archive) | zip and tar readers behind libarchive's read API |
| `brotli` | `verilith::brotli` | [`verilith-brotli`](../brotli) | Brotli |
| `core` | `verilith::core` | [`verilith-core`](../core) | shared verified building blocks (bit readers, Huffman tables, CRC-32, UTF-8) |
| `dns` | `verilith::dns` | [`verilith-dns`](../dns) | DNS message parser and serializer |
| `font` | `verilith::font` | [`verilith-font`](../font) | font sanitizer (OpenType, WOFF, WOFF2) |
| `hpack` | `verilith::hpack` | [`verilith-hpack`](../hpack) | HPACK header compression |
| `http` | `verilith::http` | [`verilith-http`](../http) | HTTP/1 parser |
| `jpeg` | `verilith::jpeg` | [`verilith-jpeg`](../jpeg) | JPEG decoder |
| `json` | `verilith::json` | [`verilith-json`](../json) | JSON parser |
| `lz4` | `verilith::lz4` | [`verilith-lz4`](../lz4) | LZ4 |
| `png` | `verilith::png` | [`verilith-png`](../png) | PNG decoder |
| `regex` | `verilith::regex` | [`verilith-regex`](../regex) | regular expressions |
| `sha2` | `verilith::sha2` | [`verilith-sha2`](../sha2) | SHA-2: SHA-224 to SHA-512 |
| `simd` | `verilith::simd` | [`verilith-simd`](../simd) | verified SIMD kernels |
| `snappy` | `verilith::snappy` | [`verilith-snappy`](../snappy) | Snappy |
| `sync` | `verilith::sync` | [`verilith-sync`](../sync) | queues, channels and locks |
| `text` | `verilith::text` | [`verilith-text`](../text) | UTF-8/16, base64, Unicode and IDNA |
| `url` | `verilith::url` | [`verilith-url`](../url) | WHATWG URL parser |
| `wasm` | `verilith::wasm` | [`verilith-wasm`](../wasm) | WebAssembly interpreter |
| `webp` | `verilith::webp` | [`verilith-webp`](../webp) | WebP decoder |
| `x509` | `verilith::x509` | [`verilith-x509`](../x509) | X.509 certificate parser |
| `xxhash` | `verilith::xxhash` | [`verilith-xxhash`](../xxhash) | XXH32 and XXH64 |
| `zlib` | `verilith::zlib` | [`verilith-zlib`](../zlib) | zlib, gzip and DEFLATE |
| `zstd` | `verilith::zstd` | [`verilith-zstd`](../zstd) | Zstandard decoder |

## License

Licensed under either of the [Apache License, Version 2.0](LICENSE-APACHE)
or the [MIT license](LICENSE-MIT), at your option.

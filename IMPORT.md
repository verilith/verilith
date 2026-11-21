# Where this repository came from

Verilith began as 24 separate repositories under
[verified-foundations](https://github.com/verified-foundations). They were
brought together here on 2026-11-21 without their git history: each
directory below is the `main` branch of its old repository at the commit
shown.

Benchmark records and write-ups made before the move name those old commits.
To find the code a record measured, look the commit up in the old repository;
to compare it with the code here, start from the import commit in this table.

| Old repository | Imported commit | Committed | Now at | Crate |
|---|---|---|---|---|
| [varchive](https://github.com/verified-foundations/varchive) | `091ed4b58f8ce8d409e7abbf71756253ba7a7608` | 2026-11-20 | `crates/archive/` | `verilith-archive` |
| [vbench](https://github.com/verified-foundations/vbench) | `6760af8c5d02e0319d42e0841928d40c6b95b7e8` | 2026-11-20 | `bench/` | not a crate |
| [vbind](https://github.com/verified-foundations/vbind) | `7bf818fc1f97be8ae8caa54a1c65bbd3a24e0f82` | 2026-11-08 | `crates/bind/` | `verilith-bind` |
| [vbrotli](https://github.com/verified-foundations/vbrotli) | `e03781caf19b7f1145fb1b90f9c3d2d7d5b9961d` | 2026-11-19 | `crates/brotli/` | `verilith-brotli` |
| [vcore](https://github.com/verified-foundations/vcore) | `9b4f0508ad1392e750adcb91384115ff501302fc` | 2026-11-20 | `crates/core/` | `verilith-core` |
| [vdns](https://github.com/verified-foundations/vdns) | `2f63df7ef0188f3486a9e7200987062f6306ccf5` | 2026-11-20 | `crates/dns/` | `verilith-dns` |
| [vfont](https://github.com/verified-foundations/vfont) | `4b85a8daaaa4524c47eb681bb3305b597c31f033` | 2026-11-20 | `crates/font/` | `verilith-font` |
| [vhpack](https://github.com/verified-foundations/vhpack) | `f57da153170055f28252ae80964158199ef41364` | 2026-11-18 | `crates/hpack/` | `verilith-hpack` |
| [vhttp](https://github.com/verified-foundations/vhttp) | `f0493a8397a3f6eb56e4ab44456cd5244385cf91` | 2026-11-20 | `crates/http/` | `verilith-http` |
| [vjpeg](https://github.com/verified-foundations/vjpeg) | `19230a99d2e5ed9b95b8ff3e484026d3c1007c91` | 2026-11-20 | `crates/jpeg/` | `verilith-jpeg` |
| [vjson](https://github.com/verified-foundations/vjson) | `6c5ac8860812a12038702b3a4c480f536a971705` | 2026-11-21 | `crates/json/` | `verilith-json` |
| [vlz4](https://github.com/verified-foundations/vlz4) | `6c14b07ab7ce6541fefe4595e15d4ce1a709f852` | 2026-11-20 | `crates/lz4/` | `verilith-lz4` |
| [vpng](https://github.com/verified-foundations/vpng) | `6ca0241a37f2e3e03443fbdaa16f65cb0688db3b` | 2026-11-18 | `crates/png/` | `verilith-png` |
| [vregex](https://github.com/verified-foundations/vregex) | `938d81c5246f9a1132c80a492d6a5eb74d8e816a` | 2026-11-21 | `crates/regex/` | `verilith-regex` |
| [vsimd](https://github.com/verified-foundations/vsimd) | `ba7dc327e7236b10811d4febe5fa9d0ce5b13a4b` | 2026-11-20 | `crates/simd/` | `verilith-simd` |
| [vsnappy](https://github.com/verified-foundations/vsnappy) | `23cd081c36bcadfd47494a88686bb10db1b6cac3` | 2026-11-20 | `crates/snappy/` | `verilith-snappy` |
| [vsync](https://github.com/verified-foundations/vsync) | `5f8235599a8c3c1038dbcb536554ab84f2f89d20` | 2026-11-18 | `crates/sync/` | `verilith-sync` |
| [vtext](https://github.com/verified-foundations/vtext) | `8da6a5e53fd55bcece8d2466dce83ae06fc31a55` | 2026-11-09 | `crates/text/` | `verilith-text` |
| [vurl](https://github.com/verified-foundations/vurl) | `c5a8568be951595ea2eacbd84d5a91b8f03d4994` | 2026-11-18 | `crates/url/` | `verilith-url` |
| [vwasm](https://github.com/verified-foundations/vwasm) | `cee8bb4e3bb22e84f1cc7d37223c510b47cef0d5` | 2026-11-10 | `crates/wasm/` | `verilith-wasm` |
| [vwebp](https://github.com/verified-foundations/vwebp) | `ccc9ddec94d9fce4a62115fb122291caf4a1eee9` | 2026-11-19 | `crates/webp/` | `verilith-webp` |
| [vx509](https://github.com/verified-foundations/vx509) | `d2c9f7168322020153489afb24da20f4953a3175` | 2026-11-20 | `crates/x509/` | `verilith-x509` |
| [vzlib](https://github.com/verified-foundations/vzlib) | `6c2df2bcf7a5f14fc420dbddc95ede7637370bda` | 2026-11-20 | `crates/zlib/` | `verilith-zlib` |
| [vzstd](https://github.com/verified-foundations/vzstd) | `0103d4d78324e711edd7887c7e9963f768e9855f` | 2026-11-20 | `crates/zstd/` | `verilith-zstd` |

## What changed in the move

The code is the same. These things are different:

- **Names.** Each crate is `verilith-<name>` (the library `verilith_<name>`
  in Rust), so the static library a crate builds is `libverilith_<name>.a`.
  C headers, C symbols and the names of example and benchmark programs are
  as they were (`vjson.h`, `vjson_parse`, `vpngcat`).
- **Dependencies between our crates** are path dependencies. Before, each
  repository pinned a commit of the others, and the pins had drifted: the
  table below lists the commit each crate was built against before the move.
  Every crate now builds against the code in this repository.
- **One Verus version**, pinned in the workspace `Cargo.toml` and
  `scripts/verus-version`. All 24 repositories already used it.
- **Build profiles** are set once in the workspace `Cargo.toml`. The three
  release profiles there reproduce what each repository had, and
  `scripts/profile <crate>` says which one a crate uses.
- **Build output** goes to the workspace's `target/`, so paths in scripts
  changed from `target/release/libvjson.a` to
  `../../target/release-abort/libverilith_json.a` and the like.

## Dependency pins before the move

| Crate | Depended on | At commit | Imported commit of that dependency |
|---|---|---|---|
| `verilith-archive` | `verilith-core` | `c7671c3702bb` | `9b4f0508ad13` |
| `verilith-archive` | `verilith-zlib` | `73bf86bb44b7` | `6c2df2bcf7a5` |
| `verilith-archive` | `verilith-zstd` | `0103d4d78324` | same |
| `verilith-brotli` | `verilith-core` | `c0f5ae28bb94` | `9b4f0508ad13` |
| `verilith-dns` | `verilith-core` | `1361d672123a` | `9b4f0508ad13` |
| `verilith-font` | `verilith-zlib` | `2ae44b8e036f` | `6c2df2bcf7a5` |
| `verilith-font` | `verilith-brotli` | `875eab8400b2` | `e03781caf19b` |
| `verilith-hpack` | `verilith-core` | `9242864fa548` | `9b4f0508ad13` |
| `verilith-http` | `verilith-core` | `9242864fa548` | `9b4f0508ad13` |
| `verilith-http` | `verilith-simd` | `aac2be4d6de9` | `ba7dc327e723` |
| `verilith-jpeg` | `verilith-simd` | `ba7dc327e723` | same |
| `verilith-json` | `verilith-core` | `9242864fa548` | `9b4f0508ad13` |
| `verilith-json` | `verilith-simd` | `d35b6dfd1a43` | `ba7dc327e723` |
| `verilith-lz4` | `verilith-core` | `14f50ca8d643` | `9b4f0508ad13` |
| `verilith-png` | `verilith-zlib` | `f3014dda02e8` | `6c2df2bcf7a5` |
| `verilith-regex` | `verilith-text` | `8da6a5e53fd5` | same |
| `verilith-regex` | `verilith-simd` | `aac2be4d6de9` | `ba7dc327e723` |
| `verilith-regex` | `verilith-core` | `9242864fa548` | `9b4f0508ad13` |
| `verilith-snappy` | `verilith-core` | `9b4f0508ad13` | same |
| `verilith-text` | `verilith-core` | `9242864fa548` | `9b4f0508ad13` |
| `verilith-text` | `verilith-simd` | `aac2be4d6de9` | `ba7dc327e723` |
| `verilith-url` | `verilith-core` | `9242864fa548` | `9b4f0508ad13` |
| `verilith-url` | `verilith-simd` | `aac2be4d6de9` | `ba7dc327e723` |
| `verilith-url` | `verilith-text` | `8da6a5e53fd5` | same |
| `verilith-webp` | `verilith-core` | `9242864fa548` | `9b4f0508ad13` |
| `verilith-webp` | `verilith-simd` | `acbeab534827` | `ba7dc327e723` |
| `verilith-zlib` | `verilith-core` | `c7671c3702bb` | `9b4f0508ad13` |
| `verilith-zstd` | `verilith-core` | `c7671c3702bb` | `9b4f0508ad13` |

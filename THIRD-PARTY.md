# Third-party material

Verilith's own code is under the MIT licence ([LICENSE-MIT](LICENSE-MIT)) or
the Apache License 2.0 ([LICENSE-APACHE](LICENSE-APACHE)), at your option. The
files below come from other projects and stay under those projects'
licences. Nothing here is linked into a crate's verified code except the
generated tables and the Brotli dictionary, as noted.

| Where | What | From | Licence |
|---|---|---|---|
| `crates/brotli/src/dictionary.bin`, `crates/brotli/tests/data/` | The Brotli static dictionary (compiled into the library) and test vectors | [google/brotli](https://github.com/google/brotli) | MIT, [LICENSE-brotli](crates/brotli/LICENSE-brotli) |
| `crates/dns/fuzz/seeds/` | Fuzzing seed inputs | [c-ares](https://github.com/c-ares/c-ares) `test/fuzzinput` | MIT, [LICENSE-c-ares](crates/dns/LICENSE-c-ares) |
| `crates/dns/cares/c-ares-use-vdns.patch` | A patch to c-ares, with lines of its source as context | [c-ares](https://github.com/c-ares/c-ares) | MIT, [LICENSE-c-ares](crates/dns/LICENSE-c-ares) |
| `crates/http/compat/llhttp/include/llhttp.h`, `crates/http/compat/llhttp/src/` | llhttp's public header and its API layer (`api.c`, `http.c`, `lenient.c`) | [nodejs/llhttp](https://github.com/nodejs/llhttp) 9.4.3 | MIT, [LICENSE-llhttp](crates/http/compat/llhttp/LICENSE-llhttp) |
| `crates/json/include/cJSON.h`, `crates/json/tests/c/cjson_tests/common.h` | cJSON's public header and a test helper; the tree-building functions in `crates/json/src/ffi.rs` are ported from cJSON 1.7.19 | [DaveGamble/cJSON](https://github.com/DaveGamble/cJSON) | MIT, notice at the top of each header |
| `crates/regex/src/tables.rs` | Unicode tables generated from RE2's (compiled into the library) | [google/re2](https://github.com/google/re2) | BSD-3-Clause, [LICENSE-re2](crates/regex/LICENSE-re2) |
| `crates/text/tests/data/`, `crates/text/src/unicode/tables.rs`, `crates/text/src/idna/tables.rs` | Unicode Character Database and IDNA files, and the tables generated from them (compiled into the library) | [Unicode, Inc.](https://www.unicode.org/) | Unicode-3.0, [LICENSE-UNICODE](crates/text/LICENSE-UNICODE) |
| `crates/url/tests/data/` | URL test data | [web-platform-tests](https://github.com/web-platform-tests/wpt) | BSD-3-Clause, [LICENSE-wpt](crates/url/LICENSE-wpt) |
| `crates/wasm/include/wasm.h`, `crates/wasm/examples/c/` | The WebAssembly C API header and its examples | [WebAssembly/wasm-c-api](https://github.com/WebAssembly/wasm-c-api) | Apache-2.0, [LICENSE-wasm-c-api](crates/wasm/LICENSE-wasm-c-api) |
| `crates/x509/mbedtls/mbedtls-use-vx509.patch` | A patch to mbedTLS, with lines of its source as context | [Mbed-TLS/mbedtls](https://github.com/Mbed-TLS/mbedtls) 3.6.4 | Apache-2.0 OR GPL-2.0-or-later (the patch's own additions are MIT) |
| `crates/x509/bench/data/`, `crates/x509/fuzz/seeds/` | Three public certificates: ISRG Root X1 and X2, and a leaf certificate issued to www.cryptography.io | Their issuers | Published certificates |

Headers that give one of our libraries another library's API
(`crates/bind/include/ada.h`, `simdjson.h` and `simdutf.h`,
`crates/font/include/opentype-sanitiser.h`,
`crates/http/include/picohttpparser.h`, `crates/text/include/vtext_icu.h`)
were written for this project. They declare the same names so that callers
compile unchanged, and contain none of the original's code.

## Fetched, not included

The benchmark harness and some test scripts download other projects at
pinned versions and build or read them locally. None of it is in this
repository. `bench/pins.sh` has the full list with versions: the original
libraries we compare against (zlib, c-ares, llhttp, picohttpparser, ada,
simdjson, cJSON, mbedTLS, libpng, libwebp, brotli, libjpeg-turbo, lz4,
snappy, libarchive, Verdict, OTS, woff2, RE2, Abseil, cre2, expat,
libxml2), Node.js, and the data sets (the Silesia corpus, ada's URL data
set, the Kodak image suite, certifi's root certificates, simdjson's
example files, Source Serif and roxmltree's benchmark files). The XML
tests also download the W3C XML Conformance Test Suite
(`crates/xml/ci.sh`).

`third-party/` is not third-party code: it holds a generated Buck2 file
that names the crates.io packages the proofs build against.

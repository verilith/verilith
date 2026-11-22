# verilith-bind

One native library for the Verilith parsers, and the bindings
built on it: drop-in C++ headers for ada, simdjson and simdutf, a Python
module and a Node.js addon. Today it covers [verilith-url](../url),
[verilith-json](../json) and [verilith-text](../text), and, as optional features,
[verilith-http](../http) (llhttp's C API) and [verilith-dns](../dns) (c-ares's DNS
message parser).

Every binding is a thin, unverified type adapter. Parsing always happens in
the verified Rust code, so each language gets the same proven core.

```
        verilith-url (verified)   verilith-json (verified)   verilith-text (verified)
                    \            |            /
                     libvbind (Rust)          one static library, one copy of std
                    /       |         \
 C ABI (vbind.h, vtext_utf.h)  PyO3 module   Node-API addon
            |
   C++ headers: ada.h, simdjson.h, simdutf.h   <- Node.js builds against these unchanged
```

## Why one library

Each Rust static library carries its own copy of the Rust standard library,
and linking two of them into one program fails with duplicate symbols. So a
program that wants verilith-url and verilith-json (Node wants both) links `libverilith_bind.a`,
which holds both. Adding a library (verilith-http and verilith-dns so far) means adding a
feature and a dependency here, not a new library.

| Feature | Default | What it adds |
|---|---|---|
| `url` | yes | verilith-url's C API (`vurl_*`) |
| `json` | yes | `vbind_json_*` over verilith-json |
| `text` | yes | verilith-text's `vtext_*` |
| `http` | no | llhttp's whole C API (`llhttp_*`): llhttp's own `api.c` and `http.c`, compiled by `build.rs` from verilith-http's `compat/llhttp`, over verilith-http's verified parser (`llhttp__internal_execute`) |
| `dns` | no | `ares_dns_parse`, `ares_expand_name` and `vdns_ares_dns_write_buf`, for a c-ares patched with `vdns/cares/c-ares-use-vdns.patch`. They call c-ares's record setters and getters, so the program must also link that patched c-ares |

## Layout

| Path | What | Lines |
|---|---|---|
| `src/lib.rs` | Re-exports the libraries' existing C APIs (`vurl_*`, `vtext_*`, llhttp's, verilith-dns's c-ares functions) | 68 |
| `build.rs` | Compiles llhttp's `api.c` and `http.c` for the `http` feature | 19 |
| `src/json.rs` | C API over verilith-json documents (`vbind_json_*`): the verified parser's token tape, plus string, number and raw-text accessors | 320 |
| `include/vbind.h` | The C header for both | 180 |
| `include/ada.h` | ada 2.9's C++ API over verilith-url | 550 |
| `include/simdjson.h` | simdjson's On-Demand C++ API over verilith-json | 830 |
| `include/vtext_utf.h` | verilith-text's transcoding and base64 C API (a copy of verilith-text's) | 70 |
| `include/simdutf.h` | simdutf 6.4's C++ API over verilith-text | 300 |
| `python/` | PyO3 module: `vbind.URL`, `vbind.loads` | 210 |
| `node/` | Node-API addon (napi-rs): `URL`, `parseJSON` | 190 |

The library repos are untouched: verilith-bind depends on them as sibling checkouts
(`../url`, `../json`, `../text`, `../http`, `../dns`).

## C++: ada, simdjson and simdutf drop-ins

`include/ada.h`, `include/simdjson.h` and `include/simdutf.h` replace the
single-header ada, simdjson and simdutf for the API surface Node.js 22 uses:

* **ada**: `ada::parse<url_aggregator>` and `parse<url>` (with or without a
  base), every getter and setter, `get_components`, `type`, `can_parse`,
  `href_from_file`, `ada::idna::to_ascii/to_unicode`,
  `ada::unicode::percent_decode`, and the public fields of `ada::url`.
* **simdjson**: `ondemand::parser::iterate`, `document`, `value`, `object`,
  `array`, `field`, `raw_json_string`, `simdjson_result` chaining, `pad`,
  `padded_string(_view)`, and every `error_code` with simdjson's messages.
* **simdutf**: `validate_utf8(_with_errors)`, `validate_ascii(_with_errors)`,
  the length functions, UTF-8/UTF-16(LE)/Latin-1 conversions including
  `convert_latin1_to_utf8_safe` and `convert_utf8_to_latin1_with_errors`,
  and base64 (`binary_to_base64`, `base64_to_binary(_safe)` for `char` and
  `char16_t`, `maximal_binary_length_from_base64`), with `result`,
  `error_code`, `base64_options` and `SIMDUTF_VERSION` "6.4.2". Only the
  `loose` last-chunk mode is supported, which is all Node uses.
  `tests/cpp/run.sh` runs every one of these through real simdutf 6.4.2
  and verilith-bind on 50,000 seeded cases (1.4 million calls): all results match
  except 255 safe base64 decodes into a buffer smaller than the maximal
  length, where simdutf fails on valid input with whitespace after the
  padding and verilith-text decodes it (Node falls back to its own decoder on any
  failure, so both give the same bytes in Node).

Link with `-lverilith_bind -lpthread -ldl -lm`.

### Node.js, built against them

Node's `configure` already supports system copies of ada, simdjson,
simdutf and llhttp, so those need no Node patch. c-ares is different: verilith-dns
replaces only its message parser, so the script applies verilith-dns's c-ares patch
to Node's bundled `deps/cares` and defines `CARES_WITH_VDNS` there
(`VBIND_DNS=0` skips this):

```sh
scripts/build-node.sh v22.23.4 parallel sequential es-module
```

runs, in effect,

```sh
./configure --shared-ada --shared-ada-includes=vbind/include --shared-ada-libname=verilith-bind ... \
            --shared-simdjson --shared-simdjson-includes=vbind/include --shared-simdjson-libname=verilith-bind ... \
            --shared-simdutf --shared-simdutf-includes=vbind/include --shared-simdutf-libname=verilith-bind ... \
            --shared-http-parser --shared-http-parser-includes=vhttp/compat/llhttp/include \
                                 --shared-http-parser-libname=verilith-bind ...
```

The resulting binary has no ada, simdjson or simdutf code in it (`nm` finds
the `vurl_*`, `vbind_json_*` and `vtext_*` symbols and no `ada::`,
`simdjson::` or `simdutf::` ones). Node's own llhttp is not built or linked
(`llhttp__internal_execute` sits among verilith-http's Rust symbols), and
`ares_dns_parse` and `ares_expand_name` are verilith-dns's: c-ares's own record
parser is compiled out. `process.versions.simdutf` still reads
6.4.2, the API version the header implements.

**Node's tests** (v22.23.4, suites `parallel sequential es-module wpt
module-hooks message sea sqlite`, 4,284 tests), run on this build and on
the official v22.23.4 binary:

| | pass | fail |
|---|---|---|
| Official binary | 4,281 | 3 |
| Built with verilith-bind (ada, simdjson) | 4,281 | 3 |
| Built with verilith-bind (ada, simdjson, simdutf) | 4,281 | 3 |
| Built with verilith-bind (ada, simdjson, simdutf, llhttp, c-ares parser) | 4,274 | 10 |

Two failures are common to both (an inspector network test and a sqlite
extension test that need things the sandbox lacks). The official binary
also fails `test-process-config`, because its config differs from this
source tree's. Swapping in verilith-text for simdutf changed no result: all of Node's Buffer,
base64, `atob`, TextDecoder and string-decoder tests pass. The verilith-bind build
fails one test the official binary passes,
`test-whatwg-url-custom-parsing`, for the same reason as the WPT
differences below.

Swapping in verilith-dns for c-ares's parser also changed no result: every
`test-dns*` and `test-c-ares` test passes. Swapping in verilith-http for llhttp
adds seven failures, all messages verilith-http rejects on purpose and lists in
its README: `--insecure-http-parser` leniency
(`test-http-insecure-parser`, `test-http-insecure-parser-per-stream`,
`test-https-insecure-parse-per-stream`), obs-fold
(`test-http-multi-line-headers`), HTTP/0.9 (`test-http-response-no-headers`,
`test-https-foafssl`), and `Transfer-Encoding: chunkedchunked` rejected
before the request reaches the application
(`test-http-transfer-encoding-repeated-chunked`). Build with `VBIND_HTTP=0`
to keep Node's llhttp.

`wpt/test-url` is skipped by Node whenever ada is a shared library ("Different
versions of Ada affect the WPT tests"). Forced to run, 24 of its 30 files
pass, and the failures are all differences between verilith-url and the URL
Standard as of Node 22's WPT snapshot:

* **ASCII `xn--` labels are not validated.** verilith-url's model treats an
  all-ASCII domain as already ASCII and never runs UTS #46 on it, so
  labels such as `xn--pokxncvks` or `xn--` that are not valid Punycode are
  accepted. This accounts for 593 of the 644 `IdnaTestV2` failures, 21 of
  33 in `toascii`, and the `test-whatwg-url-custom-parsing` failure. Newer
  WPT data in verilith-url's own tests accepts some of these, so this needs checking
  against the current Standard in verilith-url itself.
* **Unicode version.** 51 `IdnaTestV2` and 12 `toascii` cases differ in
  which code points UTS #46 maps or disallows (verilith-url uses the `idna` crate's
  tables, Node's WPT copy expects Unicode 15.1).
* **Newer spec behaviour** that Node 22's snapshot predates: `^` is
  percent-encoded in paths, and trailing spaces in opaque paths are kept as
  `%20` (13 cases across `url-constructor`, `url-setters` and
  `urlsearchparams-delete`).

### Differential tests

`tests/cpp/run.sh` compiles the same programs against the real ada 2.9.2
and simdjson 4.5.0 (fetched from their releases) and against these
headers, then compares the output:

* **JSON**: every valid JSON file gives identical results through three
  access patterns (lookups by name, an in-order pass with `raw_json()`, and a
  full tree walk), on all of Node's test fixtures and verilith-json's corpus. The
  only differences are on invalid JSON: simdjson validates lazily and can
  read the first fields of a document that is broken further on; verilith-json
  checks the whole text first, so `iterate()` fails. Node treats both as an
  invalid file.
* **URL**: on WPT's `urltestdata.json` with every setter applied, the
  differences are the spec-version ones above, plus setter **return
  values**: ada returns `true` from a setter that the Standard says to
  ignore (for example a non-numeric port), verilith-url returns `false`. The URL is
  unchanged either way, and Node only uses the return value to decide
  whether to refresh a URL that did not change.

### Speed in Node

Node's own `benchmark/url` runs are roughly even with ada, with large swings
both ways per input (`canParse` on long URLs is about half ada's speed; on
`javascript:` URLs about twice). The shim allocates a handle per parse
through the C ABI; a C++ API that parses into caller-owned storage would
remove that. Starting `npm --version`, which reads package.json files through
the simdjson header, took 123 ms with verilith-bind and 119 to 131 ms with the
official binary (30 runs each).

## Python

```python
import verilith-bind
u = verilith-bind.URL("../d?x", "https://example.org/a/b/c")   # ada_url's URL shape
u.href, u.hostname, u.search; u.port = "8080"
verilith-bind.URL.can_parse("/x", "http://a")
vbind.loads('{"a": [1, 2.5, null]}')                   # json.loads' output types
```

Errors raise `ValueError`. Build with `maturin build` (in `python/`), or run
`scripts/test-python.sh`, which builds the module and runs its tests,
including all of WPT's `urltestdata.json`.

## Node.js addon

```js
const verilith-bind = require('./vbind.node');
new verilith-bind.URL('../d', 'https://example.org/a/b/c').href;
verilith-bind.URL.canParse('/x', 'http://a');
vbind.parseJSON('{"a":1}');   // SyntaxError on invalid JSON, like JSON.parse
```

`scripts/test-node.sh` builds it and checks it against the built-in `URL` and
`JSON.parse`. The addon is for runtimes that ship their own URL and JSON
(Bun, Electron, older Node) or that want the verified parser explicitly;
Node built as above already uses verilith-url and verilith-json inside `URL` and module
loading.

## Adding a library

1. Add it as an optional dependency and feature in `Cargo.toml`.
2. If it already has a C API (verilith-http's llhttp ABI, verilith-zlib's zlib ABI, verilith-dns's
   c-ares ABI), add a `#[used]` reference in `src/lib.rs` so the static
   library keeps it, and declare it in `include/vbind.h`.
3. If the target's API is C++, write a header in `include/` over the C API.
4. Add Python and Node wrappers over the Rust API, converting types only.

## What is not verified

Everything in this repository. The trusted additions are the C ABI glue
(`src/json.rs`), the three headers, and the two language modules: about
2,300 lines that convert types and never make a parsing decision.

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
                     libverilith_bind (Rust)        one static library, one copy of std
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
| `dns` | no | `ares_dns_parse`, `ares_expand_name` and `vdns_ares_dns_write_buf`, for a c-ares patched with `crates/dns/cares/c-ares-use-vdns.patch`. They call c-ares's record setters and getters, so the program must also link that patched c-ares |

## Layout

| Path | What | Lines |
|---|---|---|
| `src/lib.rs` | Re-exports the libraries' existing C APIs (`vurl_*`, `vtext_*`, llhttp's, verilith-dns's c-ares functions) | 68 |
| `build.rs` | Compiles llhttp's `api.c` and `http.c` for the `http` feature | 19 |
| `src/json.rs` | C API over verilith-json documents (`vbind_json_*`): the verified parser's token tape, plus string, number and raw-text accessors | 320 |
| `include/vbind.h` | The C header for both | 180 |
| `include/ada.h` | ada 4.0's C++ API over verilith-url | 890 |
| `include/ada_url_pattern.h` | ada 4.0's URLPattern, copied from ada by `scripts/vendor-ada-url-pattern.py` | 7,660 |
| `include/simdjson.h` | simdjson's On-Demand C++ API over verilith-json | 830 |
| `include/vtext_utf.h` | verilith-text's transcoding and base64 C API (a copy of verilith-text's) | 90 |
| `include/simdutf.h` | simdutf 7.7's C++ API over verilith-text | 470 |
| `python/` | PyO3 module: `vbind.URL`, `vbind.loads` | 210 |
| `node/` | Node-API addon (napi-rs): `URL`, `parseJSON` | 190 |

The library repos are untouched: verilith-bind depends on them as sibling checkouts
(`../url`, `../json`, `../text`, `../http`, `../dns`).

## C++: ada, simdjson and simdutf drop-ins

`include/ada.h`, `include/simdjson.h` and `include/simdutf.h` replace the
single-header ada, simdjson and simdutf for the API surface Node.js 26 uses
(ada 4.0.0, simdjson 5.0.3 and simdutf 7.7.0, the versions Node 26.13.1
bundles):

* **ada**: `ada::parse<url_aggregator>` and `parse<url>` (with or without a
  base), every getter and setter, `get_components`, `type`, `can_parse`,
  `href_from_file`, `ada::idna::to_ascii/to_unicode`,
  `ada::unicode::percent_decode`, and the public fields of `ada::url`.
* **ada's URLPattern**: `ada::url_pattern`, `ada::parse_url_pattern` and
  the types around them, which Node's `URLPattern` class is built on. This
  is ada's own code (`include/ada_url_pattern.h`, about 4,500 lines of ada
  and the `tl::expected` it uses): the pattern syntax has no verified
  parser here yet, so the header keeps ada's pattern compiler and matcher
  unchanged and puts verilith-url under it. Every URL a pattern parses or
  canonicalizes goes through `ada::parse` and the setters above.
  `scripts/vendor-ada-url-pattern.py` writes the header from an ada
  release, and `tests/cpp/run.sh` checks that it still does.
* **simdjson**: `ondemand::parser::iterate`, `document`, `value`, `object`,
  `array`, `field`, `raw_json_string`, `simdjson_result` chaining, `pad`,
  `padded_string(_view)`, and every `error_code` with simdjson's messages.
* **simdutf**: `validate_utf8(_with_errors)`, `validate_ascii(_with_errors)`,
  `validate_utf16(le)(_with_errors)`, `to_well_formed_utf16`, `find`, the
  length functions (with `utf8_length_from_utf16_with_replacement`),
  UTF-8/UTF-16(LE)/UTF-32/Latin-1 conversions including
  `convert_latin1_to_utf8_safe` and the `_with_errors` forms, and base64:
  `binary_to_base64`, `base64_to_binary(_safe)` for `char` and `char16_t`
  with all three last-chunk modes (`loose`, `strict`,
  `stop_before_partial`) and `decode_up_to_bad_char`, the `atomic_`
  variants V8 uses for shared buffers, and
  `maximal_binary_length_from_base64`, with `result`, `full_result`,
  `error_code`, `base64_options` and `SIMDUTF_VERSION` "7.7.0". Decoding
  valid base64 in the `loose` mode, which is what `Buffer` and `atob` use,
  runs on verilith-text's verified decoder. The strict and partial modes
  and the positions reported for invalid input (what
  `Uint8Array.fromBase64` needs) and the UTF-16 helpers are unverified
  code in verilith-text's C API; see its README.
  `tests/cpp/run.sh` runs every one of these through real simdutf 7.7.0
  and verilith-bind on 50,000 seeded cases (3.6 million calls): all
  results match except 42 invalid base64 texts with a misplaced `=`, where
  both fail after writing the same bytes but simdutf's block decoder
  reports the error one step later than its own scalar decoder does.

Link with `-lverilith_bind -lpthread -ldl -lm`.

### Node.js, built against them

Node's `configure` already supports system copies of ada, simdjson,
simdutf and llhttp, so those need no Node patch. c-ares is different: verilith-dns
replaces only its message parser, so the script applies verilith-dns's c-ares patch
to Node's bundled `deps/cares` and defines `CARES_WITH_VDNS` there
(`VBIND_DNS=0` skips this):

```sh
scripts/build-node.sh v26.13.1 parallel sequential es-module
```

runs, in effect,

```sh
./configure --shared-ada --shared-ada-includes=crates/bind/include --shared-ada-libname=verilith-bind ... \
            --shared-simdjson --shared-simdjson-includes=crates/bind/include --shared-simdjson-libname=verilith-bind ... \
            --shared-simdutf --shared-simdutf-includes=crates/bind/include --shared-simdutf-libname=verilith-bind ... \
            --shared-http-parser --shared-http-parser-includes=crates/http/compat/llhttp/include \
                                 --shared-http-parser-libname=verilith-bind ...
```

The resulting binary has no ada, simdjson or simdutf parsing code in it:
`nm` finds the `vurl_*`, `vbind_json_*` and `vtext_*` symbols, and the only
`ada::` and `simdjson::` symbols are the headers' own inline wrappers and
ada's URLPattern code copied into `ada_url_pattern.h`. Node's own llhttp is
not built or linked (`llhttp__internal_execute` sits among verilith-http's
Rust symbols), and `ares_dns_parse` and `ares_expand_name` are
verilith-dns's: c-ares's own record parser is compiled out.
`process.versions` still reads ada 4.0.0, simdjson 5.0.3 and simdutf
7.7.0, the API versions the headers implement. Node 26 has Rust code of
its own (`deps/crates`, a static library); it links next to
`libverilith_bind.a` without clashing when both are built by the same
`rustc`.

**Node's tests** (v26.13.1, suites `parallel sequential es-module wpt
module-hooks message sea sqlite`), run on this build (ada, simdjson,
simdutf, llhttp and the c-ares parser all swapped) and on the official
v26.13.1 binary:

| | tests | pass | fail |
|---|---|---|---|
| Official binary | 6,833 | 6,828 | 5 |
| Built with verilith-bind | 6,769 | 6,760 | 9 |

The build runs 64 fewer tests because Node skips `wpt/test-url` when ada is
a shared library (see below). Four failures are common to both: two
`test-tls-get-ca-certificates-worker-*` tests and a sqlite extension test
that need things the sandbox lacks, and
`test-fs-rmSync-special-char-additional-error`, which fails on any build
run as root. The official binary also fails `test-process-config`, because
its config differs from this source tree's.

Every URL, URLPattern, Buffer, base64, `atob`, `Uint8Array.fromBase64`,
TextDecoder, string-decoder, DNS and c-ares test passes, and so does
`test-whatwg-url-custom-parsing`, which the Node 22 build failed. The five
failures the official binary does not have are all llhttp's lenient modes,
which verilith-http does not implement (it rejects those messages on purpose
and lists them in its README): `--insecure-http-parser`
(`test-http-insecure-parser`, `test-http-insecure-parser-per-stream`,
`test-https-insecure-parse-per-stream`), obs-fold
(`test-http-multi-line-headers`) and Node 26's `httpValidation: 'relaxed'`
(`test-http-header-value-relaxed`). Build with `VBIND_HTTP=0` to keep
Node's llhttp. The three other HTTP failures the Node 22 build had
(HTTP/0.9 responses and `Transfer-Encoding: chunkedchunked`) pass now.

`wpt/test-url` is skipped by Node whenever ada is a shared library ("Different
versions of Ada affect the WPT tests"). Forced to run, 64 of its 65 files
pass. The one failure is a single `IdnaTestV2` case (2 of its 2,671
subtests), `𾢬。ܩ。쯙5`: U+3E8AC is unassigned in Unicode 17, which Node 26's
WPT copy and ICU use, and is a Small Seal character in Unicode 18, which
verilith-text's UTS #46 tables follow. The ASCII `xn--` and Unicode 15.1
differences the Node 22 build had are gone, since Node 26's WPT data and ada
4 follow the current Standard there too.

### Differential tests

`tests/cpp/run.sh` compiles the same programs against the real ada 4.0.0
and simdjson 5.0.3 (fetched from their releases) and against these
headers, then compares the output:

* **JSON**: every valid JSON file gives identical results through three
  access patterns (lookups by name, an in-order pass with `raw_json()`, and a
  full tree walk), on Node 26's test fixtures, `deps/npm` and
  verilith-json's corpus (539 files, 1,623 reads, 1,581 identical; pass the
  files as arguments, or set `JSON_DIR`). The 42 differences are all on
  invalid JSON: simdjson validates lazily and can read the first fields of
  a document that is broken further on; verilith-json checks the whole text
  first, so `iterate()` fails. Node treats both as an invalid file.
* **URL**: on WPT's `urltestdata.json` with every setter applied (896
  URLs), the URLs themselves agree. The differences are in three places Node
  does not depend on: `get_components()` offsets (ada 4.0.0 reports
  `host_end` one byte short when there is a port, and `username_end` 0 on
  opaque URLs; Node 26 no longer calls it); setter **return values**, where
  ada returns `true` from a setter that the Standard says to ignore (for
  example a non-numeric port) and verilith-url returns `false`, with the URL
  unchanged either way; and the host and pathname setters on `file:` URLs
  with a Windows drive letter, which ada built from its release refuses and
  verilith-url applies. Official Node 26 applies them too
  (`u.pathname = "x"` on `file:///c:/foo/bar.html` gives `file:///x` in
  both).
* **URLPattern**: every case in WPT's `urlpatterntestdata.json` (361) gives
  the same pattern strings, match results and groups through real ada and
  through `ada_url_pattern.h` over verilith-url.
* **simdutf**: see above.

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
import vbind
u = vbind.URL("../d?x", "https://example.org/a/b/c")   # ada_url's URL shape
u.href, u.hostname, u.search; u.port = "8080"
vbind.URL.can_parse("/x", "http://a")
vbind.loads('{"a": [1, 2.5, null]}')                   # json.loads' output types
```

Errors raise `ValueError`. Build with `maturin build` (in `python/`), or run
`scripts/test-python.sh`, which builds the module and runs its tests,
including all of WPT's `urltestdata.json`.

## Node.js addon

```js
const vbind = require('./vbind.node');
new vbind.URL('../d', 'https://example.org/a/b/c').href;
vbind.URL.canParse('/x', 'http://a');
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
3,200 lines that convert types and never make a parsing decision. Two
further pieces do make decisions and are not verified: ada's URLPattern
code in `ada_url_pattern.h` (ada's own, unchanged), and the parts of
verilith-text's C API listed under simdutf above.

## License

Licensed under either of the [Apache License, Version 2.0](LICENSE-APACHE)
or the [MIT license](LICENSE-MIT), at your option.

"""Every comparison vbench runs: ours against the original library.

Each side is (display name, [runner executable in work/build/bin, args...]).
Wherever our library has a C ABI, both sides are the same driver source
linked against a different library, so the library is the only difference.
`data` is the input directory under work/data. `same_output` says whether
both sides must return the same check value; `check` names what the check
value is when the report should show it (compressed or printed sizes).

`api` says which of our APIs a comparison measures, and the two are never
mixed in one number:

  "drop-in"  ours behind the original's API. Both sides are the same caller
             code, so this is what a user gets by relinking, changing
             nothing.
  "native"   the same job done through our own API, against the original
             doing that job through its best API. This is what a caller
             gets after porting to our API, never what a drop-in user gets.

`pair` joins a drop-in and a native comparison that do the same task
against the same original, case by case (cases match on the name after the
first "/"); the report prints those side by side. `task` is that job in
one line, and `note` says where the two sides of a native comparison do
different amounts of work.
"""

COMPARISONS = [
    # zlib's API: vzlib (feature zlib-abi) in place of zlib.
    dict(id="zlib-inflate", suite="zlib", data="zlib", same_output=True, api="drop-in",
         ours=("vzlib", ["zlib-vzlib", "inflate"]), rival=("zlib 1.4", ["zlib-zlib", "inflate"])),
    dict(id="zlib-deflate", suite="zlib", data="zlib", same_output=False, check="compressed bytes", api="drop-in",
         ours=("vzlib", ["zlib-vzlib", "deflate"]), rival=("zlib 1.4", ["zlib-zlib", "deflate"])),
    # c-ares's record API: c-ares with vdns's patch in place of stock c-ares.
    dict(id="dns-parse", suite="dns", data="dns", same_output=True, api="drop-in",
         ours=("c-ares + vdns", ["dns-vdns", "parse"]), rival=("c-ares", ["dns-cares", "parse"])),
    dict(id="dns-write", suite="dns", data="dns", same_output=False, check="bytes written", api="drop-in",
         ours=("c-ares + vdns", ["dns-vdns", "write"]), rival=("c-ares", ["dns-cares", "write"])),
    # Parse and read every record, the task of the native comparison below.
    dict(id="dns-read", suite="dns", data="dns", same_output=True, api="drop-in", pair="dns-cares",
         task="parse a response, read every question and record (name, type, class, TTL, RDATA fields), free it",
         ours=("c-ares + vdns", ["dns-vdns", "read"]), rival=("c-ares", ["dns-cares", "read"])),
    dict(id="dns-native", suite="dns", data="dns", same_output=True, api="native", pair="dns-cares",
         task="parse a response, read every question and record (name, type, class, TTL, RDATA fields), free it",
         note="vdns parses into a reused `Message` and decodes each record's RDATA when it is read; c-ares "
              "allocates a record tree on every parse and frees it, which is the only way its API parses. "
              "Names come back in wire form from vdns and as text from c-ares.",
         ours=("vdns (Rust API)", ["dns-native"]), rival=("c-ares", ["dns-cares", "read"])),
    # llhttp's API, as Node drives it: vhttp (llhttp-abi) under llhttp's api.c.
    dict(id="http-llhttp", suite="http", data="http", same_output=True, api="drop-in", pair="http-llhttp",
         task="parse a whole message: target or reason, every header name and value, the body",
         ours=("vhttp", ["http-vhttp"]), rival=("llhttp 9.4.4", ["http-llhttp"])),
    dict(id="http-llhttp-native", suite="http", data="http", same_output=True, api="native", pair="http-llhttp",
         task="parse a whole message: target or reason, every header name and value, the body",
         note="llhttp reports each piece through a callback as it goes and can take the message in pieces; "
              "vhttp's API parses a complete head in one call and returns spans. vhttp's chunked decoder works "
              "in place, so resp-chunked includes a copy of the body into a scratch buffer on our side.",
         ours=("vhttp (Rust API)", ["http-native", "llhttp"]), rival=("llhttp 9.4.4", ["http-llhttp", "read"])),
    # picohttpparser's API: vhttp (phr-abi) in place of picohttpparser.
    dict(id="http-pico", suite="http", data="http", same_output=True, api="drop-in", pair="http-pico",
         task="parse a message head into a reused header array",
         ours=("vhttp", ["pico-vhttp"]), rival=("picohttpparser", ["pico-pico"])),
    dict(id="http-pico-native", suite="http", data="http", same_output=True, api="native", pair="http-pico",
         task="parse a message head into a reused header array",
         note="picohttpparser's API is already flat and copies nothing, so little separates the two columns. "
              "vhttp's own call also works out the body framing (Content-Length, Transfer-Encoding), which "
              "picohttpparser leaves to the caller.",
         ours=("vhttp (Rust API)", ["http-native", "pico"]), rival=("picohttpparser", ["pico-pico"])),
    # ada's C API: vurl (ada-abi) in place of ada.
    dict(id="url-ada", suite="url", data="url", same_output=True, api="drop-in",
         ours=("vurl", ["url-vurl"]), rival=("ada 4.1.1", ["url-ada"])),
    # cJSON's API: vjson (cjson feature) in place of cJSON.
    dict(id="json-cjson-parse", suite="json", data="json", same_output=True, api="drop-in", pair="json-cjson",
         task="parse a document, read every value (numbers as doubles, string and key lengths), free it",
         ours=("vjson", ["cjson-vjson", "parse"]), rival=("cJSON 1.7.19", ["cjson-cjson", "parse"])),
    dict(id="json-cjson-native", suite="json", data="json", same_output=True, api="native", pair="json-cjson",
         task="parse a document, read every value (numbers as doubles, string and key lengths), free it",
         note="vjson parses into a flat index in a reused `Parser`; cJSON allocates a node per value and frees "
              "the tree, which is the only way its API parses.",
         ours=("vjson (Rust API)", ["json-vjson", "cjson-parse"]), rival=("cJSON 1.7.19", ["cjson-cjson", "parse"])),
    dict(id="json-cjson-print", suite="json", data="json", same_output=False, check="printed bytes", api="drop-in",
         ours=("vjson", ["cjson-vjson", "print"]), rival=("cJSON 1.7.19", ["cjson-cjson", "print"])),
    # Native APIs, same work: vjson::Parser against simdjson's DOM parser.
    dict(id="json-simdjson", suite="json", data="json", same_output=True, api="native",
         task="parse a document with a reused parser, read every value",
         ours=("vjson (Rust API)", ["json-vjson"]), rival=("simdjson 5.2.0", ["json-simdjson"])),
    # mbedTLS's certificate API: mbedTLS with vx509's patch in place of stock.
    dict(id="x509-mbedtls", suite="x509", data="x509", same_output=True, api="drop-in",
         ours=("mbedTLS + vx509", ["x509-vx509"]), rival=("mbedTLS 4.3.0", ["x509-mbedtls"])),
    # Parse without copying and read the fields a TLS client reads, the task
    # of the native comparison below.
    dict(id="x509-mbedtls-read", suite="x509", data="x509", same_output=True, api="drop-in", pair="x509-mbedtls",
         task="parse a certificate in place; read serial, issuer, subject, validity, key usage, CA flag, DNS names, EKUs; free it",
         ours=("mbedTLS + vx509", ["x509-vx509", "read"]), rival=("mbedTLS 4.3.0", ["x509-mbedtls", "read"])),
    dict(id="x509-mbedtls-native", suite="x509", data="x509", same_output=True, api="native", pair="x509-mbedtls",
         task="parse a certificate in place; read serial, issuer, subject, validity, key usage, CA flag, DNS names, EKUs; free it",
         note="The two sides do not do the same amount of work, and the difference favours vx509: "
              "`mbedtls_x509_crt_parse_der_nocopy` also decodes the public key into a `mbedtls_pk_context` "
              "(for RSA, two big-number reads and checks) and allocates the name and extension lists, none "
              "of which its API lets a caller skip. vx509 checks the SubjectPublicKeyInfo structure and "
              "returns the key bytes without decoding them. Read this column as an upper bound.",
         ours=("vx509 (Rust API)", ["x509n-vx509", "read"]), rival=("mbedTLS 4.3.0", ["x509-mbedtls", "read"])),
    # Native APIs, same work: vx509::parse against Verdict's parse_x509_der,
    # both verified in Verus. Each parses and checks the whole certificate.
    dict(id="x509-verdict", suite="x509n", data="x509", same_output=True, api="native",
         task="parse and check a whole certificate",
         ours=("vx509 (Rust API)", ["x509n-vx509"]), rival=("Verdict", ["x509n-verdict"])),
    # Decode to RGBA8: vpng's Rust API against libpng (no libpng ABI yet).
    dict(id="png-libpng", suite="png", data="png", same_output=True, api="native",
         task="decode a PNG to RGBA8",
         ours=("vpng (Rust API)", ["png-vpng"]), rival=("libpng 1.6.59", ["png-libpng"])),
    # libwebp's decode API, lossless files: vwebp (webp-abi) in place of libwebp.
    dict(id="webp-lossless", suite="webp", data="webp", same_output=True, api="drop-in",
         ours=("vwebp", ["webp-vwebp"]), rival=("libwebp 1.6.0", ["webp-libwebp"])),
    # The same driver and libraries on lossy (VP8) files.
    dict(id="webp-lossy", suite="webp", data="webp-lossy", same_output=True, api="drop-in",
         ours=("vwebp", ["webp-vwebp"]), rival=("libwebp 1.6.0", ["webp-libwebp"])),
    # libarchive's read API: varchive (libarchive-abi) in place of libarchive.
    dict(id="archive-read", suite="archive", data="archive", same_output=True, api="drop-in",
         ours=("varchive", ["archive-varchive"]), rival=("libarchive 3.8.11", ["archive-libarchive"])),
    # google/brotli's decoder API: vbrotli (brotli-abi) in place of libbrotlidec.
    dict(id="brotli-decode", suite="brotli", data="brotli", same_output=True, api="drop-in",
         ours=("vbrotli", ["brotli-vbrotli"]), rival=("brotli 1.2.1", ["brotli-brotli"])),
    # The TurboJPEG API: vjpeg (turbojpeg-abi) in place of libjpeg-turbo.
    dict(id="jpeg-baseline", suite="jpeg", data="jpeg", same_output=True, api="drop-in",
         ours=("vjpeg", ["jpeg-vjpeg"]), rival=("libjpeg-turbo 3.1.4.1", ["jpeg-turbo"])),
    # The same driver and libraries on progressive files, and on 4:4:4.
    dict(id="jpeg-progressive", suite="jpeg", data="jpeg-prog", same_output=True, api="drop-in",
         ours=("vjpeg", ["jpeg-vjpeg"]), rival=("libjpeg-turbo 3.1.4.1", ["jpeg-turbo"])),
    dict(id="jpeg-444", suite="jpeg", data="jpeg-444", same_output=True, api="drop-in",
         ours=("vjpeg", ["jpeg-vjpeg"]), rival=("libjpeg-turbo 3.1.4.1", ["jpeg-turbo"])),
    # OTS's API: vfont's headers and C ABI in place of OTS. Each writes its
    # own serialization, so the sizes of the sanitized fonts differ slightly.
    dict(id="font-sanitize", suite="font", data="font", same_output=False, api="drop-in", check="sanitized bytes",
         ours=("vfont", ["font-vfont"]), rival=("OTS (2026-11)", ["font-ots"])),
    # liblz4's API: vlz4 (lz4-abi) in place of liblz4. Blocks, then frames.
    dict(id="lz4-decompress", suite="lz4", data="lz4", same_output=True, api="drop-in",
         ours=("vlz4", ["lz4-vlz4", "decompress"]), rival=("lz4 1.11.1", ["lz4-lz4", "decompress"])),
    dict(id="lz4-compress", suite="lz4", data="lz4", same_output=False, api="drop-in", check="compressed bytes",
         ours=("vlz4", ["lz4-vlz4", "compress"]), rival=("lz4 1.11.1", ["lz4-lz4", "compress"])),
    dict(id="lz4-frame-decompress", suite="lz4", data="lz4", same_output=True, api="drop-in",
         ours=("vlz4", ["lz4-vlz4", "frame-decompress"]), rival=("lz4 1.11.1", ["lz4-lz4", "frame-decompress"])),
    dict(id="lz4-frame-compress", suite="lz4", data="lz4", same_output=False, api="drop-in", check="compressed bytes",
         ours=("vlz4", ["lz4-vlz4", "frame-compress"]), rival=("lz4 1.11.1", ["lz4-lz4", "frame-compress"])),
    # snappy's C API: vsnappy (snappy-abi) in place of libsnappy.
    dict(id="snappy-uncompress", suite="snappy", data="snappy", same_output=True, api="drop-in",
         ours=("vsnappy", ["snappy-vsnappy", "uncompress"]), rival=("snappy 1.3.1", ["snappy-snappy", "uncompress"])),
    dict(id="snappy-validate", suite="snappy", data="snappy", same_output=True, api="drop-in",
         ours=("vsnappy", ["snappy-vsnappy", "validate"]), rival=("snappy 1.3.1", ["snappy-snappy", "validate"])),
    dict(id="snappy-compress", suite="snappy", data="snappy", same_output=False, api="drop-in", check="compressed bytes",
         ours=("vsnappy", ["snappy-vsnappy", "compress"]), rival=("snappy 1.3.1", ["snappy-snappy", "compress"])),
    # cre2's API (the C wrapper of RE2): vregex (cre2-abi) in place of cre2 + RE2.
    dict(id="regex-re2", suite="regex", data="regex", same_output=True, api="drop-in",
         ours=("vregex", ["regex-vregex"]), rival=("RE2 2025-11-05", ["regex-re2"])),
]

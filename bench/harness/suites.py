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

WEBP_NOTE = ("`verilith_webp::decode_to` returns a new buffer each call; libwebp's `WebPDecodeRGBAInto` "
             "writes into the caller's.")

COMPARISONS = [
    # zlib's API: verilith-zlib (feature zlib-abi) in place of zlib.
    dict(id="zlib-inflate", suite="zlib", data="zlib", same_output=True, api="drop-in", pair="zlib-inflate",
         task="decompress a zlib stream in one call, and fed 1 KB at a time into a 16 KB buffer",
         ours=("verilith-zlib", ["zlib-vzlib", "inflate"]), rival=("zlib 1.4", ["zlib-zlib", "inflate"])),
    # The same jobs through verilith-zlib's Rust API (runners/vzlib-run).
    dict(id="zlib-inflate-native", suite="zlib", data="zlib", same_output=True, api="native", pair="zlib-inflate",
         task="decompress a zlib stream in one call, and fed 1 KB at a time into a 16 KB buffer",
         note="`Decompressor::decompress_into` and `stream::Stream`: the code verilith-zlib's zlib ABI calls, without its z_stream bookkeeping.",
         ours=("verilith-zlib (Rust API)", ["zlib-native", "inflate"]), rival=("zlib 1.4", ["zlib-zlib", "inflate"])),
    dict(id="zlib-deflate", suite="zlib", data="zlib", same_output=False, check="compressed bytes", api="drop-in", pair="zlib-deflate",
         task="compress a file to a zlib stream at levels 1, 6 and 9",
         ours=("verilith-zlib", ["zlib-vzlib", "deflate"]), rival=("zlib 1.4", ["zlib-zlib", "deflate"])),
    dict(id="zlib-deflate-native", suite="zlib", data="zlib", same_output=False, check="compressed bytes", api="native", pair="zlib-deflate",
         task="compress a file to a zlib stream at levels 1, 6 and 9",
         note="`zlib_compress` returns a new `Vec`; zlib's `deflate` writes into the caller's buffer.",
         ours=("verilith-zlib (Rust API)", ["zlib-native", "deflate"]), rival=("zlib 1.4", ["zlib-zlib", "deflate"])),
    # c-ares's record API: c-ares with verilith-dns's patch in place of stock c-ares.
    dict(id="dns-parse", suite="dns", data="dns", same_output=True, api="drop-in",
         ours=("c-ares + verilith-dns", ["dns-vdns", "parse"]), rival=("c-ares", ["dns-cares", "parse"])),
    dict(id="dns-write", suite="dns", data="dns", same_output=False, check="bytes written", api="drop-in",
         ours=("c-ares + verilith-dns", ["dns-vdns", "write"]), rival=("c-ares", ["dns-cares", "write"])),
    # Parse and read every record, the task of the native comparison below.
    dict(id="dns-read", suite="dns", data="dns", same_output=True, api="drop-in", pair="dns-cares",
         task="parse a response, read every question and record (name, type, class, TTL, RDATA fields), free it",
         ours=("c-ares + verilith-dns", ["dns-vdns", "read"]), rival=("c-ares", ["dns-cares", "read"])),
    dict(id="dns-native", suite="dns", data="dns", same_output=True, api="native", pair="dns-cares",
         task="parse a response, read every question and record (name, type, class, TTL, RDATA fields), free it",
         note="verilith-dns parses into a reused `Message` and decodes each record's RDATA when it is read; c-ares "
              "allocates a record tree on every parse and frees it, which is the only way its API parses. "
              "Names come back in wire form from verilith-dns and as text from c-ares.",
         ours=("verilith-dns (Rust API)", ["dns-native"]), rival=("c-ares", ["dns-cares", "read"])),
    # llhttp's API, as Node drives it: verilith-http (llhttp-abi) under llhttp's api.c.
    dict(id="http-llhttp", suite="http", data="http", same_output=True, api="drop-in", pair="http-llhttp",
         task="parse a whole message: target or reason, every header name and value, the body",
         ours=("verilith-http", ["http-vhttp"]), rival=("llhttp 9.4.4", ["http-llhttp"])),
    dict(id="http-llhttp-native", suite="http", data="http", same_output=True, api="native", pair="http-llhttp",
         task="parse a whole message: target or reason, every header name and value, the body",
         note="llhttp reports each piece through a callback as it goes and can take the message in pieces; "
              "verilith-http's API parses a complete head in one call and returns spans. verilith-http's chunked decoder works "
              "in place, so resp-chunked includes a copy of the body into a scratch buffer on our side.",
         ours=("verilith-http (Rust API)", ["http-native", "llhttp"]), rival=("llhttp 9.4.4", ["http-llhttp", "read"])),
    # picohttpparser's API: verilith-http (phr-abi) in place of picohttpparser.
    dict(id="http-pico", suite="http", data="http", same_output=True, api="drop-in", pair="http-pico",
         task="parse a message head into a reused header array",
         ours=("verilith-http", ["pico-vhttp"]), rival=("picohttpparser", ["pico-pico"])),
    dict(id="http-pico-native", suite="http", data="http", same_output=True, api="native", pair="http-pico",
         task="parse a message head into a reused header array",
         note="picohttpparser's API is already flat and copies nothing, so little separates the two columns. "
              "verilith-http's own call also works out the body framing (Content-Length, Transfer-Encoding), which "
              "picohttpparser leaves to the caller.",
         ours=("verilith-http (Rust API)", ["http-native", "pico"]), rival=("picohttpparser", ["pico-pico"])),
    # ada's C API: verilith-url (ada-abi) in place of ada.
    dict(id="url-ada", suite="url", data="url", same_output=True, api="drop-in", pair="url-ada",
         task="parse every URL of a list and read the href of the valid ones",
         ours=("verilith-url", ["url-vurl"]), rival=("ada 4.1.1", ["url-ada"])),
    # The same job through verilith-url's Rust API, against ada's own C++ API (ada::parse into an url_aggregator, which its C API wraps).
    dict(id="url-ada-native", suite="url", data="url", same_output=True, api="native", pair="url-ada",
         task="parse every URL of a list and read the href of the valid ones",
         note="ada's C++ `ada::parse` returns the URL by value, where its C API (the drop-in column's original) also allocates each URL. "
              "verilith-url's `Url::parse_bytes` returns a `Url` that owns its href.",
         ours=("verilith-url (Rust API)", ["url-native"]), rival=("ada 4.1.1 (C++ API)", ["url-ada-cpp"])),
    # expat's API: verilith-xml (expat-abi) in place of libexpat, the same driver.
    dict(id="xml-expat-dropin-read", suite="xml", data="xml", same_output=True, api="drop-in", pair="xml-expat-read",
         task="parse a document, visit every element, attribute (normalized value) and run of character data",
         ours=("verilith-xml", ["xml-expat-vxml", "read"]), rival=("expat 2.10.0", ["xml-expat", "read"])),
    dict(id="xml-expat-dropin-check", suite="xml", data="xml", same_output=True, api="drop-in", pair="xml-expat-check",
         task="decide whether a document is well-formed (`XML_Parse` with no handlers)",
         ours=("verilith-xml", ["xml-expat-vxml", "check"]), rival=("expat 2.10.0", ["xml-expat", "check"])),
    # Native APIs: verilith-xml's Rust API against expat's SAX API.
    dict(id="xml-expat-read", suite="xml", data="xml", same_output=True, api="native", pair="xml-expat-read",
         task="parse a document, visit every element, attribute (normalized value) and run of character data",
         note="expat calls back for each item as it parses; verilith-xml parses the whole document into a tape, then "
              "the walk reads it through the API, which normalizes attribute values that need it and supplies "
              "DTD defaults. Both check the whole document.",
         ours=("verilith-xml (Rust API)", ["xml-vxml", "read"]), rival=("expat 2.10.0", ["xml-expat", "read"])),
    dict(id="xml-expat-check", suite="xml", data="xml", same_output=True, api="native", pair="xml-expat-check",
         task="decide whether a document is well-formed (expat with no handlers; verilith-xml's verified check into a reused tape)",
         ours=("verilith-xml (Rust API)", ["xml-vxml", "check"]), rival=("expat 2.10.0", ["xml-expat", "check"])),
    # libxml2's API: verilith-xml (libxml2-abi) in place of libxml2, the same driver.
    dict(id="xml-libxml2-dropin-read", suite="xml", data="xml", same_output=True, api="drop-in", pair="xml-libxml2-read",
         task="parse a document, visit every element, attribute (normalized value) and run of character data",
         ours=("verilith-xml", ["xml-libxml2-vxml", "read"]), rival=("libxml2 2.15.4", ["xml-libxml2", "read"])),
    dict(id="xml-libxml2-dropin-check", suite="xml", data="xml", same_output=True, api="drop-in", pair="xml-libxml2-check",
         task="decide whether a document is well-formed (libxml2's SAX2 handlers for the DTD, none for content)",
         ours=("verilith-xml", ["xml-libxml2-vxml", "check"]), rival=("libxml2 2.15.4", ["xml-libxml2", "check"])),
    # The same two jobs against libxml2's SAX2 API, with the same check values.
    dict(id="xml-libxml2-read", suite="xml", data="xml", same_output=False, check="check value", api="native", pair="xml-libxml2-read",
         task="parse a document, visit every element, attribute (normalized value) and run of character data",
         note="libxml2 runs its default SAX2 handlers for the DTD, which keep the declarations in a document "
              "object, with entities substituted and defaults added (the deprecated SAX1 callbacks do not "
              "receive defaults), and reuses one parser context. SAX2 also processes namespaces, which verilith-xml does "
              "not. The check values are the same on every file but attributes.xml, where libxml2's attribute "
              "values are 691 bytes longer: it keeps a CR LF in an entity's literal value as two characters, so "
              "a reference to it in an attribute value gives two spaces, where XML 1.0 (2.11, 3.3.3), expat and "
              "verilith-xml give one.",
         ours=("verilith-xml (Rust API)", ["xml-vxml", "read"]), rival=("libxml2 2.15.4", ["xml-libxml2", "read"])),
    dict(id="xml-libxml2-check", suite="xml", data="xml", same_output=True, api="native", pair="xml-libxml2-check",
         task="decide whether a document is well-formed (libxml2 with its SAX2 handlers for the DTD and none for content; verilith-xml's verified check into a reused tape)",
         ours=("verilith-xml (Rust API)", ["xml-vxml", "check"]), rival=("libxml2 2.15.4", ["xml-libxml2", "check"])),
    # cJSON's API: verilith-json (cjson feature) in place of cJSON.
    dict(id="json-cjson-parse", suite="json", data="json", same_output=True, api="drop-in", pair="json-cjson",
         task="parse a document, read every value (numbers as doubles, string and key lengths), free it",
         ours=("verilith-json", ["cjson-vjson", "parse"]), rival=("cJSON 1.7.19", ["cjson-cjson", "parse"])),
    dict(id="json-cjson-native", suite="json", data="json", same_output=True, api="native", pair="json-cjson",
         task="parse a document, read every value (numbers as doubles, string and key lengths), free it",
         note="verilith-json parses into a flat index in a reused `Parser`; cJSON allocates a node per value and frees "
              "the tree, which is the only way its API parses.",
         ours=("verilith-json (Rust API)", ["json-vjson", "cjson-parse"]), rival=("cJSON 1.7.19", ["cjson-cjson", "parse"])),
    dict(id="json-cjson-print", suite="json", data="json", same_output=False, check="printed bytes", api="drop-in",
         ours=("verilith-json", ["cjson-vjson", "print"]), rival=("cJSON 1.7.19", ["cjson-cjson", "print"])),
    # Native APIs, same work: verilith-json::Parser against simdjson's DOM parser.
    dict(id="json-simdjson", suite="json", data="json", same_output=True, api="native",
         task="parse a document with a reused parser, read every value",
         ours=("verilith-json (Rust API)", ["json-vjson"]), rival=("simdjson 5.2.0", ["json-simdjson"])),
    # mbedTLS's certificate API: mbedTLS with verilith-x509's patch in place of stock.
    dict(id="x509-mbedtls", suite="x509", data="x509", same_output=True, api="drop-in",
         ours=("mbedTLS + verilith-x509", ["x509-vx509"]), rival=("mbedTLS 4.3.0", ["x509-mbedtls"])),
    # Parse without copying and read the fields a TLS client reads, the task
    # of the native comparison below.
    dict(id="x509-mbedtls-read", suite="x509", data="x509", same_output=True, api="drop-in", pair="x509-mbedtls",
         task="parse a certificate in place; read serial, issuer, subject, validity, key usage, CA flag, DNS names, EKUs; free it",
         ours=("mbedTLS + verilith-x509", ["x509-vx509", "read"]), rival=("mbedTLS 4.3.0", ["x509-mbedtls", "read"])),
    dict(id="x509-mbedtls-native", suite="x509", data="x509", same_output=True, api="native", pair="x509-mbedtls",
         task="parse a certificate in place; read serial, issuer, subject, validity, key usage, CA flag, DNS names, EKUs; free it",
         note="The two sides do not do the same amount of work, and the difference favours verilith-x509: "
              "`mbedtls_x509_crt_parse_der_nocopy` also decodes the public key into a `mbedtls_pk_context` "
              "(for RSA, two big-number reads and checks) and allocates the name and extension lists, none "
              "of which its API lets a caller skip. verilith-x509 checks the SubjectPublicKeyInfo structure and "
              "returns the key bytes without decoding them. Read this column as an upper bound.",
         ours=("verilith-x509 (Rust API)", ["x509n-vx509", "read"]), rival=("mbedTLS 4.3.0", ["x509-mbedtls", "read"])),
    # Native APIs, same work: verilith-x509::parse against Verdict's parse_x509_der,
    # both verified in Verus. Each parses and checks the whole certificate.
    dict(id="x509-verdict", suite="x509n", data="x509", same_output=True, api="native",
         task="parse and check a whole certificate",
         ours=("verilith-x509 (Rust API)", ["x509n-vx509"]), rival=("Verdict", ["x509n-verdict"])),
    # libpng's read API, decoding to RGBA8: verilith-png (libpng-abi) in place
    # of libpng, under the same driver.
    dict(id="png-libpng-abi", suite="png", data="png", same_output=True, api="drop-in", pair="png-libpng",
         task="decode a PNG to RGBA8",
         ours=("verilith-png", ["png-vpng-abi"]), rival=("libpng 1.6.59", ["png-libpng"])),
    # The same job through verilith-png's Rust API.
    dict(id="png-libpng", suite="png", data="png", same_output=True, api="native", pair="png-libpng",
         task="decode a PNG to RGBA8",
         ours=("verilith-png (Rust API)", ["png-vpng"]), rival=("libpng 1.6.59", ["png-libpng"])),
    # libwebp's decode API, lossless files: verilith-webp (webp-abi) in place of libwebp.
    dict(id="webp-lossless", suite="webp", data="webp", same_output=True, api="drop-in", pair="webp-lossless",
         task="decode a lossless WebP to RGBA",
         ours=("verilith-webp", ["webp-vwebp"]), rival=("libwebp 1.6.0", ["webp-libwebp"])),
    # Through verilith-webp's Rust API (runners/vwebp-run).
    dict(id="webp-lossless-native", suite="webp", data="webp", same_output=True, api="native", pair="webp-lossless",
         task="decode a lossless WebP to RGBA",
         note=WEBP_NOTE,
         ours=("verilith-webp (Rust API)", ["webp-native"]), rival=("libwebp 1.6.0", ["webp-libwebp"])),
    # The same driver and libraries on lossy (VP8) files.
    dict(id="webp-lossy", suite="webp", data="webp-lossy", same_output=True, api="drop-in", pair="webp-lossy",
         task="decode a lossy WebP to RGBA",
         ours=("verilith-webp", ["webp-vwebp"]), rival=("libwebp 1.6.0", ["webp-libwebp"])),
    dict(id="webp-lossy-native", suite="webp", data="webp-lossy", same_output=True, api="native", pair="webp-lossy",
         task="decode a lossy WebP to RGBA",
         note=WEBP_NOTE,
         ours=("verilith-webp (Rust API)", ["webp-native"]), rival=("libwebp 1.6.0", ["webp-libwebp"])),
    # libarchive's read API: verilith-archive (libarchive-abi) in place of libarchive.
    dict(id="archive-read", suite="archive", data="archive", same_output=True, api="drop-in", pair="archive-read",
         task="open an archive from memory, then read every member (read/) or only every header (list/)",
         ours=("verilith-archive", ["archive-varchive"]), rival=("libarchive 3.8.11", ["archive-libarchive"])),
    dict(id="archive-read-native", suite="archive", data="archive", same_output=True, api="native", pair="archive-read",
         task="open an archive from memory, then read every member (read/) or only every header (list/)",
         note="`Archive::open` parses and checks the whole index up front, and `read_ref` borrows a stored member from the "
              "archive (after checking its CRC-32), where libarchive copies data out in blocks.",
         ours=("verilith-archive (Rust API)", ["archive-native"]), rival=("libarchive 3.8.11", ["archive-libarchive"])),
    # google/brotli's decoder API: verilith-brotli (brotli-abi) in place of libbrotlidec.
    dict(id="brotli-decode", suite="brotli", data="brotli", same_output=True, api="drop-in", pair="brotli-decode",
         task="decompress a Brotli stream in one call, and fed 1 KB at a time into a 16 KB buffer",
         ours=("verilith-brotli", ["brotli-vbrotli"]), rival=("brotli 1.2.1", ["brotli-brotli"])),
    dict(id="brotli-decode-native", suite="brotli", data="brotli", same_output=True, api="native", pair="brotli-decode",
         task="decompress a Brotli stream in one call, and fed 1 KB at a time into a 16 KB buffer",
         note="`verilith_brotli::Stream` is what the drop-in's C ABI calls, so the two columns differ only by the C ABI's argument handling.",
         ours=("verilith-brotli (Rust API)", ["brotli-native"]), rival=("brotli 1.2.1", ["brotli-brotli"])),
    # The TurboJPEG API: verilith-jpeg (turbojpeg-abi) in place of libjpeg-turbo.
    dict(id="jpeg-baseline", suite="jpeg", data="jpeg", same_output=True, api="drop-in", pair="jpeg-baseline",
         task="decode a baseline 4:2:0 JPEG to RGB",
         ours=("verilith-jpeg", ["jpeg-vjpeg"]), rival=("libjpeg-turbo 3.2.1", ["jpeg-turbo"])),
    # Through verilith-jpeg's Rust API (`decode::decode_to` into a reused buffer).
    dict(id="jpeg-baseline-native", suite="jpeg", data="jpeg", same_output=True, api="native", pair="jpeg-baseline",
         task="decode a baseline 4:2:0 JPEG to RGB",
         ours=("verilith-jpeg (Rust API)", ["jpeg-native"]), rival=("libjpeg-turbo 3.2.1", ["jpeg-turbo"])),
    # The same driver and libraries on progressive files, and on 4:4:4.
    dict(id="jpeg-progressive", suite="jpeg", data="jpeg-prog", same_output=True, api="drop-in", pair="jpeg-progressive",
         task="decode a progressive 4:2:0 JPEG to RGB",
         ours=("verilith-jpeg", ["jpeg-vjpeg"]), rival=("libjpeg-turbo 3.2.1", ["jpeg-turbo"])),
    dict(id="jpeg-progressive-native", suite="jpeg", data="jpeg-prog", same_output=True, api="native", pair="jpeg-progressive",
         task="decode a progressive 4:2:0 JPEG to RGB",
         ours=("verilith-jpeg (Rust API)", ["jpeg-native"]), rival=("libjpeg-turbo 3.2.1", ["jpeg-turbo"])),
    dict(id="jpeg-444", suite="jpeg", data="jpeg-444", same_output=True, api="drop-in", pair="jpeg-444",
         task="decode a baseline 4:4:4 JPEG to RGB",
         ours=("verilith-jpeg", ["jpeg-vjpeg"]), rival=("libjpeg-turbo 3.2.1", ["jpeg-turbo"])),
    dict(id="jpeg-444-native", suite="jpeg", data="jpeg-444", same_output=True, api="native", pair="jpeg-444",
         task="decode a baseline 4:4:4 JPEG to RGB",
         ours=("verilith-jpeg (Rust API)", ["jpeg-native"]), rival=("libjpeg-turbo 3.2.1", ["jpeg-turbo"])),
    # OTS's API: verilith-font's headers and C ABI in place of OTS. Each writes its
    # own serialization, so the sizes of the sanitized fonts differ slightly.
    dict(id="font-sanitize", suite="font", data="font", same_output=False, api="drop-in", pair="font-sanitize",
         task="sanitize a font (OpenType, TrueType, WOFF, WOFF2) into a new buffer", check="sanitized bytes",
         ours=("verilith-font", ["font-vfont"]), rival=("OTS (2026-11)", ["font-ots"])),
    dict(id="font-sanitize-native", suite="font", data="font", same_output=False, check="sanitized bytes", api="native", pair="font-sanitize",
         task="sanitize a font (OpenType, TrueType, WOFF, WOFF2) into a new buffer",
         ours=("verilith-font (Rust API)", ["font-native"]), rival=("OTS (2026-11)", ["font-ots"])),
    # liblz4's API: verilith-lz4 (lz4-abi) in place of liblz4. Blocks, then frames.
    dict(id="lz4-decompress", suite="lz4", data="lz4", same_output=True, api="drop-in", pair="lz4-decompress",
         task="decompress an LZ4 block",
         ours=("verilith-lz4", ["lz4-vlz4", "decompress"]), rival=("lz4 1.11.1", ["lz4-lz4", "decompress"])),
    # Through verilith-lz4's Rust API, into reused buffers (runners/vlz4-run).
    dict(id="lz4-decompress-native", suite="lz4", data="lz4", same_output=True, api="native", pair="lz4-decompress",
         task="decompress an LZ4 block",
         ours=("verilith-lz4 (Rust API)", ["lz4-native", "decompress"]), rival=("lz4 1.11.1", ["lz4-lz4", "decompress"])),
    dict(id="lz4-compress", suite="lz4", data="lz4", same_output=False, api="drop-in", pair="lz4-compress",
         task="compress a file as one LZ4 block", check="compressed bytes",
         ours=("verilith-lz4", ["lz4-vlz4", "compress"]), rival=("lz4 1.11.1", ["lz4-lz4", "compress"])),
    dict(id="lz4-compress-native", suite="lz4", data="lz4", same_output=False, check="compressed bytes", api="native", pair="lz4-compress",
         task="compress a file as one LZ4 block",
         ours=("verilith-lz4 (Rust API)", ["lz4-native", "compress"]), rival=("lz4 1.11.1", ["lz4-lz4", "compress"])),
    dict(id="lz4-frame-decompress", suite="lz4", data="lz4", same_output=True, api="drop-in", pair="lz4-frame-decompress",
         task="decompress an LZ4 frame",
         ours=("verilith-lz4", ["lz4-vlz4", "frame-decompress"]), rival=("lz4 1.11.1", ["lz4-lz4", "frame-decompress"])),
    dict(id="lz4-frame-decompress-native", suite="lz4", data="lz4", same_output=True, api="native", pair="lz4-frame-decompress",
         task="decompress an LZ4 frame",
         ours=("verilith-lz4 (Rust API)", ["lz4-native", "frame-decompress"]), rival=("lz4 1.11.1", ["lz4-lz4", "frame-decompress"])),
    dict(id="lz4-frame-compress", suite="lz4", data="lz4", same_output=False, api="drop-in", pair="lz4-frame-compress",
         task="compress a file as one LZ4 frame (liblz4's default frame)", check="compressed bytes",
         ours=("verilith-lz4", ["lz4-vlz4", "frame-compress"]), rival=("lz4 1.11.1", ["lz4-lz4", "frame-compress"])),
    dict(id="lz4-frame-compress-native", suite="lz4", data="lz4", same_output=False, check="compressed bytes", api="native", pair="lz4-frame-compress",
         task="compress a file as one LZ4 frame (liblz4's default frame)",
         ours=("verilith-lz4 (Rust API)", ["lz4-native", "frame-compress"]), rival=("lz4 1.11.1", ["lz4-lz4", "frame-compress"])),
    # snappy's C API: verilith-snappy (snappy-abi) in place of libsnappy.
    dict(id="snappy-uncompress", suite="snappy", data="snappy", same_output=True, api="drop-in", pair="snappy-uncompress",
         task="decompress a Snappy buffer",
         ours=("verilith-snappy", ["snappy-vsnappy", "uncompress"]), rival=("snappy 1.3.1", ["snappy-snappy", "uncompress"])),
    # Through verilith-snappy's Rust API, into reused buffers (runners/vsnappy-run).
    dict(id="snappy-uncompress-native", suite="snappy", data="snappy", same_output=True, api="native", pair="snappy-uncompress",
         task="decompress a Snappy buffer",
         ours=("verilith-snappy (Rust API)", ["snappy-native", "uncompress"]), rival=("snappy 1.3.1", ["snappy-snappy", "uncompress"])),
    dict(id="snappy-validate", suite="snappy", data="snappy", same_output=True, api="drop-in", pair="snappy-validate",
         task="check that a Snappy buffer decompresses, without writing it",
         ours=("verilith-snappy", ["snappy-vsnappy", "validate"]), rival=("snappy 1.3.1", ["snappy-snappy", "validate"])),
    dict(id="snappy-validate-native", suite="snappy", data="snappy", same_output=True, api="native", pair="snappy-validate",
         task="check that a Snappy buffer decompresses, without writing it",
         ours=("verilith-snappy (Rust API)", ["snappy-native", "validate"]), rival=("snappy 1.3.1", ["snappy-snappy", "validate"])),
    dict(id="snappy-compress", suite="snappy", data="snappy", same_output=False, api="drop-in", pair="snappy-compress",
         task="compress a file to a Snappy buffer", check="compressed bytes",
         ours=("verilith-snappy", ["snappy-vsnappy", "compress"]), rival=("snappy 1.3.1", ["snappy-snappy", "compress"])),
    dict(id="snappy-compress-native", suite="snappy", data="snappy", same_output=False, check="compressed bytes", api="native", pair="snappy-compress",
         task="compress a file to a Snappy buffer",
         ours=("verilith-snappy (Rust API)", ["snappy-native", "compress"]), rival=("snappy 1.3.1", ["snappy-snappy", "compress"])),
    # cre2's API (the C wrapper of RE2): verilith-regex (cre2-abi) in place of cre2 + RE2.
    dict(id="regex-re2", suite="regex", data="regex", same_output=True, api="drop-in", pair="regex-re2",
         task="find every match of a pattern in a text, with its groups",
         ours=("verilith-regex", ["regex-vregex"]), rival=("RE2 2025-11-05", ["regex-re2"])),
    dict(id="regex-re2-native", suite="regex", data="regex", same_output=True, api="native", pair="regex-re2",
         task="find every match of a pattern in a text, with its groups",
         note="RE2 is still reached through cre2, its C wrapper (one call per match); verilith-regex through "
              "`Regex::search_with`, with its scratch and slots reused across matches.",
         ours=("verilith-regex (Rust API)", ["regex-native"]), rival=("RE2 2025-11-05", ["regex-re2"])),
    # OpenSSL's SHA-2 API: verilith-sha2 (openssl-abi) in place of libcrypto.
    dict(id="sha256", suite="sha2", data="sha2", same_output=True, api="drop-in",
         ours=("verilith-sha2", ["sha2-vsha2", "sha256"]), rival=("OpenSSL 4.1.0", ["sha2-openssl", "sha256"])),
    dict(id="sha512", suite="sha2", data="sha2", same_output=True, api="drop-in",
         ours=("verilith-sha2", ["sha2-vsha2", "sha512"]), rival=("OpenSSL 4.1.0", ["sha2-openssl", "sha512"])),
    dict(id="sha256-stream", suite="sha2", data="sha2", same_output=True, api="drop-in",
         ours=("verilith-sha2", ["sha2-vsha2", "sha256-stream"]), rival=("OpenSSL 4.1.0", ["sha2-openssl", "sha256-stream"])),
    dict(id="sha512-stream", suite="sha2", data="sha2", same_output=True, api="drop-in",
         ours=("verilith-sha2", ["sha2-vsha2", "sha512-stream"]), rival=("OpenSSL 4.1.0", ["sha2-openssl", "sha512-stream"])),
]

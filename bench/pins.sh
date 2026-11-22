# Everything a run depends on, pinned. Sourced by the scripts.
#
# Our libraries are the crates of the verilith checkout this harness sits in
# (crates/zlib is vzlib, and so on); its commit goes into every result.

# The original libraries, built here from source with the same compiler and
# flags as everything else. "name url ref"; ref is a tag or a full commit.
ORIGINALS="
zlib            https://github.com/madler/zlib             v1.4
c-ares          https://github.com/c-ares/c-ares           4c6046531646906e9a493d542bd7f1f63da9650e
llhttp          https://github.com/nodejs/llhttp           release/v9.4.4
picohttpparser  https://github.com/h2o/picohttpparser      dd573d8fa9264c646a400e96ce9f07dea6f156e4
ada             https://github.com/ada-url/ada             v4.1.1
simdjson        https://github.com/simdjson/simdjson       v5.2.0
cjson           https://github.com/DaveGamble/cJSON        v1.7.19
mbedtls         https://github.com/Mbed-TLS/mbedtls        v3.6.8
libpng          https://github.com/pnggroup/libpng         v1.6.59
libwebp         https://github.com/webmproject/libwebp     v1.6.0
brotli          https://github.com/google/brotli           v1.2.1
libjpeg-turbo   https://github.com/libjpeg-turbo/libjpeg-turbo 3.2.1
lz4             https://github.com/lz4/lz4                 v1.11.1
snappy          https://github.com/google/snappy           1.3.1
libarchive      https://github.com/libarchive/libarchive   v3.8.11
verdict         https://github.com/secure-foundations/verdict 9bc18bc5a287c1608dcb74a6eee7b9ca94a62b67
ots             https://github.com/khaledhosny/ots         c5d249ce90ab0aa3e76eb0dfad28746f407201d0
woff2           https://github.com/google/woff2            7b67e12355fe7da148db5c19d4261f0a498a9537
re2             https://github.com/google/re2              2025-11-05
abseil-cpp      https://github.com/abseil/abseil-cpp       20260817.0
cre2            https://github.com/marcomaggi/cre2         f9ad1ced3f5358557b32d623babf317d6e4aa31d
"
# Notes on the choices:
# - c-ares: the commit vdns's c-ares patch was made and tested against
#   (cares/README.md in vdns); the latest release, v1.34.9, predates it.
# - llhttp 9.4.4 and mbedTLS 3.6.8: the versions vhttp's and vx509's
#   drop-ins were tested against.
# - Verdict: the verified X.509 parser vx509 is compared with on native APIs
#   (USENIX Security 2025), at main of 2025-11-18. Built from its Verus
#   submodule's vstd without running Verus, with the toolchain it pins (1.86).
# - OTS: main of 2026-11, the commit vfont's differential tests use (after
#   the last release, 9.2.0). woff2 is the commit OTS's own build pins.
# - RE2 is reached through cre2, its C wrapper (one file, built here from
#   its master of 2024), since vregex's drop-in API is cre2's. Abseil is
#   what RE2 needs.

# Input data: "name url commit". Each file used is also pinned by SHA-256 in
# data/SHA256SUMS, checked by fetch.sh.
DATASETS="
silesia     https://github.com/MiloszKrajewski/SilesiaCorpus                3f3fa2cdbbb3795c903b74e774acb309e1360337
url-dataset https://github.com/ada-url/url-dataset                          ef7065196980ab7956bacc60b4bda663939f659c
kodak       https://github.com/MohamedBakrAli/Kodak-Lossless-True-Color-Image-Suite dd2e1105fe8d9afe1120cd7e4c0e5e41f509a81b
certifi     https://github.com/certifi/python-certifi                       2026.11.20
simdjson-data https://github.com/simdjson/simdjson-data                    4197c425e857f0ec38e89822fdd0bd9ea21f4daf
source-serif https://github.com/adobe-fonts/source-serif                    80d3f8894c09c937bebfa9011247d2e1c79fd6f4
"
# Silesia files used (5 of 12; the others, mozilla above all, add an hour of
# level-9 compression without changing the picture).
SILESIA_FILES="dickens samba sao x-ray xml"

# Node.js for benchmark/compare.js.
: "${NODE_VERSION:=v26.13.1}"

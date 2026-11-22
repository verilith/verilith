#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
#   ./ci.sh mbedtls   mbedTLS's test suites with this crate as its parser
#   ./ci.sh fuzz      the fuzz targets under ASan, FUZZ_SECS each (default 300)
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

MBEDTLS_TAG=v3.6.8

test() {
  # no_std, no alloc, on a bare-metal target.
  rustup target add thumbv7em-none-eabihf
  cargo rustc --lib --crate-type rlib --no-default-features --target thumbv7em-none-eabihf
  cargo build --lib --no-default-features --features mbedtls --target thumbv7em-none-eabihf
  # CVEs, and differentials against OpenSSL, x509-parser, x509-cert, webpki.
  [ -d "$W/corpus/der" ] || corpus/fetch.sh "$W/corpus"
  VX509_CORPUS=$W/corpus/der cargo test --profile "$P" --features capi -- --nocapture
  # The native C API under ASan and UBSan.
  scripts/test-c.sh
}

get_mbedtls() {
  [ -d "$1" ] || git clone -q --depth 1 --branch "$MBEDTLS_TAG" --recurse-submodules --shallow-submodules \
    https://github.com/Mbed-TLS/mbedtls.git "$1"
}

mbedtls() {
  [ -z "${CI:-}" ] || pip install jsonschema jinja2
  get_mbedtls "$W/mbedtls"
  mbedtls/run-tests.sh "$W/mbedtls"
}

fuzz() {
  fuzz_tools
  get_mbedtls "$W/mbedtls-asan"
  git -C "$W/mbedtls-asan" apply --check "$PWD/mbedtls/mbedtls-use-vx509.patch" 2>/dev/null &&
    git -C "$W/mbedtls-asan" apply "$PWD/mbedtls/mbedtls-use-vx509.patch"
  cargo build --profile "$P" --features mbedtls
  CC=clang cmake -S "$W/mbedtls-asan" -B "$W/mbedtls-asan/build-asan" -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_C_COMPILER_WORKS=1 -DENABLE_TESTING=OFF -DENABLE_PROGRAMS=OFF \
    -DCMAKE_C_FLAGS="-fsanitize=address,fuzzer-no-link -g" \
    -DMBEDTLS_VX509_DIR="$PWD" -DMBEDTLS_VX509_LIB="$T/$P/libverilith_x509.a"
  cmake --build "$W/mbedtls-asan/build-asan" -j --target mbedx509 mbedcrypto
  export MBEDTLS_LIB_DIR=$W/mbedtls-asan/build-asan/library
  cd fuzz
  for t in parse mbedtls; do
    mkdir -p "corpus/$t" && cp seeds/* "corpus/$t/"
    cargo +nightly fuzz run -s address "$t" "corpus/$t" -- -max_total_time="${FUZZ_SECS:-300}" -max_len=8192
  done
}

"${1:-test}"

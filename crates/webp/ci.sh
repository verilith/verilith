#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
#   ./ci.sh fuzz      differential fuzzing against libwebp under ASan, FUZZ_SECS (default 120)
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

LIBWEBP_TAG=v1.6.0

libwebp() {
  export LIBWEBP_SRC=$W/libwebp LIBWEBP_BUILD=$W/lwbuild
  [ -f "$LIBWEBP_BUILD/cwebp" ] && return
  [ -d "$LIBWEBP_SRC" ] || git clone -q --depth 1 --branch "$LIBWEBP_TAG" https://chromium.googlesource.com/webm/libwebp "$LIBWEBP_SRC"
  cmake -S "$LIBWEBP_SRC" -B "$LIBWEBP_BUILD" -DCMAKE_BUILD_TYPE=Release -DWEBP_BUILD_CWEBP=ON -DWEBP_BUILD_DWEBP=ON > /dev/null
  cmake --build "$LIBWEBP_BUILD" -j"$(nproc)" > /dev/null
}

corpus() { # corpus DIR: libwebp's encodings of the generated images
  mkdir -p "$W/pam" "$1"
  python3 scripts/make_images.py "$W/pam"
  for p in "$W"/pam/*.pam; do
    "$LIBWEBP_BUILD/cwebp" -quiet -lossless -exact "$p" -o "$1/$(basename "${p%.pam}").webp"
  done
  scripts/make_lossy.sh "$LIBWEBP_BUILD/cwebp" "$W/pam" "$1"
}

test() {
  cargo build --profile "$P"
  cargo build --profile "$P" --features webp-abi
  cargo build --profile "$P" --example vdwebp
  cargo test --profile "$P"
  # Differential test against libwebp.
  libwebp
  corpus "$W/corpus"
  python3 scripts/make_containers.py "$W/corpus" "$W/corpus"
  [ -d "$W/libwebp-test-data" ] || git clone -q --depth 1 https://github.com/webmproject/libwebp-test-data "$W/libwebp-test-data"
  cargo build --profile "$P"
  make -C difftest diff
  ./difftest/diff "$W"/corpus/* "$W"/libwebp-test-data/*.webp difftest/regress/*.webp
  # The CVE-2023-4863 demo.
  make -C difftest cve_demo
  mkdir -p "$W/cve"
  python3 scripts/make_cve_trigger.py "$W/cve"
  ./difftest/cve_demo "$W"/cve/*.webp
}

fuzz() {
  apt clang cmake
  libwebp
  corpus "$W/seeds"
  cargo build --profile "$P"
  make -C difftest fuzz_diff
  ./difftest/fuzz_diff -max_total_time="${FUZZ_SECS:-120}" -timeout=60 "$W/seeds"
}

"${1:-test}"

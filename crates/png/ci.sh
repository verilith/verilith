#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

LIBPNG_TAG=v1.6.59

test() {
  cargo build --profile "$P" --example vpngcat
  cargo test --profile "$P"
  # Differential test against libpng (PngSuite and libpng's test images).
  if [ ! -f "$W/libpng/build/libpng16.a" ]; then
    [ -d "$W/libpng" ] || git clone -q --depth 1 --branch "$LIBPNG_TAG" https://github.com/pnggroup/libpng "$W/libpng"
    cmake -S "$W/libpng" -B "$W/libpng/build" -DCMAKE_BUILD_TYPE=Release -DPNG_SHARED=OFF -DPNG_TESTS=OFF > /dev/null
    cmake --build "$W/libpng/build" -j"$(nproc)" > /dev/null
  fi
  LIBPNG_DIR=$W/libpng ./difftest/build.sh
  difftest/compare.sh "$W"/libpng/contrib/pngsuite/*.png "$W"/libpng/contrib/testpngs/*.png
  # Mutation fuzzing against libpng.
  seeds=$(ls "$W"/libpng/contrib/pngsuite/*.png "$W"/libpng/contrib/testpngs/*.png | grep -v '/x[^/]*$')
  fuzz/run.sh "$W/mutants" 2000 "${GITHUB_RUN_NUMBER:-1}" $seeds
}

"${1:-test}"

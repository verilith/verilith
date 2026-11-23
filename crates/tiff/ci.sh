#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo build --profile "$P" --example vtiffcat
  cargo test --profile "$P"
  # Differential test against libtiff, on a generated corpus.
  apt libtiff-dev imagemagick
  difftest/build.sh
  difftest/gen.sh "$W/corpus"
  VTIFFCAT=$T/$P/examples/vtiffcat difftest/compare.sh "$W"/corpus/*.tif
  # Mutation fuzzing against libtiff.
  VTIFFCAT=$T/$P/examples/vtiffcat fuzz/run.sh "$W/mutants" 2000 "${GITHUB_RUN_NUMBER:-1}" $(ls "$W"/corpus/*.tif | grep -v big_)
}

"${1:-test}"

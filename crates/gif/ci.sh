#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo build --profile "$P" --example vgifcat
  cargo test --profile "$P"
  # Differential test against giflib, on a generated corpus.
  apt libgif-dev python3-pil
  difftest/build.sh
  python3 difftest/gen.py "$W/corpus"
  VGIFCAT=$T/$P/examples/vgifcat difftest/compare.sh "$W"/corpus/*.gif
  # Mutation fuzzing against giflib.
  VGIFCAT=$T/$P/examples/vgifcat fuzz/run.sh "$W/mutants" 2000 "${GITHUB_RUN_NUMBER:-1}" "$W"/corpus/*.gif
}

"${1:-test}"

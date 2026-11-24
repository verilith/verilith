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
  # The giflib C API, through programs written for giflib (and giflib's own
  # giftext, from its source).
  cargo build --profile "$P" --features gif-abi
  if [ ! -d "$W/giflib-5.2.2" ]; then
    curl -sSfL --retry 3 -o "$W/giflib.tar.gz" https://downloads.sourceforge.net/project/giflib/giflib-5.2.2.tar.gz \
      && tar xzf "$W/giflib.tar.gz" -C "$W" || true
  fi
  src=""
  [ -f "$W/giflib-5.2.2/giftext.c" ] && src=$W/giflib-5.2.2
  PROFILE=$P VGIFCAT=$T/$P/examples/vgifcat GIFLIB_SRC=$src difftest/abi.sh "$W"/corpus/*.gif "$W"/mutants/*.gif
}

"${1:-test}"

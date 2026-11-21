#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
#   ./ci.sh fuzz      every fuzz target under ASan, FUZZ_SECS each (default 120)
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  apt zlib1g-dev
  # Without zlib-abi: that feature exports zlib's names, which would
  # replace the system zlib the tests compare against. The drop-in
  # builds are checked by the C programs below.
  cargo test --profile "$P"
  cargo test --profile "$P" --features libdeflate-abi
  mkdir -p "$W/gz"
  for f in src/*.rs README.md; do gzip -9c "$f" > "$W/gz/$(basename "$f").gz"; done
  tests/c/run.sh "$W"/gz/*.gz
  tests/c/run_deflate.sh src/*.rs README.md
}

fuzz() {
  fuzz_tools
  cd fuzz
  for t in $(cargo +nightly fuzz list); do
    cargo +nightly fuzz run "$t" -- -max_total_time="${FUZZ_SECS:-120}"
  done
}

"${1:-test}"

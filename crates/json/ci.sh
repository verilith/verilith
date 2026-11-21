#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
#   ./ci.sh fuzz      the fuzz targets under ASan, FUZZ_SECS each (default 120)
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  [ -d "$W/JSONTestSuite" ] || git clone -q --depth 1 https://github.com/nst/JSONTestSuite "$W/JSONTestSuite"
  JSON_TEST_SUITE=$W/JSONTestSuite/test_parsing cargo test --profile "$P" --all-features
  # The cJSON ABI and the native C API.
  scripts/test-c.sh
}

fuzz() {
  fuzz_tools
  scripts/test-c.sh > /dev/null || true   # fetches cJSON
  cd fuzz
  for t in parse cjson_parse cjson_ops ondemand; do
    cargo +nightly fuzz run "$t" -- -max_total_time="${FUZZ_SECS:-120}" -max_len=4096
  done
}

"${1:-test}"

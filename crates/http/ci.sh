#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
#   ./ci.sh fuzz      every fuzz target under ASan, FUZZ_SECS each (default 60)
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo test --profile "$P" --features capi
  # The native C API, and picohttpparser's test suite on the phr ABI.
  scripts/test-c.sh
  # The llhttp drop-in agrees with llhttp (differential test).
  [ -d "$W/llhttp" ] || git clone -q --depth 1 --branch release/v9.4.4 https://github.com/nodejs/llhttp "$W/llhttp"
  LLHTTP="$W/llhttp" OUT="$W/lt" compat/llhttp/test/build.sh
  for seed in 1 2 3; do python3 compat/llhttp/test/diff.py "$W/lt" 3000 $seed; done
  # The httparse drop-in crate builds.
  cargo build --release --manifest-path compat/httparse/Cargo.toml
}

fuzz() {
  fuzz_tools
  scripts/fuzz.sh "${FUZZ_SECS:-60}"
}

"${1:-test}"

#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
#   ./ci.sh miri      the tests under Miri (nightly)
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo test --profile "$P"
  (cd bench && cargo build --release)
}

miri() {
  rustup toolchain install nightly --profile minimal --component miri,rust-src
  cargo +nightly miri test
}

"${1:-test}"

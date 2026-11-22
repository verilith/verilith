#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  # The references: libarchive, bsdtar, libzstd.
  apt libarchive-dev libarchive-tools libzstd1
  cargo test --profile "$P"
  # The C drop-in check.
  bash tests/c/run.sh
}

"${1:-test}"

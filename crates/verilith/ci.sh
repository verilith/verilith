#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  # Nothing on by default, and every feature resolves and builds.
  cargo check
  cargo check --all-features
  cargo doc --all-features --no-deps
}

"${1:-test}"

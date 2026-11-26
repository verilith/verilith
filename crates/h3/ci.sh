#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo test --profile "$P"
}

"${1:-test}"

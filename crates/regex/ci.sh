#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  # The tables are what the generator makes from RE2's, when a checkout is given.
  [ -z "${RE2_SRC:-}" ] || scripts/check_tables.sh "$RE2_SRC"
  cargo test --profile "$P"
  # The C API. The comparison with cre2 runs when RE2_PREFIX and CRE2_SRC are set.
  tests/capi/run.sh
}

"${1:-test}"

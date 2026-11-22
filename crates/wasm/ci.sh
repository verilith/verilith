#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
#   ./ci.sh differential   compare with wasmi on 20,000 generated modules
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  ./scripts/fetch-testsuite.sh
  # Spec tests, trusted primitives.
  cargo test --profile "$P"
  # The C API examples.
  ./scripts/capi.sh
}

differential() {
  cd fuzz && cargo run --release -- 20000 "${GITHUB_RUN_NUMBER:-1}"
}

"${1:-test}"

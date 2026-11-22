#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo test --profile "$P"
  # Tables are what the generators write.
  python3 tools/gen_unicode.py tests/data "$W/unicode_tables.rs"
  diff -q "$W/unicode_tables.rs" src/unicode/tables.rs
  python3 tools/gen_idna.py tests/data "$W/idna_tables.rs"
  diff -q "$W/idna_tables.rs" src/idna/tables.rs
  # The C API against ICU.
  apt libicu74
  scripts/icu_diff.sh 200000
}

"${1:-test}"

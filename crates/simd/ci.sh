#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  # Generated files are what the generators write.
  python3 tools/gen_x86.py src/x86.rs src/safe.rs src/x86_emu.rs
  python3 tools/gen_refs.py src/refs.rs
  python3 tools/gen_difftest.py tests/difftest.rs
  python3 tools/gen_wasm_x86.py src/wasm_x86.rs
  python3 tools/check_wasm_neon.py
  git diff --exit-code -- .
  # Differential tests against the CPU, which needs AVX2.
  grep -qw avx2 /proc/cpuinfo
  cargo test --profile "$P"
}

"${1:-test}"

#!/usr/bin/env bash
# Verifies the crate with Verus. Needs `cargo-verus` on PATH (a Verus build
# whose vstd matches the version pinned in Cargo.toml) and z3 (found via
# VERUS_Z3_PATH or next to the verus binary).
#
# Also fails if the source assumes anything it should prove: `assume` or
# `admit` anywhere, or an `external_body` outside the table accessors in
# src/data.rs (see TRUST.md).
set -euo pipefail
cd "$(dirname "$0")/.."
if grep -nE '\b(assume|admit)\s*\(' src/*.rs; then
  echo "error: assume/admit in the source" >&2
  exit 1
fi
if grep -nE 'external_body|verifier::external|axiom fn' src/*.rs | grep -vE '^src/data.rs:'; then
  echo "error: trusted code outside src/data.rs" >&2
  exit 1
fi
cargo verus "${VERUS_CMD:-verify}" -- "$@"

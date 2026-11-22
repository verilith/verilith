#!/usr/bin/env bash
# Verifies the crate with Verus. Needs `cargo-verus` on PATH (a Verus build
# from the commit in scripts/verus-version at the repository root, whose vstd
# matches the version pinned in the workspace Cargo.toml) and z3 (found via
# VERUS_Z3_PATH or next to the verus binary). Goes through Cargo so the
# verilith-core and verilith-simd dependencies resolve.
set -euo pipefail
cd "$(dirname "$0")/.."
exec cargo verus "${VERUS_CMD:-verify}" -- "$@"

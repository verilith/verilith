#!/usr/bin/env bash
# Verifies the crate with Verus. Needs `cargo-verus` on PATH (a Verus build,
# from the commit in .github/workflows/ci.yml, whose vstd matches the version
# pinned in Cargo.toml) and z3 (found via VERUS_Z3_PATH or next to the verus
# binary). Goes through Cargo so the vcore and vsimd dependencies resolve.
set -euo pipefail
cd "$(dirname "$0")/.."
cargo verus "${VERUS_CMD:-verify}" --features cjson -- "$@"

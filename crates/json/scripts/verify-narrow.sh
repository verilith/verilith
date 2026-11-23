#!/usr/bin/env bash
# Verifies the crate as 32-bit targets such as wasm32 build it: Verus
# compiles for wasm32-unknown-unknown, where `usize` is 32 bits, a token's
# positions are one `u32` and `MAX_INPUT` is 2^31 - 1 (spec.rs, parser.rs).
# scripts/verify.sh verifies the 64-bit layout. Needs what scripts/verify.sh
# needs, plus the wasm32-unknown-unknown standard library, which this adds.
set -euo pipefail
cd "$(dirname "$0")/.."
rustup target add wasm32-unknown-unknown > /dev/null 2>&1 || true
exec cargo verus "${VERUS_CMD:-verify}" --target wasm32-unknown-unknown -- "$@"

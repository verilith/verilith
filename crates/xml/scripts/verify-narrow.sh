#!/usr/bin/env bash
# Verifies the crate with the 32-bit token layout (`tape::Tok`, 16 bytes),
# the one 32-bit targets such as wasm32 build, on this 64-bit host: the
# feature `narrow-tokens` selects it. scripts/verify.sh verifies the 64-bit
# layout. Needs what scripts/verify.sh needs.
set -euo pipefail
cd "$(dirname "$0")/.."
exec cargo verus "${VERUS_CMD:-verify}" --features narrow-tokens -- "$@"

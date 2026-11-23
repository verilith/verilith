#!/usr/bin/env bash
# Verifies the crate as wasm32 builds it: Verus compiling for
# wasm32-unknown-unknown, so with a 32-bit usize and without the x86 and Arm
# paths. scripts/verify.sh verifies the host build. Needs what
# scripts/verify.sh needs.
set -euo pipefail
cd "$(dirname "$0")/.."
. ../../scripts/verus-version
rustup target add --toolchain "$VERUS_TOOLCHAIN" wasm32-unknown-unknown > /dev/null 2>&1
exec cargo verus "${VERUS_CMD:-verify}" --target wasm32-unknown-unknown -- "$@"

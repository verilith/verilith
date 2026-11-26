#!/usr/bin/env bash
# Runs the proofs (needs cargo-verus on PATH).
set -euo pipefail
cd "$(dirname "$0")/.."
exec cargo verus "${VERUS_CMD:-verify}" -- "$@"

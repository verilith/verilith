#!/usr/bin/env bash
# Runs every cargo-fuzz target under AddressSanitizer for $1 seconds each
# (default 60). Needs a nightly toolchain and `cargo install cargo-fuzz`.
set -euo pipefail
cd "$(dirname "$0")/.."
secs="${1:-60}"
for t in request capi chunked httparse_api; do
    echo "== $t"
    cargo +nightly fuzz run "$t" -- -max_total_time="$secs" -max_len=1024
done

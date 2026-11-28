#!/usr/bin/env bash
# Exact counts for WebP lossless prefix codes over the files given:
#   bench/webp-root/sweep.sh ROOT_BITS FILE...
# Builds an instrumented copy of crates/webp (instrument.py) in a temporary
# git worktree of HEAD, decodes the files, and prints the counters.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
bits=$1; shift
tmp=$(mktemp -d)
trap 'git -C "$root" worktree remove --force "$tmp/wt" > /dev/null 2>&1 || true; rm -rf "$tmp"' EXIT
git -C "$root" worktree add -q --detach "$tmp/wt" HEAD
python3 "$here/instrument.py" "$tmp/wt" "$bits"
mkdir -p "$tmp/wt/bench"; rm -rf "$tmp/wt/bench/webp-root"; cp -r "$here" "$tmp/wt/bench/webp-root"; rm -rf "$tmp/wt/bench/webp-root/target"
CARGO_TARGET_DIR="$tmp/target" cargo build -q --release --manifest-path "$tmp/wt/bench/webp-root/Cargo.toml"
"$tmp/target/release/webp-root" "$@"

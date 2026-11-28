#!/usr/bin/env bash
# Output size of one-shot DEFLATE for each block size (deflate::MAX_TOKS,
# tokens per block) in TOKENS, at levels 1, 6 and 9, over the files given.
#   bench/zlib-blocks/sweep.sh "4096 8192 16384 32768 65536" FILE...
# Builds each value from a temporary git worktree of HEAD, so the checkout
# is never changed. The sizes are exact: no timing is involved.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
tokens=$1; shift
tmp=$(mktemp -d)
trap 'git -C "$root" worktree remove --force "$tmp/wt" > /dev/null 2>&1 || true; rm -rf "$tmp"' EXIT
git -C "$root" worktree add -q --detach "$tmp/wt" HEAD
mkdir -p "$tmp/wt/bench"
cp -r "$here" "$tmp/wt/bench/zlib-blocks"
rm -rf "$tmp/wt/bench/zlib-blocks/target"
for t in $tokens; do
  sed -i -E "s/^pub const MAX_TOKS: usize = [0-9]+;/pub const MAX_TOKS: usize = $t;/" "$tmp/wt/crates/zlib/src/deflate.rs"
  grep -q "^pub const MAX_TOKS: usize = $t;" "$tmp/wt/crates/zlib/src/deflate.rs"
  CARGO_TARGET_DIR="$tmp/target" cargo build -q --release --manifest-path "$tmp/wt/bench/zlib-blocks/Cargo.toml"
  "$tmp/target/release/zlib-blocks" 1,6,9 "$@"
done

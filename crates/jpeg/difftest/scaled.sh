#!/usr/bin/env bash
# Compares decode_scaled with libjpeg-turbo's djpeg at 1/8, 1/4 and 1/2 (and
# the full-size decode at 8/8), byte for byte.
#   difftest/scaled.sh FILE...
# DJPEG is libjpeg-turbo 3.2.1's djpeg (default: $HOME/ext/ljtbuild/djpeg).
set -euo pipefail
cd "$(dirname "$0")/.."
djpeg=${DJPEG:-$HOME/ext/ljtbuild/djpeg}
cargo build --release -q --example scaled
bin=$(cargo metadata --format-version 1 --no-deps | python3 -c 'import json,sys; print(json.load(sys.stdin)["target_directory"])')/release/examples/scaled
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
same=0 differ=0 rejected=0
for f in "$@"; do
  for m in 1 2 4 8; do
    if ! "$djpeg" -scale "$m/8" -pnm -outfile "$tmp/r.pnm" "$f" 2> /dev/null; then
      continue
    fi
    if ! "$bin" "$m" "$f" "$tmp/v.pnm" 2> /dev/null; then
      rejected=$((rejected + 1)); echo "rejected: $f at $m/8"; continue
    fi
    if cmp -s "$tmp/r.pnm" "$tmp/v.pnm"; then same=$((same + 1)); else differ=$((differ + 1)); echo "differs: $f at $m/8"; fi
  done
done
echo "identical: $same, different: $differ, rejected by vjpeg only: $rejected"
[ "$differ" -eq 0 ]

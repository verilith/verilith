#!/bin/bash
# Runs each parser in its own process, ROUNDS times in rotating order, each
# for ITERS sustained iterations, and prints each parser's best ns/URL.
# Separate runs keep one parser's frequency boost or cache state from
# leaking into another's numbers.
#   EXT=~/ext bench/run.sh [ROUNDS] [ITERS] [CPU]
set -e
cd "$(dirname "$0")"
ROUNDS=${1:-5}; ITERS=${2:-50}; CPU=${3:-2}
DATA=${EXT:-$HOME/ext}/url-dataset/out.txt
RUSTFLAGS="-C target-cpu=x86-64-v3" cargo build --release -q
P=(vurl ada "curl (set)" "url" "curl (set+get)")
out=$(mktemp)
for r in $(seq 1 "$ROUNDS"); do
  for i in "${!P[@]}"; do
    p=${P[$(( (i + r) % ${#P[@]} ))]}
    taskset -c "$CPU" target/release/urlbench "$DATA" "$ITERS" "$p" | tail -n +2 >> "$out"
  done
done
for p in "vurl" "ada" "curl (set)" "url (servo)" "curl (set+get)"; do
  awk -v p="$p" 'index($0, p " ") == 1 { for (i = 1; i <= NF; i++) if ($i == "ns/url") v = $(i-1); if (best == "" || v < best) best = v } END { printf "%-15s %8.1f ns/URL\n", p, best }' "$out"
done
rm -f "$out"

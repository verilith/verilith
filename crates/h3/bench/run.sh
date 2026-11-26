#!/usr/bin/env bash
# Builds for this CPU and prints ns per stream for each implementation: each
# runs in a process of its own, pinned to one core; the table is the best of
# five such runs (each itself the best of 30 timed batches).
set -euo pipefail
cd "$(dirname "$0")"
RUSTFLAGS="-C target-cpu=native" cargo build --release -q
for _ in 1 2 3 4 5; do
  for p in verilith h3; do
    taskset -c "${CPU:-2}" ./target/release/h3bench "$p"
  done
done | awk -F'\t' '{
  k = $1 "\t" $2
  if (!(k in best)) order[n++] = k
  if (!(k in best) || $3 + 0 < best[k]) best[k] = $3 + 0
} END { for (i = 0; i < n; i++) { split(order[i], a, "\t"); printf "%-10s %-10s %8d ns\n", a[1], a[2], best[order[i]] } }'

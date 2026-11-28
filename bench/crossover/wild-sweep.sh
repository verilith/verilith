#!/usr/bin/env bash
# LZ4 decode time for each WILD_MAX in VALUES (verilith-core lz.rs):
#   bench/crossover/wild-sweep.sh "64 128 192 256 320 512" REPS FILE...
# Builds one lz4dec per value from a temporary git worktree of HEAD, then
# runs them in turn REPS times (interleaved, so drift in the machine's
# speed hits every value alike) and prints each value's fastest round per
# file, in ns per byte. This is timing, the check on a model, not a model.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
values=$1; reps=$2; shift 2
tmp=$(mktemp -d)
trap 'git -C "$root" worktree remove --force "$tmp/wt" > /dev/null 2>&1 || true; rm -rf "$tmp"' EXIT
git -C "$root" worktree add -q --detach "$tmp/wt" HEAD
mkdir -p "$tmp/wt/bench"; rm -rf "$tmp/wt/bench/crossover"
cp -r "$here" "$tmp/wt/bench/crossover"; rm -rf "$tmp/wt/bench/crossover/target"
for v in $values; do
  sed -i -E "s/^pub const WILD_MAX: usize = [0-9]+;/pub const WILD_MAX: usize = $v;/" "$tmp/wt/crates/core/src/lz.rs"
  grep -q "^pub const WILD_MAX: usize = $v;" "$tmp/wt/crates/core/src/lz.rs"
  CARGO_TARGET_DIR="$tmp/target" cargo build -q --release --manifest-path "$tmp/wt/bench/crossover/Cargo.toml" --bin lz4dec
  cp "$tmp/target/release/lz4dec" "$tmp/lz4dec-$v"
done
for r in $(seq "$reps"); do
  for v in $values; do
    "$tmp/lz4dec-$v" 20 "$@" | sed "s/^/$v\t/"
  done
done | python3 -c '
import sys, collections
best = collections.defaultdict(lambda: float("inf"))
for l in sys.stdin:
    v, f, t = l.split()
    best[(f, int(v))] = min(best[(f, int(v))], float(t))
files = sorted({f for f, _ in best}); vals = sorted({v for _, v in best})
print("file\t" + "\t".join(f"WILD_MAX={v}" for v in vals))
for f in files:
    print(f + "\t" + "\t".join(f"{best[(f, v)]:.4f}" for v in vals))
'

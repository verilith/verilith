#!/usr/bin/env bash
# Builds and runs the benchmarks: each row in its own process, three
# times, keeping the fastest. Prints a TSV: row, implementation, ns.
set -euo pipefail
cd "$(dirname "$0")"
[ -d vendor ] || ./setup.sh
cargo build --release -q
rows=$(./target/release/quicbench | tail -n +2 | cut -f1 | sort -u)
echo -e "row\timpl\tns"
for r in $rows; do
  for i in 1 2 3; do ./target/release/quicbench "$r" | tail -n +2; done |
    awk -F'\t' '{k=$1"\t"$2; if (!(k in m) || $3 < m[k]) m[k]=$3; if (!(k in o)) o[k]=n++} END {for (k in o) print o[k]"\t"k"\t"m[k]}' |
    sort -n | cut -f2-
done

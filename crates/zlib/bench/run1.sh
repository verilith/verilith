#!/bin/sh
# Runs each library alone in its own process, pinned to one core, and
# prints one table per mode. Usage: bench/run1.sh inflate|deflate DIR [ROUNDS] [CORE]
set -e
cd "$(dirname "$0")"
mode=$1; dir=$2; rounds=${3:-9}; core=${4:-2}
bin=target/release/vzlib-bench
for k in 0 1 2 3; do
    VZLIB_BENCH_ONLY=$k taskset -c "$core" "$bin" "$mode" "$dir" "$rounds" > "/tmp/vzlib-bench.$k"
done
# Column k+4 of run k is library k's number; the rest of the row is shared.
awk -F'\t' -v OFS='\t' 'FNR==1 {f++} f==1 {row[FNR]=$0; next} {split(row[FNR], r, "\t"); r[f+3]=$(f+3); s=r[1]; for (i=2; i<=length(r); i++) s=s OFS r[i]; row[FNR]=s} END {for (i=1; i<=FNR; i++) print row[i]}' /tmp/vzlib-bench.0 /tmp/vzlib-bench.1 /tmp/vzlib-bench.2 /tmp/vzlib-bench.3

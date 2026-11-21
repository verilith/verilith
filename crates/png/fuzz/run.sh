#!/bin/bash
# Mutation-fuzzes vpng against libpng: writes N mutants of the given seed
# files (CRCs repaired so the mutations reach the decoder) and compares the
# two decoders on each. Usage: fuzz/run.sh OUTDIR N SEED FILES...
set -euo pipefail
cd "$(dirname "$0")/.."
out=$1 n=$2 seed=$3; shift 3
python3 -I fuzz/mutate.py "$out" "$n" "$seed" "$@"
difftest/compare.sh "$out"/*.png

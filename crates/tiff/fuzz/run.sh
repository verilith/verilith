#!/usr/bin/env bash
# Mutation fuzzing against libtiff: writes N mutants of the seed files
# (fuzz/mutate.py) and decodes each with verilith-tiff and libtiff, as
# difftest/compare.sh does.
#   fuzz/run.sh OUT N SEED FILES...
# A mutant that both decode to different results, or that only verilith-tiff
# decodes, fails the run, but for the departures compare.sh counts; mutants
# that only libtiff decodes are counted.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=$1 n=$2 seed=$3
shift 3
rm -rf "$out"
python3 "$here/mutate.py" "$out" "$n" "$seed" "$@"
"$here/../difftest/compare.sh" "$out"/*.tif

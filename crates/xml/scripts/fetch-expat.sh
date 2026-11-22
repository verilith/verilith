#!/usr/bin/env bash
# Fetches libexpat at a pinned commit into target/upstream/libexpat, for
# the differential fuzzers (fuzz/) and the comparisons (bench/).
set -euo pipefail
cd "$(dirname "$0")/.."
UP=${UPSTREAM:-$PWD/target/upstream}
EXPAT_REV=2120251ef8e5fd5f398063b6508be27796689bd9   # R_2_7_3
d=$UP/libexpat
if [ ! -d "$d/.git" ]; then
  git init -q "$d"
  git -C "$d" remote add origin https://github.com/libexpat/libexpat
fi
if [ "$(git -C "$d" rev-parse HEAD 2>/dev/null)" != "$EXPAT_REV" ]; then
  git -C "$d" fetch -q --depth 1 origin "$EXPAT_REV"
  git -C "$d" checkout -q FETCH_HEAD
fi
echo "$d/expat"

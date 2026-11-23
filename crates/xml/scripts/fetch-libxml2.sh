#!/usr/bin/env bash
# Fetches libxml2 at a pinned commit into target/upstream/libxml2, for its
# test suite (scripts/test-libxml2.sh).
set -euo pipefail
cd "$(dirname "$0")/.."
UP=${UPSTREAM:-$PWD/target/upstream}
LIBXML2_REV=96498992efa48d52b0e8b83058bd88dbdaf153c1   # v2.15.4
d=$UP/libxml2
if [ ! -d "$d/.git" ]; then
  git init -q "$d"
  git -C "$d" remote add origin https://github.com/GNOME/libxml2
fi
if [ "$(git -C "$d" rev-parse HEAD 2>/dev/null)" != "$LIBXML2_REV" ]; then
  git -C "$d" fetch -q --depth 1 origin "$LIBXML2_REV"
  git -C "$d" checkout -q FETCH_HEAD
fi
echo "$d"

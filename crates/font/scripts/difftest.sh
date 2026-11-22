#!/usr/bin/env bash
# Differential test against OTS: runs both sanitizers on every file in the
# given directories and reports where they agree and differ, and checks
# that every font vfont emits is accepted by OTS and is unchanged by a
# second pass through vfont.
#   OTS=/path/to/ots-sanitize scripts/difftest.sh DIR...
set -uo pipefail
cd "$(dirname "$0")/.."
OTS=${OTS:-ots-sanitize}
V=${CARGO_TARGET_DIR:-$PWD/../../target}/release/examples/vfont-sanitize
cargo build --release --example vfont-sanitize 2>/dev/null
tmp=$(mktemp -d)
for d in "$@"; do
  both=0; ots=0; vf=0; none=0; crash=0; rej=0; nonidem=0
  for f in "$d"/*; do
    [ -f "$f" ] || continue
    "$OTS" "$f" "$tmp/o1" >/dev/null 2>&1; r1=$?
    timeout 60 "$V" "$f" "$tmp/o2" >/dev/null 2>&1; r2=$?
    if [ $r2 -gt 1 ]; then crash=$((crash+1)); echo "CRASH $f ($r2)"; fi
    if [ $r2 = 0 ]; then
      # What we emit must be a fixed point, and OTS must accept it.
      "$V" "$tmp/o2" "$tmp/o3" >/dev/null 2>&1 && cmp -s "$tmp/o2" "$tmp/o3" || { nonidem=$((nonidem+1)); echo "NOT-IDEMPOTENT $f"; }
      "$OTS" "$tmp/o2" "$tmp/o4" >/dev/null 2>&1 || { rej=$((rej+1)); echo "OTS-REFUSES-OUTPUT $f"; }
    fi
    if [ $r1 = 0 ] && [ $r2 = 0 ]; then both=$((both+1))
    elif [ $r1 = 0 ]; then ots=$((ots+1)); [ -n "${VERBOSE:-}" ] && echo "OTS-ONLY $f"
    elif [ $r2 = 0 ]; then vf=$((vf+1)); [ -n "${VERBOSE:-}" ] && echo "VFONT-ONLY $f"
    else none=$((none+1)); fi
  done
  echo "$d: both accept $both, only OTS $ots, only vfont $vf, both refuse $none, crashes $crash, outputs OTS refuses $rej, outputs not idempotent $nonidem"
done
rm -rf "$tmp"

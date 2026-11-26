#!/usr/bin/env bash
# Verifies crates with Verus and fails unless each reports 0 errors.
#   scripts/verify.sh [CRATE...]     (default: every verified crate)
# CRATE is a directory under crates/. Needs cargo-verus on PATH, the release
# in scripts/verus-version (scripts/install-verus.sh), and z3 (VERUS_Z3_PATH, or next to
# the verus binary). VERUS_CMD=focus skips re-verifying a crate's
# dependencies (they are still compiled).
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
# Dependencies first.
all="core sha2 simd checksum sync text xxhash zlib zstd brotli lz4 snappy json dns url http hpack h2 x509 png webp jpeg gif tiff font archive regex wasm xml"
[ $# -gt 0 ] && crates="$*" || crates=$all
log=${VERIFY_LOG_DIR:-$root/target/verify}
mkdir -p "$log"
status=0
for c in $crates; do
  s="$root/crates/$c/scripts/verify.sh"
  [ -x "$s" ] || { echo "$c: no scripts/verify.sh" >&2; status=1; continue; }
  start=$(date +%s)
  "$s" > "$log/$c.log" 2>&1; rc=$?
  line=$(grep -E "verification results:: [0-9]+ verified, [0-9]+ errors" "$log/$c.log" | tail -1)
  if [ $rc -eq 0 ] && [ -z "$line" ]; then
    # Cargo had nothing to rebuild: the crate was verified by an earlier run.
    echo "ok   $c: unchanged since it was last verified"
  elif [ $rc -eq 0 ] && echo "$line" | grep -qE ", 0 errors"; then
    echo "ok   $c: ${line#*:: } ($(( $(date +%s) - start ))s)"
  else
    echo "FAIL $c (exit $rc): ${line:-no result line}; see $log/$c.log"; status=1
  fi
done
exit $status

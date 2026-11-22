#!/usr/bin/env bash
# crosscheck.sh CRATE...: verifies each crate twice, with `cargo verus`
# (the way the Verus project supports) and through Buck2 (all of its parts),
# and fails unless both count the same number of verified proofs. This is
# the check on the Buck2 rules: a proof they stopped checking is a count
# that comes up short.
set -uo pipefail
cd "$(dirname "$0")/.."
status=0
for c in "$@"; do
  # Cargo prints no count for a crate it verified before and finds unchanged.
  rm -rf "${CARGO_TARGET_DIR:-target}"/verus-partial/debug/.fingerprint/verilith-"$c"-*
  cargo_line=$(VERUS_CMD=focus scripts/verify.sh "$c")
  echo "cargo: $cargo_line"
  buck_line=$(scripts/prove.sh "$c") || { echo "FAIL $c: Buck2 did not verify it"; status=1; continue; }
  echo "buck2: $buck_line"
  a=$(echo "$cargo_line" | sed -nE 's/^ok +[^:]+: ([0-9]+) verified, 0 errors.*/\1/p')
  b=$(echo "$buck_line" | sed -nE 's/^ok +[^:]+: ([0-9]+) verified, 0 errors.*/\1/p')
  if [ -n "$a" ] && [ "$a" = "$b" ] && [ "$a" -gt 0 ]; then
    echo "same $c: $a verified both ways"
  else
    echo "FAIL $c: cargo verus counts '${a:-none}', Buck2 counts '${b:-none}'"; status=1
  fi
done
exit $status

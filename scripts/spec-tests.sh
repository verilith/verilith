#!/usr/bin/env bash
# Checks crates' specifications themselves against upstream conformance
# suites. A proof shows that the code computes what spec.rs says; this
# shows that what spec.rs says is what the suite expects.
#   scripts/spec-tests.sh CRATE...     (default: every crate with spec-tests/)
#
# For each crate, crates/CRATE/spec-tests/gen.sh fetches the suite at a
# pinned commit and turns each case into a proof function whose one
# assertion, `assert(spec_fn(input) == expected) by (compute_only)`, Verus
# proves by evaluating the spec function on the concrete input with its
# interpreter. No SMT solver, no exec code, no lemma is involved: the spec
# is run as written. Fails unless every case is verified.
#
# Needs cargo-verus on PATH, as scripts/verify.sh does.
set -uo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
UP=$ROOT/target/upstream
export ROOT UP
# fetch URL DIR REV: a shallow clone of REV.
fetch() {
  if [ ! -d "$2/.git" ]; then
    git init -q "$2"
    git -C "$2" remote add origin "$1"
  fi
  git -C "$2" fetch -q --depth 1 origin "$3" && git -C "$2" checkout -q FETCH_HEAD
}
if [ $# -gt 0 ]; then crates="$*"; else
  crates=$(cd "$ROOT/crates" && for d in */spec-tests/gen.sh; do echo "${d%%/*}"; done)
fi
mkdir -p "$UP" "$ROOT/target/spec-tests"
status=0
for c in $crates; do
  dir=$ROOT/crates/$c/spec-tests
  log=$ROOT/target/spec-tests/$c.log
  [ -f "$dir/gen.sh" ] || { echo "FAIL $c: no spec-tests/gen.sh"; status=1; continue; }
  start=$(date +%s)
  if ! (cd "$dir" && . ./gen.sh) > "$log" 2>&1; then
    echo "FAIL $c: generating the cases failed; see $log"; status=1; continue
  fi
  want=$(cat "$dir/src/cases.count")
  # Extra Verus flags, such as a larger --rlimit, which also bounds the
  # evaluator's time.
  args=$(cat "$dir/verus-args" 2>/dev/null || true)
  # shellcheck disable=SC2086
  (cd "$dir" && CARGO_TARGET_DIR=$ROOT/target/spec-tests/target cargo verus focus -- $args) >> "$log" 2>&1
  rc=$?
  line=$(grep -E "verification results:: [0-9]+ verified, [0-9]+ errors" "$log" | tail -1)
  got=$(echo "$line" | sed -E 's/.*:: ([0-9]+) verified.*/\1/')
  if [ $rc -eq 0 ] && echo "$line" | grep -qE ", 0 errors" && [ "${got:-0}" -ge "$want" ]; then
    echo "ok   $c: $want cases from $(cat "$dir/src/cases.source") ($(( $(date +%s) - start ))s)"
  else
    echo "FAIL $c (exit $rc): ${line:-no result line}, $want cases; see $log"
    grep -B2 -A6 "^error" "$log" | head -40
    status=1
  fi
done
exit $status

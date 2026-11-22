#!/usr/bin/env bash
# Verifies crates with Verus through Buck2, and prints one line for each.
#   scripts/prove.sh [CRATE | TARGET]...     (default: every verified crate)
# CRATE is a directory under crates/ (zlib); TARGET is a Buck2 target, such
# as one part of a crate: '//crates/wasm:wasm[part2]'. Needs buck2
# (scripts/install-buck2.sh) and, on PATH, verus built from the commit in
# scripts/verus-version. With PROVE_OUT set, the result files are also
# copied into that directory.
set -euo pipefail
cd "$(dirname "$0")/.."
targets=()
for a in "$@"; do
  case "$a" in
    //*) targets+=("$a") ;;
    *) targets+=("//crates/$a:$a") ;;
  esac
done
[ ${#targets[@]} -gt 0 ] || targets=(//crates/...)
# stdout is "TARGET PATH" for each target built; a failure prints Verus's
# errors and leaves through set -e.
built=$(buck2 build --console simple --show-full-output "${targets[@]}")
echo "$built" | python3 -c '
import json, os, shutil, sys
out = os.environ.get("PROVE_OUT")
n = 0
for line in sys.stdin:
    target, _, path = line.strip().partition(" ")
    if not path:
        continue
    r = json.load(open(path))
    crate, verified = r.get("crate"), r.get("verified")
    # verus.py writes a result only for a run with no errors; check anyway.
    if r.get("errors") != 0 or not isinstance(verified, int) or not crate:
        sys.exit("FAIL %s: %s" % (target, r))
    part = secs = ""
    if r.get("parts", 1) > 1 and "part" in r:
        part = " part %d/%d" % (r["part"] + 1, r["parts"])
    if "seconds" in r:
        secs = " (%.0fs)" % r["seconds"]
    print("ok   %s%s: %d verified, 0 errors%s" % (crate, part, verified, secs))
    if out:
        os.makedirs(out, exist_ok=True)
        name = crate + part.replace(" ", "-").replace("/", "of") + ".json"
        shutil.copy(path, os.path.join(out, name))
    n += 1
if n == 0:
    sys.exit("FAIL: Buck2 built nothing")
'

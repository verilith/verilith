#!/usr/bin/env bash
# Differential test of vhttp's llhttp.wasm, run through the callbacks undici
# registers (trace.mjs), with compat/llhttp/test/diff.py's message
# generator and checks:
#
#   compat/undici/test/run.sh REF_WASM [N] [SEEDS...]
#
# REF_WASM is the reference: undici's own lib/llhttp/llhttp.wasm (stock
# llhttp), or a native trace binary to compare against vhttp's
# native llhttp drop-in (compat/llhttp/test/build.sh's trace-vhttp).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
ref=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
n=${2:-1000}
shift 2 || shift $#
seeds=${*:-1}
"$here/../build.sh" > /dev/null
out=$root/target/undici/diff
mkdir -p "$out"
rm -f "$out/trace-vhttp" "$out/trace-llhttp"
printf '#!/bin/sh\nexec node %s %s "$@"\n' "$here/trace.mjs" "$root/target/undici/llhttp.wasm" > "$out/trace-vhttp"
if [ -x "$ref" ] && [ "${ref%.wasm}" = "$ref" ]; then
    # The wasm callbacks have no chunk events, so leave those lines out.
    printf '#!/bin/sh\n"%s" "$@" | LC_ALL=C grep -av "^chunk "\nexit 0\n' "$ref" > "$out/trace-llhttp"
else
    printf '#!/bin/sh\nexec node %s %s "$@"\n' "$here/trace.mjs" "$ref" > "$out/trace-llhttp"
fi
chmod +x "$out/trace-vhttp" "$out/trace-llhttp"
status=0
for s in $seeds; do
    python3 "$root/compat/llhttp/test/diff.py" "$out" "$n" "$s" || status=1
done
exit $status

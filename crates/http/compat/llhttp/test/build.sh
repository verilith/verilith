#!/usr/bin/env bash
# Builds the trace harness twice: against llhttp ($LLHTTP, a checkout of an
# llhttp release branch) and against vhttp's drop-in. Output in $OUT.
set -euo pipefail
cd "$(dirname "$0")/.."
OUT=${OUT:-target}
mkdir -p "$OUT"
cargo build --profile release-abort --features llhttp-abi --manifest-path ../../Cargo.toml -q
cc -O2 -Wall -Iinclude test/trace.c src/api.c src/http.c "${CARGO_TARGET_DIR:-../../../../target}/release-abort/libverilith_http.a" -lpthread -ldl -lm -o "$OUT/trace-vhttp"
if [ -n "${LLHTTP:-}" ]; then
  cc -O2 -Wall -I"$LLHTTP/include" test/trace.c "$LLHTTP"/src/llhttp.c "$LLHTTP"/src/api.c "$LLHTTP"/src/http.c -o "$OUT/trace-llhttp"
  # The drop-in with lenient parsers on llhttp's own parser (llhttp-lenient).
  cargo build --profile release-abort --features llhttp-lenient --manifest-path ../../Cargo.toml -q --target-dir ../../target/lenient
  cc -O2 -Wall -Iinclude -I"$LLHTTP/src" test/trace.c src/lenient.c src/api.c src/http.c \
    ../../target/lenient/release-abort/libverilith_http.a -lpthread -ldl -lm -o "$OUT/trace-vhttp-lenient"
fi

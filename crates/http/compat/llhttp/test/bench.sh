#!/usr/bin/env bash
# ns per message through llhttp's API, llhttp against vhttp's drop-in, on
# the README's benchmark messages (test/msg, the same as bench/src/main.rs).
# $LLHTTP is a checkout of an llhttp release branch (bench/run.sh fetches
# one into bench/ext/llhttp). Both are built for this CPU. Each parser runs
# in processes of its own, pinned to one core, five sustained runs each;
# the best run counts.
set -euo pipefail
cd "$(dirname "$0")/.."
LLHTTP=${LLHTTP:-../../bench/ext/llhttp}
OUT=${OUT:-../../target/llhttp-bench}
mkdir -p "$OUT"
CARGO_TARGET_DIR="$OUT/target" RUSTFLAGS="-C target-cpu=native" cargo build --profile release-abort --features llhttp-abi --manifest-path ../../Cargo.toml -q
cc -O3 -march=native -Iinclude test/bench.c src/api.c src/http.c "$OUT/target/release-abort/libverilith_http.a" -lpthread -ldl -lm -o "$OUT/bench-vhttp"
cc -O3 -march=native -I"$LLHTTP/include" test/bench.c "$LLHTTP"/src/llhttp.c "$LLHTTP"/src/api.c "$LLHTTP"/src/http.c -o "$OUT/bench-llhttp"
for t in llhttp vhttp; do
  for _ in 1 2 3 4 5; do
    taskset -c "${CPU:-2}" "$OUT/bench-$t" req test/msg/small.txt test/msg/pico.txt test/msg/browser.txt
    taskset -c "${CPU:-2}" "$OUT/bench-$t" res test/msg/response.txt
  done | awk -v t="$t" '{ k = $1; sub(".*/", "", k); sub("\\.txt$", "", k); if (!(k in b)) o[n++] = k; if (!(k in b) || $2 < b[k]) b[k] = $2 }
    END { printf "%s:", t; for (i = 0; i < n; i++) printf " %s %d", o[i], b[o[i]]; print "" }'
done

#!/usr/bin/env bash
# Fetches picohttpparser and llhttp at the revisions the README's numbers
# use, builds everything for this CPU, and prints ns per message for each
# parser: each parser runs in a process of its own, pinned to one core, for
# a sustained 15 x 50000 messages per run; the table is the best of five
# such runs.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p ext
[ -d ext/picohttpparser ] || { git clone -q https://github.com/h2o/picohttpparser ext/picohttpparser && git -C ext/picohttpparser checkout -q dd573d8fa9264c646a400e96ce9f07dea6f156e4; }
[ -d ext/llhttp ] || git clone -q --depth 1 --branch release/v9.4.4 https://github.com/nodejs/llhttp ext/llhttp
RUSTFLAGS="-C target-cpu=native" cargo build --release -q
PARSERS=("vhttp (head + framing)" "vhttp (head only)" "vhttp::httparse" "httparse" "picohttpparser" "llhttp")
for _ in 1 2 3 4 5; do
  for p in "${PARSERS[@]}"; do
    BENCH_ONLY="$p" taskset -c "${CPU:-2}" ./target/release/vhttp-bench
  done
done | awk -F'\t' 'NF == 3 && $3 + 0 > 0 {
  k = $1 "\t" $2
  if (!(k in best)) order[n++] = k
  if (!(k in best) || $3 < best[k]) best[k] = $3
} END { print "message\tparser\tns/msg"; for (i = 0; i < n; i++) print order[i] "\t" best[order[i]] }'

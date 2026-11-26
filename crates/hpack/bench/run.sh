#!/usr/bin/env bash
# Fetches nghttp2 1.70.0 and h2 0.4.21, builds everything for this CPU, and
# prints, for each workload and encoder, ns per header block and bytes per
# block. Each encoder runs in a process of its own, pinned to one core; the
# table is the best of five runs.
#
# h2's HPACK encoder is private; ext/h2 is h2's crates.io source with one
# line changed (`mod hpack;` made `pub mod hpack;`).
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p ext
if [ ! -d ext/nghttp2 ]; then
  curl -sSfL https://github.com/nghttp2/nghttp2/releases/download/v1.70.0/nghttp2-1.70.0.tar.xz | tar xJ -C ext
  mv ext/nghttp2-1.70.0 ext/nghttp2
fi
if [ ! -d ext/h2 ]; then
  curl -sSfL https://static.crates.io/crates/h2/h2-0.4.21.crate | tar xz -C ext
  mv ext/h2-0.4.21 ext/h2
  sed -i.bak 's/^mod hpack;$/#[allow(missing_docs)] pub mod hpack;/' ext/h2/src/lib.rs
  grep -q '^#\[allow(missing_docs)\] pub mod hpack;$' ext/h2/src/lib.rs
fi
RUSTFLAGS="-C target-cpu=native" cargo build --release -q
ENCODERS=(vhpack h2 nghttp2)
for _ in 1 2 3 4 5; do
  for e in "${ENCODERS[@]}"; do
    if command -v taskset > /dev/null; then
      BENCH_ONLY="$e" taskset -c "${CPU:-2}" ./target/release/vhpack-bench
    else
      BENCH_ONLY="$e" ./target/release/vhpack-bench
    fi
  done
done | awk -F'\t' 'NF == 4 && $3 + 0 > 0 {
  k = $1 "\t" $2
  if (!(k in best)) { order[n++] = k; bytes[k] = $4 }
  if (!(k in best) || $3 < best[k]) best[k] = $3
} END { print "workload\tencoder\tns/block\tbytes/block"; for (i = 0; i < n; i++) print order[i] "\t" best[order[i]] "\t" bytes[order[i]] }'

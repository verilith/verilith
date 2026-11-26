#!/usr/bin/env bash
# Fetches nghttp2 1.70.0, builds the benchmark for this CPU, and prints the
# table in ../README.md (best of ROUNDS rounds, pinned to one core).
#   bench/run.sh [ROUNDS]          the benchmark
#   bench/run.sh agree [CASES]     the differential check against h2 and nghttp2
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p ext
v=1.70.0
if [ ! -d ext/nghttp2-$v ]; then
  curl -sSfL --retry 3 -o ext/ng.tar.xz https://github.com/nghttp2/nghttp2/releases/download/v$v/nghttp2-$v.tar.xz
  tar -C ext -xf ext/ng.tar.xz && rm ext/ng.tar.xz
fi
export NGHTTP2_LIB=$PWD/ext/nghttp2-$v/lib
RUSTFLAGS="-C target-cpu=native" cargo build --release -q
exec taskset -c "${CPU:-2}" ./target/release/vh2-bench "$@"

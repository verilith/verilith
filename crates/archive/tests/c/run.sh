#!/usr/bin/env bash
# The drop-in check: one C program written against <archive.h>, linked once
# with the system's libarchive and once with varchive, must print the same
# thing for every archive in tests/data. Needs libarchive's headers
# (libarchive-dev, or `brew install libarchive`) and cargo.
set -euo pipefail
cd "$(dirname "$0")/../.."
out=${TMPDIR:-/tmp}/varchive-c-$$
mkdir -p "$out"
inc=""; lib="-larchive"
if [ -d /opt/homebrew/opt/libarchive ]; then
  inc="-I/opt/homebrew/opt/libarchive/include"; lib="-L/opt/homebrew/opt/libarchive/lib -larchive"
fi
cargo build -q --release --features libarchive-abi --target-dir "$out/target"
cc -O2 $inc tests/c/lsar.c $lib -o "$out/lsar-libarchive"
sys="-lpthread -ldl -lm"
[ "$(uname -s)" = Darwin ] && sys="-framework CoreFoundation"
cc -O2 $inc tests/c/lsar.c "$out/target/release/libverilith_archive.a" $sys -o "$out/lsar-varchive"
"$out/lsar-libarchive" tests/data/* > "$out/a.txt"
"$out/lsar-varchive" tests/data/* > "$out/b.txt"
if diff "$out/a.txt" "$out/b.txt"; then
  echo "ok: $(wc -l < "$out/a.txt" | tr -d ' ') lines identical"
  rm -rf "$out"
else
  echo "FAILED: outputs differ (kept in $out)"; exit 1
fi

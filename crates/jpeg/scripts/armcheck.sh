#!/usr/bin/env bash
# Checks the AArch64 build (the NEON paths) against the x86-64 build on an
# x86-64 machine: decodes every file in the given directories with both, the
# AArch64 one under qemu-aarch64, and compares a hash of the pixels. Needs
# the aarch64-unknown-linux-gnu Rust target, aarch64-linux-gnu-gcc and
# qemu-aarch64. LIBJPEG_SRC is a libjpeg-turbo checkout and LIBJPEG_BUILD its
# build directory (for turbojpeg.h and jconfig.h only).
#
#   scripts/armcheck.sh DIR...
set -euo pipefail
cd "$(dirname "$0")/.."
S=${LIBJPEG_SRC:-$HOME/ext/libjpeg-turbo}
B=${LIBJPEG_BUILD:-$HOME/ext/ljtbuild}
export CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER=aarch64-linux-gnu-gcc
cargo build --release --features turbojpeg-abi --target aarch64-unknown-linux-gnu --target-dir target/a64
cargo build --release --features turbojpeg-abi --target-dir target/tj
T=$(mktemp -d)
aarch64-linux-gnu-gcc -O2 -static -I"$S/src" -I"$B" -o "$T/hash_a64" difftest/hash.c \
  target/a64/aarch64-unknown-linux-gnu/release/libverilith_jpeg.a -lpthread -lm -ldl 2>/dev/null
cc -O2 -I"$S/src" -I"$B" -o "$T/hash_x86" difftest/hash.c target/tj/release/libverilith_jpeg.a -lpthread -lm -ldl
bad=0
for d in "$@"; do
  find "$d" -maxdepth 1 -type f | sort | xargs -n 200 "$T/hash_x86" > "$T/x86.txt"
  find "$d" -maxdepth 1 -type f | sort | xargs -n 200 qemu-aarch64 "$T/hash_a64" > "$T/a64.txt"
  n=$(diff "$T/x86.txt" "$T/a64.txt" | grep -c '^<' || true)
  echo "$d: $(wc -l < "$T/x86.txt") files, $n differ"
  [ "$n" = 0 ] || bad=1
done
rm -rf "$T"
exit $bad

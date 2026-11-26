#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo test --profile "$P"
  # Without std: a bare-metal build, and the tests with the vector kernels
  # chosen at compile time instead of detected.
  rustup target add thumbv7em-none-eabihf > /dev/null
  cargo build --profile "$P" --no-default-features --target thumbv7em-none-eabihf
  RUSTFLAGS="-C target-cpu=native" CARGO_TARGET_DIR="$T/nostd" cargo test --profile "$P" --no-default-features
  # The crc32x and udot kernels, on emulated AArch64.
  if [ -n "${CI:-}" ]; then
    apt qemu-user gcc-aarch64-linux-gnu
    rustup target add aarch64-unknown-linux-gnu
    CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER=aarch64-linux-gnu-gcc \
    CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER="qemu-aarch64 -cpu max -L /usr/aarch64-linux-gnu" \
      cargo test --profile "$P" --target aarch64-unknown-linux-gnu
  fi
}

"${1:-test}"

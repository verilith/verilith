#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  # The round calls in src/compress.rs are generated.
  python3 tools/gen_rounds.py --check
  cargo test --profile "$P"
  cargo test --profile "$P" --features openssl-abi --test openssl
  # The ARMv8 SHA2 kernel, on emulated AArch64 (on an x86 runner; the Arm
  # runner runs it natively above).
  if [ -n "${CI:-}" ] && [ "$(uname -m)" = x86_64 ]; then
    apt qemu-user gcc-aarch64-linux-gnu
    rustup target add aarch64-unknown-linux-gnu
    CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER=aarch64-linux-gnu-gcc \
    CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER="qemu-aarch64 -cpu max -L /usr/aarch64-linux-gnu" \
      cargo test --profile "$P" --target aarch64-unknown-linux-gnu --test kernels --test vectors
  fi
}

"${1:-test}"

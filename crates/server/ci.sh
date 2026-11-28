#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests, then the constant-time check
#   ./ci.sh ctstatic  the static constant-time check of the kTLS key layout
#                     (x86-64 and AArch64; needs Python with capstone and
#                     pyelftools, and on x86-64 gcc-aarch64-linux-gnu)
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo test --profile "$P"
  ctstatic
}

# The static constant-time check (../../scripts/ctcheck.py) of the one
# place this crate handles a TLS secret, the key layout for kTLS
# (examples/ctcheck.rs), on x86-64 and AArch64, as in ../aes/ci.sh.
ctstatic() {
  if [ "$(uname -s)" != Linux ]; then echo "ctstatic: Linux only, skipped"; return; fi
  if [ -n "${CI:-}" ]; then python3 -m pip install -q capstone==5.0.7 pyelftools==0.33; fi
  local t="$T/ctcheck-$crate"
  CARGO_TARGET_DIR="$t" cargo clean -q -p verilith-server
  RUSTFLAGS="-C remark=stack-frame-layout" CARGO_TARGET_DIR="$t" \
    cargo build --profile "$P" --example ctcheck 2> "$t-x86.frames" || { cat "$t-x86.frames"; exit 1; }
  python3 ../../scripts/ctcheck.py ctcheck.json "$t/$P/examples/ctcheck" --frames "$t-x86.frames"
  # The dev-dependencies include aws-lc, C, which needs a C toolchain and
  # headers for AArch64: the GNU cross compiler (on an Arm runner, the
  # native one).
  local a64=aarch64-unknown-linux-gnu
  rustup target add "$a64"
  if [ "$(uname -m)" = x86_64 ]; then
    apt gcc-aarch64-linux-gnu
    export CC_aarch64_unknown_linux_gnu=aarch64-linux-gnu-gcc AR_aarch64_unknown_linux_gnu=aarch64-linux-gnu-ar \
      CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER=aarch64-linux-gnu-gcc
  fi
  RUSTFLAGS="-C remark=stack-frame-layout" CARGO_TARGET_DIR="$t" \
    cargo build --profile "$P" --example ctcheck --target "$a64" 2> "$t-a64.frames" \
    || { cat "$t-a64.frames"; exit 1; }
  python3 ../../scripts/ctcheck.py ctcheck.json "$t/$a64/$P/examples/ctcheck" --frames "$t-a64.frames"
  echo "ctstatic: no secret-dependent branches, addresses or variable-time instructions"
}

"${1:-test}"

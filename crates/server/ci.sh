#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests, then the constant-time check
#   ./ci.sh ctstatic  the static constant-time check of the kTLS key layout
#                     (x86-64 and AArch64; needs Python with capstone and
#                     pyelftools, and clang)
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
  # The dev-dependencies include aws-lc, C, built for AArch64 with clang.
  rustup target add aarch64-unknown-linux-musl
  CC_aarch64_unknown_linux_musl="clang --target=aarch64-linux-musl" AR_aarch64_unknown_linux_musl=llvm-ar \
  RUSTFLAGS="-C remark=stack-frame-layout -C linker=rust-lld" CARGO_TARGET_DIR="$t" \
    cargo build --profile "$P" --example ctcheck --target aarch64-unknown-linux-musl 2> "$t-a64.frames" \
    || { cat "$t-a64.frames"; exit 1; }
  python3 ../../scripts/ctcheck.py ctcheck.json "$t/aarch64-unknown-linux-musl/$P/examples/ctcheck" --frames "$t-a64.frames"
  echo "ctstatic: no secret-dependent branches, addresses or variable-time instructions"
}

"${1:-test}"

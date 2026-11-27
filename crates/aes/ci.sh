#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests, then the constant-time check
#   ./ci.sh ct        the Valgrind constant-time check only (x86-64)
#   ./ci.sh ctstatic  the static constant-time check of the machine code only
#                     (x86-64 and AArch64; needs Python with capstone and
#                     pyelftools)
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo test --profile "$P"
  # no_std, on targets with no std at all (the rlib), in the release
  # profile and in dev (dev compiles every function, so it is what catches
  # an intrinsic LLVM cannot lower on a target).
  for t in thumbv7em-none-eabihf aarch64-unknown-none x86_64-unknown-none; do
    rustup target add "$t"
    for p in "$P" dev; do
      cargo rustc --profile "$p" --lib --crate-type rlib --no-default-features --target "$t"
    done
  done
  # The AArch64 kernels on emulated AArch64 (on an x86 runner; the Arm
  # runner runs them natively above).
  if [ -n "${CI:-}" ] && [ "$(uname -m)" = x86_64 ]; then
    apt qemu-user gcc-aarch64-linux-gnu
    rustup target add aarch64-unknown-linux-gnu
    CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER=aarch64-linux-gnu-gcc \
    CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER="qemu-aarch64 -cpu max -L /usr/aarch64-linux-gnu" \
      cargo test --profile "$P" --target aarch64-unknown-linux-gnu
  fi
  ct
  ctstatic
}

# The constant-time check (examples/ctgrind.rs): Valgrind's memcheck, with
# the secrets marked undefined, must report nothing; and must report each of
# the two leaking controls, or the check is not seeing what it should.
ct() {
  if [ "$(uname -m)" != x86_64 ]; then echo "ct: x86-64 only, skipped"; return; fi
  apt valgrind
  cargo build --profile "$P" --example ctgrind
  local bin="$T/$P/examples/ctgrind" vg="valgrind -q --error-exitcode=1"
  for c in branch index; do
    if $vg "$bin" --control "$c" 2> /dev/null; then
      echo "ct: memcheck missed the $c control"; exit 1
    fi
  done
  $vg "$bin"
  echo "ct: no secret-dependent branches or addresses"
}

# The static constant-time check (../../scripts/ctcheck.py): a taint
# analysis of the machine code of every entry point (key expansion, H, the
# block cipher, and sealing and opening on the AES-NI, VAES and AArch64
# paths), for every input, on the binary as this profile builds it for
# x86-64 and for AArch64. LLVM's stack-frame-layout remarks tell it which
# stack slots are variables; they do not change the code (the build with
# them is the one checked). Each control in examples/ctcheck.rs must be
# reported, or the check is not seeing what it should.
ctstatic() {
  if [ -n "${CI:-}" ]; then python3 -m pip install -q capstone==5.0.7 pyelftools==0.33; fi
  local t="$T/ctcheck-$crate"
  # The remarks come only from a build that compiles the crate, so clean it.
  CARGO_TARGET_DIR="$t" cargo clean -q -p verilith-aes
  RUSTFLAGS="-C remark=stack-frame-layout" CARGO_TARGET_DIR="$t" \
    cargo build --profile "$P" --example ctcheck 2> "$t-x86.frames" || { cat "$t-x86.frames"; exit 1; }
  python3 ../../scripts/ctcheck.py ctcheck.json "$t/$P/examples/ctcheck" --frames "$t-x86.frames"
  # AArch64 (musl, so that rust-lld links it with no C toolchain for it).
  rustup target add aarch64-unknown-linux-musl
  RUSTFLAGS="-C remark=stack-frame-layout -C linker=rust-lld" CARGO_TARGET_DIR="$t" \
    cargo build --profile "$P" --example ctcheck --target aarch64-unknown-linux-musl 2> "$t-a64.frames" \
    || { cat "$t-a64.frames"; exit 1; }
  python3 ../../scripts/ctcheck.py ctcheck.json "$t/aarch64-unknown-linux-musl/$P/examples/ctcheck" --frames "$t-a64.frames"
  echo "ctstatic: no secret-dependent branches, addresses or variable-time instructions"
}

"${1:-test}"

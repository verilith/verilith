#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests, then the constant-time checks
#   ./ci.sh ct        the Valgrind constant-time check only (x86-64)
#   ./ci.sh ctstatic  the static constant-time check of the machine code only
#                     (x86-64 and AArch64; needs Python with capstone and
#                     pyelftools)
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo test --profile "$P"
  ct
  ctstatic
}

# The constant-time check of the key schedule (examples/ctgrind.rs):
# Valgrind's memcheck, with the secrets marked undefined, must report
# nothing; and must report the leaking control, or the check is not seeing
# what it should.
ct() {
  if [ "$(uname -m)" != x86_64 ]; then echo "ct: x86-64 only, skipped"; return; fi
  apt valgrind
  cargo build --profile "$P" --features ctgrind --example ctgrind
  local bin="$T/$P/examples/ctgrind" vg="valgrind -q --error-exitcode=1"
  if $vg "$bin" --control compare 2> /dev/null; then
    echo "ct: memcheck missed the compare control"; exit 1
  fi
  $vg "$bin"
  echo "ct: no secret-dependent branches or addresses"
}

# The static constant-time check (../../scripts/ctcheck.py) of this crate's
# own code on secrets (examples/ctcheck.rs), on x86-64 and AArch64, as in
# ../aes/ci.sh.
ctstatic() {
  if [ -n "${CI:-}" ]; then python3 -m pip install -q capstone==5.0.7 pyelftools==0.33; fi
  local t="$T/ctcheck-$crate"
  CARGO_TARGET_DIR="$t" cargo clean -q -p verilith-tls
  RUSTFLAGS="-C remark=stack-frame-layout" CARGO_TARGET_DIR="$t" \
    cargo build --profile "$P" --example ctcheck 2> "$t-x86.frames" || { cat "$t-x86.frames"; exit 1; }
  python3 ../../scripts/ctcheck.py ctcheck.json "$t/$P/examples/ctcheck" --frames "$t-x86.frames"
  rustup target add aarch64-unknown-linux-musl
  RUSTFLAGS="-C remark=stack-frame-layout -C linker=rust-lld" CARGO_TARGET_DIR="$t" \
    cargo build --profile "$P" --example ctcheck --target aarch64-unknown-linux-musl 2> "$t-a64.frames" \
    || { cat "$t-a64.frames"; exit 1; }
  python3 ../../scripts/ctcheck.py ctcheck.json "$t/aarch64-unknown-linux-musl/$P/examples/ctcheck" --frames "$t-a64.frames"
  echo "ctstatic: no secret-dependent branches, addresses or variable-time instructions"
}

"${1:-test}"

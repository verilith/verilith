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
  # The round calls in src/compress.rs are generated.
  python3 tools/gen_rounds.py --check
  cargo test --profile "$P"
  cargo test --profile "$P" --features openssl-abi --test openssl --test openssl512
  cargo test --profile "$P" --features digest,digest010,oid --test digest
  # no_std, on targets with no std at all (the rlib: the staticlib needs a
  # panic handler), with the digest traits. Each in the release profile and
  # in dev: dev compiles every function, including kernels a release build
  # drops as dead code, so it is what catches an intrinsic LLVM cannot lower
  # on a target (x86_64-unknown-none has no SSE registers; see src/cpu.rs).
  for t in thumbv7em-none-eabihf aarch64-unknown-none x86_64-unknown-none; do
    rustup target add "$t"
    for p in "$P" dev; do
      cargo rustc --profile "$p" --lib --crate-type rlib --no-default-features --features digest,digest010,oid --target "$t"
    done
  done
  # The ARMv8 SHA2 kernel, on emulated AArch64 (on an x86 runner; the Arm
  # runner runs it natively above).
  if [ -n "${CI:-}" ] && [ "$(uname -m)" = x86_64 ]; then
    apt qemu-user gcc-aarch64-linux-gnu
    rustup target add aarch64-unknown-linux-gnu
    CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER=aarch64-linux-gnu-gcc \
    CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER="qemu-aarch64 -cpu max -L /usr/aarch64-linux-gnu" \
      cargo test --profile "$P" --target aarch64-unknown-linux-gnu --test isa --test kernels --test vectors --test kernels512 --test vectors512
  fi
  ct
  ctstatic
}

# The constant-time check (examples/ctgrind.rs): Valgrind's memcheck, with
# the secrets marked undefined, must report nothing; and must report each of
# the two leaking controls, or the check is not seeing what it should.
ct() {
  if [ "$(uname -m)" != x86_64 ]; then echo "ct: x86-64 only, skipped"; return; fi
  apt valgrind binutils
  cargo build --profile "$P" --example ctgrind
  local bin="$T/$P/examples/ctgrind" vg="valgrind -q --error-exitcode=1"
  for c in branch index; do
    if $vg "$bin" --control "$c" 2> /dev/null; then
      echo "ct: memcheck missed the $c control"; exit 1
    fi
  done
  $vg "$bin"
  # Valgrind's CPU has no SHA-NI, so that kernel is checked on its code: its
  # only conditional jumps are the two on the length (is there a block, is
  # there another), it calls nothing, and every load or store is at the
  # state, the round constants, or the block offset, all public.
  local f
  f=$(objdump -d --no-show-raw-insn -C "$bin" | awk '/^[0-9a-f]+ <verilith_sha2::shani::tf::compress_blocks>:/{f=1} f&&/^$/{exit} f')
  [ -n "$f" ] || { echo "ct: SHA-NI kernel not found"; exit 1; }
  local jumps calls
  jumps=$(grep -cE '\sj[a-z]+ ' <<< "$f" || true)
  calls=$(grep -cE '\scall' <<< "$f" || true)
  if [ "$jumps" != 2 ] || [ "$calls" != 0 ]; then
    echo "ct: the SHA-NI kernel has $jumps jumps and $calls calls, not 2 and 0:"; echo "$f"; exit 1
  fi
  grep -B2 -E '\sj[a-z]+ ' <<< "$f"
  echo "ct: no secret-dependent branches or addresses"
}

# The static constant-time check (../../scripts/ctcheck.py): a taint
# analysis of the machine code of every kernel (portable, BMI2, AVX2,
# SHA-NI, ARMv8, and the dispatch) and, on x86-64, of SHA-256 and SHA-512
# (examples/ctcheck.rs), for every input, on the binary as this profile
# builds it for x86-64 and for AArch64, as in ../aes/ci.sh. Each control
# must be reported. The MACs are left to `ct` (see the example).
ctstatic() {
  if [ -n "${CI:-}" ]; then python3 -m pip install -q capstone==5.0.7 pyelftools==0.33; fi
  local t="$T/ctcheck-$crate"
  CARGO_TARGET_DIR="$t" cargo clean -q -p verilith-sha2
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

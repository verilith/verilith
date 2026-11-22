# Shared helpers for the vbench scripts. Sourced, not run.
set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
# The verilith checkout this harness is part of: our libraries are its crates.
REPO=$(cd "$ROOT/.." && pwd)
WORK=${WORK:-$ROOT/work}
SRC=$WORK/src
DATA=$WORK/data
BUILD=$WORK/build
BIN=$BUILD/bin
. "$ROOT/pins.sh"

OS=$(uname -s)
# rustup installed by Homebrew is keg-only, and ~/.cargo/bin may not be on PATH
# in a non-login shell: find cargo there if it is not already on PATH.
# Both must come from the same place: a lone cargo symlink without rustc is no use.
if ! command -v cargo >/dev/null 2>&1 || ! command -v rustc >/dev/null 2>&1 || ! rustc -vV >/dev/null 2>&1; then
  for d in /opt/homebrew/opt/rustup/bin /usr/local/opt/rustup/bin "$HOME/.cargo/bin"; do
    if [ -x "$d/cargo" ] && [ -x "$d/rustc" ] && "$d/rustc" -vV >/dev/null 2>&1; then PATH="$d:$PATH"; export PATH; break; fi
  done
fi
ARCH=$(uname -m)
if [ "$OS" = Darwin ]; then
  NPROC=$(sysctl -n hw.ncpu)
  SHA256="shasum -a 256"
else
  NPROC=$(nproc)
  SHA256="sha256sum"
fi

say() { printf '\033[1m==> %s\033[0m\n' "$*" >&2; }
warn() { printf '\033[33mwarning: %s\033[0m\n' "$*" >&2; }
die() { printf '\033[31merror: %s\033[0m\n' "$*" >&2; exit 1; }

# macOS: if the selected Xcode cannot link a trivial program against its SDK
# (seen with Xcode 26.6 + a newer Command Line Tools SDK: "ld: tapi error:
# malformed file"), fall back to the Command Line Tools toolchain. Checked once
# per run; children inherit DEVELOPER_DIR.
if [ "$OS" = Darwin ] && [ -z "${VBENCH_LINK_CHECKED:-}" ]; then
  export VBENCH_LINK_CHECKED=1
  _probe() { local d; d=$(mktemp -d); printf 'int main(void){return 0;}\n' > "$d/p.c"
    "$@" cc "$d/p.c" -o "$d/p" >/dev/null 2>&1 && "$d/p"; local r=$?; rm -rf "$d"; return $r; }
  if ! _probe env; then
    clt=/Library/Developer/CommandLineTools
    if [ -z "${DEVELOPER_DIR:-}" ] && [ -d "$clt" ] && _probe env DEVELOPER_DIR="$clt"; then
      export DEVELOPER_DIR="$clt"
      warn "the selected Xcode ($(xcode-select -p 2>/dev/null)) cannot link a test program; using DEVELOPER_DIR=$clt"
    else
      die "cc cannot link a test program; check 'xcode-select -p' and 'cc -v' (try DEVELOPER_DIR=/Library/Developer/CommandLineTools)"
    fi
  fi
fi

# git_get DIR URL REF: clone URL into DIR at REF (tag, branch or commit),
# or move an existing clone to REF.
git_get() {
  local dir=$1 url=$2 ref=$3
  if [ ! -d "$dir/.git" ]; then
    rm -rf "$dir"
    git clone -q "$url" "$dir" || { warn "git_get: cannot clone $url"; return 1; }
  fi
  if ! git -C "$dir" checkout -q --detach "$ref" 2>/dev/null; then
    # git fetch takes a branch, tag or full hash, not a short hash, so fall
    # back to fetching every branch and tag, then try again.
    git -C "$dir" fetch -q origin "$ref" 2>/dev/null ||
      git -C "$dir" fetch -q --tags origin "+refs/heads/*:refs/remotes/origin/*" ||
      { warn "git_get: cannot fetch from $url"; return 1; }
    git -C "$dir" checkout -q --detach "$ref" 2>/dev/null ||
      git -C "$dir" checkout -q --detach "origin/$ref" 2>/dev/null ||
      { warn "git_get: $ref not found in $url"; return 1; }
  fi
  # A branch name resolves to the remote's latest commit.
  if git -C "$dir" rev-parse -q --verify "origin/$ref" >/dev/null; then
    { git -C "$dir" fetch -q origin "$ref" && git -C "$dir" checkout -q --detach "origin/$ref"; } ||
      { warn "git_get: cannot update $dir to origin/$ref"; return 1; }
  fi
}

# Original library source dir by name.
orig() { echo "$SRC/$1"; }
# Our library's crate directory. Libraries keep their short names here
# (vzlib is crates/zlib, the crate verilith-zlib), as the results do.
ours() { echo "$REPO/crates/${1#v}"; }
# The Cargo profile that crate's release builds use.
ours_profile() { "$REPO/scripts/profile" "${1#v}"; }

# Compiler flags for every C/C++ file and every Rust crate: optimized for
# this CPU, the same on both sides of every comparison.
cpu_flags() {
  local f order="-march=native -mcpu=native"
  case "$ARCH" in arm64|aarch64) order="-mcpu=native -march=native" ;; esac
  for f in $order; do
    if echo 'int main(void){return 0;}' | ${CC:-cc} $f -x c - -o /dev/null 2>/dev/null; then echo "$f"; return; fi
  done
}
: "${CC:=cc}"
: "${CXX:=c++}"
CPUFLAG=${CPUFLAG-$(cpu_flags)}
export CPUFLAG
CFLAGS_BENCH="-O3 -DNDEBUG $CPUFLAG"
export RUSTFLAGS="${RUSTFLAGS:--C target-cpu=native}"
# Every profile a crate may name (scripts/profile) gets the same settings;
# they differ only in panic = abort, which stays as each crate had it.
for _p in RELEASE RELEASE_FAT RELEASE_ABORT; do
  export CARGO_PROFILE_${_p}_LTO=fat
  export CARGO_PROFILE_${_p}_CODEGEN_UNITS=1
  export CARGO_PROFILE_${_p}_DEBUG=line-tables-only
done

# Libraries a Rust staticlib needs when linked from C.
if [ "$OS" = Darwin ]; then RUST_LIBS="-lc -lm -liconv"; else RUST_LIBS="-lpthread -ldl -lm"; fi

# One timed run at a time on a shared machine. Builds may overlap, timing may
# not: take this lock (a directory, so mkdir is atomic) around timed runs only.
VF_BENCH_LOCK=${VF_BENCH_LOCK:-$HOME/vf-bench.lock}
bench_lock() {
  local waited=0
  while ! mkdir "$VF_BENCH_LOCK" 2>/dev/null; do
    local owner; owner=$(awk 'NR==1{print $1}' "$VF_BENCH_LOCK/pid" 2>/dev/null || true)
    if [ -n "$owner" ] && ! kill -0 "$owner" 2>/dev/null; then
      warn "removing stale bench lock left by dead pid $owner"; rm -rf "$VF_BENCH_LOCK"; continue
    fi
    # A lock with no pid file (another tool's bare mkdir, or a job killed
    # before it wrote one) counts as stale once it is VF_BENCH_LOCK_STALE
    # seconds old (default 3 hours, longer than any one timed run).
    if [ -z "$owner" ]; then
      local m; m=$(stat -c %Y "$VF_BENCH_LOCK" 2>/dev/null || stat -f %m "$VF_BENCH_LOCK" 2>/dev/null || echo "")
      if [ -n "$m" ] && [ $(( $(date +%s) - m )) -gt "${VF_BENCH_LOCK_STALE:-10800}" ]; then
        warn "removing bench lock with no owner, unchanged for over ${VF_BENCH_LOCK_STALE:-10800}s"; rmdir "$VF_BENCH_LOCK" 2>/dev/null || rm -rf "$VF_BENCH_LOCK"; continue
      fi
    fi
    if [ $((waited % 60)) -eq 0 ]; then say "waiting for the bench lock $VF_BENCH_LOCK (held by: $(cat "$VF_BENCH_LOCK/who" 2>/dev/null || echo unknown))"; fi
    sleep 5; waited=$((waited + 5))
  done
  echo $$ > "$VF_BENCH_LOCK/pid"; echo "vbench $* (pid $$, since $(date '+%H:%M'))" > "$VF_BENCH_LOCK/who"
  trap bench_unlock EXIT INT TERM
}
bench_unlock() { if [ "$(cat "$VF_BENCH_LOCK/pid" 2>/dev/null)" = "$$" ]; then rm -rf "$VF_BENCH_LOCK"; fi; trap - EXIT INT TERM; }

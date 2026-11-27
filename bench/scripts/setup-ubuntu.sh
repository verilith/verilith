#!/usr/bin/env bash
# One-shot setup of a fresh Ubuntu (24.04 or later, x86-64 or arm64) machine
# for every benchmark in this repo: bench/run.sh (the libraries and Node.js)
# and bench/server/run.py (HTTP servers, including HTTP/3).
#
#   bench/scripts/setup-ubuntu.sh            # everything
#   bench/scripts/setup-ubuntu.sh --no-server   # only what bench/run.sh needs
#   bench/scripts/setup-ubuntu.sh --no-h3       # skip building the HTTP/3 tools
#
# Run it as the user who will run the benchmarks (it uses sudo for apt).
# Safe to rerun: each step skips what is already there. Then:
#
#   sudo bench/scripts/linux-quiet.sh on      # see bench/README.md
#   VBENCH_CPU=<cpu it printed> bench/run.sh
#   bench/server/run.py
set -euo pipefail
server=1 h3=1
for a in "$@"; do
  case $a in
    --no-server) server=0; h3=0 ;;
    --no-h3) h3=0 ;;
    -h|--help) sed -n '2,16p' "$0"; exit 0 ;;
    *) echo "unknown option $a (see --help)" >&2; exit 2 ;;
  esac
done
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)
say() { printf '\033[1m==> %s\033[0m\n' "$*" >&2; }
warn() { printf '\033[33mwarning: %s\033[0m\n' "$*" >&2; }
[ "$(uname -s)" = Linux ] || { echo "this script is for Ubuntu; on a Mac see bench/README.md" >&2; exit 1; }
command -v apt-get >/dev/null || { echo "no apt-get: this script is for Ubuntu or Debian" >&2; exit 1; }
# Disk: the originals, their builds and two Node.js builds come to about
# 40 GB under bench/work, the server tools to a few more. AWS's Ubuntu
# images start with an 8 GB root volume.
free=$(df -Pk "$REPO" | awk 'NR==2 {print int($4 / 1048576)}')
if [ "$free" -lt 60 ]; then
  warn "only ${free} GB free on the disk holding $REPO; a full run needs about 60 GB (grow the volume, or use the instance's NVMe disk)"
fi
SUDO=""
[ "$(id -u)" = 0 ] || SUDO=sudo
apt_install() { $SUDO env DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends "$@"; }

# --- Packages ------------------------------------------------------------
# bench/run.sh: compilers and build tools for the originals (OpenSSL needs
# perl, libjpeg-turbo NASM on x86-64, mbedTLS 4 Python with jsonschema and
# jinja2, libpng the system zlib), and Node.js's build (python3, ninja).
pkgs="build-essential git curl ca-certificates cmake ninja-build pkg-config unzip xz-utils patch perl
      python3 python3-venv python3-jsonschema python3-jinja2 zlib1g-dev binutils util-linux file"
case $(uname -m) in x86_64) pkgs="$pkgs nasm" ;; esac
# bench/server/run.py: the servers and load generators that Ubuntu ships.
# (h2o is not packaged in Ubuntu 26.04; h3/build.sh's h2o stands in for it.)
if [ $server = 1 ]; then
  pkgs="$pkgs nginx-light wrk nghttp2-client openssl procps"
  if apt-cache show h2o >/dev/null 2>&1; then pkgs="$pkgs h2o"; fi
fi
# bench/server/h3/build.sh: what it lists at its top.
if [ $h3 = 1 ]; then
  pkgs="$pkgs golang autoconf automake libtool ruby bison libev-dev libc-ares-dev libuv1-dev
        libpcre2-dev libssl-dev"
  # A C++23 compiler with <print>: g++ 14 or later (Ubuntu 24.04's default is 13).
  if ! echo '#include <print>' | g++ -std=c++23 -x c++ -fsyntax-only - 2>/dev/null; then pkgs="$pkgs g++-14"; fi
fi
say "apt-get install (sudo)"
$SUDO apt-get update -q
# shellcheck disable=SC2086
apt_install $pkgs
# perf, for looking at profiles by hand (the benchmarks read the counters
# themselves): the tools matching the running kernel, if the archive has them.
apt_install "linux-tools-$(uname -r)" >/dev/null 2>&1 || apt_install linux-tools-generic >/dev/null 2>&1 \
  || warn "no linux-tools package for kernel $(uname -r): perf is not installed (the benchmarks do not need it)"
# A distribution nginx starts itself on port 80 when installed; the
# benchmarks start their own, so stop and disable the system service.
if [ $server = 1 ] && command -v systemctl >/dev/null && systemctl is-enabled nginx >/dev/null 2>&1; then
  $SUDO systemctl disable --now nginx >/dev/null 2>&1 || true
fi

# --- Rust ------------------------------------------------------------------
export PATH="$HOME/.cargo/bin:$PATH"
if ! command -v rustup >/dev/null; then
  say "install Rust (rustup, stable)"
  # rustup-init itself, which is what https://sh.rustup.rs downloads.
  t=$(mktemp -d)
  curl -sSfL -o "$t/rustup-init" "https://static.rust-lang.org/rustup/dist/$(uname -m)-unknown-linux-gnu/rustup-init"
  chmod +x "$t/rustup-init"
  "$t/rustup-init" -y -q --profile minimal --default-toolchain stable
  rm -rf "$t"
else
  say "update Rust stable"
  rustup -q toolchain install stable --profile minimal
fi
# Verdict (the x509n suite) pins its own toolchain; fetch it now rather
# than in the middle of a timed run.
rustup -q toolchain install "$(sed -n 's/^channel *= *"\(.*\)"/\1/p' "$REPO/bench/runners/verdict-run/rust-toolchain.toml")" --profile minimal

# --- bench/server: our server and the Rust baselines ------------------------
if [ $server = 1 ]; then
  # tls-rustls adds the verilith-rustls row (the same server on rustls), h3
  # the HTTP/3 listener; neither changes the default TLS backend.
  features=tls,tls-rustls
  [ $h3 = 1 ] && features=$features,h3
  say "build verilith-server ($features) and the hyper and may-minihttp baselines"
  (cd "$REPO" && cargo build -q --release -p verilith-server --features "$features")
  (cd "$REPO/bench/server/baselines/hyper" && cargo build -q --release)
  (cd "$REPO/bench/server/baselines/may-minihttp" && cargo build -q --release)
  # Bun, for the bun baseline: its release binary, where run.py looks.
  if ! command -v bun >/dev/null && [ ! -x "$HOME/.bun/bin/bun" ]; then
    say "install Bun (github.com/oven-sh/bun release)"
    case $(uname -m) in x86_64) b=bun-linux-x64 ;; aarch64) b=bun-linux-aarch64 ;; *) b="" ;; esac
    t=$(mktemp -d)
    if [ -n "$b" ] && curl -sSfL -o "$t/bun.zip" "https://github.com/oven-sh/bun/releases/latest/download/$b.zip" \
       && unzip -q "$t/bun.zip" -d "$t"; then
      mkdir -p "$HOME/.bun/bin" && mv "$t/$b/bun" "$HOME/.bun/bin/bun"
    else
      warn "could not install Bun: the bun baseline will be skipped"
    fi
    rm -rf "$t"
  fi
fi
if [ $h3 = 1 ]; then
  t3=${H3_TOOLS:-$REPO/target/h3-tools}
  if [ -x "$t3/bin/h2load" ] && [ -x "$t3/nginx/sbin/nginx" ] && [ -x "$t3/bin/h2o" ]; then
    say "HTTP/3 tools already built in $t3 (remove it to rebuild)"
  else
    say "build the HTTP/3 tools (bench/server/h3/build.sh)"
    "$REPO/bench/server/h3/build.sh" "$t3"
  fi
  say "build the h3-quinn baseline"
  (cd "$REPO/bench/server/baselines/h3-quinn" && cargo build -q --release)
fi

say "done. Rust is in ~/.cargo/bin: open a new shell or run 'source ~/.cargo/env'."
echo "next: sudo bench/scripts/linux-quiet.sh on; then VBENCH_CPU=<cpu> bench/run.sh; then bench/server/run.py" >&2

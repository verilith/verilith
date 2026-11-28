#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests over HTTP/1.1, h2c, HTTPS and HTTP/3, and
#                     the binary in front of verilith-server
# Runs anywhere with curl; with CI set it also installs the system packages
# it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo test --profile "$P" --features h3
  binary
}

# The binary, configured from its command line, in front of
# verilith-server: one route, compressed and plain.
binary() {
  cargo build --profile "$P" --bin verilith-proxy
  cargo build --profile "$P" -p verilith-server --bin verilith-server
  local up=18941 port=18942 ok=1
  "$T/$P/verilith-server" --http "$up" --threads 1 &
  local spid=$!
  "$T/$P/verilith-proxy" --http "$port" --threads 1 --upstream up=127.0.0.1:$up --route /=up &
  local pid=$!
  for _ in $(seq 100); do curl -s -o /dev/null "http://127.0.0.1:$port/" && break; sleep 0.05; done
  [ "$(curl -s "http://127.0.0.1:$port/plaintext")" = "Hello, World!" ] || ok=0
  [ "$(curl -s -o /dev/null -w '%{http_code}' "http://127.0.0.1:$port/missing")" = 404 ] || ok=0
  kill "$pid" "$spid"
  [ "$ok" = 1 ] || { echo "binary: wrong answer" >&2; exit 1; }
  echo "binary: ok"
}

"${1:-test}"

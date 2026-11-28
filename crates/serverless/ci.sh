#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests, and the Rust example guest built for wasm32
#                     and served end to end
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo test --profile "$P"
  guest
}

# Builds examples/hello for wasm32 and checks it answers through the binary.
guest() {
  rustup target add wasm32-unknown-unknown
  (cd examples/hello && cargo build --release)
  cargo build --profile "$P" --bin verilith-serverless
  local port=18931 ok=1
  "$T/$P/verilith-serverless" --http "$port" --threads 1 \
    --fn hello=examples/hello/target/wasm32-unknown-unknown/release/hello.wasm &
  local pid=$!
  for _ in $(seq 100); do curl -s -o /dev/null "http://127.0.0.1:$port/" && break; sleep 0.05; done
  [ "$(curl -s "http://127.0.0.1:$port/fn/hello?name=ci")" = "Hello, ci!" ] || ok=0
  [ "$(curl -s -d shout "http://127.0.0.1:$port/fn/hello")" = "SHOUT" ] || ok=0
  kill "$pid"
  [ "$ok" = 1 ] || { echo "guest: wrong answer" >&2; exit 1; }
  echo "guest: ok"
}

"${1:-test}"

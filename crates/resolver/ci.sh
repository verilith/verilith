#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests: the resolver against a local hierarchy of
#                     servers on 127.0.0.2-9 (tests/hier), over UDP, TCP,
#                     DNS over TLS and DNS over HTTPS; DNSSEC validation
#                     against a signed hierarchy on 127.0.1.2-11 (tests/sec)
# Runs anywhere 127.0.0.0/8 is on the loopback interface (Linux; on macOS
# add the aliases first: sudo ifconfig lo0 alias 127.0.0.N for N in 2..9).
. "$(dirname "$0")/../../scripts/ci-lib.sh"

test() {
  cargo test --profile "$P" --features tls
}

"${1:-test}"

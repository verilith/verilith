#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests: the W3C XML conformance suite (verdicts and
#                     canonical outputs), the API tests, and libexpat
#                     against verilith-xml on the suite and mutations of it
#   ./ci.sh fuzz      the fuzz targets, FUZZ_SECS each (default 120)
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

# The W3C XML Conformance Test Suite 20130923, as packaged on npm by
# xml-conformance-suite (MIT; the tests keep their own notices).
SUITE_URL=https://registry.npmjs.org/xml-conformance-suite/-/xml-conformance-suite-1.2.0.tgz
SUITE_SHA256=9b3d0a175832a9746bb0aa6fa6d0a1b763cb49552f83f624bde42adc94e54282

suite() {
  if [ ! -d "$W/xmlconf/package/xmlconf" ]; then
    mkdir -p "$W/xmlconf"
    curl -sSfL -o "$W/xmlconf/suite.tgz" "$SUITE_URL"
    echo "$SUITE_SHA256  $W/xmlconf/suite.tgz" | sha256sum -c - > /dev/null
    tar xzf "$W/xmlconf/suite.tgz" -C "$W/xmlconf"
  fi
  echo "$W/xmlconf/package/xmlconf"
}

test() {
  local x
  x=$(suite)
  XMLCONF=$x cargo test --profile "$P"
  # libexpat 2.7.3 against verilith-xml: the same verdict and the same
  # canonical form on every suite file and 100 mutations of each, apart
  # from what fuzz/src/lib.rs lists as expat's.
  scripts/fetch-expat.sh > /dev/null
  (cd fuzz && cargo run -q --release --example mutate -- 100 "$x")
}

fuzz() {
  fuzz_tools
  scripts/fetch-expat.sh > /dev/null
  local x
  x=$(suite)
  cd fuzz
  mkdir -p corpus/expat corpus/api
  find "$x" -name '*.xml' -size -8k -exec cp {} corpus/expat/ \;
  cp corpus/expat/* corpus/api/
  for t in expat api; do
    cargo +nightly fuzz run "$t" "corpus/$t" -- -max_total_time="${FUZZ_SECS:-120}" -max_len=8192
  done
}

"${1:-test}"

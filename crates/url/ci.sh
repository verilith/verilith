#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
#   ./ci.sh fuzz      every fuzz target under ASan, FUZZ_SECS each (default 120)
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

ADA_COMMIT=62daadd7348d76f870330d0f36162b1a74d99700
URL_DATASET_COMMIT=ef7065196980ab7956bacc60b4bda663939f659c

test() {
  # WPT urltestdata, setters, toascii.
  cargo test --profile "$P"
  # The C API against ada, on 20,000 URLs of ada's dataset.
  if [ ! -d "$W/ext/ada" ]; then
    git clone -q https://github.com/ada-url/ada "$W/ext/ada"
    git -C "$W/ext/ada" checkout -q "$ADA_COMMIT"
    (cd "$W/ext/ada" && python3 singleheader/amalgamate.py)
  fi
  if [ ! -d "$W/ext/url-dataset" ]; then
    git clone -q https://github.com/ada-url/url-dataset "$W/ext/url-dataset"
    git -C "$W/ext/url-dataset" checkout -q "$URL_DATASET_COMMIT"
  fi
  head -20000 "$W/ext/url-dataset/out.txt" > "$W/u20k.txt"
  EXT=$W/ext tests/capi/run.sh "$W/u20k.txt"
}

fuzz() {
  fuzz_tools
  for t in $(cargo +nightly fuzz list); do
    cargo +nightly fuzz run "$t" -- -max_total_time="${FUZZ_SECS:-120}" -rss_limit_mb=4096
  done
}

"${1:-test}"

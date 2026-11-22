#!/usr/bin/env bash
# What CI runs for this crate, besides Verus (scripts/verify.sh).
#   ./ci.sh           the tests
#   ./ci.sh fuzz      the fuzz targets under ASan, FUZZ_SECS each (default 300)
# Runs anywhere; with CI set it also installs the system packages it needs.
. "$(dirname "$0")/../../scripts/ci-lib.sh"

CARES_COMMIT=4c6046531646906e9a493d542bd7f1f63da9650e

cares() { # cares DIR [cmake args]: c-ares at CARES_COMMIT, built into DIR/build
  local dir=$1; shift
  if [ ! -d "$dir" ]; then
    git clone -q https://github.com/c-ares/c-ares.git "$dir"
    git -C "$dir" checkout -q "$CARES_COMMIT"
  fi
  cmake -S "$dir" -B "$dir/build" -DCARES_STATIC=ON -DCARES_SHARED=OFF \
    -DCMAKE_POSITION_INDEPENDENT_CODE=ON -DCARES_BUILD_TOOLS=OFF "$@" > /dev/null
  cmake --build "$dir/build" -j > /dev/null
}

test() {
  apt cmake libgtest-dev libgmock-dev
  cares "$W/c-ares" -DCMAKE_BUILD_TYPE=Release
  # Unit tests, CVEs, typed RDATA, errors, differentials, the c-ares adapter.
  CARES_LIB_DIR=$W/c-ares/build/lib cargo test --profile "$P" --features cares,capi -- --nocapture
  # The native C API under ASan and UBSan.
  scripts/test-c.sh
  # c-ares's own test suite with this crate as its parser.
  cargo build --profile "$P" --features cares,ares-abi
  if [ ! -d "$W/c-ares-vdns" ]; then
    git clone -q "$W/c-ares" "$W/c-ares-vdns"
    git -C "$W/c-ares-vdns" apply "$PWD/cares/c-ares-use-vdns.patch"
  fi
  cmake -S "$W/c-ares-vdns" -B "$W/c-ares-vdns/build" -DCMAKE_BUILD_TYPE=Release \
    -DCARES_STATIC=OFF -DCARES_SHARED=ON -DCARES_BUILD_TESTS=ON \
    -DCARES_VDNS_LIB="$T/$P/libverilith_dns.a" > /dev/null
  cmake --build "$W/c-ares-vdns/build" -j > /dev/null
  "$W/c-ares-vdns/build/bin/arestest" --gtest_filter='-*Live*:LibraryTest.ParseAcceptsMaxLengthName'
}

fuzz() {
  fuzz_tools
  cares "$W/c-ares-asan" -DCMAKE_BUILD_TYPE=RelWithDebInfo -DCMAKE_C_FLAGS="-fsanitize=address -fno-omit-frame-pointer"
  export CARES_LIB_DIR=$W/c-ares-asan/build/lib
  cd fuzz
  for t in parse expand_name ares_dns_parse ares_dns_write; do
    mkdir -p "corpus/$t" && cp seeds/* "corpus/$t/"
    cargo +nightly fuzz run -s address "$t" "corpus/$t" -- -max_total_time="${FUZZ_SECS:-300}" -max_len=4096
  done
}

"${1:-test}"

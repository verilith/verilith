#!/bin/sh
# Builds mbedTLS ($1, a v4.3.0 checkout with submodules, fetched recursively) with the vx509 patch
# and runs its test suites. Every suite must pass, except that x509parse must
# fail on exactly the cases in expected-x509parse-failures.txt (see README.md).
set -e
here=$(cd "$(dirname "$0")" && pwd)
mbed=$1
(cd "$here/.." && cargo build --profile release-fat --features mbedtls)
git -C "$mbed" apply --check "$here/mbedtls-use-vx509.patch" 2>/dev/null && git -C "$mbed" apply "$here/mbedtls-use-vx509.patch"
cmake -S "$mbed" -B "$mbed/build-vx" -DCMAKE_BUILD_TYPE=Release -DMBEDTLS_VX509_DIR="$here/.." \
    -DMBEDTLS_VX509_LIB="${CARGO_TARGET_DIR:-$here/../../../target}/release-fat/libverilith_x509.a"
cmake --build "$mbed/build-vx" -j"$(nproc)"
# Serially: the PSA storage suites share key files in the working
# directory and fail when run in parallel, with or without vx509.
cd "$mbed/build-vx" && ctest -E '^x509parse-suite$' --output-on-failure
cd tests && ./test_suite_x509parse | grep 'FAILED$' | sed 's/ *\.* *FAILED$//' > /tmp/x509parse-failures.txt || true
if diff -u "$here/expected-x509parse-failures.txt" /tmp/x509parse-failures.txt; then
    echo "x509parse: only the documented departures fail"
else
    echo "x509parse: failures differ from expected-x509parse-failures.txt" >&2
    exit 1
fi

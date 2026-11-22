#!/usr/bin/env bash
# Runs the native C API's tests (tests/c/native.c) under ASan and UBSan.
# Then builds the C library with picohttpparser's symbol names and runs
# picohttpparser's own test suite (test.c, at a pinned commit) against it,
# under ASan and UBSan.
#
# Every failing check must be one of the known, deliberate differences
# listed in KNOWN below (file test.c, by line):
#  - obsolete line folding is rejected (92-102, 199-209);
#  - more than one space between request-line or status-line parts is
#    rejected (157, 260);
#  - a bare LF line ending is rejected (234-235) and so are bare LFs in
#    chunked trailers (chunked-consume-trailer 316-361 and 345);
#  - on a partial result, the out-parameters are left untouched instead of
#    holding what was parsed so far (107-119, 221-242).
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
T=${CARGO_TARGET_DIR:-$PWD/../../target}
UP=$ROOT/target/upstream
PICO_REV=465a7ff09fbd3432fe56c673451f5460154d1f07
PICOTEST_REV=70b9797596d81896cba49e5918fd5b1edf57269b

fetch() { # url dir rev
    if [ ! -d "$2/.git" ]; then
        git init -q "$2"
        git -C "$2" remote add origin "$1"
    fi
    git -C "$2" fetch -q --depth 1 origin "$3"
    git -C "$2" checkout -q FETCH_HEAD
}
# The native C API (include/vhttp.h).
OUT=$ROOT/target/ctest
mkdir -p "$OUT"
cargo build --profile release-abort --features capi
${CC:-cc} -std=c99 -fsanitize=address,undefined -fno-sanitize-recover=undefined -g -Wall -Wextra -Werror \
    -I include -o "$OUT/native" tests/c/native.c "$T/release-abort/libverilith_http.a" -lpthread -ldl -lm
"$OUT/native"
${CXX:-c++} -fsyntax-only -Wall -Wextra -Werror -x c++ include/vhttp.h

mkdir -p "$UP"
fetch https://github.com/h2o/picohttpparser "$UP/picohttpparser" "$PICO_REV"
fetch https://github.com/h2o/picotest "$UP/picohttpparser/picotest" "$PICOTEST_REV"

cargo build --profile release-abort --features phr-abi
OUT=$ROOT/target/ctest
mkdir -p "$OUT"
CC=${CC:-cc}
$CC -fsanitize=address,undefined -g -I include -o "$OUT/pico_test" \
    -include picohttpparser.h "$UP/picohttpparser/test.c" "$UP/picohttpparser/picotest/picotest.c" \
    "$T/release-abort/libverilith_http.a" -lpthread -ldl -lm
"$OUT/pico_test" > "$OUT/pico_test.log" 2>&1 || true

KNOWN="92 93 95 96 97 98 99 100 101 102 107 111 113 117 119 157
199 200 201 203 204 205 206 207 208 209 221 223 226 228 231 233 234 235 240 241 242 260
316 317 318 323 345 353 355 356 361"
status=0
fails=$(grep -E '^ *not ok [0-9]+ - .*test\.c [0-9]+$' "$OUT/pico_test.log" | sed -E 's/.*test\.c ([0-9]+)$/\1/' | sort -un || true)
for line in $fails; do
    if ! echo " $KNOWN " | tr '\n' ' ' | grep -q " $line "; then
        echo "unexpected failure: test.c line $line"
        status=1
    fi
done
total=$(grep -cE '^ *(not )?ok [0-9]+ - .*test\.c [0-9]+$' "$OUT/pico_test.log" || true)
nfail=$(grep -cE '^ *not ok [0-9]+ - .*test\.c [0-9]+$' "$OUT/pico_test.log" || true)
echo "picohttpparser test.c: $((total - nfail)) of $total checks pass; $nfail known differences"
if grep -q "ERROR: AddressSanitizer\|runtime error" "$OUT/pico_test.log"; then
    echo "sanitizer report:"; grep -A5 "ERROR: AddressSanitizer\|runtime error" "$OUT/pico_test.log"; status=1
fi
exit $status

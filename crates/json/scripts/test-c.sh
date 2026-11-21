#!/usr/bin/env bash
# Builds the C library and runs:
#  1. JSONTestSuite's test_parsing files through the C API, next to upstream
#     cJSON for comparison;
#  2. the upstream cJSON test files that only need the public API (through
#     tests/c/cjson_tests/common.h, a shim for upstream's common.h);
#  3. the native C API's tests (tests/c/native.c), and JSONTestSuite through
#     it, reading every value of every accepted file.
# Upstream sources are cloned at pinned commits into target/upstream.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
UP=$ROOT/target/upstream
CJSON_REV=6d9f2443ab071f86e5d9b43025a40929ec41c46c        # cJSON v1.7.19
SUITE_REV=1ef36fa01286573e846ac449e8683f8833c5b26a

fetch() { # url dir rev
    if [ ! -d "$2/.git" ]; then
        git init -q "$2"
        git -C "$2" remote add origin "$1"
    fi
    git -C "$2" fetch -q --depth 1 origin "$3"
    git -C "$2" checkout -q FETCH_HEAD
}
mkdir -p "$UP"
fetch https://github.com/DaveGamble/cJSON "$UP/cJSON" "$CJSON_REV"
fetch https://github.com/nst/JSONTestSuite "$UP/JSONTestSuite" "$SUITE_REV"

cargo build --profile release-abort --features cjson,capi
LIB=${CARGO_TARGET_DIR:-$ROOT/../../target}/release-abort/libverilith_json.a
LIBS="-lm -lpthread -ldl"
OUT=$ROOT/target/ctest
mkdir -p "$OUT"
CC=${CC:-cc}
SAN="-fsanitize=address,undefined -g"

# 1. JSONTestSuite
$CC $SAN -I include -o "$OUT/pf_vjson" tests/c/parse_file.c "$LIB" $LIBS
$CC $SAN -I "$UP/cJSON" -o "$OUT/pf_cjson" tests/c/parse_file.c "$UP/cJSON/cJSON.c" -lm
cd "$UP/JSONTestSuite/test_parsing"
"$OUT/pf_vjson" ./* > "$OUT/suite_vjson.txt"
"$OUT/pf_cjson" ./* > "$OUT/suite_cjson.txt"
cd "$ROOT"
wrong() { awk '($2 ~ /^\.\/y_/ && $1=="REJECT") || ($2 ~ /^\.\/n_/ && $1=="ACCEPT") {print $2}' "$1"; }
echo "JSONTestSuite (C API) mismatches, vjson: $(wrong "$OUT/suite_vjson.txt" | wc -l)"
wrong "$OUT/suite_vjson.txt" | sed 's/^/  /'
echo "JSONTestSuite (C API) mismatches, cJSON: $(wrong "$OUT/suite_cjson.txt" | wc -l)"

# 2. Upstream cJSON tests that need only the public API.
# Known, intentional differences (vjson follows RFC 8259 where cJSON does not):
#  - parse_string_should_parse_strings feeds raw control characters inside a
#    string, which RFC 8259 forbids.
KNOWN="parse_string_should_parse_strings"
status=0
# Tests of cJSON internals vjson does not have (its buffer growth and BOM
# helper) are dropped; the BOM is covered by parse_with_opts.
INTERNAL="ensure_should_fail_on_failed_realloc skip_utf8_bom_should_skip_bom skip_utf8_bom_should_not_skip_bom_if_not_at_beginning"
for t in parse_with_opts parse_value parse_array parse_object parse_string parse_number parse_examples compare_tests \
         print_array print_number print_object print_string print_value \
         misc_tests cjson_add minify_tests readme_examples; do
    cp "$UP/cJSON/tests/$t.c" "$OUT/$t.c"
    for f in $INTERNAL; do
        sed -i -e "/RUN_TEST($f)/d" -e "/^static void $f(void)$/,/^}$/d" "$OUT/$t.c"
    done
    $CC $SAN -I tests/c/cjson_tests -I include -I "$UP/cJSON/tests" \
        -o "$OUT/$t" "$OUT/$t.c" "$UP/cJSON/tests/unity/src/unity.c" "$LIB" $LIBS
    if (cd "$UP/cJSON/tests" && "$OUT/$t" > "$OUT/$t.log" 2>&1); then
        echo "upstream $t: $(grep -E 'Tests' "$OUT/$t.log")"
    else
        echo "upstream $t: $(grep -E 'Tests' "$OUT/$t.log")"
        while read -r line; do
            name=$(echo "$line" | cut -d: -f3)
            if echo " $KNOWN " | grep -q " $name "; then
                echo "  known difference: $name"
            else
                echo "  $line"
                status=1
            fi
        done < <(grep ':FAIL' "$OUT/$t.log")
    fi
done

# 3. The native C API.
$CC $SAN -fno-sanitize-recover=undefined -Wall -Wextra -Werror -I include -o "$OUT/native" tests/c/native.c "$LIB" $LIBS
"$OUT/native"
${CXX:-c++} -fsyntax-only -Wall -Wextra -Werror -x c++ include/vjson.h
(cd "$UP/JSONTestSuite/test_parsing" && "$OUT/native" ./* > "$OUT/suite_native.txt")
echo "JSONTestSuite (native C API) mismatches: $(wrong "$OUT/suite_native.txt" | wc -l)"
if [ "$(wrong "$OUT/suite_native.txt" | wc -l)" != 0 ] || [ "$(wc -l < "$OUT/suite_native.txt")" != "$(wc -l < "$OUT/suite_vjson.txt")" ]; then
    wrong "$OUT/suite_native.txt" | sed 's/^/  /'
    status=1
fi
exit $status

# Sourced by scripts/spec-tests.sh, in this directory, with fetch and $UP.
SUITE_REV=1ef36fa01286573e846ac449e8683f8833c5b26a   # the commit scripts/test-c.sh uses
fetch https://github.com/nst/JSONTestSuite "$UP/JSONTestSuite" "$SUITE_REV"
python3 -I gen.py "$UP/JSONTestSuite/test_parsing" src
echo "JSONTestSuite ${SUITE_REV:0:7}" > src/cases.source

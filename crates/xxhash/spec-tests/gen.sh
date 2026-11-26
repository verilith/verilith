# Sourced by scripts/spec-tests.sh, in this directory, with fetch and $UP.
XXHASH_REV=2ec67caeb18ec15ae60c0853174331089acddfc0
fetch https://github.com/Cyan4973/xxHash "$UP/xxHash" "$XXHASH_REV"
python3 -I gen.py "$UP/xxHash/tests/sanity_test_vectors.h" src
echo "xxHash sanity_test_vectors.h ${XXHASH_REV:0:7}" > src/cases.source

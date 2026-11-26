# Sourced by scripts/spec-tests.sh, in this directory, with fetch and $UP.
# NIST's CAVP SHA-2 byte-oriented response files (shabytetestvectors.zip),
# as pyca/cryptography keeps them in its test vectors.
PYCA_REV=4726b80a89667712565b0b5fdf29318066bc1ab3
fetch https://github.com/pyca/cryptography "$UP/pyca-cryptography" "$PYCA_REV"
python3 -I gen.py "$UP/pyca-cryptography/vectors/cryptography_vectors/hashes/SHA2" src
echo "NIST CAVP SHA-2 ShortMsg (pyca/cryptography ${PYCA_REV:0:7})" > src/cases.source

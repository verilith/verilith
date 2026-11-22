#!/bin/sh
# Downloads the corpus sources into $1 and extracts the certificates into $1/der.
set -e
dir=${1:-corpus-data}
mkdir -p "$dir/vec"
curl -sSfL -o "$dir/limbo.json" https://raw.githubusercontent.com/C2SP/x509-limbo/main/limbo.json
curl -sSfL -o "$dir/vectors.whl" \
  https://files.pythonhosted.org/packages/py3/c/cryptography-vectors/cryptography_vectors-50.0.2-py3-none-any.whl
python3 -m zipfile -e "$dir/vectors.whl" "$dir/vec"
python3 "$(dirname "$0")/extract.py" "$dir" "$dir/der"

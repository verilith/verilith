#!/bin/sh
# Builds the Python module and runs its tests (no maturin needed).
set -e
cd "$(dirname "$0")/.."
cargo build --profile release-abort -p verilith-bind-python
out=target/python
mkdir -p "$out"
cp "${CARGO_TARGET_DIR:-$PWD/../../target}/release-abort/libvbind_py.so" "$out/vbind.abi3.so"
URLTESTDATA=${URLTESTDATA:-../url/tests/data/urltestdata.json} \
  PYTHONPATH="$out" python3 -m unittest -v tests/python/test_vbind.py

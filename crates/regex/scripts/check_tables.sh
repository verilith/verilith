#!/usr/bin/env bash
# Checks that src/tables.rs is what tools/gen_tables.py makes from RE2's
# Unicode tables.   scripts/check_tables.sh RE2_CHECKOUT
set -euo pipefail
cd "$(dirname "$0")/.."
python3 tools/gen_tables.py "$1" | diff -q - src/tables.rs
echo "src/tables.rs matches $1"

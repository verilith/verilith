#!/bin/sh
# Fetches the WebAssembly 2.0 core spec tests at a pinned commit into
# tests/testsuite (used by tests/spec.rs).
set -e
COMMIT=7ef86ddeed81458f9031a49a40b3a3f99c1c6a8a
DIR="$(dirname "$0")/../tests/testsuite"
if [ ! -d "$DIR/.git" ]; then
    git clone -q https://github.com/WebAssembly/testsuite.git "$DIR"
fi
git -C "$DIR" fetch -q origin "$COMMIT" 2>/dev/null || git -C "$DIR" fetch -q --unshallow origin || true
git -C "$DIR" checkout -q "$COMMIT"

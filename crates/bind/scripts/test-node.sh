#!/bin/sh
# Builds the Node-API addon and runs its tests.
set -e
cd "$(dirname "$0")/.."
cargo build --profile release-abort -p verilith-bind-node
mkdir -p target
cp "${CARGO_TARGET_DIR:-$PWD/../../target}/release-abort/libverilith_bind_node.so" target/vbind.node
node --test tests/node/test.js

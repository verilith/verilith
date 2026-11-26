#!/usr/bin/env bash
# Copies quinn-proto and quiche from the Cargo registry into vendor/, with
# their frame parsers made public so the benchmarks and the agreement test
# can call them. Nothing else in them changes.
set -euo pipefail
cd "$(dirname "$0")"
QUINN=0.11.19
QUICHE=0.24.9
probe=$(mktemp -d)
trap 'rm -rf "$probe"' EXIT
mkdir -p "$probe/src"
printf '[package]\nname="p"\nversion="0.0.0"\nedition="2021"\n[dependencies]\nquinn-proto="=%s"\nquiche="=%s"\n[workspace]\n' $QUINN $QUICHE > "$probe/Cargo.toml"
echo 'fn main(){}' > "$probe/src/main.rs"
(cd "$probe" && cargo fetch -q)
reg=$(dirname "$(find "${CARGO_HOME:-$HOME/.cargo}/registry/src" -maxdepth 2 -name "quinn-proto-$QUINN" | head -1)")
rm -rf vendor && mkdir vendor
cp -r "$reg/quinn-proto-$QUINN" vendor/quinn-proto
cp -r "$reg/quiche-$QUICHE" vendor/quiche
# quinn-proto: the frame module and its iterator.
sed -i "s/^mod frame;/pub mod frame;/; s/^mod token;/pub mod token;/" vendor/quinn-proto/src/lib.rs
sed -i 's/pub(crate) /pub /g' vendor/quinn-proto/src/frame.rs
sed -i 's/^pub struct FrameType(u64);/pub struct FrameType(pub u64);/' vendor/quinn-proto/src/frame.rs
sed -i 's/^pub(crate) struct ResetToken/pub struct ResetToken/' vendor/quinn-proto/src/token.rs
# quinn-proto: transport parameter fields, to read them back.
sed -i 's/pub(crate) \([$a-z_]* *:\)/pub \1/' vendor/quinn-proto/src/transport_parameters.rs
# quiche: the frame module, and transport parameter decoding.
sed -i "s/^mod frame;/pub mod frame;/; s/^mod ranges;/pub mod ranges;/" vendor/quiche/src/lib.rs
sed -i 's/pub(crate) fn decode(/pub fn decode(/; s/pub(crate) fn encode</pub fn encode</' vendor/quiche/src/transport_params.rs
# quiche: the ECN counts of an ACK frame.
sed -i 's/^    \(ect0_count\|ect1_count\|ecn_ce_count\): u64,/    pub \1: u64,/' vendor/quiche/src/frame.rs
echo "setup: vendor/quinn-proto $QUINN, vendor/quiche $QUICHE"

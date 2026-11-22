#!/bin/sh
# Runs every benchmark row in its own process, three times, and prints the
# best time per row and certificate (ns). Needs MBEDTLS_DIR with two Release
# builds of mbedTLS 3.6.4: build/ (stock) and build-vx/ (with
# -DMBEDTLS_VX509_DIR, see ../mbedtls/README.md).
set -e
cd "$(dirname "$0")"
cargo build --release -q
(cd .. && cargo build --profile release-fat -q --features mbedtls)
out=$(mktemp -d)
for v in build build-vx; do
    extra=""
    [ $v = build-vx ] && extra="${CARGO_TARGET_DIR:-$PWD/../../../target}/release-fat/libverilith_x509.a -lpthread -ldl -lm"
    cc -O2 -DDATA_DIR="\"$PWD/data\"" -I "$MBEDTLS_DIR/include" mbedtls_bench.c \
        "$MBEDTLS_DIR/$v/library/libmbedx509.a" "$MBEDTLS_DIR/$v/library/libmbedcrypto.a" $extra -o "$out/mb-$v"
done
rows="vx509 parse|vx509 parse + visit every field|x509-parser parse_x509_certificate|x509-cert Certificate::from_der|webpki EndEntityCert::try_from|OpenSSL X509::from_der"
for i in 1 2 3; do
    echo "$rows" | tr '|' '\n' | while read -r row; do ./target/release/x509bench "$row"; done
    "$out/mb-build" "mbedTLS 3.6.4"
    "$out/mb-build-vx" "vx509-backed mbedTLS"
done | sort -t'	' -k1,1 -k2,2 -k3,3n | awk -F'\t' '!seen[$1 FS $2]++'
rm -r "$out"

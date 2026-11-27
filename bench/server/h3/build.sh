#!/usr/bin/env bash
# Build the HTTP/3 tools bench/server needs and no distribution ships yet:
#
#   h2load   nghttp2's load generator with HTTP/3 (ngtcp2 + nghttp3 on aws-lc),
#            the same tool and output run.py already uses for HTTP/2
#   nginx    mainline with --with-http_v3_module, on BoringSSL (what nginx's
#            QUIC docs name first)
#   h2o      master, with its own QUIC stack (quicly) and mruby, like the
#            h2o 2.2 baseline
#
#   bench/server/h3/build.sh [PREFIX]     # default: <repo>/target/h3-tools
#
# Everything is pinned below and built from source into PREFIX; run.py finds
# PREFIX/bin/h2load, PREFIX/nginx/sbin/nginx and PREFIX/bin/h2o there (or
# set H2LOAD_H3, NGINX_H3, H2O_H3). Needs a C/C++ toolchain, cmake, ninja,
# go, autotools, pkg-config, ruby and bison, a C++23 compiler (g++ 14), plus libev, c-ares, libuv,
# zlib, pcre2 and libssl headers. Debian/Ubuntu:
#
#   sudo apt-get install build-essential g++-14 cmake ninja-build golang autoconf automake \
#     libtool pkg-config ruby bison libev-dev libc-ares-dev libuv1-dev zlib1g-dev \
#     libpcre2-dev libssl-dev
#
# The h3 baseline written in Rust (h3 + quinn) is baselines/h3-quinn and is
# built with cargo like the hyper one.
set -euo pipefail

AWS_LC=v5.15.0
BORINGSSL=0.20261105.0
NGHTTP3=v1.19.0
NGTCP2=v1.26.0
NGHTTP2=v1.71.0
NGINX=release-1.31.10
H2O=d3e43fcf00c3e6b17826b95d2d362d646185918a   # master, 2026-11

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
PREFIX=${1:-$ROOT/target/h3-tools}
SRC=$PREFIX/src
JOBS=${JOBS:-$(nproc 2>/dev/null || sysctl -n hw.ncpu)}
mkdir -p "$SRC"
# nghttp2's apps are C++23 (<print>): GCC 14 or later, or a clang with a
# library that has it. Ubuntu 24.04's default g++ 13 does not.
if [ -z "${CXX23:-}" ]; then
    for c in g++-15 g++-14 g++; do
        if command -v "$c" >/dev/null && echo '#include <print>' | "$c" -std=c++23 -x c++ -fsyntax-only - 2>/dev/null; then
            CXX23=$c; break
        fi
    done
fi
[ -n "${CXX23:-}" ] || { echo "need a C++23 compiler with <print> (g++-14: apt-get install g++-14), or set CXX23" >&2; exit 1; }
PREFIX=$(cd "$PREFIX" && pwd)
SRC=$PREFIX/src

fetch() { # repo ref dir: a fresh shallow checkout of one tag or commit
    rm -rf "$SRC/$3"
    git init -q "$SRC/$3"
    git -C "$SRC/$3" fetch -q --depth 1 "https://github.com/$1" "$2"
    git -C "$SRC/$3" -c advice.detachedHead=false checkout -q FETCH_HEAD
    if [ -f "$SRC/$3/.gitmodules" ]; then
        git -C "$SRC/$3" submodule -q update --init --recursive --depth 1
    fi
}

step() { echo "== $*"; }

# aws-lc: the crypto under ngtcp2 and h2load, as nghttp2's README builds it.
if [ ! -f "$PREFIX/aws-lc/lib/libcrypto.a" ] && [ ! -f "$PREFIX/aws-lc/lib64/libcrypto.a" ]; then
    step "aws-lc $AWS_LC"
    fetch aws/aws-lc "$AWS_LC" aws-lc
    cmake -S "$SRC/aws-lc" -B "$SRC/aws-lc/build" -G Ninja -DCMAKE_BUILD_TYPE=Release \
        -DBUILD_TESTING=OFF -DDISABLE_GO=ON -DCMAKE_INSTALL_PREFIX="$PREFIX/aws-lc" -DCMAKE_INSTALL_LIBDIR=lib
    ninja -C "$SRC/aws-lc/build" install
fi

if [ ! -f "$PREFIX/lib/pkgconfig/libnghttp3.pc" ]; then
    step "nghttp3 $NGHTTP3"
    fetch ngtcp2/nghttp3 "$NGHTTP3" nghttp3
    (cd "$SRC/nghttp3" && autoreconf -fi >/dev/null &&
        ./configure -q --prefix="$PREFIX" --enable-lib-only &&
        make -s -j"$JOBS" && make -s install)
fi

if [ ! -f "$PREFIX/lib/pkgconfig/libngtcp2_crypto_boringssl.pc" ]; then
    step "ngtcp2 $NGTCP2"
    fetch ngtcp2/ngtcp2 "$NGTCP2" ngtcp2
    (cd "$SRC/ngtcp2" && autoreconf -fi >/dev/null &&
        ./configure -q --prefix="$PREFIX" --enable-lib-only --with-boringssl \
            BORINGSSL_CFLAGS="-I$PREFIX/aws-lc/include" \
            BORINGSSL_LIBS="-L$PREFIX/aws-lc/lib -lssl -lcrypto" &&
        make -s -j"$JOBS" && make -s install)
fi

if [ ! -x "$PREFIX/bin/h2load" ]; then
    step "nghttp2 $NGHTTP2 (h2load with HTTP/3)"
    fetch nghttp2/nghttp2 "$NGHTTP2" nghttp2
    (cd "$SRC/nghttp2" && autoreconf -fi >/dev/null &&
        ./configure -q --prefix="$PREFIX" --enable-app --enable-http3 --disable-python-bindings \
            --with-libngtcp2 --with-libnghttp3 \
            PKG_CONFIG_PATH="$PREFIX/lib/pkgconfig:$PREFIX/aws-lc/lib/pkgconfig" \
            OPENSSL_CFLAGS="-I$PREFIX/aws-lc/include" OPENSSL_LIBS="-L$PREFIX/aws-lc/lib -lssl -lcrypto" \
            LDFLAGS="-Wl,-rpath,$PREFIX/lib" CXX="$CXX23" &&
        make -s -j"$JOBS" && make -s install)
fi

# BoringSSL for nginx: built in place, the layout nginx's --with-openssl
# docs for QUIC expect (include/ and build/libssl.a).
if [ ! -f "$SRC/boringssl/build/libssl.a" ]; then
    step "BoringSSL $BORINGSSL"
    fetch google/boringssl "$BORINGSSL" boringssl
    cmake -S "$SRC/boringssl" -B "$SRC/boringssl/build" -G Ninja -DCMAKE_BUILD_TYPE=Release -DBUILD_TESTING=OFF
    ninja -C "$SRC/boringssl/build" ssl crypto
fi

# BoringSSL is C++: nginx links it with the C compiler, so name the C++
# runtime (after --no-as-needed, since nginx puts -lssl after our flags).
case "$(uname)" in
    Darwin) CXXLIB="-lc++" ;;
    *) CXXLIB="-Wl,--no-as-needed -lstdc++" ;;
esac
if [ ! -x "$PREFIX/nginx/sbin/nginx" ]; then
    step "nginx $NGINX (http_v3)"
    fetch nginx/nginx "$NGINX" nginx
    (cd "$SRC/nginx" && auto/configure --prefix="$PREFIX/nginx" \
            --with-http_ssl_module --with-http_v2_module --with-http_v3_module \
            --without-http_gzip_module \
            --with-cc-opt="-O2 -I$SRC/boringssl/include" \
            --with-ld-opt="-L$SRC/boringssl/build $CXXLIB" >/dev/null &&
        make -s -j"$JOBS" && make -s install)
fi

if [ ! -x "$PREFIX/bin/h2o" ]; then
    step "h2o $H2O (QUIC, mruby)"
    fetch h2o/h2o "$H2O" h2o
    cmake -S "$SRC/h2o" -B "$SRC/h2o/build" -G Ninja -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_INSTALL_PREFIX="$PREFIX" -DWITH_MRUBY=ON -DWITH_BUNDLED_SSL=OFF
    ninja -C "$SRC/h2o/build" h2o
    ninja -C "$SRC/h2o/build" install
fi

step "done"
# sed, not head: head exits after its lines, and with pipefail the
# writer's SIGPIPE would fail the build.
"$PREFIX/bin/h2load" --version | sed -n 1p
"$PREFIX/nginx/sbin/nginx" -V 2>&1 | sed -n 1,2p
"$PREFIX/bin/h2o" --version | sed -n 1p

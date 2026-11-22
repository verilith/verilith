#!/usr/bin/env bash
# Builds every runner into work/build/bin. Each suite builds on its own: a
# suite that fails to build is reported and skipped, the rest still run.
#   scripts/build.sh [SUITE...]     (default: all)
. "$(dirname "$0")/lib.sh"
mkdir -p "$BIN" "$BUILD/log"
H=$ROOT/harness
S=$ROOT/suites
RUNNER_SRC="$H/runner.c $H/counters.c"

# cc_runner OUT SRC... [-- extra link args]: a C runner with the harness.
cc_runner() {
  local out=$1; shift
  $CC $CFLAGS_BENCH -std=gnu11 -I"$H" "$@" $RUNNER_SRC -o "$BIN/$out"
}
cxx_runner() {
  local out=$1; shift
  $CC $CFLAGS_BENCH -c "$H/runner.c" -I"$H" -o "$BUILD/runner.o"
  $CC $CFLAGS_BENCH -c "$H/counters.c" -I"$H" -o "$BUILD/counters.o"
  $CXX $CFLAGS_BENCH -std=c++17 -I"$H" "$@" "$BUILD/runner.o" "$BUILD/counters.o" -o "$BIN/$out"
}

# rust_lib REPO FEATURES: builds REPO's staticlib with FEATURES; prints the .a path.
rust_lib() {
  local repo=$1 features=$2 name tdir profile
  name=verilith_${repo#v}
  profile=$(ours_profile "$repo")
  tdir=$WORK/target/$repo-$(echo "${features:-default}" | tr ', ' '__')
  cargo build -q --profile "$profile" --lib --manifest-path "$(ours "$repo")/Cargo.toml" --target-dir "$tdir" \
    ${features:+--features "$features"} >&2 || die "cargo build of $repo failed"
  echo "$tdir/$profile/lib$name.a"
}

# rust_runner PACKAGE OUT: a runner from runners/, our library through its own API.
rust_runner() {
  cargo build -q --release --manifest-path "$ROOT/runners/Cargo.toml" --target-dir "$WORK/target/runners" -p "$1"
  cp "$WORK/target/runners/release/$1" "$BIN/$2"
}

# cmake_build SRC BUILDDIR [cmake args...]
cmake_build() {
  local src=$1 dir=$2; shift 2
  cmake -S "$src" -B "$dir" -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_FLAGS="$CFLAGS_BENCH" \
    -DCMAKE_CXX_FLAGS="$CFLAGS_BENCH" -DBUILD_SHARED_LIBS=OFF "$@" >/dev/null
  cmake --build "$dir" -j "$NPROC" >/dev/null
}

build_zlib() {
  local z; z=$(orig zlib)
  local zfiles=""
  for f in adler32 compress crc32 deflate infback inffast inflate inftrees trees uncompr zutil; do zfiles="$zfiles $z/$f.c"; done
  cc_runner zlib-zlib -I"$z" "$S/zlib/zlib.c" $zfiles
  local lib; lib=$(rust_lib vzlib zlib-abi)
  cc_runner zlib-vzlib -I"$z" "$S/zlib/zlib.c" "$lib" $RUST_LIBS
  # The compressed inputs, made once by zlib itself.
  "$BIN/zlib-zlib" prepare "$DATA/zlib"
}

build_dns() {
  local src; src=$(orig c-ares)
  local cmk="-DCARES_STATIC=ON -DCARES_SHARED=OFF -DCARES_BUILD_TOOLS=OFF -DCARES_BUILD_TESTS=OFF"
  cmake_build "$src" "$BUILD/c-ares" $cmk
  # The same commit with vdns's patch, linked to vdns.
  local psrc=$BUILD/c-ares-vdns-src
  rm -rf "$psrc"; cp -R "$src" "$psrc"; rm -rf "$psrc/.git"
  (cd "$psrc" && patch -p1 -s < "$(ours vdns)/cares/c-ares-use-vdns.patch")
  local lib; lib=$(rust_lib vdns cares,ares-abi)
  cmake_build "$psrc" "$BUILD/c-ares-vdns" $cmk -DCARES_VDNS_LIB="$lib"
  local sys=""
  [ "$OS" = Darwin ] && sys="-lresolv -framework CoreFoundation -framework SystemConfiguration"
  local inc="-I$src/include -I$BUILD/c-ares -DCARES_STATICLIB"
  cc_runner dns-cares $inc "$S/dns/dns.c" "$BUILD/c-ares/lib/libcares.a" $sys
  if [ "$OS" = Darwin ]; then
    cc_runner dns-vdns $inc "$S/dns/dns.c" "$BUILD/c-ares-vdns/lib/libcares.a" "$lib" $sys $RUST_LIBS
  else
    cc_runner dns-vdns $inc "$S/dns/dns.c" -Wl,--start-group "$BUILD/c-ares-vdns/lib/libcares.a" "$lib" -Wl,--end-group $RUST_LIBS
  fi
  rust_runner vdns-run dns-native
}

build_http() {
  local ll; ll=$(orig llhttp)
  cc_runner http-llhttp -I"$ll/include" "$S/http/llhttp.c" "$ll/src/api.c" "$ll/src/http.c" "$ll/src/llhttp.c"
  local lib; lib=$(rust_lib vhttp llhttp-abi)
  cc_runner http-vhttp -I"$ll/include" "$S/http/llhttp.c" "$ll/src/api.c" "$ll/src/http.c" "$lib" $RUST_LIBS
  local pico; pico=$(orig picohttpparser)
  cc_runner pico-pico -I"$pico" "$S/http/pico.c" "$pico/picohttpparser.c"
  lib=$(rust_lib vhttp phr-abi)
  cc_runner pico-vhttp -I"$pico" "$S/http/pico.c" "$lib" $RUST_LIBS
  rust_runner vhttp-run http-native
}

build_url() {
  local ada; ada=$(orig ada)
  local sh=$BUILD/ada-singleheader
  mkdir -p "$sh"
  (cd "$ada" && AMALGAMATE_OUTPUT_PATH="$sh" python3 singleheader/amalgamate.py >/dev/null)
  [ -f "$sh/ada.cpp" ] || die "ada amalgamation failed"
  $CXX $CFLAGS_BENCH -std=c++20 -I"$sh" -c "$sh/ada.cpp" -o "$BUILD/ada.o"
  $CC $CFLAGS_BENCH -I"$H" -I"$sh" -c "$S/url/url.c" -o "$BUILD/url.o"
  $CC $CFLAGS_BENCH -c "$H/runner.c" -I"$H" -o "$BUILD/runner.o"
  $CC $CFLAGS_BENCH -c "$H/counters.c" -I"$H" -o "$BUILD/counters.o"
  $CXX "$BUILD/url.o" "$BUILD/ada.o" "$BUILD/runner.o" "$BUILD/counters.o" -o "$BIN/url-ada"
  local lib; lib=$(rust_lib vurl ada-abi)
  $CC "$BUILD/url.o" "$BUILD/runner.o" "$BUILD/counters.o" "$lib" $RUST_LIBS -o "$BIN/url-vurl"
}

build_json() {
  local cj; cj=$(orig cjson)
  cc_runner cjson-cjson -I"$cj" "$S/json/cjson.c" "$cj/cJSON.c" -lm
  local lib; lib=$(rust_lib vjson cjson)
  cc_runner cjson-vjson -I"$cj" "$S/json/cjson.c" "$lib" $RUST_LIBS
  local sj; sj=$(orig simdjson)/singleheader
  cxx_runner json-simdjson -I"$sj" "$S/json/simdjson.cpp" "$sj/simdjson.cpp"
  rust_runner vjson-run json-vjson
}

build_x509() {
  local src; src=$(orig mbedtls)
  local cmk="-DENABLE_TESTING=OFF -DENABLE_PROGRAMS=OFF -DUSE_SHARED_MBEDTLS_LIBRARY=OFF -DGEN_FILES=OFF"
  cmake_build "$src" "$BUILD/mbedtls" $cmk
  local psrc=$BUILD/mbedtls-vx509-src
  rm -rf "$psrc"; cp -R "$src" "$psrc"; rm -rf "$psrc/.git"
  (cd "$psrc" && patch -p1 -s < "$(ours vx509)/mbedtls/mbedtls-use-vx509.patch")
  local lib; lib=$(rust_lib vx509 mbedtls)
  cmake_build "$psrc" "$BUILD/mbedtls-vx509" $cmk -DMBEDTLS_VX509_DIR="$(ours vx509)" -DMBEDTLS_VX509_LIB="$lib"
  cc_runner x509-mbedtls -I"$src/include" "$S/x509/x509.c" \
    "$BUILD/mbedtls/library/libmbedx509.a" "$BUILD/mbedtls/library/libmbedcrypto.a"
  if [ "$OS" = Darwin ]; then
    cc_runner x509-vx509 -I"$src/include" "$S/x509/x509.c" \
      "$BUILD/mbedtls-vx509/library/libmbedx509.a" "$BUILD/mbedtls-vx509/library/libmbedcrypto.a" "$lib" $RUST_LIBS
  else
    cc_runner x509-vx509 -I"$src/include" "$S/x509/x509.c" -Wl,--start-group \
      "$BUILD/mbedtls-vx509/library/libmbedx509.a" "$BUILD/mbedtls-vx509/library/libmbedcrypto.a" "$lib" \
      -Wl,--end-group $RUST_LIBS
  fi
  rust_runner vx509-run x509n-vx509
}

# Native APIs: vx509::parse against Verdict's parse_x509_der, no mbedTLS.
# Verdict builds in its own cargo project (runners/verdict-run) with the
# toolchain Verdict pins, which rustup installs on first use.
build_x509n() {
  rust_runner vx509-run x509n-vx509
  [ -d "$(orig verdict)/deps/verus/source/vstd" ] || die "Verdict's deps/verus submodule is missing; rerun scripts/fetch.sh"
  ln -sfn "$(orig verdict)" "$WORK/verdict"
  (cd "$ROOT/runners/verdict-run" && cargo build -q --release --target-dir "$WORK/target/verdict-run")
  cp "$WORK/target/verdict-run/release/verdict-run" "$BIN/x509n-verdict"
}

# libpng with the platform's zlib, as it ships.
build_libpng() {
  cmake_build "$(orig libpng)" "$BUILD/libpng" -DPNG_SHARED=OFF -DPNG_TESTS=OFF -DPNG_TOOLS=OFF -DPNG_FRAMEWORK=OFF
}
png_inc() { echo "-I$(orig libpng) -I$BUILD/libpng"; }
png_lib() { echo "$BUILD/libpng/libpng16.a -lz -lm"; }

build_png() {
  build_libpng
  cc_runner png-libpng $(png_inc) "$S/png/libpng.c" $(png_lib)
  rust_runner vpng-run png-vpng
}

build_webp() {
  local w; w=$(orig libwebp)
  [ -f "$BUILD/libpng/libpng16.a" ] || build_libpng
  cmake_build "$w" "$BUILD/libwebp" -DWEBP_BUILD_ANIM_UTILS=OFF -DWEBP_BUILD_CWEBP=OFF -DWEBP_BUILD_DWEBP=OFF \
    -DWEBP_BUILD_GIF2WEBP=OFF -DWEBP_BUILD_IMG2WEBP=OFF -DWEBP_BUILD_VWEBP=OFF -DWEBP_BUILD_WEBPINFO=OFF \
    -DWEBP_BUILD_WEBPMUX=OFF -DWEBP_BUILD_EXTRAS=OFF -DWEBP_BUILD_LIBWEBPMUX=OFF
  local wl="$BUILD/libwebp/libwebp.a $BUILD/libwebp/libsharpyuv.a"
  cc_runner webp-libwebp -I"$w/src" "$S/webp/webp.c" $wl -lpthread -lm
  local lib; lib=$(rust_lib vwebp webp-abi)
  cc_runner webp-vwebp -I"$w/src" "$S/webp/webp.c" "$lib" $RUST_LIBS
  # Inputs: the PNG photos, encoded by libwebp, lossless and lossy (quality
  # 75, cwebp's default).
  $CC $CFLAGS_BENCH -I"$w/src" $(png_inc) "$S/webp/mkwebp.c" $wl $(png_lib) -lpthread -o "$BUILD/mkwebp"
  mkdir -p "$DATA/webp" "$DATA/webp-lossy"
  for f in "$DATA"/png/*.png; do
    b=$(basename "$f" .png)
    [ -f "$DATA/webp/$b.webp" ] || "$BUILD/mkwebp" "$f" "$DATA/webp/$b.webp"
    [ -f "$DATA/webp-lossy/$b.webp" ] || "$BUILD/mkwebp" "$f" "$DATA/webp-lossy/$b.webp" 75
  done
}

# google/brotli's decoder API: libbrotlidec against vbrotli (brotli-abi).
build_brotli() {
  local b; b=$(orig brotli)
  cmake_build "$b" "$BUILD/brotli" -DBROTLI_DISABLE_TESTS=ON -DBROTLI_BUILD_TOOLS=OFF
  local inc="-I$b/c/include"
  cc_runner brotli-brotli $inc "$S/brotli/brotli.c" "$BUILD/brotli/libbrotlidec.a" "$BUILD/brotli/libbrotlicommon.a"
  local lib; lib=$(rust_lib vbrotli brotli-abi)
  cc_runner brotli-vbrotli $inc "$S/brotli/brotli.c" "$lib" $RUST_LIBS
  # The compressed inputs, made once by google/brotli's encoder.
  $CC $CFLAGS_BENCH $inc "$S/brotli/mkbr.c" "$BUILD/brotli/libbrotlienc.a" "$BUILD/brotli/libbrotlicommon.a" -lm -o "$BUILD/mkbr"
  mkdir -p "$DATA/brotli/br"
  local f q n
  for f in "$DATA"/brotli/*; do
    [ -f "$f" ] || continue
    n=$(basename "$f")
    for q in 5 11; do
      [ -f "$DATA/brotli/br/$n.q$q.br" ] || "$BUILD/mkbr" "$f" "$DATA/brotli/br/$n.q$q.br" $q
    done
  done
}

# libjpeg-turbo as it ships: with its SIMD code (NEON on AArch64; on x86-64
# that needs NASM or Yasm, and the build stops without one rather than
# quietly timing the C code).
build_jpeg() {
  local j; j=$(orig libjpeg-turbo)
  [ -f "$BUILD/libpng/libpng16.a" ] || build_libpng
  cmake_build "$j" "$BUILD/libjpeg-turbo" -DENABLE_SHARED=OFF -DENABLE_STATIC=ON -DWITH_TURBOJPEG=ON \
    -DWITH_JAVA=OFF -DWITH_TESTS=OFF -DWITH_TOOLS=OFF -DWITH_FUZZ=OFF -DREQUIRE_SIMD=ON
  local jl="$BUILD/libjpeg-turbo/libturbojpeg.a"
  cc_runner jpeg-turbo -I"$j/src" "$S/jpeg/jpeg.c" "$jl" -lm
  local lib; lib=$(rust_lib vjpeg turbojpeg-abi)
  cc_runner jpeg-vjpeg -I"$j/src" "$S/jpeg/jpeg.c" "$lib" $RUST_LIBS
  # Inputs: the PNG photos, encoded by libjpeg-turbo: baseline and
  # progressive 4:2:0 at quality 75 (cjpeg's default), and baseline 4:4:4
  # at quality 90.
  $CC $CFLAGS_BENCH -I"$j/src" $(png_inc) "$S/jpeg/mkjpeg.c" "$jl" $(png_lib) -o "$BUILD/mkjpeg"
  mkdir -p "$DATA/jpeg" "$DATA/jpeg-prog" "$DATA/jpeg-444"
  local f b
  for f in "$DATA"/png/*.png; do
    b=$(basename "$f" .png)
    [ -f "$DATA/jpeg/$b.jpg" ] || "$BUILD/mkjpeg" "$f" "$DATA/jpeg/$b.jpg" 75 420
    [ -f "$DATA/jpeg-prog/$b.jpg" ] || "$BUILD/mkjpeg" "$f" "$DATA/jpeg-prog/$b.jpg" 75 420 progressive
    [ -f "$DATA/jpeg-444/$b.jpg" ] || "$BUILD/mkjpeg" "$f" "$DATA/jpeg-444/$b.jpg" 90 444
  done
}

# OTS's API: OTS against vfont's headers of the same names over its C ABI.
# OTS's own build is meson; its sources and the WOFF2 decoder it uses are
# compiled here directly, with the flags everything else gets. Graphite
# tables are left out, as in OTS built with -Dgraphite=false (they need lz4);
# no input has them.
build_font() {
  local o w b; o=$(orig ots); w=$(orig woff2); b=$(orig brotli)
  cmake_build "$b" "$BUILD/brotli" -DBROTLI_DISABLE_TESTS=ON -DBROTLI_BUILD_TOOLS=OFF
  local d=$BUILD/ots; mkdir -p "$d"
  printf '#define PACKAGE "ots"\n#define VERSION "vbench"\n#define OTS_COLR_CYCLE_CHECK 1\n#define OTS_SYNTHESIZE_MISSING_GVAR 1\n' > "$d/config.h"
  local f objs=""
  for f in "$o"/src/*.cc "$w"/src/table_tags.cc "$w"/src/variable_length.cc "$w"/src/woff2_common.cc \
           "$w"/src/woff2_dec.cc "$w"/src/woff2_out.cc; do
    case "$(basename "$f" .cc)" in feat|glat|gloc|sile|silf|sill) continue ;; esac
    $CXX $CFLAGS_BENCH -std=c++17 -DHAVE_CONFIG_H -I"$d" -I"$o/include" -I"$w/include" -I"$b/c/include" \
      -c "$f" -o "$d/$(basename "${f%.cc}").o"
    objs="$objs $d/$(basename "${f%.cc}").o"
  done
  rm -f "$d/libots.a"; ar rcs "$d/libots.a" $objs
  cxx_runner font-ots -I"$o/include" "$S/font/font.cpp" "$d/libots.a" \
    "$BUILD/brotli/libbrotlidec.a" "$BUILD/brotli/libbrotlicommon.a" -lz
  local lib; lib=$(rust_lib vfont "")
  cxx_runner font-vfont -I"$(ours vfont)/include" "$S/font/font.cpp" "$lib" $RUST_LIBS
}

# liblz4's API (lz4.h, lz4frame.h): liblz4 against vlz4 (lz4-abi).
build_lz4() {
  local l; l=$(orig lz4)/lib
  cc_runner lz4-lz4 -I"$l" "$S/lz4/lz4.c" "$l/lz4.c" "$l/lz4hc.c" "$l/lz4frame.c" "$l/xxhash.c"
  local lib; lib=$(rust_lib vlz4 lz4-abi)
  cc_runner lz4-vlz4 -I"$l" "$S/lz4/lz4.c" "$lib" $RUST_LIBS
  # The compressed inputs, made once by liblz4 itself.
  "$BIN/lz4-lz4" prepare "$DATA/lz4"
}

# snappy's C API (snappy-c.h): libsnappy against vsnappy (snappy-abi).
build_snappy() {
  local s; s=$(orig snappy)
  cmake_build "$s" "$BUILD/snappy" -DSNAPPY_BUILD_TESTS=OFF -DSNAPPY_BUILD_BENCHMARKS=OFF
  # libsnappy is C++: its runner links with the C++ driver.
  $CC $CFLAGS_BENCH -std=gnu11 -I"$H" -I"$s" -c "$S/snappy/snappy.c" -o "$BUILD/snappy-driver.o"
  $CC $CFLAGS_BENCH -c "$H/runner.c" -I"$H" -o "$BUILD/runner.o"
  $CC $CFLAGS_BENCH -c "$H/counters.c" -I"$H" -o "$BUILD/counters.o"
  $CXX $CFLAGS_BENCH "$BUILD/snappy-driver.o" "$BUILD/runner.o" "$BUILD/counters.o" "$BUILD/snappy/libsnappy.a" -o "$BIN/snappy-snappy"
  local lib; lib=$(rust_lib vsnappy snappy-abi)
  cc_runner snappy-vsnappy -I"$s" "$S/snappy/snappy.c" "$lib" $RUST_LIBS
  # The compressed inputs, made once by libsnappy itself.
  "$BIN/snappy-snappy" prepare "$DATA/snappy"
}

# libarchive's read API: libarchive against varchive (libarchive-abi).
# libarchive is built with zlib only (the zlib built above for the zlib
# suite's version), so DEFLATE is zlib's on one side and vzlib's on the other.
build_archive() {
  local src z; src=$(orig libarchive); z=$(orig zlib)
  cmake_build "$z" "$BUILD/zlib-cmake" -DZLIB_BUILD_EXAMPLES=OFF -DZLIB_BUILD_TESTING=OFF -DZLIB_BUILD_SHARED=OFF
  local zlib; zlib=$(ls "$BUILD"/zlib-cmake/libz*.a | head -n 1)
  local off=""
  for o in TEST OPENSSL MBEDTLS NETTLE LIBB2 LZ4 LZO LZMA ZSTD BZip2 LIBXML2 EXPAT WIN32_XMLLITE PCREPOSIX PCRE2POSIX LIBGCC CNG ICONV ACL XATTR CAT CPIO UNZIP; do
    off="$off -DENABLE_$o=OFF"
  done
  cmake_build "$src" "$BUILD/libarchive" $off -DENABLE_TAR=ON -DENABLE_ZLIB=ON \
    -DZLIB_LIBRARY="$zlib" -DZLIB_INCLUDE_DIR="$z;$BUILD/zlib-cmake" -DCMAKE_POLICY_VERSION_MINIMUM=3.5
  local inc="-I$src/libarchive"
  cc_runner archive-libarchive $inc "$S/archive/archive.c" "$BUILD/libarchive/libarchive/libarchive.a" "$zlib"
  local lib; lib=$(rust_lib varchive libarchive-abi)
  cc_runner archive-varchive $inc "$S/archive/archive.c" "$lib" $RUST_LIBS
  # The archives, made once by libarchive's bsdtar: the five Silesia files
  # (large members), and dickens cut into 2000 files of 4 KiB (many small
  # members, which is what a source tarball looks like).
  #
  # --no-mac-metadata: on macOS bsdtar otherwise stores each file's extended
  # attributes as an extra "._NAME" member in a tar, and libarchive's tar
  # reader on macOS (only there) folds those members into the next entry
  # instead of returning them. varchive returns them as members, as
  # libarchive does everywhere else, so with them in the archive the two
  # sides do different work and the check values differ.
  local d=$DATA/archive t=$BUILD/archive-tree bsdtar="$BUILD/libarchive/bin/bsdtar --no-mac-metadata"
  if [ ! -f "$BUILD/archive-inputs-v2" ]; then
    rm -rf "$t" "$d"; mkdir -p "$t/silesia" "$t/small" "$d"
    for f in $SILESIA_FILES; do cp "$DATA/zlib/$f" "$t/silesia/$f"; done
    head -c 8192000 "$DATA/zlib/dickens" | (cd "$t/small" && split -b 4096 -a 4 - f)
    (cd "$t/small" && i=0 && for f in f*; do mkdir -p "d$((i % 40))"; mv "$f" "d$((i % 40))/$f.txt"; i=$((i + 1)); done)
    (cd "$t" && $bsdtar --format pax -cf "$d/silesia.tar" silesia \
      && $bsdtar --format zip -cf "$d/silesia.zip" silesia \
      && $bsdtar --format zip --options zip:compression=store -cf "$d/silesia-stored.zip" silesia \
      && $bsdtar --format pax -cf "$d/small.tar" small \
      && $bsdtar --format pax -czf "$d/small.tar.gz" small \
      && $bsdtar --format zip -cf "$d/small.zip" small)
    touch "$BUILD/archive-inputs-v2"
  fi
}

build_regex() {
  # RE2 needs Abseil: build and install both into one prefix.
  local pre=$BUILD/re2-prefix
  local cmk="-DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_STANDARD=17 -DBUILD_SHARED_LIBS=OFF -DCMAKE_INSTALL_PREFIX=$pre -DCMAKE_INSTALL_LIBDIR=lib"
  cmake -S "$(orig abseil-cpp)" -B "$BUILD/abseil" $cmk -DCMAKE_CXX_FLAGS="$CFLAGS_BENCH" \
    -DABSL_BUILD_TESTING=OFF -DABSL_PROPAGATE_CXX_STD=ON >/dev/null
  cmake --build "$BUILD/abseil" -j "$NPROC" >/dev/null
  cmake --install "$BUILD/abseil" >/dev/null
  cmake -S "$(orig re2)" -B "$BUILD/re2" $cmk -DCMAKE_CXX_FLAGS="$CFLAGS_BENCH" \
    -DCMAKE_PREFIX_PATH="$pre" -DRE2_BUILD_TESTING=OFF >/dev/null
  cmake --build "$BUILD/re2" -j "$NPROC" >/dev/null
  cmake --install "$BUILD/re2" >/dev/null
  # cre2, RE2's C wrapper: one file.
  local cre2; cre2=$(orig cre2)/src
  $CXX $CFLAGS_BENCH -std=c++17 -I"$cre2" -I"$pre/include" \
    -Dcre2_VERSION_INTERFACE_CURRENT=0 -Dcre2_VERSION_INTERFACE_REVISION=0 \
    -Dcre2_VERSION_INTERFACE_AGE=0 '-Dcre2_VERSION_INTERFACE_STRING="0.0.0"' \
    -c "$cre2/cre2.cpp" -o "$BUILD/cre2.o"
  $CC $CFLAGS_BENCH -I"$H" -I"$cre2" -c "$S/regex/regex.c" -o "$BUILD/regex.o"
  $CC $CFLAGS_BENCH -c "$H/runner.c" -I"$H" -o "$BUILD/runner.o"
  $CC $CFLAGS_BENCH -c "$H/counters.c" -I"$H" -o "$BUILD/counters.o"
  local objs="$BUILD/regex.o $BUILD/runner.o $BUILD/counters.o"
  if [ "$OS" = Darwin ]; then
    $CXX $objs "$BUILD/cre2.o" "$pre/lib/libre2.a" "$pre"/lib/libabsl_*.a -framework CoreFoundation -o "$BIN/regex-re2"
  else
    $CXX $objs "$BUILD/cre2.o" "$pre/lib/libre2.a" -Wl,--start-group "$pre"/lib/libabsl_*.a -Wl,--end-group -lpthread -o "$BIN/regex-re2"
  fi
  local lib; lib=$(rust_lib vregex cre2-abi)
  $CC $objs "$lib" $RUST_LIBS -o "$BIN/regex-vregex"
}

# XML: expat's and libxml2's SAX APIs against verilith-xml's own API
# (native: vxml has neither ABI yet).
build_xml() {
  local src; src=$(orig expat)/expat
  cmake_build "$src" "$BUILD/expat" -DEXPAT_BUILD_TOOLS=OFF -DEXPAT_BUILD_EXAMPLES=OFF -DEXPAT_BUILD_TESTS=OFF \
    -DEXPAT_BUILD_DOCS=OFF -DEXPAT_SHARED_LIBS=OFF
  local a; a=$(find "$BUILD/expat" -name 'libexpat*.a' | head -1)
  cc_runner xml-expat -I"$src/lib" "$S/xml/expat.c" "$a"
  # libxml2 as it builds by default, less its programs, tests and iconv (its
  # own UTF-8, UTF-16, ISO-8859-x and ASCII decoders remain).
  local x; x=$(orig libxml2)
  cmake_build "$x" "$BUILD/libxml2" -DLIBXML2_WITH_PROGRAMS=OFF -DLIBXML2_WITH_TESTS=OFF \
    -DLIBXML2_WITH_PYTHON=OFF -DLIBXML2_WITH_ICONV=OFF -DLIBXML2_WITH_ZLIB=OFF
  local l; l=$(find "$BUILD/libxml2" -name 'libxml2*.a' | head -1)
  local sys="-lm"
  [ "$OS" = Darwin ] || sys="$sys -lpthread"
  cc_runner xml-libxml2 -I"$x/include" -I"$BUILD/libxml2" "$S/xml/libxml2.c" "$l" $sys
  rust_runner vxml-run xml-vxml
}

# --print-lib REPO FEATURES: build one of our staticlibs and print its path.
if [ "${1:-}" = --print-lib ]; then rust_lib "$2" "${3:-}"; exit; fi

ALL="zlib dns http url json x509 x509n png webp brotli jpeg regex archive lz4 snappy font xml"
want=${*:-$ALL}
failed=""
for s in $want; do
  say "build $s"
  set +e
  ( set -euo pipefail; "build_$s" ) > "$BUILD/log/$s.log" 2>&1
  rc=$?
  set -e
  if [ $rc -ne 0 ]; then
    warn "suite $s failed to build; see $BUILD/log/$s.log (last lines below). The other suites still run."
    tail -n 15 "$BUILD/log/$s.log" >&2
    failed="$failed $s"
  fi
done
[ -z "$failed" ] || warn "not built:$failed"
echo "$failed" > "$BUILD/failed"
if [ -n "$failed" ] && [ "$(echo $failed | wc -w)" -eq "$(echo $want | wc -w)" ]; then die "no suite built"; fi

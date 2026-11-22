#!/usr/bin/env bash
# rust-prelink.sh IN.a OUT.a: writes OUT.a, IN.a (one of our Rust staticlibs)
# as a single relocatable object in which only the library's own API stays
# global. Rust's standard library, its runtime and compiler_builtins, which
# every Rust staticlib carries a copy of, become local.
#
# Node 26 links a Rust static library of its own (deps/crates). Linked
# beside it, ours fail on symbols both copies of std define
# (rust_eh_personality, std::panicking::EMPTY_PANIC); after this each copy
# is private to its own library. The code is not recompiled: it is the same
# library the benchmarks measure.
set -euo pipefail
in=$(cd "$(dirname "$1")" && pwd)/$(basename "$1"); out=$2
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/x"; (cd "$tmp/x" && ar x "$in")
if [ "$(uname)" = Darwin ]; then pre=_; else pre=; fi
# The API: global symbols defined by our own crates' objects (verilith_*)
# and by any C or C++ compiled into the library (members that are not a
# Rust codegen unit), less Rust-mangled names (v0 _R..., legacy
# _ZN...17h<hash>E), the runtime's (rust_*, __*) and LLVM's anon.* names.
# DW.ref.rust_eh_personality (ELF only) stays global: it is a weak, hidden
# COMDAT that the other Rust library's objects refer to as well.
mine=()
for m in "$tmp"/x/*; do
  case $(basename "$m") in verilith_*) mine+=("$m") ;; *.rcgu.o) ;; *) mine+=("$m") ;; esac
done
nm -g --defined-only "${mine[@]}" 2>/dev/null | awk 'NF>=3 {print $3}' | sort -u \
  | grep -Ev "^${pre}(_R|rust_|__|anon\.)" | grep -Ev "^${pre}_ZN.*17h[0-9a-f]{16}E$" > "$tmp/keep" || true
[ -s "$tmp/keep" ] || { echo "rust-prelink.sh: no API symbols found in $1" >&2; exit 1; }
if [ "$(uname)" = Darwin ]; then
  # In -r mode ld64 makes the unlisted symbols private extern, then static.
  ld -r -o "$tmp/all.o" -exported_symbols_list "$tmp/keep" "$tmp"/x/*
else
  ld -r -o "$tmp/all.o" "$tmp"/x/*
  echo DW.ref.rust_eh_personality >> "$tmp/keep"
  objcopy --keep-global-symbols="$tmp/keep" "$tmp/all.o"
fi
rm -f "$out"; ar rcs "$out" "$tmp/all.o"

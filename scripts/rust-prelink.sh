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
# BSD ar (macOS) extracts the symbol table as a member, __.SYMDEF or
# "__.SYMDEF SORTED", unreadable (mode 0); it is not an object.
rm -f "$tmp"/x/__.SYMDEF*
if [ "$(uname)" = Darwin ]; then pre=_; else pre=; fi
# The API: global symbols defined by the library's own crates' objects
# and by any C or C++ compiled into the library (members that are not a
# Rust codegen unit), less Rust-mangled names (v0 _R..., legacy
# _ZN...17h<hash>E), the runtime's (rust_*, __*), compiler_builtins' C
# atomics (atomic_*, __aarch64_*) and LLVM's anon.* names.
# The personality routine stays shared too. On ELF that is
# DW.ref.rust_eh_personality, a weak, hidden COMDAT every Rust library's
# objects refer to. On macOS it is _rust_eh_personality itself, kept global
# and made a weak definition: ld64's compact unwind table holds only a few
# personality routines per image (C++'s is one), so one local copy per
# library does not link. Weak, the copies coalesce with Node's into one;
# it is the same rustc's code in each.
# Rust codegen units are named CRATE-HASH.*.rcgu.o; the runtime's crates
# are the ones below, every other crate is the library's.
runtime=" std core alloc compiler_builtins unwind std_detect panic_abort panic_unwind rustc_std_workspace_core rustc_std_workspace_alloc rustc_std_workspace_std addr2line gimli object miniz_oxide adler2 hashbrown memchr cfg_if libc rustc_demangle "
mine=(); ours=()
for m in "$tmp"/x/*; do
  b=$(basename "$m")
  case $b in
    *.rcgu.o) case $runtime in *" ${b%%-*} "*) ;; *) mine+=("$m"); ours+=("$m") ;; esac ;;
    *) mine+=("$m") ;;
  esac
done
# Apple's nm (llvm-nm) reads the LLVM bitcode that fat LTO leaves in the
# Mach-O object and fails on bitcode from a newer LLVM than its own;
# --no-llvm-bc makes it read the object's symbol table. Errors are not
# hidden: a silent failure here would hide the whole API.
nmflags=(-g --defined-only); [ "$(uname)" = Darwin ] && nmflags+=(--no-llvm-bc)
api() { nm "${nmflags[@]}" "$@" | awk 'NF>=3 {print $3}' | sort -u \
  | grep -Ev "^${pre}(_R|rust_|__|_aarch64_|atomic_|anon\.)" | grep -Ev "^${pre}_ZN.*17h[0-9a-f]{16}E$" || true; }
api "${mine[@]}" > "$tmp/keep"
# The guard: the library's own Rust objects must export something.
[ ${#ours[@]} -gt 0 ] && [ -n "$(api "${ours[@]}")" ] \
  || { echo "rust-prelink.sh: found no API symbols in the library's own objects in $1" >&2; exit 1; }
if [ "$(uname)" = Darwin ]; then
  # In -r mode ld64 makes the unlisted symbols private extern, then static.
  echo _rust_eh_personality >> "$tmp/keep"
  ld -r -o "$tmp/all.o" -exported_symbols_list "$tmp/keep" "$tmp"/x/*
  python3 - "$tmp/all.o" <<'PY'
# Set N_WEAK_DEF on the global _rust_eh_personality in a Mach-O 64 object.
import struct, sys
f = sys.argv[1]; b = bytearray(open(f, 'rb').read())
assert struct.unpack_from('<I', b)[0] == 0xfeedfacf, 'not a 64-bit Mach-O object'
ncmds = struct.unpack_from('<I', b, 16)[0]; off = 32; done = 0
for _ in range(ncmds):
    cmd, size = struct.unpack_from('<II', b, off)
    if cmd == 0x2:  # LC_SYMTAB
        symoff, nsyms, stroff = struct.unpack_from('<III', b, off + 8)
        for i in range(nsyms):
            e = symoff + 16 * i
            strx, typ, sect, desc = struct.unpack_from('<IBBH', b, e)
            name = b[stroff + strx:b.index(0, stroff + strx)]
            if name == b'_rust_eh_personality' and typ & 0x0e == 0x0e and typ & 0x01:
                struct.pack_into('<H', b, e + 6, desc | 0x0080); done += 1
    off += size
if done != 1:
    sys.exit('rust-prelink.sh: expected one global _rust_eh_personality, found %d' % done)
open(f, 'wb').write(b)
PY
else
  ld -r -o "$tmp/all.o" "$tmp"/x/*
  echo DW.ref.rust_eh_personality >> "$tmp/keep"
  objcopy --keep-global-symbols="$tmp/keep" "$tmp/all.o"
fi
rm -f "$out"; ar rcs "$out" "$tmp/all.o"

#!/usr/bin/env python3
"""Keeps CPU intrinsics in verilith-simd.

Verified code reaches SIMD and other CPU instructions through
verilith-simd, whose specifications are tested against the CPU, and copies,
scans and checksums through verilith-core. A crate that calls
`core::arch`/`std::arch` intrinsics directly gets neither: its kernels are
unverified, or carry a trusted contract of their own.

This fails when a library source file (crates/*/src, outside crates/simd)
names `core::arch` or `std::arch` for anything other than `asm!` (value
barriers, constant-time fences), feature detection or `wasm32::unreachable`,
unless the file is listed in scripts/arch-allow.txt with the reason. A
file in that list that no longer uses intrinsics is an error too, so the
list only shrinks.

    scripts/arch-check.py         check
    scripts/arch-check.py --list  print the files that use intrinsics
"""
import pathlib
import re
import sys

root = pathlib.Path(__file__).resolve().parent.parent
use = re.compile(r"\b(?:core|std)::arch\b(?!::asm!)(?!::is_\w+_feature_detected!)(?!::wasm32::unreachable\b)")


def users():
    out = []
    for f in sorted((root / "crates").glob("*/src/**/*.rs")):
        rel = f.relative_to(root).as_posix()
        if rel.startswith("crates/simd/"):
            continue
        for line in f.read_text(errors="replace").splitlines():
            code = line.split("//", 1)[0]
            if use.search(code):
                out.append(rel)
                break
    return out


def allow():
    m = {}
    for line in (root / "scripts" / "arch-allow.txt").read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        path, _, why = line.partition(" ")
        m[path] = why.strip()
    return m


def main():
    found = users()
    if "--list" in sys.argv:
        print("\n".join(found))
        return 0
    a = allow()
    bad = 0
    for f in found:
        if f not in a:
            print(f"arch-check: {f} calls core::arch intrinsics directly; use verilith-simd "
                  f"(or verilith-core for copies, scans and checksums), or add it to "
                  f"scripts/arch-allow.txt with the reason", file=sys.stderr)
            bad = 1
        elif not a[f]:
            print(f"arch-check: {f} is in scripts/arch-allow.txt without a reason", file=sys.stderr)
            bad = 1
    for f in a:
        if f not in found:
            print(f"arch-check: {f} is in scripts/arch-allow.txt but no longer uses intrinsics; "
                  f"remove it", file=sys.stderr)
            bad = 1
    if not bad:
        print(f"arch-check: ok ({len(found)} allowed files)")
    return bad


sys.exit(main())

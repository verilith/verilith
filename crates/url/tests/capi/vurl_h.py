#!/usr/bin/env python3
"""Prints vurl_c.h: ada_c.h's function prototypes renamed ada_* -> vurl_*
(the types are ada_c.h's own)."""
import re, sys

src = open(sys.argv[1]).read()
src = re.sub(r"/\*.*?\*/", "", src, flags=re.S)
src = re.sub(r"//[^\n]*", "", src)
src = re.sub(r"#[^\n]*", "", src)
out = ['#include "ada_c.h"']
depth = 0
stmt = ""
for ch in src:
    if ch == "{":
        depth += 1
    elif ch == "}":
        depth -= 1
        stmt = ""
        continue
    if depth:
        continue
    stmt += ch
    if ch == ";":
        s = " ".join(stmt.split())
        stmt = ""
        if "(" in s and not s.startswith("typedef"):
            out.append(re.sub(r"\bada_(\w+)\s*\(", r"vurl_\1(", s, count=1))
print("\n".join(out))

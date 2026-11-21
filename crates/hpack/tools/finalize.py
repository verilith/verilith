#!/usr/bin/env python3
"""Rewrites `self` to `final(self)` in the ensures clauses of `&mut self`
functions (Verus's new mutable-reference syntax). Usage: finalize.py FILE"""
import re, sys
p = sys.argv[1]
lines = open(p).read().split("\n")
out = []
in_mut = False
in_ens = False
for l in lines:
    if re.search(r"fn \w+\(&mut self", l):
        in_mut = True
    if in_mut and l.strip() == "ensures":
        in_ens = True
    elif in_ens and (l.strip() == "{" or l.strip().startswith("decreases") or l.strip().startswith("requires")):
        in_ens = False
        in_mut = False
    if in_ens:
        l = re.sub(r"(?<![\w(])self\.", "final(self).", l)
    out.append(l)
open(p, "w").write("\n".join(out))

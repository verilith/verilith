#!/usr/bin/env python3
"""Checks that the SIMD128 backend proves what the NEON kernels assume.

For each public function in src/wasm_neon.rs (verified against the
SIMD128 specs in src/wasm.rs), the function of the same name in
src/neon.rs (the contract the NEON kernels are verified against) must
have the same signature, `requires` and `ensures`, word for word, and its
body must forward to it on WebAssembly (`wasm_or!(crate::wasm_neon::NAME`).
Then on wasm32 with simd128 every wrapper the kernels call there is
proven, not trusted.

On x86-64 the wrappers forward to src/wasm_neon.rs as well, and the
SIMD128 functions it uses are proven on SSE in src/wasm_x86.rs: for each
public function there, the function of the same name in src/wasm.rs must
have the same contract, word for word, and forward to it on x86-64
(`x86_or!(crate::wasm_x86::NAME`). Exits 1 and says what differs
otherwise.
"""
import re
import sys
from pathlib import Path

src = Path(__file__).resolve().parent.parent / "src"


def contracts(text):
    """name -> (signature through the end of `ensures`, body)."""
    out = {}
    for m in re.finditer(r"^pub fn (\w+)(.*?)^\{\n(.*?)^\}\n", text, re.M | re.S):
        out[m.group(1)] = (" ".join(m.group(2).split()), m.group(3))
    return out


wasm = contracts((src / "wasm_neon.rs").read_text())
neon = contracts((src / "neon.rs").read_text())
bad = []
for name, (sig, _) in sorted(wasm.items()):
    if not name.startswith("v"):
        continue
    if name not in neon:
        bad.append(f"{name}: not a wrapper in neon.rs")
        continue
    nsig, nbody = neon[name]
    if nsig != sig:
        bad.append(f"{name}: contract differs\n  neon.rs:      {nsig}\n  wasm_neon.rs: {sig}")
    if not re.search(r"wasm_or!\(crate::wasm_neon::" + name + r"\b", nbody):
        bad.append(f"{name}: neon.rs does not forward to wasm_neon::{name}")
for name, (_, body) in sorted(neon.items()):
    m = re.search(r"wasm_or!\(crate::wasm_neon::(\w+)", body)
    if m and m.group(1) not in wasm:
        bad.append(f"{name}: forwards to missing wasm_neon::{m.group(1)}")
w128 = contracts((src / "wasm.rs").read_text())
x86 = contracts((src / "wasm_x86.rs").read_text())
for name, (sig, _) in sorted(x86.items()):
    if name not in w128:
        bad.append(f"{name}: not a function in wasm.rs")
        continue
    wsig, wbody = w128[name]
    if wsig != sig:
        bad.append(f"{name}: contract differs\n  wasm.rs:     {wsig}\n  wasm_x86.rs: {sig}")
    if not re.search(r"x86_or!\(crate::wasm_x86::" + name + r"\b", wbody):
        bad.append(f"{name}: wasm.rs does not forward to wasm_x86::{name}")
for name, (_, body) in sorted(w128.items()):
    m = re.search(r"x86_or!\(crate::wasm_x86::(\w+)", body)
    if m and m.group(1) not in x86:
        bad.append(f"{name}: forwards to missing wasm_x86::{m.group(1)}")
if bad:
    print("\n".join(bad))
    sys.exit(1)
n = sum(1 for k in wasm if k.startswith("v"))
print(f"check_wasm_neon: {n} NEON contracts proven on SIMD128, all forwarded; {len(x86)} SIMD128 contracts proven on SSE, all forwarded")

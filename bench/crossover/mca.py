#!/usr/bin/env python3
"""Cost model for a size cutoff between two kernels, from the instructions
each one executes, with no timing.

    python3 mca.py wild memcpy 16 512 16
    python3 mca.py crc512 crc256 256 1024 64

For each length n from START to STOP (inclusive) by STEP, `trace.py` (under
gdb) records the instructions one call of each kernel executes on n bytes,
the platform's memcpy included. That straight-line trace goes to llvm-mca
for each CPU model below, which gives:

- `lat`: cycles for one call on its own (`-iterations=1`): what a caller
  waiting on the result pays (a CRC over one buffer).
- `tput`: cycles per call when calls run back to back (`-iterations=100`,
  divided by 100): what a decoder's inner loop pays per copy.

Both are deterministic: the same binary and llvm-mca version give the same
numbers. What the model leaves out: glibc's `xtest` (see `trace`; `endbr64` and
`call` are replaced there too); cache misses (inputs are hot), and
branch mispredictions (each kernel's length-dependent branches go one way
per call; a caller whose lengths vary pays about one mispredict either way).
Prints a table and, per CPU and measure, the smallest n from which the first
kernel is no slower than the second through STOP.
"""
import os
import re
import subprocess
import sys
import tempfile

CPUS = os.environ.get("CPUS", "icelake-server,sapphirerapids,znver4").split(",")
HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "target", "release", "crossover")


def trace(kernel, n):
    with tempfile.NamedTemporaryFile("r", suffix=".s") as f:
        env = dict(os.environ, TRACE_OUT=f.name)
        subprocess.run(["gdb", "-q", "-batch", "-x", os.path.join(HERE, "trace.py"), "--args", BIN, kernel, str(n)],
                       env=env, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        lines = f.read().splitlines()
    out = []
    skip = False
    for l in lines:
        fn, l = l.split("\t", 1)
        # The wrappers' own stack frames (see `wild` and `platform` in
        # main.rs): inlined into a decoder's loop, `copy_lits` has none.
        # llvm-mca has no stack engine, so pushes and pops would count as a
        # chain of `rsp` updates that the hardware does not wait for.
        if fn.split("::")[-1] in ("wild", "platform") and re.match(r"(push|pop)\s|(add|sub)\s+rsp,", l):
            continue
        # glibc's vzeroupper return on CPUs with RTM is `xtest; jne`, which
        # llvm-mca models at about 100 cycles. CPUs without RTM (every AMD
        # one, and Intel ones with TSX turned off, most since 2021) take
        # the same path without it, so it is left out.
        if l.startswith("xtest"):
            skip = True
            continue
        if skip:
            skip = False
            if l.startswith("jne"):
                continue
        l = re.sub(r"\s+#.*$", "", l)          # gdb's "# 0x..." address notes
        l = re.sub(r"\s*<[^>]*>", "", l)        # symbol+offset after targets
        l = l.replace("bnd ", "").replace("notrack ", "").strip()
        # llvm-mca has no scheduling data for these and charges them 100
        # cycles: `endbr64` decodes as a nop, and a call's work besides the
        # (predicted) jump is pushing the return address.
        if l.startswith("endbr64"):
            l = "nop"
        elif l.startswith("call"):
            l = "push rax"
        out.append(l)
    return out


def mca(trace_lines, cpu, iters):
    src = ".intel_syntax noprefix\n" + "\n".join(trace_lines) + "\n"
    r = subprocess.run(["llvm-mca", "-mtriple=x86_64", f"-mcpu={cpu}", f"-iterations={iters}"],
                       input=src, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"llvm-mca -mcpu={cpu}: {r.stderr[:2000]}")
    m = re.search(r"Total Cycles:\s+(\d+)", r.stdout)
    return int(m.group(1))


def main():
    a, b, start, stop, step = sys.argv[1], sys.argv[2], *map(int, sys.argv[3:6])
    ns = list(range(start, stop + 1, step))
    rows = {}
    for n in ns:
        ta, tb = trace(a, n), trace(b, n)
        r = {}
        for cpu in CPUS:
            r[cpu] = (mca(ta, cpu, 1), mca(tb, cpu, 1), mca(ta, cpu, 100) / 100, mca(tb, cpu, 100) / 100)
        rows[n] = (len(ta), len(tb), r)
    print(f"# {a} vs {b}: instructions, then per CPU lat {a}/{b} and tput {a}/{b} (cycles)")
    print("n\tins_a\tins_b\t" + "\t".join(f"{c}" for c in CPUS))
    for n in ns:
        ia, ib, r = rows[n]
        cells = [f"{r[c][0]}/{r[c][1]} {r[c][2]:.1f}/{r[c][3]:.1f}" for c in CPUS]
        print(f"{n}\t{ia}\t{ib}\t" + "\t".join(cells))
    print(f"# smallest n from which {a} is no slower than {b} for every n up to {stop}")
    for cpu in CPUS:
        res = []
        for k, name in ((0, "lat"), (2, "tput")):
            first = None
            for n in reversed(ns):
                if rows[n][2][cpu][k] <= rows[n][2][cpu][k + 1]:
                    first = n
                else:
                    break
            res.append(f"{name} {first if first is not None else '>' + str(stop)}")
        print(f"{cpu}\t" + "\t".join(res))


if __name__ == "__main__":
    main()

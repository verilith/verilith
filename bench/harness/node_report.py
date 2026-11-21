#!/usr/bin/env python3
"""Summarizes Node's benchmark/compare.js output (compare.csv) the vbench way.

compare.js runs every benchmark configuration --runs times on each binary
("old" = official, "new" = hardened) and reports a rate (operations per
second) per run. The runs are not paired, so for each configuration:

  speedup = median rate (hardened) / median rate (official)  (> 1: hardened faster)

with a 95% bootstrap confidence interval (10,000 resamples of each side,
fixed seed). Node's own benchmark/compare.R (a Welch t-test) can be run on
the same CSV for a second opinion.

Usage: node_report.py compare.csv OUTDIR -> OUTDIR/summary.csv, summary.md
"""
import csv
import os
import random
import statistics
import sys
from collections import OrderedDict


def boot_ci(old, new, reps=10000, seed=1):
    rng = random.Random(seed)
    rs = []
    for _ in range(reps):
        o = statistics.median(rng.choices(old, k=len(old)))
        n = statistics.median(rng.choices(new, k=len(new)))
        rs.append(n / o)
    rs.sort()
    return rs[int(0.025 * reps)], rs[int(0.975 * reps) - 1]


def main():
    path, out = sys.argv[1], sys.argv[2]
    groups = OrderedDict()
    for r in csv.DictReader(open(path)):
        k = (r["filename"], r["configuration"])
        groups.setdefault(k, {"old": [], "new": []})[r["binary"].strip('"')].append(float(r["rate"]))
    rows = []
    for (fn, conf), d in groups.items():
        if not d["old"] or not d["new"]:
            continue
        mo, mn = statistics.median(d["old"]), statistics.median(d["new"])
        lo, hi = boot_ci(d["old"], d["new"])
        verdict = "faster" if lo > 1 else "slower" if hi < 1 else "no measurable difference"
        rows.append(dict(benchmark=fn, configuration=conf, runs=min(len(d["old"]), len(d["new"])),
                         official_rate=round(mo, 2), hardened_rate=round(mn, 2), speedup=round(mn / mo, 4),
                         ci95_lo=round(lo, 4), ci95_hi=round(hi, 4), verdict=verdict))
    if not rows:
        print("no results in", path)
        return
    with open(os.path.join(out, "summary.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    L = ["## Node.js: hardened build vs official build (benchmark/compare.js)\n",
         "Same Node source, compiler and flags; the hardened build has our libraries swapped in "
         "(see node/build-check.txt). Speedup is the hardened build's median rate divided by the official "
         "build's, so above 1.00x means the hardened Node is faster; 95% bootstrap CI in brackets, bold "
         "when it excludes 1.00x.\n",
         "| benchmark | configuration | speedup (95% CI) |", "| --- | --- | --- |"]
    for r in rows:
        s = f"{r['speedup']:.2f}x ({r['ci95_lo']:.2f}–{r['ci95_hi']:.2f})"
        if r["verdict"] != "no measurable difference":
            s = f"**{r['speedup']:.2f}x** ({r['ci95_lo']:.2f}–{r['ci95_hi']:.2f})"
        L.append(f"| {r['benchmark']} | {r['configuration']} | {s} |")
    open(os.path.join(out, "summary.md"), "w").write("\n".join(L) + "\n")
    print(f"wrote {out}/summary.csv and summary.md")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Interleaved benchmark runner: each implementation runs in its own process,
rounds alternate between implementations, and the median is reported."""
import subprocess, sys, statistics, re
binary, impls, cfgs, rounds = sys.argv[1], sys.argv[2].split(','), sys.argv[3].split(','), int(sys.argv[4])
res = {}
for _ in range(rounds):
    for cfg in cfgs:
        for w in impls:
            out = subprocess.run([f"target/release/{binary}", w] + cfg.split(), capture_output=True, text=True, timeout=300).stdout
            ns = float(re.search(r"([\d.]+) ns", out).group(1))
            res.setdefault((cfg, w), []).append(ns)
for cfg in cfgs:
    print(f"[{cfg}]", '  '.join(f"{w}={statistics.median(res[(cfg, w)]):.1f}" for w in impls))

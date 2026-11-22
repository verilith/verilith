#!/usr/bin/env python3
"""Runs vbench comparisons: ours against the original library, alternating.

For every comparison in suites.py it starts two long-lived runner processes
(ours and the original), lists their cases, and for each case:

  1. warms both up and picks one iteration count so that a sample takes
     about --target-ms (at least one call);
  2. takes --pairs samples of each, alternating A B, B A, A B, ... so drift
     (heat, clock changes, background work) hits both sides equally;
  3. writes every sample (time, instructions, cycles, check value) to
     raw.csv in the output directory.

report.py turns raw.csv into the summary (median ratio, 95% CI). Standard
library only.
"""
import argparse
import csv
import os
import platform
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import suites  # noqa: E402

FIELDS = ["suite", "comparison", "case", "bytes", "pair", "side", "contender", "iters", "ns", "instructions", "cycles", "check"]


class Runner:
    def __init__(self, argv, env, cpu):
        if cpu is not None and platform.system() == "Linux":
            argv = ["taskset", "-c", str(cpu)] + argv
        self.p = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, env=env, text=True, bufsize=1)
        self.argv = argv

    def ask(self, cmd):
        self.p.stdin.write(cmd + "\n")
        self.p.stdin.flush()
        line = self.p.stdout.readline()
        if not line:
            raise RuntimeError(f"runner {' '.join(self.argv)} exited (command: {cmd})")
        line = line.rstrip("\n")
        if line.startswith("error"):
            raise RuntimeError(f"runner {' '.join(self.argv)}: {line}")
        return line

    def cases(self):
        self.p.stdin.write("cases\n")
        self.p.stdin.flush()
        out = []
        while True:
            line = self.p.stdout.readline()
            if not line:
                raise RuntimeError(f"runner {' '.join(self.argv)} exited while listing cases")
            line = line.rstrip("\n")
            if line == ".":
                return out
            name, nbytes = line.rsplit("\t", 1)
            out.append((name, int(nbytes)))

    def run(self, case, iters):
        ns, ins, cyc, check = self.ask(f"run {case} {iters}").split("\t")
        return int(ns), int(ins), int(cyc), check

    def close(self):
        try:
            self.p.stdin.write("quit\n")
            self.p.stdin.flush()
            self.p.stdin.close()
        except OSError:
            pass
        try:
            self.p.wait(timeout=30)
        except subprocess.TimeoutExpired:
            self.p.kill()


def calibrate(a, b, case, target_ns):
    """Iterations per sample so the slower side takes about target_ns."""
    iters = 1
    while True:
        ta = a.run(case, iters)[0]
        tb = b.run(case, iters)[0]
        t = max(ta, tb)
        if t >= target_ns / 4 or iters >= 1 << 40:
            break
        iters *= 4 if t < target_ns / 64 else 2
    per = max(t / iters, 1e-3)
    return max(1, int(round(target_ns / per)))


def run_comparison(cmp, args, writer, log):
    bindir, datadir = args.bin, args.data
    env = dict(os.environ)
    env["VBENCH_DATA"] = os.path.join(datadir, cmp["data"])
    sides = []
    for key in ("ours", "rival"):
        name, argv = cmp[key]
        exe = os.path.join(bindir, argv[0])
        if not os.path.exists(exe):
            log(f"  skip {cmp['id']}: {exe} was not built")
            return False
        sides.append((key, name, [exe] + list(argv[1:])))
    if not os.path.isdir(env["VBENCH_DATA"]):
        log(f"  skip {cmp['id']}: no data at {env['VBENCH_DATA']}")
        return False
    a = Runner(sides[0][2], env, args.cpu)
    b = Runner(sides[1][2], env, args.cpu)
    try:
        ca, cb = a.cases(), b.cases()
        names_b = {n for n, _ in cb}
        cases = [(n, by) for n, by in ca if n in names_b]
        missing = [n for n, _ in ca if n not in names_b] + [n for n, _ in cb if n not in {x for x, _ in ca}]
        if missing:
            log(f"  note: cases on one side only, skipped: {', '.join(missing)}")
        if args.case:
            rx = re.compile(args.case)
            cases = [c for c in cases if rx.search(c[0])]
        if args.quick:
            cases = cases[:: max(1, len(cases) // 3)][:3]
        target = args.target_ms * 1e6
        for name, nbytes in cases:
            t0 = time.time()
            iters = calibrate(a, b, name, target)
            for _ in range(2):  # settle at the chosen size
                a.run(name, iters)
                b.run(name, iters)
            checks = set()
            ra, rb = [], []
            for i in range(args.pairs):
                order = ((0, a), (1, b)) if i % 2 == 0 else ((1, b), (0, a))
                for side, r in order:
                    ns, ins, cyc, check = r.run(name, iters)
                    key, cname, _ = sides[side]
                    writer.writerow({
                        "suite": cmp["suite"], "comparison": cmp["id"], "case": name, "bytes": nbytes,
                        "pair": i, "side": key, "contender": cname, "iters": iters, "ns": ns,
                        "instructions": ins, "cycles": cyc, "check": check,
                    })
                    (ra if side == 0 else rb).append(ns)
                    checks.add((key, check))
            ratio = sorted(y / x for x, y in zip(ra, rb))[len(ra) // 2]
            same = len({c for _, c in checks}) == 1
            flag = "" if same or not cmp.get("same_output", True) else "  CHECK DIFFERS"
            log(f"  {name:<40} {iters:>9} it  median {ratio:6.3f}x  ({time.time() - t0:5.1f}s){flag}")
    finally:
        a.close()
        b.close()
    return True


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bin", default=os.path.join(ROOT, "work", "build", "bin"), help="directory with the runner executables")
    ap.add_argument("--data", default=os.path.join(ROOT, "work", "data"), help="directory with the input data sets")
    ap.add_argument("--out", help="results directory (raw.csv is written here)")
    ap.add_argument("--pairs", type=int, default=31, help="A/B sample pairs per case (default 31)")
    ap.add_argument("--target-ms", type=float, default=25, help="time per sample (default 25 ms)")
    ap.add_argument("--only", help="comma-separated suites or comparison ids to run")
    ap.add_argument("--case", help="regex: run only matching cases")
    ap.add_argument("--quick", action="store_true", help="at most three cases per comparison (smoke test)")
    ap.add_argument("--cpu", type=int, help="Linux: pin both runners to this CPU")
    ap.add_argument("--list", action="store_true", help="list comparisons and exit")
    args = ap.parse_args()

    comps = suites.COMPARISONS
    if args.list:
        for c in comps:
            print(f"{c['id']:<22} {c['suite']:<6} {c['api']:<8} {c['ours'][0]} vs {c['rival'][0]}")
        return
    if not args.out:
        ap.error("--out is required")
    if args.only:
        want = set(args.only.split(","))
        comps = [c for c in comps if c["suite"] in want or c["id"] in want]
    os.makedirs(args.out, exist_ok=True)
    path = os.path.join(args.out, "raw.csv")
    new = not os.path.exists(path)
    logf = open(os.path.join(args.out, "run.log"), "a")

    def log(msg):
        print(msg, flush=True)
        logf.write(msg + "\n")
        logf.flush()

    with open(path, "a", newline="") as f:
        w = csv.DictWriter(f, fieldnames=FIELDS)
        if new:
            w.writeheader()
        for c in comps:
            log(f"{c['id']}: {c['ours'][0]} vs {c['rival'][0]}")
            try:
                run_comparison(c, args, w, log)
            except RuntimeError as e:
                log(f"  FAILED: {e}")
            f.flush()


if __name__ == "__main__":
    main()

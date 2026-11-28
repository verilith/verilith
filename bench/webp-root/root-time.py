#!/usr/bin/env python3
"""Wall-clock check of the table-root model: decode time with R table bits.
    root-time.py "10 11 12" REPS FILE...
For each R, a temporary git worktree of HEAD gets: core's MAX_ROOT = R,
WebP's codes built with R bits, and try_lit's refill thresholds 4R and 3R
(40 and 30 at R = 10: four, then three, table codes per refill). Only for
timing: the proofs are not redone for R > 10. Runs the builds in turn REPS
times and prints each one's fastest time and its pixel checksum. With
BUILD_ONLY=1 (R <= 10) only the codes' table bits change. With
KEEP_BINS=DIR the builds are also left in DIR (for cachegrind-roots.sh)."""
import os, re, subprocess, sys, tempfile, shutil
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.abspath(os.path.join(here, "..", ".."))
rs = [int(x) for x in sys.argv[1].split()]
reps = int(sys.argv[2]); files = sys.argv[3:]
tmp = tempfile.mkdtemp()
bins = {}
try:
    for r in rs:
        wt = os.path.join(tmp, f"wt{r}")
        subprocess.run(["git", "-C", root, "worktree", "add", "-q", "--detach", wt, "HEAD"], check=True)
        def sub(path, old, new, count=1):
            p = os.path.join(wt, path); s = open(p).read()
            assert s.count(old) >= 1, (path, old)
            open(p, "w").write(s.replace(old, new) if count == 0 else s.replace(old, new, count))
        if os.environ.get("BUILD_ONLY") and r <= 10:
            # Only the codes' table bits; MAX_ROOT and the refill points stay.
            sub("crates/webp/src/codes.rs", "build(&lens, MAX_ROOT)", f"build(&lens, {r})")
        else:
            sub("crates/core/src/htable.rs", "pub const MAX_ROOT: u32 = 10;", f"pub const MAX_ROOT: u32 = {r};")
            sub("crates/webp/src/pixels.rs", "if t.cnt < 40 {", f"if t.cnt < {4 * r} {{")
            sub("crates/webp/src/pixels.rs", "if t.cnt < 30 {", f"if t.cnt < {3 * r} {{", 0)
        shutil.copytree(here, os.path.join(wt, "bench", "webp-root"), dirs_exist_ok=True,
                        ignore=shutil.ignore_patterns("target"))
        tgt = os.path.join(tmp, "target")
        subprocess.run(["cargo", "build", "-q", "--release", "--bin", "webptime", "--manifest-path",
                        os.path.join(wt, "bench", "webp-root", "Cargo.toml")],
                       env=dict(os.environ, CARGO_TARGET_DIR=tgt), check=True)
        b = os.path.join(tmp, f"webptime-{r}"); shutil.copy(os.path.join(tgt, "release", "webptime"), b); bins[r] = b
        if os.environ.get("KEEP_BINS"):
            os.makedirs(os.environ["KEEP_BINS"], exist_ok=True)
            shutil.copy(b, os.environ["KEEP_BINS"])
    best = {r: float("inf") for r in rs}; sums = {}
    for _ in range(reps):
        for r in rs:
            out = subprocess.run([bins[r], "5"] + files, capture_output=True, text=True, check=True).stdout.split()
            best[r] = min(best[r], float(out[0])); sums[r] = out[1]
    base = best[rs[0]]
    for r in rs:
        print(f"R={r}\t{best[r]:.3f} ms\t{(best[r] / base - 1) * 100:+.2f}%\tpixels {sums[r]}")
finally:
    for r in rs:
        subprocess.run(["git", "-C", root, "worktree", "remove", "--force", os.path.join(tmp, f"wt{r}")],
                       capture_output=True)
    shutil.rmtree(tmp, ignore_errors=True)

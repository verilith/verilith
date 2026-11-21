#!/usr/bin/env python3
"""affected.py [BASE]: which crates a change touches, as JSON for CI.

A crate is affected when a file under its directory changed, or a crate it
depends on (directly or not) is affected. A change to the workspace itself
(the root Cargo.toml or Cargo.lock, scripts/, .github/) affects every crate.
With no BASE, or BASE=all, every crate is affected.

Prints {"verify": [...], "test": [...], "arm": [...]}: directory names under
crates/. "verify" leaves out the crates with nothing to verify. Standard
library only; needs cargo for `cargo metadata`.
"""
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# Crates whose tests also run on an Arm runner (the non-x86 code paths).
ARM = {"json"}
# Paths that affect every crate.
GLOBAL = ("Cargo.toml", "Cargo.lock", "scripts/", ".github/")


def main():
    base = sys.argv[1] if len(sys.argv) > 1 else "all"
    meta = json.loads(subprocess.check_output(
        ["cargo", "metadata", "--format-version", "1", "--no-deps"], cwd=ROOT))
    crates = {}  # directory name -> package
    by_name = {}
    for p in meta["packages"]:
        d = os.path.relpath(os.path.dirname(p["manifest_path"]), ROOT)
        parts = d.split(os.sep)
        if len(parts) == 2 and parts[0] == "crates":
            crates[parts[1]] = p
            by_name[p["name"]] = parts[1]
    deps = {c: {by_name[d["name"]] for d in p["dependencies"] if d["name"] in by_name}
            for c, p in crates.items()}

    if base == "all":
        hit = set(crates)
    else:
        files = subprocess.check_output(
            ["git", "diff", "--name-only", base, "HEAD"], cwd=ROOT, text=True).split("\n")
        hit = set()
        for f in filter(None, files):
            parts = f.split("/")
            if f.startswith(GLOBAL):
                hit = set(crates)
                break
            if parts[0] == "crates" and len(parts) > 2 and parts[1] in crates:
                hit.add(parts[1])
        # A crate that depends on an affected crate is affected.
        grew = True
        while grew:
            grew = False
            for c, ds in deps.items():
                if c not in hit and ds & hit:
                    hit.add(c)
                    grew = True

    verified = {c for c, p in crates.items()
                if ((p.get("metadata") or {}).get("verus") or {}).get("verify")}
    has_ci = {c for c in crates if os.path.exists(os.path.join(ROOT, "crates", c, "ci.sh"))}
    print(json.dumps({
        "verify": sorted(hit & verified),
        "test": sorted(hit & has_ci),
        "arm": sorted(hit & ARM),
    }))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""affected.py [BASE]: which crates a change touches, as JSON for CI.

A crate is affected when a file under its directory changed, or a crate it
depends on (directly or not) is affected. A change to the workspace itself
(the root Cargo.toml or Cargo.lock, scripts/, .github/) affects every crate,
except that the files only proofs use (PROOF_ONLY) leave the tests alone.
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
ARM = {"aes", "json", "sha2"}
# Paths that affect every crate.
GLOBAL = ("Cargo.toml", "Cargo.lock", "scripts/", ".github/")
# Of those, the ones only Verus and Buck2 read: no ci.sh runs or sources
# them, so they change no test. (A file here that a test starts to use must
# leave this list.)
PROOF_ONLY = (
    "scripts/BUCK", "scripts/buck2-version", "scripts/buckify.py", "scripts/crosscheck.sh",
    "scripts/install-buck2.sh", "scripts/install-verus.sh", "scripts/proof-plan.py",
    "scripts/prove.sh", "scripts/trust-ledger.py", "scripts/verify.sh", "scripts/verus-version",
    ".github/actions/buck2/", ".github/actions/verus/",
)


def touched(files, crates, deps, global_paths):
    """The crates `files` change, and every crate that depends on one."""
    if any(f.startswith(global_paths) for f in files):
        return set(crates)
    hit = set()
    for f in files:
        parts = f.split("/")
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
    return hit


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
        hit = tested = set(crates)
    else:
        files = subprocess.check_output(
            ["git", "diff", "--name-only", base, "HEAD"], cwd=ROOT, text=True).split("\n")
        files = list(filter(None, files))
        hit = touched(files, crates, deps, GLOBAL)
        tested = touched([f for f in files if not f.startswith(PROOF_ONLY)], crates, deps, GLOBAL)

    verified = {c for c, p in crates.items()
                if ((p.get("metadata") or {}).get("verus") or {}).get("verify")}
    has_ci = {c for c in crates if os.path.exists(os.path.join(ROOT, "crates", c, "ci.sh"))}
    print(json.dumps({
        "verify": sorted(hit & verified),
        "test": sorted(tested & has_ci),
        "arm": sorted(tested & ARM),
    }))


if __name__ == "__main__":
    main()

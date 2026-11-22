#!/usr/bin/env python3
"""proof-plan.py: which proofs CI has to check, as JSON.

Every crate with proofs is one Buck2 target (crates/<name>/BUCK), verified in
one or more parts. A part is identified by a hash of everything that can
change its result:

  * the files Buck2 says the target is built from: the crate's sources, the
    sources of the crates it depends on, verus/verus.py and
    scripts/verus-version (the Verus commit and Rust toolchain);
  * the BUCK files that define those targets (which carry the features, the
    vstd features, and the crates.io checksums) and the .bzl rules;
  * .buckconfig, the Buck2 version, and the platform.

When a part passes, CI saves an empty cache entry named after that hash.
This script lists the parts and drops the ones that already have an entry,
so a proof whose inputs have not changed is not checked again. An entry
counts only if it was saved by this branch or by the default branch: GitHub
lets a pull request read no others, and neither do we.

    proof-plan.py --platform Linux-X64 [--all] [--crates "a b"] [--summary FILE]

--all ignores the saved entries (the weekly run uses it). Prints
{"run": [...], "proved": [...]}; each item has "name" (for the job),
"target" (for buck2 build), "crate" and "key". Standard library only; needs
buck2 on PATH.
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import urllib.error
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# Bump to throw every saved entry away.
SCHEME = "v1"
# In every hash, whatever Buck2's queries say.
ALWAYS = [".buckconfig", ".buckroot", "scripts/buck2-version"]


def buck2(*args):
    out = subprocess.run(["buck2", *args], cwd=ROOT, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True)
    if out.returncode != 0:
        sys.stderr.write(out.stderr)
        sys.exit(f"proof-plan.py: buck2 {args[0]} failed")
    return out.stdout


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def bzl_files():
    out = []
    for base, dirs, files in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in (".git", "buck-out", "target", "node_modules")]
        out += [os.path.relpath(os.path.join(base, f), ROOT) for f in files if f.endswith(".bzl")]
    return out


def plan(platform):
    parts = json.loads(buck2("uquery", "kind(verus_library, //crates/...)",
                             "--output-attribute", "^parts$", "--json"))
    targets = sorted(parts)
    if not targets:
        sys.exit("proof-plan.py: Buck2 found no verus_library targets")
    inputs = json.loads(buck2("uquery", "inputs(deps(%s))", *targets, "--json"))
    buildfiles = json.loads(buck2("uquery", "buildfile(deps(%s))", *targets, "--json"))
    always = ALWAYS + bzl_files()
    file_hash = {}
    items = []
    for t in targets:
        files = set(inputs[t]) | set(buildfiles[t]) | set(always)
        h = hashlib.sha256()
        h.update(f"{SCHEME}\0{platform}\0{t}\0".encode())
        n = 0
        for f in sorted(files):
            path = os.path.join(ROOT, f)
            if not os.path.isfile(path):
                # The prelude's own BUCK files live inside the buck2 binary,
                # which scripts/buck2-version pins. Anything else must exist.
                if f.startswith("prelude/"):
                    continue
                sys.exit(f"proof-plan.py: {t} is built from {f}, which is not a file")
            if f not in file_hash:
                file_hash[f] = sha256_file(path)
            h.update(f"{f}\0{file_hash[f]}\0".encode())
            n += 1
        if not any(f.endswith(".rs") for f in files):
            sys.exit(f"proof-plan.py: {t} has no Rust sources among its inputs")
        digest = h.hexdigest()[:40]
        crate = t.rsplit(":", 1)[1]
        count = parts[t]["parts"]
        for k in range(count):
            items.append({
                "crate": crate,
                "name": crate if count == 1 else f"{crate} {k + 1}/{count}",
                "target": f"//crates/{crate}:{crate}[part{k}]",
                "key": f"proved-{SCHEME}-{platform}-{crate}-{k + 1}of{count}-{digest}",
            })
    return items


def saved_keys():
    """Keys of the entries this run may trust, or None if they cannot be listed."""
    repo, token = os.environ.get("GITHUB_REPOSITORY"), os.environ.get("GITHUB_TOKEN")
    if not repo or not token:
        return None
    refs = {os.environ.get("GITHUB_REF")}
    for b in (os.environ.get("DEFAULT_BRANCH"), os.environ.get("GITHUB_BASE_REF")):
        if b:
            refs.add("refs/heads/" + b)
    refs.discard(None)
    keys = set()
    api = os.environ.get("GITHUB_API_URL", "https://api.github.com")
    for page in range(1, 51):
        url = f"{api}/repos/{repo}/actions/caches?key=proved-{SCHEME}-&per_page=100&page={page}"
        req = urllib.request.Request(url, headers={
            "Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28"})
        try:
            with urllib.request.urlopen(req, timeout=30) as r:
                caches = json.load(r)["actions_caches"]
        except (urllib.error.URLError, KeyError, ValueError, TimeoutError) as e:
            print(f"proof-plan.py: cannot list saved entries ({e}); checking everything",
                  file=sys.stderr)
            return None
        keys.update(c["key"] for c in caches if c.get("ref") in refs)
        if len(caches) < 100:
            break
    return keys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--platform", required=True, help="RUNNER_OS-RUNNER_ARCH of the verify jobs")
    ap.add_argument("--all", action="store_true", help="ignore the saved entries")
    ap.add_argument("--crates", default="all", help="only these crates (space separated)")
    ap.add_argument("--summary", help="append a Markdown table of the plan to this file")
    a = ap.parse_args()
    items = plan(a.platform)
    if a.crates.strip() not in ("", "all"):
        want = set(a.crates.split())
        items = [i for i in items if i["crate"] in want]
    saved = None if a.all else saved_keys()
    run = [i for i in items if saved is None or i["key"] not in saved]
    proved = [i for i in items if saved is not None and i["key"] in saved]
    if a.summary:
        with open(a.summary, "a", encoding="utf-8") as f:
            f.write(f"### Proofs\n\n{len(run)} to check, {len(proved)} already passed with "
                    "these inputs.\n\n| Proof | | Inputs |\n|---|---|---|\n")
            for what, group in (("check", run), ("passed before", proved)):
                for i in group:
                    f.write(f"| {i['name']} | {what} | `{i['key'].rsplit('-', 1)[1][:12]}` |\n")
    print(json.dumps({"run": run, "proved": proved}))


if __name__ == "__main__":
    main()

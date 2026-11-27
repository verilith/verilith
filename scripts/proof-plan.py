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

    proof-plan.py --platform Linux-X64 [--cargo] [--all] [--base REV]
                  [--crates "a b"] [--summary FILE]

--cargo keys each crate for a `cargo verus` run (scripts/verify.sh, the Arm
jobs) instead of the Buck2 parts: one item per crate, hashed from the same
files as its Buck2 target plus what Cargo reads besides them (each crate's
Cargo.toml and build.rs in the crate's dependency closure, the crate's
scripts/verify.sh, scripts/verify.sh, the Verus installer, the root
Cargo.toml apart from its member list, and the Cargo.lock entries the crate
can reach).

--base REV drops every item whose key is the same at REV: a pull request
(REV = the base branch it merges into) checks only the proofs it changes.
The base branch's own runs check the rest; this gate, unlike the others,
is about the change, not the branch.

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
import tempfile
import tomllib
import urllib.error
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# Bump to throw every saved entry away.
SCHEME = "v1"
# In every hash, whatever Buck2's queries say.
ALWAYS = [".buckconfig", ".buckroot", "scripts/buck2-version"]
# Also in every --cargo hash: how a crate is verified through Cargo.
CARGO_ALWAYS = ["scripts/verify.sh", "scripts/install-verus.sh", "scripts/verus-version",
                ".github/actions/verus/action.yml"]


def buck2(root, *args):
    out = subprocess.run(["buck2", *args], cwd=root, stdout=subprocess.PIPE,
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


def bzl_files(root):
    out = []
    for base, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in (".git", "buck-out", "target", "node_modules")]
        out += [os.path.relpath(os.path.join(base, f), root) for f in files if f.endswith(".bzl")]
    return out


class Cargo:
    """What Cargo reads for a crate besides its Buck2 inputs."""

    def __init__(self, root):
        with open(os.path.join(root, "Cargo.toml"), "rb") as f:
            ws = tomllib.load(f)
        self.dirs = {}  # package name -> directory, relative to root
        for d in ws["workspace"]["members"]:
            with open(os.path.join(root, d, "Cargo.toml"), "rb") as f:
                self.dirs[tomllib.load(f)["package"]["name"]] = d
        # Crates kept out of the workspace (crates/tls-aws-lc) can still be
        # path dependencies of a member, and so appear in Cargo.lock.
        for d in sorted(os.listdir(os.path.join(root, "crates"))):
            m = os.path.join(root, "crates", d, "Cargo.toml")
            if os.path.isfile(m):
                with open(m, "rb") as f:
                    pkg = tomllib.load(f).get("package")
                if pkg:
                    self.dirs.setdefault(pkg["name"], f"crates/{d}")
        # The root manifest without the list of crates in the workspace
        # (adding a crate changes no other crate's build).
        ws["workspace"].pop("members", None)
        ws["workspace"].pop("exclude", None)
        self.manifest = json.dumps(ws, sort_keys=True)
        with open(os.path.join(root, "Cargo.lock"), "rb") as f:
            self.lock = tomllib.load(f)["package"]
        self.by_name = {}
        for p in self.lock:
            self.by_name.setdefault(p["name"], []).append(p)

    def _find(self, dep):
        # A lock entry names a dependency as "name", "name version" or
        # "name version (source)".
        parts = dep.split(" ")
        cands = self.by_name.get(parts[0], [])
        if len(parts) > 1:
            cands = [p for p in cands if p["version"] == parts[1]]
        if len(cands) != 1:
            sys.exit(f"proof-plan.py: cannot resolve {dep!r} in Cargo.lock")
        return cands[0]

    def reach(self, package):
        """Every Cargo.lock entry `package` can reach (dev and build
        dependencies included), itself first."""
        seen, todo = [], [self._find(package)]
        while todo:
            p = todo.pop()
            if any(p is q for q in seen):
                continue
            seen.append(p)
            todo += [self._find(d) for d in p.get("dependencies", [])]
        return seen

    def material(self, root, crate_dir):
        """(files, extra text) for crate_dir's `cargo verus` key."""
        with open(os.path.join(root, crate_dir, "Cargo.toml"), "rb") as f:
            name = tomllib.load(f)["package"]["name"]
        files = set(CARGO_ALWAYS) | {f"{crate_dir}/scripts/verify.sh", "Cargo.lock"}
        lock = []
        for p in self.reach(name):
            if p.get("source") is None:
                d = self.dirs[p["name"]]
                files.add(f"{d}/Cargo.toml")
                if os.path.isfile(os.path.join(root, d, "build.rs")):
                    files.add(f"{d}/build.rs")
            lock.append(json.dumps(p, sort_keys=True))
        files.discard("Cargo.lock")  # only the entries it can reach count
        return files, self.manifest + "\0" + "\0".join(sorted(lock))


def plan(platform, root=ROOT, cargo=False):
    parts = json.loads(buck2(root, "uquery", "kind(verus_library, //crates/...)",
                             "--output-attribute", "^parts$", "--json"))
    targets = sorted(parts)
    if not targets:
        sys.exit("proof-plan.py: Buck2 found no verus_library targets")
    inputs = json.loads(buck2(root, "uquery", "inputs(deps(%s))", *targets, "--json"))
    buildfiles = json.loads(buck2(root, "uquery", "buildfile(deps(%s))", *targets, "--json"))
    always = ALWAYS + bzl_files(root)
    cargo_info = Cargo(root) if cargo else None
    file_hash = {}
    items = []
    for t in targets:
        files = set(inputs[t]) | set(buildfiles[t]) | set(always)
        crate = t.rsplit(":", 1)[1]
        extra = ""
        if cargo_info:
            more, extra = cargo_info.material(root, f"crates/{crate}")
            files |= more
        h = hashlib.sha256()
        h.update(f"{SCHEME}\0{platform}\0{t}\0".encode())
        if cargo:
            h.update(f"cargo\0{extra}\0".encode())
        for f in sorted(files):
            path = os.path.join(root, f)
            if not os.path.isfile(path):
                # The prelude's own BUCK files live inside the buck2 binary,
                # which scripts/buck2-version pins. Anything else must exist.
                if f.startswith("prelude/"):
                    continue
                sys.exit(f"proof-plan.py: {t} is built from {f}, which is not a file")
            if f not in file_hash:
                file_hash[f] = sha256_file(path)
            h.update(f"{f}\0{file_hash[f]}\0".encode())
        if not any(f.endswith(".rs") for f in files):
            sys.exit(f"proof-plan.py: {t} has no Rust sources among its inputs")
        digest = h.hexdigest()[:40]
        if cargo:
            # One `cargo verus` run per crate, whatever its Buck2 parts.
            items.append({
                "crate": crate,
                "name": crate,
                "target": crate,
                "key": f"proved-{SCHEME}-{platform}-cargo-{crate}-{digest}",
            })
            continue
        count = parts[t]["parts"]
        for k in range(count):
            items.append({
                "crate": crate,
                "name": crate if count == 1 else f"{crate} {k + 1}/{count}",
                "target": f"//crates/{crate}:{crate}[part{k}]",
                "key": f"proved-{SCHEME}-{platform}-{crate}-{k + 1}of{count}-{digest}",
            })
    return items


def base_keys(platform, rev, cargo):
    """The keys the same plan gives at REV (hashed by this script, so the
    two are comparable), or None if that tree cannot be planned; then
    nothing is dropped."""
    tmp = tempfile.mkdtemp(prefix="proof-plan-base-")
    tree = os.path.join(tmp, "tree")
    try:
        subprocess.run(["git", "worktree", "add", "--detach", "-q", tree, rev], cwd=ROOT,
                       check=True, stdout=subprocess.DEVNULL)
        return {i["key"] for i in plan(platform, root=tree, cargo=cargo)}
    except (subprocess.CalledProcessError, SystemExit, OSError, KeyError, ValueError) as e:
        print(f"proof-plan.py: cannot plan {rev} ({e}); checking every proof", file=sys.stderr)
        return None
    finally:
        if os.path.isdir(tree):
            subprocess.run(["buck2", "kill"], cwd=tree, stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL)
        subprocess.run(["git", "worktree", "remove", "--force", tree], cwd=ROOT,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


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
    ap.add_argument("--cargo", action="store_true", help="key `cargo verus` runs, one per crate")
    ap.add_argument("--all", action="store_true", help="ignore the saved entries")
    ap.add_argument("--base", help="drop the items whose key is the same at this revision")
    ap.add_argument("--crates", default="all", help="only these crates (space separated)")
    ap.add_argument("--summary", help="append a Markdown table of the plan to this file")
    a = ap.parse_args()
    items = plan(a.platform, cargo=a.cargo)
    unchanged = []
    if a.base:
        keys = base_keys(a.platform, a.base, a.cargo)
        if keys is not None:
            unchanged = [i for i in items if i["key"] in keys]
            items = [i for i in items if i["key"] not in keys]
    if a.crates.strip() not in ("", "all"):
        want = set(a.crates.split())
        items = [i for i in items if i["crate"] in want]
    saved = None if a.all else saved_keys()
    run = [i for i in items if saved is None or i["key"] not in saved]
    proved = [i for i in items if saved is not None and i["key"] in saved]
    if a.summary:
        with open(a.summary, "a", encoding="utf-8") as f:
            title = "Proofs, through Cargo" if a.cargo else "Proofs"
            f.write(f"### {title} ({a.platform})\n\n{len(run)} to check, {len(proved)} already "
                    "passed with these inputs")
            if a.base:
                f.write(f", {len(unchanged)} the same as on the base branch (its own runs "
                        "check those)")
            f.write(".\n\n| Proof | | Inputs |\n|---|---|---|\n")
            for what, group in (("check", run), ("passed before", proved),
                                ("same as base", unchanged)):
                for i in group:
                    f.write(f"| {i['name']} | {what} | `{i['key'].rsplit('-', 1)[1][:12]}` |\n")
    print(json.dumps({"run": run, "proved": proved}))


if __name__ == "__main__":
    main()

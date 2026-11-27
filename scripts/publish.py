#!/usr/bin/env python3
"""Publish every verilith crate to crates.io, in dependency order.

    scripts/publish.py            dry run: package and build every crate
    scripts/publish.py --publish  publish for real (needs a crates.io token:
                                  `cargo login`, or CARGO_REGISTRY_TOKEN)

A publish is permanent: a version can be yanked, never deleted or replaced.
See RELEASING.md.

The crates published are the workspace members without `publish = false`,
plus crates/tls-aws-lc, which is outside the workspace (aws-lc is C, and
the workspace builds only Rust). The order is a topological sort of their
dependencies on each other. A crate whose version is already on crates.io
is skipped, so after a failure (or crates.io's rate limit) the script can
be run again and carries on where it stopped.

crates.io lets a new account publish about 5 new crates at once and then
one new crate every 10 minutes. On a 429 the script waits and tries again;
for a first publish of all the crates, that is several hours. Asking
help@crates.io to raise the limit for the first release avoids the wait.
"""

import argparse
import json
import os
import subprocess
import sys
import time
import urllib.error
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# Outside the workspace (see its Cargo.toml), published all the same.
EXTRA = ["crates/tls-aws-lc/Cargo.toml"]
RATE_LIMIT_WAIT = 10 * 60 + 15
RATE_LIMIT_TRIES = 60


def metadata(manifest=None):
    cmd = ["cargo", "metadata", "--no-deps", "--format-version", "1"]
    if manifest:
        cmd += ["--manifest-path", os.path.join(ROOT, manifest)]
    out = subprocess.run(cmd, cwd=ROOT, check=True, capture_output=True, text=True)
    return json.loads(out.stdout)["packages"]


def crates():
    """name -> (version, manifest path, workspace member?, local deps)."""
    pkgs = [(p, True) for p in metadata()]
    pkgs += [(p, False) for m in EXTRA for p in metadata(m)]
    pkgs = [(p, ws) for p, ws in pkgs if p["publish"] != []]
    names = {p["name"] for p, _ in pkgs}
    out = {}
    for p, ws in pkgs:
        deps = set()
        for d in p["dependencies"]:
            if d["name"] not in names:
                continue
            if d["kind"] == "dev" and d.get("req") in (None, "*"):
                continue  # path-only dev-dependency: cargo publish drops it
            deps.add(d["name"])
        out[p["name"]] = (p["version"], p["manifest_path"], ws, deps)
    return out


def order(cs):
    done, seq = set(), []
    while len(seq) < len(cs):
        ready = sorted(n for n, c in cs.items() if n not in done and c[3] <= done)
        if not ready:
            sys.exit("dependency cycle among: " + ", ".join(sorted(set(cs) - done)))
        seq += ready
        done |= set(ready)
    return seq


def on_crates_io(name, version):
    n = name.lower()
    path = {1: f"1/{n}", 2: f"2/{n}", 3: f"3/{n[0]}/{n}"}.get(len(n), f"{n[:2]}/{n[2:4]}/{n}")
    req = urllib.request.Request(
        f"https://index.crates.io/{path}", headers={"User-Agent": "verilith-publish-script"}
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            lines = r.read().decode().splitlines()
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return False
        raise
    return any(json.loads(l)["vers"] == version for l in lines if l.strip())


def run(cmd):
    print("+", " ".join(cmd), flush=True)
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    sys.stdout.write(p.stdout)
    sys.stderr.write(p.stderr)
    return p


def publish(cs, seq):
    for name in seq:
        version, manifest, ws, _ = cs[name]
        if on_crates_io(name, version):
            print(f"= {name} {version} is already on crates.io", flush=True)
            continue
        # tls-aws-lc has no lockfile of its own (it is not in Cargo.lock).
        cmd = ["cargo", "publish"]
        cmd += ["--locked", "-p", name] if ws else ["--manifest-path", manifest]
        for attempt in range(RATE_LIMIT_TRIES):
            p = run(cmd)
            if p.returncode == 0:
                break
            text = p.stdout + p.stderr
            if "429" in text or "Too Many Requests" in text:
                print(f"rate limited; waiting {RATE_LIMIT_WAIT}s", flush=True)
                time.sleep(RATE_LIMIT_WAIT)
                continue
            if "already exists" in text:
                break
            sys.exit(f"publishing {name} failed")
        else:
            sys.exit(f"publishing {name}: still rate limited, run again later")


def dry_run(cs, seq):
    ws = [n for n in seq if cs[n][2]]
    # Members that depend on a crate outside the workspace cannot be built
    # against the temporary registry cargo makes for a workspace dry run.
    after = {n for n in seq if not cs[n][2]}
    changed = True
    while changed:
        changed = False
        for n in ws:
            if n not in after and cs[n][3] & after:
                after.add(n)
                changed = True
    first = [n for n in ws if n not in after]
    cmd = ["cargo", "publish", "--dry-run", "--locked", "--workspace"]
    cmd += [a for n in ws if n in after for a in ("--exclude", n)]
    if run(cmd).returncode != 0:
        sys.exit("dry run failed")
    for n in [n for n in seq if n in after]:
        # These need crates published in this same release to resolve, so
        # only their contents are checked here; their build is checked by
        # the normal test runs, and for real when they are published.
        version, manifest, member, _ = cs[n]
        cmd = ["cargo", "package", "--list"]
        cmd += ["-p", n] if member else ["--manifest-path", manifest]
        if run(cmd).returncode != 0:
            sys.exit(f"packaging {n} failed")
    print(f"\ndry run passed: {len(first)} crates built from their packages, "
          f"{len(after)} packaged only ({', '.join(sorted(after))})")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--publish", action="store_true", help="publish for real")
    ap.add_argument("--list", action="store_true", help="print the order and stop")
    a = ap.parse_args()
    cs = crates()
    seq = order(cs)
    print("publish order:", flush=True)
    for i, n in enumerate(seq, 1):
        print(f"  {i:2} {n} {cs[n][0]}")
    if a.list:
        return
    if a.publish:
        publish(cs, seq)
    else:
        dry_run(cs, seq)


if __name__ == "__main__":
    main()

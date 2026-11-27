#!/usr/bin/env python3
"""Checks the npm packages under node/ before they are published: every
version matches Cargo.toml's, there is one platform package per napi target,
each holds its binary, README and licence files and has the
metadata npm shows (a bare package is what npm's spam filter flags), and
verilith lists each as an optional
dependency. Run in node/ after `napi artifacts` (.github/workflows/publish-npm.yml).
To move to a new version: `npx napi version` after setting it in package.json,
then the optionalDependencies by hand."""
import json
import os
import re
import sys

cargo = open("Cargo.toml").read()
version = re.search(r'^version = "([^"]+)"', cargo, re.M).group(1)
root = json.load(open("package.json"))
bad = []
if root["version"] != version:
    bad.append(f"package.json is {root['version']}, Cargo.toml is {version}")
dirs = sorted(os.listdir("npm"))
if len(dirs) != len(root["napi"]["targets"]):
    bad.append(f"{len(dirs)} platform packages for {len(root['napi']['targets'])} targets")
names = set()
for d in dirs:
    p = json.load(open(f"npm/{d}/package.json"))
    names.add(p["name"])
    if p["version"] != version:
        bad.append(f"{p['name']} is {p['version']}, Cargo.toml is {version}")
    if root.get("optionalDependencies", {}).get(p["name"]) != version:
        bad.append(f"package.json's optionalDependencies lack {p['name']} {version}")
    if not os.path.isfile(f"npm/{d}/{p['main']}"):
        bad.append(f"no binary for {p['name']} (npm/{d}/{p['main']})")
    for key in ("description", "keywords", "author", "license", "homepage", "repository"):
        if not p.get(key):
            bad.append(f"{p['name']}'s package.json has no {key}")
    for f in ("README.md", "LICENSE-MIT", "LICENSE-APACHE"):
        if not os.path.isfile(f"npm/{d}/{f}") or f not in p.get("files", []):
            bad.append(f"{p['name']} lacks {f}, or its package.json's files does")
    if "npmjs.com/package/verilith)" not in open(f"npm/{d}/README.md").read():
        bad.append(f"npm/{d}/README.md does not point to the verilith package")
for extra in set(root.get("optionalDependencies", {})) - names:
    bad.append(f"package.json's optionalDependencies name {extra}, which has no package")
if bad:
    sys.exit("\n".join(bad))
print(f"verilith {version}, platform packages: {' '.join(dirs)}")

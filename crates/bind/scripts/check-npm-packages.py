#!/usr/bin/env python3
"""Checks the npm packages under node/ before they are published: every
version matches Cargo.toml's, there is one platform package per napi target,
each holds its binary, and verilith-bind lists each as an optional
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
for extra in set(root.get("optionalDependencies", {})) - names:
    bad.append(f"package.json's optionalDependencies name {extra}, which has no package")
if bad:
    sys.exit("\n".join(bad))
print(f"verilith-bind {version}, platform packages: {' '.join(dirs)}")

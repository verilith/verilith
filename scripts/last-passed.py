#!/usr/bin/env python3
"""last-passed.py WORKFLOW BRANCH: the newest commit on BRANCH whose push run
of WORKFLOW (a file under .github/workflows/) passed, for CI.

CI tests what changed since that commit. Runs on a branch queue, and GitHub
cancels a queued run when the next one arrives, so the commit a push was made
on top of may never have been tested; nor was one whose run failed. Fails
(and CI then tests everything) when the runs cannot be listed or the commit
is not an ancestor of HEAD. Standard library only; needs GITHUB_TOKEN and
GITHUB_REPOSITORY.
"""
import json
import os
import subprocess
import sys
import urllib.parse
import urllib.request


def main():
    workflow, branch = sys.argv[1], sys.argv[2]
    repo, token = os.environ["GITHUB_REPOSITORY"], os.environ["GITHUB_TOKEN"]
    api = os.environ.get("GITHUB_API_URL", "https://api.github.com")
    query = urllib.parse.urlencode(
        {"branch": branch, "event": "push", "status": "success", "per_page": 20})
    req = urllib.request.Request(
        f"{api}/repos/{repo}/actions/workflows/{workflow}/runs?{query}",
        headers={"Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json",
                 "X-GitHub-Api-Version": "2022-11-28"})
    with urllib.request.urlopen(req, timeout=30) as r:
        runs = json.load(r)["workflow_runs"]
    for run in runs:  # newest first
        sha = run["head_sha"]
        ancestor = subprocess.run(["git", "merge-base", "--is-ancestor", sha, "HEAD"],
                                  stderr=subprocess.DEVNULL).returncode == 0
        if ancestor:
            print(sha)
            return
    sys.exit(f"last-passed.py: no passed {workflow} run on {branch} is an ancestor of HEAD")


if __name__ == "__main__":
    main()

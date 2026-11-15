#!/usr/bin/env python3
"""Invariant: every pin of a dependency names one revision, and that revision
is on the dependency's trunk.

`lake-manifest.json` is the source of truth. Two things can disagree with it,
and each is a hard failure (exit 1):

1. `docbuild/lake-manifest.json` must pin every package it shares with the
   root manifest at the same revision. It shares the root's `packagesDir`, so
   a stale entry there compiles the docs against a library that never built.
2. A package pinned to a bare 40-hex commit must have that commit reachable
   from its repository's default branch. A pull-request tip has no owner: once
   that branch is rebased or deleted the pin stops resolving, and nothing fails
   until the next clean clone. A tag or branch name in `inputRev` is a
   maintained target and is not asked about.

Check 2 needs `gh` and the network. Without them it prints NOT_RUN instead of
passing, and `--require-api` (which CI passes) turns NOT_RUN into a failure.

Usage:  python3 scripts/check_pin.py [--require-api] [repo_root]
"""

from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys

from _output import force_utf8_output

SHA40 = re.compile(r"\A[0-9a-f]{40}\Z")


def manifest_revs(path: pathlib.Path) -> dict[str, dict]:
    return {p["name"]: p for p in json.loads(path.read_text())["packages"]}


def docbuild_findings(root: pathlib.Path, packages: dict[str, dict]) -> list[str]:
    doc_manifest = root / "docbuild" / "lake-manifest.json"
    if not doc_manifest.exists():
        return []
    out = []
    for name, doc in sorted(manifest_revs(doc_manifest).items()):
        rev, doc_rev = (packages.get(name) or {}).get("rev"), doc.get("rev")
        if rev is not None and doc_rev is not None and rev != doc_rev:
            out.append(f"docbuild/lake-manifest.json pins {name} at {doc_rev!r} but "
                       f"lake-manifest.json pins {rev!r}")
    return out


def repo_slug(url: str | None) -> str | None:
    """`owner/name` from a GitHub remote, or None if it is not one."""
    for prefix in ("https://github.com/", "git@github.com:", "ssh://git@github.com/"):
        if url and url.strip().startswith(prefix):
            slug = url.strip()[len(prefix):].removesuffix(".git").strip("/")
            return slug or None
    return None


def gh_json(*args: str):
    """`gh` stdout parsed as JSON, or (None, why-not)."""
    try:
        proc = subprocess.run(("gh", *args), capture_output=True, text=True,
                              timeout=60, encoding="utf-8")
    except (OSError, subprocess.SubprocessError) as exc:
        return None, f"could not run gh: {exc}"
    if proc.returncode != 0:
        return None, f"gh exited {proc.returncode}: {proc.stderr.strip()[:200]}"
    try:
        return json.loads(proc.stdout), None
    except json.JSONDecodeError as exc:
        return None, f"gh returned unparseable JSON: {exc}"


def reachable_from_default(slug: str, rev: str):
    """(True/False/None, detail). None means the question could not be asked."""
    meta, why = gh_json("api", f"repos/{slug}", "--jq", "{d: .default_branch}")
    if meta is None:
        return None, why
    default = meta.get("d")
    if not default:
        return None, f"{slug} reports no default branch"
    # base...head with base=rev: the trunk is ahead of an ancestor and
    # identical to its own tip. Behind or diverged means rev is not on it.
    cmp_, why = gh_json("api", f"repos/{slug}/compare/{rev}...{default}",
                        "--jq", "{s: .status, a: .ahead_by, b: .behind_by}")
    if cmp_ is None:
        return None, why
    status = cmp_.get("s")
    if status in {"ahead", "identical"}:
        return True, f"{default} is {status}"
    return False, (f"compare {rev[:12]}...{default} is {status!r} "
                   f"(ahead {cmp_.get('a')}, behind {cmp_.get('b')})")


def trunk_findings(packages: dict[str, dict], require_api: bool) -> list[str]:
    out = []
    for name, pkg in sorted(packages.items()):
        rev = str(pkg.get("inputRev") or "")
        if not (SHA40.match(rev) and rev == pkg.get("rev")):
            continue
        slug = repo_slug(pkg.get("url"))
        ok, detail = (None, f"url {pkg.get('url')!r} is not a GitHub remote") \
            if slug is None else reachable_from_default(slug, rev)
        if ok is None:
            print(f"NOT_RUN  {name} reachability: {detail}")
            if require_api:
                out.append(f"{name}: --require-api was passed and reachability "
                           f"could not be checked ({detail})")
        elif ok:
            print(f"OK    {name} {rev[:12]} is on {slug}'s default branch ({detail})")
        else:
            out.append(f"{name} is pinned to {rev[:12]}, which is not reachable from "
                       f"{slug}'s default branch: {detail}. Merge it, or pin a commit "
                       "that is on the trunk.")
    return out


def main(argv: list[str]) -> int:
    require_api = "--require-api" in argv
    paths = [a for a in argv if not a.startswith("--")]
    root = pathlib.Path(paths[0]).resolve() if paths else pathlib.Path(__file__).resolve().parent.parent
    packages = manifest_revs(root / "lake-manifest.json")
    failures = docbuild_findings(root, packages) + trunk_findings(packages, require_api)
    if failures:
        print(f"FAIL  pin coherence ({len(failures)} problem(s)):")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(f"OK    {len(packages)} pinned packages agree across lake-manifest.json "
          "and docbuild")
    return 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main(sys.argv[1:]))

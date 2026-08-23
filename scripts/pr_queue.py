#!/usr/bin/env python3
"""Rank the open PR queue for an unattended landing loop.

The queue is not review-bound, it is CI-bound: every branch is based directly on
`main` and the 90-minute build job serialises. So the useful ordering is not
"oldest first" but "what can a local run actually finish right now" — a PR whose
CI is still pending can be gated locally in minutes instead of waiting on
GitHub, and a PR that overlaps an already-landed one needs a rebase first.

Prints one line per PR, most actionable first:

    <n>  <state>  <files-overlapping-others>  <title>

where state is one of:

    READY      CI green, not draft. Review it and hand it to a human to merge.
    GATE       CI pending or absent. Run the local gates; that is the fast path.
    FIX        CI red. The failure is the work.
    CONFLICT   Behind main in a file another open PR also touches. Rebase first.
    SKIP       Draft with no commits, or explicitly parked.
    DONE       A landing iteration already gated and reviewed this exact head.
               Waiting on a human to merge; sorts last so the loop moves on.

A PR that touches the loop's own machinery -- the gate scripts, the edit hook,
the skills, this file -- is flagged BOOTSTRAP and sorts ahead of every state.
It is not a bigger version of READY: it is the PR that decides whether anything
after it is gated correctly at all.

Exit codes: 0 when work is queued, 2 when no iteration can make progress. The
two reasons for 2 are printed and are not interchangeable -- `BLOCKED ON YOU`
(everything is gated, reviewed, and waiting on a merge) versus `QUEUE DRAINED`
(there is genuinely nothing open). A loop that reports "nothing to do" for the
first of those has failed silently.

Usage:  python3 scripts/pr_queue.py [--json]
"""

from __future__ import annotations

import json
import subprocess
import sys
from collections import Counter

REPO = "chris-dare-dev/derived-alg-geo-lean"
FIELDS = (
    "number,title,headRefName,isDraft,mergeable,additions,files,statusCheckRollup,"
    "createdAt,headRefOid,comments"
)

# The landing loop halts before the merge, by design. Without a marker it would
# therefore re-pick the same head PR on every wakeup and re-run a full build to
# reach the same verdict. A loop verdict comment quotes the head commit it was
# written against, so a PR counts as DONE only until someone pushes to it --
# a new commit invalidates the marker and the PR returns to the queue.
DONE_MARKER = "Run by the `land-pr` loop"


def already_landed(pr: dict) -> bool:
    head = (pr.get("headRefOid") or "")[:7]
    if not head:
        return False
    return any(
        DONE_MARKER in (c.get("body") or "") and head in (c.get("body") or "")
        for c in (pr.get("comments") or [])
    )

# A PR that changes the machinery the landing loop itself runs on sorts ahead of
# everything, whatever its size. Until it is on `main`, every later iteration is
# gated by the wrong version of these files -- or, for a branch cut before they
# existed, by nothing at all. Size-first ordering is the right rule for the
# stack and the wrong rule here, so bootstrap is a separate axis, not a state.
BOOTSTRAP_PATHS = {
    "scripts/gates.sh",
    "scripts/check_mathlib_style.py",
    "scripts/pr_queue.py",
    ".claude/settings.json",
}
BOOTSTRAP_PREFIXES = (".claude/skills/", ".claude/agents/")


def is_bootstrap(paths: list[str]) -> bool:
    return any(p in BOOTSTRAP_PATHS or p.startswith(BOOTSTRAP_PREFIXES) for p in paths)


def gh_json(args: list[str]) -> object:
    return json.loads(subprocess.check_output(["gh", *args], text=True, encoding="utf-8"))


def rollup(pr: dict) -> str:
    """Collapse the check rollup to green / red / pending / none."""
    checks = pr.get("statusCheckRollup") or []
    if not checks:
        return "none"
    concls = [(c.get("conclusion") or "").upper() for c in checks]
    if any(c in {"FAILURE", "TIMED_OUT", "CANCELLED", "ACTION_REQUIRED"} for c in concls):
        return "red"
    if any(c == "" for c in concls):
        return "pending"
    if all(c in {"SUCCESS", "SKIPPED", "NEUTRAL"} for c in concls):
        return "green"
    return "pending"


def classify(pr: dict, contested: set[str]) -> tuple[str, list[str]]:
    overlap = sorted({f for f in pr["_paths"] if f in contested})
    if already_landed(pr):
        return "DONE", overlap
    if pr.get("mergeable") == "CONFLICTING":
        return "CONFLICT", overlap
    if pr["additions"] == 0:
        return "SKIP", overlap
    state = {"red": "FIX", "green": "READY", "pending": "GATE", "none": "GATE"}[rollup(pr)]
    if state == "READY" and pr["isDraft"]:
        # Green but still a draft: the local gates are the cheap way to decide
        # whether it is actually finished, so treat it as gate work.
        state = "GATE"
    return state, overlap


ORDER = {"READY": 0, "GATE": 1, "FIX": 2, "CONFLICT": 3, "SKIP": 4, "DONE": 5}


def main(argv: list[str]) -> int:
    prs = gh_json(["pr", "list", "-R", REPO, "--state", "open", "--limit", "200", "--json", FIELDS])
    for pr in prs:
        pr["_paths"] = [f["path"] for f in (pr.get("files") or [])]

    # A file two open PRs both touch is where the landing order starts to matter.
    counts = Counter(p for pr in prs for p in pr["_paths"])
    contested = {p for p, n in counts.items() if n > 1}

    rows = []
    for pr in prs:
        state, overlap = classify(pr, contested)
        rows.append(
            {
                "number": pr["number"],
                "state": state,
                "title": pr["title"],
                "branch": pr["headRefName"],
                "additions": pr["additions"],
                "draft": pr["isDraft"],
                "checks": rollup(pr),
                "contested_files": overlap,
                "bootstrap": is_bootstrap(pr["_paths"]),
                "_paths": pr["_paths"],
            }
        )
    # Landing order is smallest-diff-first, and that is not a heuristic. This
    # queue is a cumulative stack: every branch is based on `main`, but each
    # slice contains all of its predecessors, so PR sizes run 65, 134, 168, ...
    # 2925 additions along one chain. Land the base and the next PR's diff
    # collapses to its own slice; land the tip and you have merged 26 issues in
    # one unreviewable commit.
    paths = {r["number"]: set(r.pop("_paths")) for r in rows}
    for r in rows:
        mine = paths[r["number"]]
        r["stacked_under"] = sorted(
            n for n, other in paths.items() if n != r["number"] and mine < other
        )
    rows.sort(key=lambda r: (not r["bootstrap"], ORDER[r["state"]], r["additions"], r["number"]))

    if "--json" in argv:
        json.dump(rows, sys.stdout, indent=2)
        print()
        return 0

    by_state = Counter(r["state"] for r in rows)
    print(f"{len(rows)} open PRs: " + ", ".join(f"{k}={v}" for k, v in sorted(by_state.items())))
    print()
    for r in rows:
        n = len(r["stacked_under"])
        if r["bootstrap"]:
            flag = "  [BOOTSTRAP -- gates every later iteration]"
        elif n:
            flag = f"  [base of a {n}-deep stack]"
        else:
            flag = ""
        print(f"{r['number']:>5}  {r['state']:<8} +{r['additions']:<5} {r['title'][:56]}{flag}")
    if any(r["bootstrap"] for r in rows):
        print("\nBootstrap PRs first: until they land, later iterations run on stale gates.")

    waiting = [r for r in rows if r["state"] == "DONE"]
    actionable = [r for r in rows if r["state"] not in ("DONE", "SKIP")]

    if actionable:
        print("\nLand top-down. Each merge shrinks the diff of everything below it.")
        if waiting:
            print(f"Separately, {len(waiting)} PR(s) are gated and reviewed, waiting on a merge: "
                  + ", ".join(f"#{r['number']}" for r in waiting))
        return 0

    # Nothing left to work on. Say which of the two very different reasons it is,
    # because a loop that reports "nothing to do" when the real answer is "27 PRs
    # need you" has failed silently -- it looks identical to a drained queue.
    print()
    if waiting:
        print(f"BLOCKED ON YOU: {len(waiting)} PR(s) are gated, reviewed, and waiting on a merge.")
        for r in waiting:
            print(f"  #{r['number']}  +{r['additions']:<5} {r['title'][:56]}")
        print("\nNo iteration can make progress until some of these merge: the loop does not "
              "merge, and re-reviewing an unchanged head would only repeat a posted verdict.")
    else:
        print("QUEUE DRAINED: no open PR needs a landing iteration.")

    # Exit 2 distinguishes "stop the loop, and here is why" from a clean run
    # with work still queued (0) and from a tool failure (1).
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

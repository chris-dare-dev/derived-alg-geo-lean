#!/usr/bin/env python3
"""Keep `scripts/nolints.json` a ratchet rather than a dumping ground.

`lake exe runLinter DerivedAlgGeo` already rejects any violation that is not listed
in `scripts/nolints.json`, so new code cannot add one. What it cannot detect is
someone silencing a failure with `runLinter --update`, which rewrites the whole
file from the current run and blesses the new violation along with every
existing one. That turns the gate off without touching CI or any Lean file.

This script closes that hole from the other side: the list may shrink, never
grow. The dg-category and stability-condition subsystems entered the unified
library without exceptions and must remain clean.

Usage:
    python3 scripts/check_nolints.py
    python3 scripts/check_nolints.py --relax   # after deliberately shrinking it
"""

from __future__ import annotations

import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

NOLINTS = Path("scripts/nolints.json")
BASELINE_REF = "origin/main"

# The backlog as measured when the algebraic-geometry gate was first wired, 2026-08-14.
# Lower it whenever the real count drops -- `--relax` does that for you. It is
# never raised: a change that needs a new exception needs a human argument for
# that exception, in review, not a bumped constant.
CEILING = 199

# Per-linter ceilings, for the same reason and with more resolution: they catch
# an `--update` run from a library that lints clean today, which would add its
# output here and quietly disable its own gate. Declaration names cannot be used
# for that check -- plenty of genuine project declarations live in Mathlib-rooted
# namespaces like `ModuleCat.` -- but any such update grows a count.
PER_LINTER_CEILING = {
    "docBlame": 144,
    "unusedArguments": 27,
    "defsWithUnderscore": 16,
    "simpNF": 12,
}


def main(argv: list[str]) -> int:
    if not NOLINTS.exists():
        print(f"::error::{NOLINTS} is missing; the DerivedAlgGeo linter gate depends on it")
        return 1

    entries = json.loads(NOLINTS.read_text(encoding="utf-8"))
    by_linter = Counter(linter for linter, _ in entries)
    total = len(entries)

    if "--relax" in argv:
        print(f"set CEILING = {total} and PER_LINTER_CEILING = {dict(sorted(by_linter.items()))}")
        return 0

    print(f"nolints: {total} entries (ceiling {CEILING}) — " +
          ", ".join(f"{k}={v}" for k, v in sorted(by_linter.items())))

    if total > CEILING:
        print(
            f"::error::nolints grew from {CEILING} to {total}. Fix the declaration "
            "instead, or argue for the exception in review — do not resolve a linter "
            "failure with `runLinter --update`."
        )
        return 1

    if total < CEILING:
        print(
            f"note: the backlog shrank by {CEILING - total}. Run with --relax and "
            "lower CEILING so the ratchet holds the new ground."
        )

    grown = {
        linter: (n, PER_LINTER_CEILING.get(linter, 0))
        for linter, n in by_linter.items()
        if n > PER_LINTER_CEILING.get(linter, 0)
    }
    if grown:
        for linter, (now, was) in sorted(grown.items()):
            print(f"::error::{linter} grew from {was} to {now}")
        return 1

    # Identity, not just count: a count-level ratchet lets a change bless one
    # NEW violation by retiring one old entry of the same linter -- totals
    # unchanged, gate green (2026-08-18 adversarial review, finding P2-8).
    # Diffing entry identities against the committed baseline on origin/main
    # closes that: any entry present here and absent there is a new
    # suppression, and a new suppression needs a human argument in review, not
    # a swap. CI checks out with fetch-depth 0, so the ref is available there;
    # a local clone without it degrades to the count checks above, loudly.
    try:
        # encoding="utf-8" is load-bearing, not decoration. `text=True` alone
        # decodes with the LOCALE encoding, which is UTF-8 on Linux and macOS
        # and cp1252 on Windows -- and nolints.json carries Lean declaration
        # names, which are full of non-ASCII. The failure is also much worse
        # than it looks: the UnicodeDecodeError is raised on subprocess's
        # reader THREAD, so nothing propagates here, `.stdout` comes back None,
        # and the traceback a reader actually sees is a TypeError from
        # json.loads three lines down. Observed on a Windows runner 2026-08-23.
        baseline_raw = subprocess.run(
            ["git", "show", f"{BASELINE_REF}:{NOLINTS.as_posix()}"],
            capture_output=True, text=True, check=True, encoding="utf-8",
        ).stdout
    except (subprocess.CalledProcessError, OSError):
        print(f"note: {BASELINE_REF} is not available; entry-identity check "
              "skipped (count ceilings above still hold).")
        return 0

    baseline = {tuple(e) for e in json.loads(baseline_raw)}
    added = sorted(tuple(e) for e in entries if tuple(e) not in baseline)
    if added:
        for linter, name in added:
            print(f"::error::new nolints entry: [{linter}] {name}")
        print(f"::error::{len(added)} entr{'y is' if len(added) == 1 else 'ies are'} "
              f"not in {BASELINE_REF}'s nolints.json. Fix the declaration, or "
              "argue for the exception in review; swapping an old entry for a "
              "new one is not a fix.")
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

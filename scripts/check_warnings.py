#!/usr/bin/env python3
"""Keep the compiler-warning backlog a ratchet, and keep deprecations at zero.

`lake exe runLinter` gates Batteries' *linters* against `scripts/nolints.json`.
Nothing gated the warnings Lean itself emits during elaboration, so they only
ever accumulated: 93 of them by 2026-09-13, in which a Mathlib deprecation with
a real deadline was indistinguishable from twenty `simpa` nags.

Two rules, for two different kinds of debt.

**Deprecations are not allowed at all in code this repository owns.** A
deprecated Mathlib declaration is removed a few releases later, so every one of
these is a build break with a date on it. `DerivedAlgGeo/` and `scripts/` were
brought to zero when this gate was wired; a dependency's own deprecations are
listed in the baseline and only counted, because the fix for those is upstream
and a pin bump.

**Everything else may shrink, never grow.** The baseline records each
`(file, message)` with how many times it occurs, so adding a fourth unused simp
argument to a file that already has three is caught even though the file and
the message are both already known. Line and column are deliberately not
recorded: they churn under every unrelated edit above them, and a gate that
cries wolf on an unrelated edit is a gate that gets bypassed.

Usage:
    python3 scripts/check_warnings.py build.log
    python3 scripts/check_warnings.py build.log --relax   # after really fixing some
"""

from __future__ import annotations

import collections
import json
import re
import sys
from pathlib import Path

from _output import force_utf8_output

BASELINE = Path("scripts/warning-baseline.json")

#: Paths this repository is responsible for. A deprecation under one of these is
#: a failure; a deprecation anywhere else (a dependency built from source) is
#: recorded and counted, because we cannot fix it here.
OWNED_PREFIXES = ("DerivedAlgGeo/", "scripts/")

#: `warning: <file>:<line>:<col>: <message>` as Lean emits it. Only the first
#: line of a multi-line message is keyed; the continuation lines carry the
#: suggested replacement and wrap differently between Lean versions.
WARNING_RE = re.compile(r"^warning: (?P<file>[^:]+):\d+:\d+: (?P<msg>.*)$")

DEPRECATED = "has been deprecated"


def parse(log: str) -> collections.Counter[tuple[str, str]]:
    """Count each `(file, message)`, ignoring a line repeated verbatim.

    One build replays cached modules and reprints their warnings, so the same
    `file:line:col: message` can appear several times in one log while being one
    warning. Distinct lines or columns under one `(file, message)` are distinct
    warnings and are counted separately.
    """
    seen: set[str] = set()
    counts: collections.Counter[tuple[str, str]] = collections.Counter()
    for raw in log.splitlines():
        line = raw.rstrip("\r")
        if line in seen:
            continue
        m = WARNING_RE.match(line)
        if not m:
            continue
        seen.add(line)
        counts[(m.group("file"), m.group("msg").strip())] += 1
    return counts


def load_baseline() -> collections.Counter[tuple[str, str]]:
    entries = json.loads(BASELINE.read_text(encoding="utf-8"))
    return collections.Counter({(f, msg): n for f, msg, n in entries})


def write_baseline(counts: collections.Counter[tuple[str, str]]) -> None:
    entries = sorted([f, msg, n] for (f, msg), n in counts.items())
    BASELINE.write_text(
        json.dumps(entries, indent=1, ensure_ascii=False) + "\n", encoding="utf-8"
    )


def owned(path: str) -> bool:
    return path.startswith(OWNED_PREFIXES)


def main(argv: list[str]) -> int:
    args = [a for a in argv if not a.startswith("--")]
    relax = "--relax" in argv

    if not args:
        print("::error::usage: check_warnings.py <build log> [--relax]")
        return 1
    log_path = Path(args[0])
    if not log_path.exists():
        print(f"::error::{log_path} is missing; the warning gate has nothing to read")
        return 1
    if not BASELINE.exists():
        print(f"::error::{BASELINE} is missing; the warning gate depends on it")
        return 1

    current = parse(log_path.read_text(encoding="utf-8", errors="replace"))
    baseline = load_baseline()

    if not current:
        # A warm build that recompiled nothing prints nothing, and an empty
        # result would silently "pass" every rule below. That is the vacuous
        # pass this gate exists to avoid.
        print("::error::no warnings parsed from the build log -- the capture is "
              "wrong, or the build was fully cached and printed nothing. This "
              "gate cannot pass on an empty reading.")
        return 1

    failures = 0

    deprecations = sorted(
        (f, msg, n) for (f, msg), n in current.items()
        if DEPRECATED in msg and owned(f)
    )
    if deprecations:
        print(f"::error::{len(deprecations)} deprecation warning(s) in code this "
              "repository owns. Each one is a build break on a future Mathlib "
              "bump; fix the call site rather than recording it here.")
        for f, msg, n in deprecations:
            print(f"  {f} ({n}x): {msg}")
        failures += 1

    added = {k: n - baseline.get(k, 0) for k, n in current.items()
             if n > baseline.get(k, 0)}
    if added:
        total_new = sum(added.values())
        print(f"::error::{total_new} new compiler warning(s) not in {BASELINE}. "
              "Fix them, or argue for the exception in review -- do not "
              "regenerate the baseline to make this pass.")
        for (f, msg), n in sorted(added.items()):
            was = baseline.get((f, msg), 0)
            print(f"  {f} ({was} -> {was + n}): {msg}")
        failures += 1

    removed = {k: baseline[k] - current.get(k, 0) for k in baseline
               if baseline[k] > current.get(k, 0)}
    total_fixed = sum(removed.values())

    if failures:
        return 1

    print(f"warnings: {sum(current.values())} "
          f"(baseline {sum(baseline.values())}, {len(current)} distinct)")

    if total_fixed:
        if relax:
            write_baseline(current)
            print(f"--relax: baseline lowered by {total_fixed}; commit "
                  f"{BASELINE} with the fix.")
        else:
            print(f"::notice::{total_fixed} baseline warning(s) are gone. Run "
                  f"`python3 scripts/check_warnings.py {log_path} --relax` and "
                  f"commit {BASELINE} so the gate keeps the ground you won.")

    return 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main(sys.argv[1:]))

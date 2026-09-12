#!/usr/bin/env python3
"""Turn `scripts/StabilityConditionAudit.lean` into a gate.

`Audit.lean` is a build target, so it cannot rot — but it is **not a gate**:
`#print axioms` prints `[sorryAx]` and exits 0, so a sorry-backed declaration
builds green. This script is what makes the audit fail.

Usage:

    lake env lean scripts/StabilityConditionAudit.lean > audit.txt 2>&1
    python3 scripts/check_audit.py audit.txt

An optional second argument overrides the path to `Audit.lean` (default: the
copy next to this script). It exists so the truncation check below can be
tested against fixtures; the gate itself always runs with the default.

Exits non-zero, with the offending declarations named, on any of:

* an axiom outside [propext, Classical.choice, Quot.sound],
* `sorryAx` anywhere,
* an empty sweep (the vacuous pass),
* a **parse mismatch** — see below,
* a **record count that disagrees with `Audit.lean`** — the truncation check,
  see below.

## The parse-mismatch check is not paranoia

An earlier ad-hoc version of this check used `'([^']+)'` to capture the
declaration name. That silently dropped every declaration whose name ends in an
apostrophe — `NormalizedShift.ext'` and `GLTilde.ext'` — because the closing
quote of the printed name is immediately preceded by one. The check reported
187 declarations while the file actually printed 189, and nobody noticed,
because a gate that skips a declaration looks exactly like a gate that passes
it.

So this script counts the marker phrase independently of the structured parse
and fails if the two disagree. A gate that cannot say how much it covered is
not a gate.

## Neither is the truncation check

The parse-mismatch check compares the parse against the output. It cannot see
an output that is *itself* short. On 2026-08-07 two audit runs died
mid-elaboration — a concurrent Lean build was saturating memory on the same
machine — and left output files truncated at 661 and then 558 records of the
677 commanded. This script counted what was present and printed
"ok: 661 declarations": a truncated output is indistinguishable from a
complete, smaller audit unless you know how many records were commanded. The
incident is recorded in `formalization.yaml`'s builds_clean_note
(TRUST-PROSE RECONCILIATION, 2026-08-07).

So this script now also counts the `#print axioms` commands in `Audit.lean`
itself and fails when the output's record count disagrees. Same principle as
above, one level up: the expected count comes from outside the artifact being
judged.

The count is textual — lines of `Audit.lean` starting with `#print axioms ` —
so do not begin a comment line with that string.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from _output import force_utf8_output

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

# Lazy, so a name ending in `'` still terminates correctly: the regex needs the
# literal `' depends on axioms: [` to follow, and no declaration name contains
# that.
ENTRY = re.compile(r"'(.+?)' depends on axioms: \[([^\]]*)\]")
NO_AXIOMS = re.compile(r"'(.+?)' does not depend on any axioms")

# One `#print axioms` command produces exactly one axiom report, so the line
# count here is the record count a complete output must contain.
PRINT_AXIOMS = re.compile(r"^#print axioms ", re.MULTILINE)


def main(path: str, audit_lean: str | None = None) -> int:
    source = (Path(audit_lean) if audit_lean
              else Path(__file__).resolve().parent / "StabilityConditionAudit.lean")
    # Since #480 an audit may be split: the named file is an imports-only
    # umbrella and the records live in `<stem>/*.lean` beside it. Count across
    # the umbrella plus every area file; for an unsplit audit (DGCategory, and
    # any fixture) the glob is empty and this is the old single-file count.
    sources = [source] + sorted((source.parent / source.stem).glob("*.lean"))
    try:
        commanded = sum(
            len(PRINT_AXIOMS.findall(f.read_text(encoding="utf-8")))
            for f in sources)
    except OSError as e:
        # Failing open here would resurrect exactly the blind spot this check
        # exists to close.
        print(f"::error::cannot read {source} to count `#print axioms` commands "
              f"({e}); without that count a truncated output is indistinguishable "
              f"from a complete audit")
        return 1

    raw = open(path, encoding="utf-8").read()
    # `#print axioms` output wraps at the terminal width, unpredictably, so
    # flatten before parsing rather than reading it line by line.
    flat = " ".join(raw.split())

    entries = [(n, {a.strip() for a in axs.split(",") if a.strip()})
               for n, axs in ENTRY.findall(flat)]
    entries += [(n, set()) for n in NO_AXIOMS.findall(flat)]

    # Both report shapes must be counted. `#print axioms` emits "does not depend
    # on any axioms" for an axiom-free declaration, and that phrase does NOT
    # contain "depends on axioms" -- so counting only the first phrase would make
    # `entries` exceed `expected` the moment one such declaration appears, and
    # this guard would fail a run that is in fact fully parsed. Latent today
    # (all 497 currently report axioms), wrong the first time one does not.
    expected = (flat.count("depends on axioms")
                + flat.count("does not depend on any axioms"))
    if len(entries) != expected:
        print(f"::error::audit parse mismatch: parsed {len(entries)} entries but the "
              f"output contains {expected} axiom reports. The gate would be checking "
              f"less than it claims; fix the parser, do not lower the count.")
        return 1

    if not entries:
        print("::error::audit swept 0 declarations -- the vacuous pass")
        return 1

    # The cross-check against the source of the commands, not the output. An
    # audit run that dies mid-elaboration (2026-08-07: twice, at 661 and 558 of
    # 677, under memory pressure from a concurrent Lean build) leaves a
    # well-formed prefix that the checks above accept as a complete, smaller
    # audit.
    if len(entries) != commanded:
        if len(entries) < commanded:
            print(f"::error::audit output contains {len(entries)} records but "
                  f"{source.name} issues {commanded} `#print axioms` commands. "
                  f"The output is TRUNCATED, or was produced by an older "
                  f"{source.name}. A truncated file usually means the run died "
                  f"mid-elaboration (e.g. under memory pressure from a "
                  f"concurrent build). Re-run the audit with nothing else "
                  f"building; do not lower the count.")
        else:
            print(f"::error::audit output contains {len(entries)} records but "
                  f"{source.name} issues only {commanded} `#print axioms` "
                  f"commands -- the output came from a different {source.name} "
                  f"than the one being checked. Re-run the audit against the "
                  f"current tree.")
        return 1

    bad = [(n, sorted(axs - ALLOWED)) for n, axs in entries if not axs <= ALLOWED]
    if bad:
        for name, extra in bad:
            print(f"::error::{name} depends on {extra}")
        print(f"::error::{len(bad)} of {len(entries)} declarations are outside the allowlist")
        return 1

    print(f"ok: {len(entries)} declarations, all within "
          f"[propext, Classical.choice, Quot.sound], no sorryAx, "
          f"count matches the {commanded} commands in {source.name}")
    return 0


if __name__ == "__main__":
    force_utf8_output()
    if len(sys.argv) not in (2, 3):
        print(__doc__)
        sys.exit(2)
    sys.exit(main(*sys.argv[1:]))

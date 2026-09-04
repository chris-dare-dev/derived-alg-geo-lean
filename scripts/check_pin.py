#!/usr/bin/env python3
"""Assert pins.json matches what this working tree actually resolves.

HARD GATE (exit 1): lean_toolchain and mathlib_rev/mathlib_input_rev in pins.json
must equal lean-toolchain and the mathlib entry of lake-manifest.json. Also checks
mfc_rev when pins.json records it.

ADVISORY (exit 0, prints WARN): the recorded_at/recorded_from provenance stamp,
and cross_repo.status. `ALIGNED` and `MERGED` both
satisfy the single-pin premise. A DIVERGED peer blocks that premise but does
not fail this repo's build. Past
cross_repo.divergence_until it is reported as OVERDUE, still exit 0 -- escalation
is a human decision, not a build break.

Usage:  python3 scripts/check_pin.py [repo_root]
"""

import json
import pathlib
import subprocess
import sys
from datetime import date

root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else __file__).resolve()
if root.is_file():
    root = root.parent.parent

pins_path = root / "pins.json"
if not pins_path.exists():
    print(f"FAIL  no pins.json at {pins_path}")
    sys.exit(1)

pins = json.loads(pins_path.read_text())
manifest = json.loads((root / "lake-manifest.json").read_text())
toolchain = (root / "lean-toolchain").read_text().strip()

packages = {p.get("name"): p for p in manifest.get("packages", [])}
failures = []


def check(label, expected, actual):
    if expected != actual:
        failures.append(f"{label}: pins.json says {expected!r}, tree resolves {actual!r}")


check("lean_toolchain", pins["lean_toolchain"], toolchain)

mathlib = packages.get("mathlib")
if mathlib is None:
    failures.append("mathlib absent from lake-manifest.json")
else:
    check("mathlib_rev", pins["mathlib_rev"], mathlib.get("rev"))
    check("mathlib_input_rev", pins["mathlib_input_rev"], mathlib.get("inputRev"))

for key, pkg in (("mfc_rev", "MathFormalContract"),):
    expected = pins.get(key)
    if expected is None:
        if pkg in packages:
            failures.append(f"{key} is null in pins.json but {pkg} is in the manifest")
    elif pkg not in packages:
        failures.append(f"{key} is {expected!r} but {pkg} is absent from the manifest")
    else:
        check(key, expected, packages[pkg].get("rev"))

# The SECOND pin to the same repository: CI installs the mfc CLI by pip from a
# commit named in ci.yml, independent of the Lake dependency above. Until
# 2026-08-19 nothing compared the two, and they drifted (2026-08-18
# adversarial review, P3-15). The emitter (Lean) and the validator/sealer
# (Python) must read one schema; this check keeps both pins recorded and equal
# to each other via pins.json.
import re

ci_text = (root / ".github" / "workflows" / "ci.yml").read_text()
cli_pins = set(re.findall(
    r"math-formal-contract-lean@([0-9a-f]{40})", ci_text))
expected_cli = pins.get("mfc_cli_rev")
if expected_cli is None:
    failures.append("mfc_cli_rev is missing from pins.json; ci.yml installs "
                    "the mfc CLI by pip and that pin must be recorded")
elif not cli_pins:
    failures.append("ci.yml no longer pins the mfc CLI by commit; record how "
                    "CI obtains mfc or restore the pinned install")
elif cli_pins != {expected_cli}:
    failures.append(f"mfc_cli_rev: pins.json says {expected_cli!r}, ci.yml "
                    f"installs {sorted(cli_pins)!r}")
elif expected_cli != pins.get("mfc_rev"):
    failures.append(f"mfc_cli_rev {expected_cli!r} differs from mfc_rev "
                    f"{pins.get('mfc_rev')!r}; the Lean emitter and the "
                    f"Python validator would read different schemas")

# The FOURTH place these revisions are pinned: `docbuild/lake-manifest.json`.
# `docbuild` is a nested package sharing the parent's `packagesDir`, and it
# requires DerivedAlgGeo first precisely so shared dependencies resolve to the
# top-level pins. But it still records its own revision per package, and until
# 2026-09-04 nothing compared the two.
#
# They drifted, and the symptom was thoroughly misleading. 9c6eff20 bumped
# MathFormalContract in `lake-manifest.json`, both keys of `pins.json` and the
# ci.yml URL, and left docbuild on an older revision than any of them -- so
# doc-gen died on `@[discharges "gltilde-universal-cover"]` with `unexpected
# token; expected ']'`, a parse error in a file that compiles clean under
# `lake build`. Mathlib matched throughout, which is why nothing looked wrong.
#
# Only SHARED packages are compared, and only where both record a revision:
# docbuild carries doc-gen4 and its dependencies, which the parent neither has
# nor should, and requires DerivedAlgGeo itself by path, which has no `rev`.
doc_manifest = root / "docbuild" / "lake-manifest.json"
if doc_manifest.exists():
    doc_packages = {p["name"]: p.get("rev")
                    for p in json.loads(doc_manifest.read_text())["packages"]}
    for name, pin in sorted(packages.items()):
        doc_rev = doc_packages.get(name)
        if doc_rev is not None and pin.get("rev") is not None \
                and doc_rev != pin.get("rev"):
            failures.append(
                f"docbuild/lake-manifest.json pins {name} at {doc_rev!r} but "
                f"lake-manifest.json pins {pin.get('rev')!r}; the docs build "
                f"would compile the library against a different {name}")

if failures:
    print(f"FAIL  {pins['repo']} pin coherence ({len(failures)} problem(s)):")
    for f in failures:
        print(f"  - {f}")
    print("\nFix by re-recording pins.json from this tree, or by correcting the pin.")
    sys.exit(1)

print(f"OK    {pins['repo']} pins match the tree ({toolchain}, mathlib {pins['mathlib_rev'][:12]})")

# The provenance stamp, ADVISORY on purpose.
#
# `recorded_at` / `recorded_from` say when this record was last taken and from
# which commit. Nothing read them, and they were never once updated: set at
# `550d3d2f` (2026-08-18, origin/main ae1424a) and unchanged through four later
# commits that changed the pins beneath them -- including two mfc re-pins. A
# provenance line that does not describe its own file is worse than none,
# because it reads as evidence.
#
# The check is the cheapest one that could have caught all four: if pins.json
# itself was last modified AFTER `recorded_at`, the stamp does not describe the
# file it sits in. No self-reference, no assumption about what a commit
# contains, and it needs only `git log` on a full checkout (`fetch-depth: 0`,
# ci.yml:181).
#
# WARN rather than FAIL, matching `cross_repo.status` above: this repo runs
# many concurrent lanes and a new hard gate on a shared file turns every one of
# them red for a stamp. Promoting it is the owner's call, and the one-line
# change is `failures.append(...)` instead of `print("WARN ...")`.
stamp_date = pins.get("recorded_at")
if stamp_date:
    try:
        last_touched = subprocess.run(
            # %as (AUTHOR date), not %cs: a rebase rewrites the committer
            # date, which would make a PR that sat for a few days warn about a
            # stamp nobody touched. The author date is when the change was
            # actually made and survives the rebase.
            ["git", "-C", str(root), "log", "-1", "--format=%as", "--", "pins.json"],
            capture_output=True, text=True, check=False, timeout=10,
        ).stdout.strip()
    except (OSError, subprocess.SubprocessError):  # pragma: no cover - no git
        last_touched = ""
    if last_touched and date.fromisoformat(last_touched) > date.fromisoformat(stamp_date):
        print(
            f"WARN  the provenance stamp is stale: recorded_at is {stamp_date} "
            f"but pins.json was last modified {last_touched}."
        )
        print(
            "      Whatever changed the pins did not re-record where they came "
            "from. Update recorded_at + recorded_from in the same commit that "
            "moves a pin."
        )

cross = pins.get("cross_repo") or {}
status = cross.get("status")
if status and status not in {"ALIGNED", "MERGED"}:
    until = cross.get("divergence_until")
    overdue = ""
    if until and date.fromisoformat(until) < date.today():
        overdue = f" -- OVERDUE since {until}"
    print(
        f"WARN  cross-repo {status}{overdue}: peer {cross.get('peer')} is on "
        f"{cross.get('peer_toolchain')} / mathlib {(cross.get('peer_mathlib_rev') or '')[:12]}"
    )
    print("      The single-pin trunk premise does not hold while this is DIVERGED.")

sys.exit(0)

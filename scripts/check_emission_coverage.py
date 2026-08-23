#!/usr/bin/env python3
"""Check that the emission covers every tracked Lean module, and carries no sorry.

Stdlib only, like check_audit.py and check_coverage_map.py.

`lake exe emit` is the repository's `sorry` gate: it imports the sweep umbrella's
`.olean`s, calls `collectAxioms` on every constant of every in-scope module, and
exits 1 when any closure contains `sorryAx`. That check is complete over the
environment it sweeps -- and that is the whole problem this script exists for,
because *which* environment it sweeps is a property of one import line.

`MathFormalContract.emitToFileForRootsImpl` builds its environment with
`importModules #[{module := rootLib}]`. The `additionalRoots` argument widens the
scope filter, not the import. So a library root that no import reaches is not
"partially covered" or "reported missing": it contributes zero constants, the
emitter finds zero sorries in it, and the run is green. Measured on 2026-08-14
before #361, the emission covered 406 of 419 tracked modules -- the dg-category
subsystem, development probes, and the former vendor umbrella were absent, with
nothing in CI saying so. The vendor root has since been retired.

A gate that can shrink to nothing while still passing is the vacuous pass this
repository's attestation design exists to make impossible. This script is the
guard: it recomputes the obligation from the tracked files still present in the
working tree on every run, so adding a library root without importing it into
`DerivedAlgGeoSweep.lean` fails loudly rather than quietly reducing what is
gated. Filtering deleted paths matters for structural changes: `git ls-files`
continues to report an indexed file until the deletion is committed.

Exclusions are deliberate, and each is justified below in EXCLUDED_PREFIXES.

    python3 scripts/check_emission_coverage.py [attest/lean-emission.json]
"""

import json
import subprocess
import sys
from pathlib import Path

DEFAULT_EMISSION = Path("attest/lean-emission.json")

# Paths whose `.lean` files are not library modules of the swept environment.
#
# `.claude/` is agent configuration and historical review fixtures; `scripts/`
# holds the hand-maintained audits and is elaborated by its own CI steps, each of
# which fails on `sorryAx` directly. `exe/` roots cannot appear in an emission
# built from their own imports, so CI elaborates them individually -- see the
# "No declaration uses sorry" step in .github/workflows/ci.yml. Widening this
# tuple reduces what is gated; do not add to it without saying what else gates
# the code you are removing.
EXCLUDED_PREFIXES = (".claude/", "scripts/", "exe/")

# Non-root `srcDir` values from lakefile.toml, longest first. There are no gated
# library sources outside the repository root at present; keeping the mechanism
# explicit makes a future non-root source directory fail until it is registered.
SRC_DIRS: tuple[str, ...] = ()


def module_of(path: str) -> str:
    """The Lean module name a tracked source path declares."""
    for src_dir in SRC_DIRS:
        if path.startswith(src_dir):
            path = path[len(src_dir):]
            break
    return path[: -len(".lean")].replace("/", ".")


def tracked_modules() -> dict[str, str]:
    """Every gated module, mapped back to the path that declares it."""
    out = subprocess.run(
        ["git", "ls-files", "*.lean"],
        capture_output=True, text=True, check=True, encoding="utf-8",
    ).stdout.split()
    return {
        module_of(p): p
        for p in out
        if not p.startswith(EXCLUDED_PREFIXES) and Path(p).is_file()
    }


def main(argv: list[str]) -> int:
    emission_path = Path(argv[1]) if len(argv) > 1 else DEFAULT_EMISSION
    try:
        doc = json.loads(emission_path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        print(f"error: no emission at {emission_path}; run `lake exe emit --out "
              f"{emission_path}` first", file=sys.stderr)
        return 1
    except json.JSONDecodeError as exc:
        print(f"error: {emission_path} is not valid JSON: {exc}", file=sys.stderr)
        return 1

    emitted = set(doc.get("modules", []))
    constants = doc.get("constants", [])
    if not emitted or not constants:
        # The vacuous pass, stated as itself: an emission with no modules or no
        # constants trivially contains no sorry.
        print(f"error: {emission_path} reports {len(emitted)} module(s) and "
              f"{len(constants)} constant(s); an empty sweep is not a pass",
              file=sys.stderr)
        return 1

    tracked = tracked_modules()
    missing = sorted(set(tracked) - emitted)
    # Re-check `sorryAx` here rather than trusting the exit code alone: the
    # artifact is what is uploaded and read later, so the claim should be
    # checkable from the artifact.
    sorried = sorted(
        c["name"] for c in constants if "sorryAx" in c.get("axioms", [])
    )

    for module in missing:
        print(f"error: {tracked[module]} declares module {module}, which the "
              f"emission does not cover -- import it into DerivedAlgGeoSweep.lean",
              file=sys.stderr)
    for name in sorried:
        print(f"error: {name} depends on sorryAx", file=sys.stderr)

    if missing or sorried:
        print(f"FAIL: {len(missing)} uncovered module(s), {len(sorried)} "
              f"sorry-backed constant(s)", file=sys.stderr)
        return 1

    print(f"ok: {len(tracked)} tracked module(s) covered by {len(emitted)} "
          f"emitted module(s); no constant depends on sorryAx")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

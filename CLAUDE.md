# Working in DerivedAlgGeo

## Repository shape

This repository contains one public Lean library: `DerivedAlgGeo`. Its source
root is `DerivedAlgGeo/` and its all-library umbrella is `DerivedAlgGeo.lean`.
The layout follows Mathlib's subject hierarchy.

The principal areas are:

- `DerivedAlgGeo/AlgebraicGeometry/` for coherent sheaves, cohomology,
  divisors, duality, intersection theory, numerical geometry, and
  Riemann--Roch;
- `DerivedAlgGeo/CategoryTheory/DGCategory/` for dg-category theory;
- `DerivedAlgGeo/CategoryTheory/Triangulated/TStructure/` for t-structures;
- `DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/` for
  Bridgeland stability foundations and applications;
- `DerivedAlgGeo/LinearAlgebra/` for lattice and matrix prerequisites;
- `DerivedAlgGeo/Development/` for code intentionally excluded from the stable
  root.

Never add imports or namespaces rooted at `CohLean`, `DGLean`, or
`BridgelandStabLean`; those migration artifacts are retired.

## Editing rules

- Prefer the narrowest import and the nearest umbrella.
- Use Mathlib's namespace for extensions of an existing Mathlib API.
- Keep generic layers independent of specialized geometric applications.
- Preserve explicit trust boundaries; do not use `sorry`, `admit`, or a hidden
  axiom to cross an unfinished mathematical seam.
- Do not edit generated build artifacts by hand.
- Do not alter unrelated work in a dirty tree.

Read `CONTRIBUTING.md` before creating a new directory or publishing a
change; it owns the human-facing placement and contribution rules.

## Required verification

**Full verification runs on the self-hosted Windows runners, not on your machine.**
`.github/workflows/ci.yml` routes `push` and `workflow_dispatch` to
`["self-hosted", "owner-win"]`, and it triggers on `agent/**`. So pushing an agent
branch already runs the whole gate there; to get a verdict without pushing, use

```bash
gh workflow run ci.yml --ref <branch>
```

Do **not** run `scripts/gates.sh` as a matter of course. Several agent lanes share
one Mac, Lake takes one core per job by default, and four concurrent full gates
oversubscribe a 14-core machine five times over — that is how a ten-minute gate
becomes an hour. Run it locally only when you need a verdict that the runners
cannot give you, and expect it to be slow when other lanes are building.

Neither the local script nor the runner lane is CI-equivalent on its own, and the
difference has bitten: every gate in `gates.sh` runs in CI, but CI also runs the
`mfc` contract tooling, which the script does not reproduce. Say "N gates pass",
not "CI is green". See `CONTRIBUTING.md`.

The normal build, for iteration, stays local — Lean's `.olean` files are
platform-specific, so the Windows runners can never warm this checkout:

```bash
lake build
```

Cap its parallelism. `LEAN_NUM_THREADS=2` limits Lake to two concurrent `lean`
processes; without it Lake takes one per core. On this machine it is set for every
agent session in `~/.claude/settings.json`, so a plain `lake build` is already
capped — set it explicitly if you are building from a shell that does not inherit
that.

```bash
LEAN_NUM_THREADS=2 lake build
```

Useful focused commands are:

```bash
lake build AlgebraicGeometryAudit StabilityConditionAudit DGCategoryAudit
lake exe runLinter DerivedAlgGeo
lake exe lint-style
python3 scripts/check_source_independence.py
python3 scripts/check_coverage_map.py
```

New public declarations must be added to the relevant audit. The declaration
sweep in `scripts/EnumDecls.lean` and
`scripts/check_audit_complete.py` guards the opposite direction, so renames
must update both the source declaration and its audit record.

`DerivedAlgGeoSweep.lean` is verification-only. It imports the stable root and
development probes for full emitter coverage; do not treat it as a public
package boundary.

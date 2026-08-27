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

The normal build is:

```bash
lake build
```

The full local gate is:

```bash
scripts/gates.sh
```

It is not CI-equivalent, and the difference has bitten: every gate in it runs in
CI, but CI also runs the `mfc` contract tooling, which the script does not
reproduce. Treat a green run as necessary, not sufficient. See `CONTRIBUTING.md`.

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

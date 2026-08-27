# Contributing to DerivedAlgGeo

## Place code by mathematics

All stable Lean code lives below `DerivedAlgGeo/`. Follow the existing subject
hierarchy; do not add new top-level libraries or restore retired repository
roots.

Choose the narrowest natural home:

- geometric objects and theorems: `DerivedAlgGeo/AlgebraicGeometry/`;
- dg, derived, triangulated, and stability-category theory:
  `DerivedAlgGeo/CategoryTheory/`;
- reusable lattice or matrix theory: `DerivedAlgGeo/LinearAlgebra/`;
- exploratory API probes: `DerivedAlgGeo/Development/`.

Use Mathlib's established namespace when extending a Mathlib concept. Add a
same-named umbrella for a new non-leaf directory and export stable leaves
through their nearest existing umbrellas.

Keep generic `Algebra`, `Topology`, and `LinearAlgebra` modules independent of
specialized geometry and stability applications. A new top-level subject is
appropriate only for a coherent body of reusable mathematics, not for one
milestone or provenance boundary.

## Proof and trust policy

Committed library code must not use `sorry`, `admit`, or hidden axioms. Explicit
mathematical hypotheses and structure fields are acceptable; proof holes are
not. Keep conditional geometry honest by recording the exact hypothesis that a
later realization must supply.

Public declarations belong in the appropriate hand-maintained axiom audit:

- `scripts/AlgebraicGeometryAudit.lean`
- `scripts/StabilityConditionAudit.lean`
- `scripts/DGCategoryAudit.lean`

The completeness ratchet rejects growth in unaudited public declarations. When
the ratchet improves, lower its ceiling; never raise one to make a change pass.

## Local workflow

Build the stable root while developing:

```bash
lake build
```

Run the fast gate before requesting review:

```bash
scripts/gates.sh fast
```

Run the full gate before merge:

```bash
scripts/gates.sh
```

The full gate includes:

- Mathlib-style and environment linting for `DerivedAlgGeo`;
- all three axiom audits and the audit-completeness ratchet;
- source-independence, pin, paper-coverage, and no-lint checks;
- roadmap/tracker agreement, when `gh` is available;
- repository-wide emission and `sorryAx` coverage checks.

**A green `scripts/gates.sh` is not a green CI.** The containment runs one way:
every gate in the script also runs in CI, but CI runs more than the script does.
CI's `Contract gates` step additionally runs the `mfc` contract tooling —
`validate`, `env`, `bundle`, `lint`, and `check-ilean-coverage` against the
pinned registry — from a virtualenv it builds per run, and the script does not
reproduce any of it. Expect to learn about those failures from CI.

This file previously called the script "the complete CI-equivalent gate". It was
not, and the difference is not academic: a roadmap entry left at `planned` after
its issue closed reddened CI on `main` and on every open pull request while
`scripts/gates.sh` stayed green on all of them. The `roadmap` gate above closes
that particular hole; the `mfc` steps remain CI-only.

For a focused audit run:

```bash
lake build AlgebraicGeometryAudit StabilityConditionAudit DGCategoryAudit
lake env lean scripts/StabilityConditionAudit.lean \
  > /tmp/stability-condition-audit.txt 2>&1
python3 scripts/check_audit.py /tmp/stability-condition-audit.txt
```

## Documentation

Module docstrings should explain the mathematical statement, assumptions,
conventions, and relationship to surrounding APIs. Avoid provenance language
such as “the old CohLean version”; Git already records that history.

Build generated API documentation through the nested package:

```bash
cd docbuild
lake build DerivedAlgGeo:docs
```

## Changes that move declarations

Structural changes must update imports, umbrellas, audit names, registry
bindings, source-independence checks, documentation, and CI paths in the same
change. A move is complete only when `scripts/gates.sh` passes from a clean
checkout.

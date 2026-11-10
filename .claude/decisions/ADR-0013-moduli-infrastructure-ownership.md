# ADR-0013 — Own reusable moduli infrastructure in the monorepo

- **Status:** partially superseded by ADR-0014. Its paths (the Decision list)
  and the SF8/SF9 ownership lines under Consequences are superseded; the
  monorepo choice and the final trust clause remain in force.
- **Date:** 2026-08-17 (America/New_York)
- **Decider:** Chris Dare
- **Decision:** implement relative-perfect, Quot, stack, and good-moduli
  infrastructure under the repository's Mathlib-style subject hierarchy.

## Context

The stability-in-families roadmap previously parked Quot schemes, algebraic
stacks, and good moduli spaces behind an ownership decision.  The repository
is now a single `DerivedAlgGeo` library and needs these subjects for both the
current stability program and later derived-algebraic-geometry developments.
A pin-based external-owner boundary no longer matches that direction.

## Decision

The monorepo owns the reusable layers, with generic geometry separated from
Bridgeland-specific adapters:

- relative-perfect objects and their moduli problem live under
  `DerivedAlgGeo/AlgebraicGeometry/Moduli/PerfectComplex`;
- Quot and bounded parameter-space constructions live under
  `DerivedAlgGeo/AlgebraicGeometry/Quot`;
- stacks in groupoids and descent live under
  `DerivedAlgGeo/AlgebraicGeometry/Stacks`;
- good-moduli constructions live under
  `DerivedAlgGeo/AlgebraicGeometry/Moduli/GoodModuli`;
- stability-specific use of those layers remains under
  `DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Families`.

Dependencies point from generic categorical and site foundations to stacks,
from coherent and derived geometry to Quot and perfect-complex moduli, and
from stacks plus parameter spaces to good moduli.  The families layer may
consume those subjects.  None of the generic geometry subjects imports a
Bridgeland-specific theorem merely to state its core definitions.

The current relative-perfect object file temporarily imports the honest
`Dqc` construction from the families layer because that construction predates
this decision.  Issue #528 owns moving the general scheme-derived seam to a
neutral algebraic-geometry module; this temporary edge must not spread to the
stack or Quot substrates.

## Consequences

- Issue #214's parked ownership decision is resolved in favor of the
  monorepo.
- SF8 owns relative-perfect objects, their groupoid-valued moduli problem,
  boundedness witnesses, and Quot/parameter spaces.
- SF9 owns the reusable stack substrate, algebraicity applications,
  semistable reduction, and good moduli spaces.
- No structure field, typeclass instance, or roadmap status may stand in for
  an unproved algebraicity, boundedness, properness, or descent theorem.

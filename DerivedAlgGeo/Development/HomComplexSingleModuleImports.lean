/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexSingleModule

/-!
# Import boundary for represented Hom-complex normalization

This compile-only fixture checks the actual imported module closure of the
neutral normalization root. It is exported only by `Development`.

## Main definitions

No definition is exported; the `run_cmd` fixture checks imports.

## Main results

Compilation succeeds only when the neutral root avoids the listed consumers.

## Implementation notes

The check traverses `Lean.getEnv.header.moduleNames` rather than source text.

## References

The repository's geometry firewall and the ownership policy.

## Tags

import boundary, Hom-complex, development probe
-/

run_cmd do
  let modules := (← Lean.getEnv).header.moduleNames
  let forbidden := #[`DerivedAlgGeo.AlgebraicGeometry, `Mathlib.AlgebraicGeometry,
    `DerivedAlgGeo.Algebra.Homology.DerivedCategory,
    `Mathlib.Algebra.Homology.DerivedCategory,
    `DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition,
    `Mathlib.CategoryTheory.Triangulated.StabilityCondition]
  for moduleName in modules do
    if forbidden.any (fun pre => pre.isPrefixOf moduleName) then
      throwError "Neutral Hom-complex root imported forbidden module {moduleName}"

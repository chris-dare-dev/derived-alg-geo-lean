# Structural cutover ledger

This ledger records known ownership defects that have been confirmed by the
signature test in `placement.md`. It is a migration queue, not an allowlist:
new code must use the canonical owner immediately, and touching one of these
blocks should normally move it rather than add more declarations beside it.

## Completed roots

- Generic moduli boundedness: `CategoryTheory/Moduli/Boundedness.lean`.
- Generic replete subprestack machinery:
  `CategoryTheory/Pseudofunctor/ObjectProperty/`, reusing Mathlib's
  `Pseudofunctor.ObjectProperty.fullsubcategory`.
- Ordinary ring/module helpers already extracted to `Algebra/Module/`.
- Generic sheaves and ringed-site module sheaves:
  `CategoryTheory/Sites/Sheaves/`.
- Generic abelian and derived-category infrastructure:
  `CategoryTheory/Abelian/` and
  `CategoryTheory/Triangulated/DerivedCategory/`.

## Confirmed next lanes

1. `AlgebraicGeometry/Modules/ExteriorPower.lean` begins with
   `LinearMap.exteriorPower` and its `ιMulti` theorem. Their signatures contain
   only rings, modules, semilinear maps, and exterior powers; move them to a
   `LinearAlgebra/ExteriorPower/` root and leave the presheaf/sheaf consumer in
   its categorical or geometric layer.
2. `AlgebraicGeometry/Divisors/Determinant.lean` begins with
   `Module.topExteriorPower` and `finrank_topExteriorPower`. They are ordinary
   exterior-power facts and belong with the same linear-algebra root.
3. `AlgebraicGeometry/CoherentSheaf/Abelian/Kernels.lean` contains
   `LinearMap.kerMap` and `IsLocalizedModule.kerMap`. Their signatures mention
   only modules, linear maps, and localization; move them under
   `Algebra/Module/Localization/` before the coherent-sheaf consumer.
4. Review geometric moduli selectors that are only indexed
   isomorphism-closed predicates. Keep their finite-type witnesses geometric,
   but express every actual subprestack through the canonical pseudofunctor
   object-property root once restriction stability is proved.

For each lane, remove the old path rather than retaining an import-only shim,
update audits and umbrellas in the same pull request, and add a focused
layering guard preventing the declaration from returning to its consumer.

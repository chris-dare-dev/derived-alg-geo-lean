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
- Ordinary semilinear and top exterior-power algebra:
  `LinearAlgebra/ExteriorPower/`.
- Exterior powers of presheaves of modules over an arbitrary ring presheaf:
  `CategoryTheory/Sites/Sheaves/Modules/ExteriorPower.lean`; scheme
  sheafification and restriction comparisons remain geometric consumers.

## Confirmed next lanes

1. Review the current adjunction roots against the higher-categorical source
   of the concept. Reuse Mathlib's existing
   `CategoryTheory.Bicategory.Adjunction` hierarchy for adjunctions between
   1-morphisms and its `Cat` comparison for ordinary adjoint functors; do not
   define a parallel notion. The current
   `CategoryTheory/Adjunction/PreservesColimits.lean` must be split by
   signature: its adjunction-free lemma belongs with generic limit-preservation
   infrastructure, while its reflective specialization should consume the
   bicategorical/ordinary comparison at the weakest useful layer. Establish a
   documented `CategoryTheory/Bicategory/` extension root now; reserve an
   `n`- or `∞`-category root for actual reusable formal interfaces rather than
   placeholder directories.
2. `AlgebraicGeometry/CoherentSheaf/Abelian/Kernels.lean` contains
   `LinearMap.kerMap` and `IsLocalizedModule.kerMap`. Their signatures mention
   only modules, linear maps, and localization; move them under
   `Algebra/Module/Localization/` before the coherent-sheaf consumer.
3. Review geometric moduli selectors that are only indexed
   isomorphism-closed predicates. Keep their finite-type witnesses geometric,
   but express every actual subprestack through the canonical pseudofunctor
   object-property root once restriction stability is proved.

For each lane, remove the old path rather than retaining an import-only shim,
update audits and umbrellas in the same pull request, and add a focused
layering guard preventing the declaration from returning to its consumer.

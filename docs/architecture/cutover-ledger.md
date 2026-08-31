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
- Higher-categorical adjunctions: Mathlib's
  `CategoryTheory.Bicategory.Adjunction`, extended under
  `CategoryTheory/Bicategory/Adjunction/`; ordinary adjoint functors are the
  `Cat` specialization through `Adjunction.bicategoricalEquiv`.
- Generic preservation through composition and reflective transport:
  `CategoryTheory/Limits/Preserves/`. The former repository
  `CategoryTheory/Adjunction/` root is retired.
- Module-localization kernel maps:
  `Algebra/Module/Localization/Kernels.lean`. This owns `LinearMap.kerMap` and
  the `IsLocalizedModule.{kerMap,kernelMap,kernelNatTrans}` chain; the
  coherent-sheaf kernel theorem imports and directly reuses that root.

## Confirmed next lanes

1. Review geometric moduli selectors that are only indexed
   isomorphism-closed predicates. Keep their finite-type witnesses geometric,
   but express every actual subprestack through the canonical pseudofunctor
   object-property root once restriction stability is proved.

For each lane, remove the old path rather than retaining an import-only shim,
update audits and umbrellas in the same pull request, and add a focused
layering guard preventing the declaration from returning to its consumer.

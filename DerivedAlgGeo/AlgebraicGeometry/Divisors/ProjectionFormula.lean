/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Dual
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.ProjectionFormula

/-!
# The projection formula for an intrinsically invertible sheaf

For a morphism of schemes f : X ⟶ Y, a module sheaf M on X and an intrinsically invertible module
sheaf L on Y, the projection map f_*M ⊗ L ⟶ f_*(M ⊗ f^*L) is an isomorphism. The tensor inverse of L
is its sheafified dual.

## Main definitions

This file has no definitions.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_projectionMap_of_isInvertible`: the projection map
  `AlgebraicGeometry.Scheme.Modules.projectionMap` is an isomorphism when the target sheaf is
  intrinsically invertible.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.isIso_projectionMap` proves the statement when the line bundle
comes with an explicit tensor inverse. This file supplies the inverse
`AlgebraicGeometry.Scheme.Modules.dualLine` with the isomorphism
`AlgebraicGeometry.Scheme.Modules.tensorDualIso` from
`DerivedAlgGeo/AlgebraicGeometry/Divisors/Dual.lean`, and the isomorphism in the other order from
`AlgebraicGeometry.Scheme.Modules.tensorCommIso`. It is a separate file so that the pullback files
do not import the construction of duals.

## References

* The Stacks Project, Tag 01CB (Lemma 17.16.1, the stalk of a tensor product of modules on a ringed
  space), Tag 01CD (Lemma 17.16.4, pullback of a tensor product of modules on ringed spaces) and Tag
  01E8 (Lemma 20.54.2, the projection formula for a finite locally free module). The statements were
  not obtained verbatim: only summaries of those pages were fetched, so these tags give the
  literature context and are not quoted.

## Tags

projection formula, invertible sheaf, dual, pushforward, pullback
-/

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

noncomputable section

/-- **The projection formula for an intrinsically invertible sheaf** (Stacks, Tag 01E8 at `q = 0`,
rank one): for every module sheaf `M` on `X` and every invertible sheaf `L` on `Y`,
`f_*M ⊗ L ⟶ f_*(M ⊗ f^*L)` is an isomorphism. The tensor inverse of `L` is `dualLine L`. -/
theorem isIso_projectionMap_of_isInvertible (M : X.Modules) (L : Y.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} (show SheafOfModules Y.ringCatSheaf from L)] :
    IsIso (projectionMap f M L) :=
  (pullbackPushforwardAdjunction f).isIso_projectionMorphism_of_tensorInverse M
    { obj := dualLine L
      rightIso := tensorDualIso L
      leftIso := tensorCommIso (dualLine L) L ≪≫ tensorDualIso L }

end

end AlgebraicGeometry.Scheme.Modules

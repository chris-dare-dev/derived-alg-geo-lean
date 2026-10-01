/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Dual
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.ProjectionFormula

/-!
# The projection formula for an intrinsically invertible sheaf

`Modules/Pullback/ProjectionFormula.lean` proves that the projection map
`f_*M ⊗ L ⟶ f_*(M ⊗ f^*L)` is an isomorphism when `L` comes with an explicit tensor inverse
(`isIso_projectionMap`, for `LineBundleData`). This file is the one place where that meets the
sheafified dual of `Divisors/Dual.lean`, which is the tensor inverse of any intrinsically
invertible sheaf: `isIso_projectionMap_of_isInvertible` (Stacks, Tag 01E8 at `q = 0`, rank one).

It is its own leaf so that the pullback root stays independent of the divisor and dual
constructions, as `Divisors/FiniteLocallyFreePullback.lean` does for local freeness.
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

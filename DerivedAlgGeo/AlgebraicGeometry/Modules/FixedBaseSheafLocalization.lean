/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.FixedBaseSheaf
import DerivedAlgGeo.Algebra.Category.ModuleCat.Localization

/-!
# Localizing the two-open section pullback

Fixed-base sections of a module sheaf on a union are a pullback of the
sections on its two opens. Canonical module localization is exact, so the
localized cone is still a pullback. This is only a statement about localized
sections of the source sheaf on these two opens and their union: identifying
them with sections on a geometric base change requires separate affine-chart
comparisons. No objectwise-localized sheaf is constructed here.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} (Y : Scheme.{u})
  (φ : R ⟶ Γ(Y, ⊤)) (M : Y.Modules)
  (U V : Y.Opens) (S : Submonoid R)

/-- The two-open pullback cone remains a limit after localizing its four
section modules at `S`. -/
noncomputable def localizedFixedBaseSectionsTwoOpenLimit :
    IsLimit ((ModuleCat.localizedModuleFunctor S).mapCone
      (TopCat.Sheaf.interUnionPullbackCone
        ((modulesToFixedBaseSheaf Y φ).obj M) U V)) :=
  isLimitOfPreserves (ModuleCat.localizedModuleFunctor S)
    (fixedBaseSectionsTwoOpenLimit Y φ M U V)

end AlgebraicGeometry

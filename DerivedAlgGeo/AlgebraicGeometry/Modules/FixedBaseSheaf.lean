/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# A module sheaf viewed over a fixed base ring

Given `R → Γ(Y, 𝒪_Y)`, every section module of an `𝒪_Y`-module is an
`R`-module, compatibly with restriction. This keeps the sheaf condition in
`ModuleCat R`, so its two-open pullback cone can subsequently be localized.

This is an underived change of scalars. It supplies neither a comparison with
sections after scheme base change nor a derived global-sections theorem.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} (Y : Scheme.{u})
  (φ : R ⟶ Γ(Y, ⊤))

/-- View an `𝒪_Y`-module sheaf as a sheaf of modules over a fixed ring `R`,
using `R → Γ(Y, 𝒪_Y)`. The sheaf and all its restriction maps are retained. -/
noncomputable def modulesToFixedBaseSheaf :
    Y.Modules ⥤ TopCat.Sheaf (ModuleCat R) Y :=
  SheafOfModules.forgetToSheafModuleCat Y.ringCatSheaf (.op ⊤)
      (initialOpOfTerminal isTerminalTop) ⋙
    sheafCompose _ (ModuleCat.restrictScalars φ.hom)

/-- The fixed `R`-action is the original `𝒪_Y(U)`-action after restricting
`φ(r)` from the whole scheme to `U`. -/
theorem modulesToFixedBaseSheaf_smul (M : Y.Modules) (U : Y.Opens)
    (r : R) (x : ((modulesToFixedBaseSheaf Y φ).obj M).presheaf.obj (.op U)) :
    r • x = (M.smul (Y.presheaf.map U.leTop.op (φ.hom r))).hom x :=
  rfl

/-- Sections on an open as `R`-modules, obtained by evaluating the fixed-base
sheaf. -/
noncomputable def fixedBaseSectionsFunctor (U : Y.Opens) :
    Y.Modules ⥤ ModuleCat R :=
  modulesToFixedBaseSheaf Y φ ⋙
    TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op U)

/-- The sheaf condition for two opens, in `ModuleCat R`. This is the exact
pullback cone to which flat localization can later be applied. -/
noncomputable def fixedBaseSectionsTwoOpenLimit (M : Y.Modules)
    (U V : Y.Opens) :
    IsLimit (TopCat.Sheaf.interUnionPullbackCone
      ((modulesToFixedBaseSheaf Y φ).obj M) U V) :=
  TopCat.Sheaf.isLimitPullbackCone _ U V

end AlgebraicGeometry

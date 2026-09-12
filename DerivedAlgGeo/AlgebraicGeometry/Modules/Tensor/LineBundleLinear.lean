/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.GlobalSections
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.LineBundle
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Linear
import DerivedAlgGeo.CategoryTheory.Linear.Adjunction

/-!
# Linear Hom comparisons for line bundles

The categorical line-bundle equivalences in `LineBundle.lean` are compatible with scalar
actions. Over an arbitrary scheme the scalars are global functions; over a field they are
restricted along the structure morphism.

This file supplies only the linear algebra bridge. In particular it does not assert that
`L⁻¹ ⊗ N` is coherent or that its global sections are finite-dimensional.

## Main results

* `unitHomTopLinearEquiv` upgrades maps from the tensor unit to a linear sections comparison;
* `LineBundleData.tensorLeftHomLinearEquiv` upgrades the tensor adjunction;
* `LineBundleData.lineHomTopLinearEquivOver` identifies `Hom(L, N)` with the global sections of
  `L⁻¹ ⊗ N` as vector spaces over the base field.
-/

open CategoryTheory Limits MonoidalCategory Opposite
open AlgebraicGeometry.Cohomology
open scoped AlgebraicGeometry

universe u w

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

private noncomputable instance unitHomModule (M : X.Modules) :
    Module Γ(X, (⊤ : X.Opens))
      ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :=
  Scheme.homModuleGlobal X _ _

/-- Maps from the tensor unit to `M` are linearly equivalent to the global sections of `M`. -/
noncomputable def unitHomTopLinearEquiv (M : X.Modules) :
    ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) ≃ₗ[Γ(X, (⊤ : X.Opens))]
      Γ(M, (⊤ : X.Opens)) where
  __ := unitHomTopEquiv M
  map_add' _ _ := rfl
  map_smul' r f := by
    change ((f.val.app (op (⊤ : X.Opens))).hom
      (((globalSectionSmul (.unit X.ringCatSheaf) r).val.app (op (⊤ : X.Opens))).hom
        (show X.presheaf.obj (op (⊤ : X.Opens)) from 1))) =
        r • (f.val.app (op (⊤ : X.Opens))).hom
          (show X.presheaf.obj (op (⊤ : X.Opens)) from 1)
    rw [globalSectionSmul_app]
    have hres : X.presheaf.map
        (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op r = r := by
      rw [show (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op =
        𝟙 (op (⊤ : X.Opens)) from Subsingleton.elim _ _]
      simp
    rw [hres]
    change (f.val.app (op (⊤ : X.Opens))).hom
        (r • (show X.presheaf.obj (op (⊤ : X.Opens)) from 1)) =
      r • (f.val.app (op (⊤ : X.Opens))).hom
        (show X.presheaf.obj (op (⊤ : X.Opens)) from 1)
    exact (f.val.app (op (⊤ : X.Opens))).hom.map_smul r _

private noncomputable instance unitHomModuleOver {k : Type u} [Field k]
    (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k))] (M : Y.Modules) :
    Module k ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M) :=
  Variety.homModule Y _ _

/-- The tensor-unit Hom/sections comparison is linear over the base field. -/
noncomputable def unitHomTopLinearEquivOver {k : Type u} [Field k]
    (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k))] (M : Y.Modules) :
    ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M) ≃ₗ[k]
      linearGlobalSectionsObj (k := k) Y M where
  __ := unitHomTopEquiv M
  map_add' _ _ := rfl
  map_smul' r f := by
    change ((f.val.app (op (⊤ : Y.Opens))).hom
      (((globalSectionSmul (.unit Y.ringCatSheaf)
        (baseFieldToGlobalSections Y r)).val.app (op (⊤ : Y.Opens))).hom
          (show Y.presheaf.obj (op (⊤ : Y.Opens)) from 1))) =
      baseFieldToGlobalSections Y r •
        (f.val.app (op (⊤ : Y.Opens))).hom
          (show Y.presheaf.obj (op (⊤ : Y.Opens)) from 1)
    rw [globalSectionSmul_app]
    have hres : Y.presheaf.map
        (homOfLE (show (⊤ : Y.Opens) ≤ ⊤ from le_top)).op
          (baseFieldToGlobalSections Y r) = baseFieldToGlobalSections Y r := by
      rw [show (homOfLE (show (⊤ : Y.Opens) ≤ ⊤ from le_top)).op =
        𝟙 (op (⊤ : Y.Opens)) from Subsingleton.elim _ _]
      simp
    rw [hres]
    exact (f.val.app (op (⊤ : Y.Opens))).hom.map_smul
      (baseFieldToGlobalSections Y r) _

namespace LineBundleData

private noncomputable instance tensorLeftEquivalenceFunctorAdditive
    (L : LineBundleData X) : L.tensorLeftEquivalence.functor.Additive := by
  change (tensorLeft L.line).Additive
  infer_instance

private noncomputable instance tensorLeftEquivalenceFunctorLinear
    (R : Type w) [Semiring R] [Linear R X.Modules] [MonoidalPreadditive X.Modules]
    [MonoidalLinear R X.Modules] (L : LineBundleData X) :
    L.tensorLeftEquivalence.functor.Linear R := by
  change (tensorLeft L.line).Linear R
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The tensor-Hom adjunction of a line bundle is linear over every compatible scalar ring. -/
noncomputable def tensorLeftHomLinearEquiv (R : Type w) [Semiring R]
    [Linear R X.Modules] [MonoidalPreadditive X.Modules] [MonoidalLinear R X.Modules]
    (L : LineBundleData X) (M N : X.Modules) :
    (tensorObj L.line M ⟶ N) ≃ₗ[R]
      (M ⟶ tensorObj L.inverse N) :=
  L.tensorLeftEquivalence.toAdjunction.homLinearEquiv M N

/-- The line-bundle Hom/sections comparison is linear over global functions. -/
noncomputable def lineHomTopLinearEquiv (L : LineBundleData X) (N : X.Modules) :
    (L.line ⟶ N) ≃ₗ[Γ(X, (⊤ : X.Opens))] Γ(tensorObj L.inverse N, (⊤ : X.Opens)) :=
  (CategoryTheory.Linear.homCongr Γ(X, (⊤ : X.Opens))
      (tensorUnitRightIso L.line).symm (Iso.refl N)).trans
    ((L.tensorLeftHomLinearEquiv Γ(X, (⊤ : X.Opens))
      (SheafOfModules.unit X.ringCatSheaf) N).trans
      (unitHomTopLinearEquiv (tensorObj L.inverse N)))

/-- The line-bundle Hom/sections comparison is linear over the base field. -/
noncomputable def lineHomTopLinearEquivOver {k : Type u} [Field k]
    (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k))]
    (L : LineBundleData Y) (N : Y.Modules) :
    (L.line ⟶ N) ≃ₗ[k]
      linearGlobalSectionsObj (k := k) Y (tensorObj L.inverse N) :=
  (CategoryTheory.Linear.homCongr k
      (tensorUnitRightIso L.line).symm (Iso.refl N)).trans
    ((L.tensorLeftHomLinearEquiv k
      (SheafOfModules.unit Y.ringCatSheaf) N).trans
      (unitHomTopLinearEquivOver Y (tensorObj L.inverse N)))

end LineBundleData

end

end AlgebraicGeometry.Scheme.Modules

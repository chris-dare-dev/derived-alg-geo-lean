/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.FixedBaseSections
import DerivedAlgGeo.Algebra.Category.ModuleCat.Localization

/-!
# Scalar extension of the actual pullback map on sections

The pullback adjunction unit is linear over the source base ring. If its
target is also a module over a larger ring compatibly with the structural
maps, the scalar-extension adjunction transposes the actual unit map to a
map from extended global sections. This does not assert it is an isomorphism.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped ChangeOfRings
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R A : CommRingCat.{u}} {Y Z : Scheme.{u}}
  (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
  (a : R ⟶ A) (ψ : A ⟶ Γ(Z, ⊤))

private noncomputable def fixedBaseSections_restrictScalars
    (compat : φ ≫ f.appTop = a ≫ ψ) (N : Z.Modules) :
    (fixedBaseSectionsFunctor Z (φ ≫ f.appTop) ⊤).obj N ⟶
      (ModuleCat.restrictScalars a.hom).obj
        ((fixedBaseSectionsFunctor Z ψ ⊤).obj N) := by
  let K := (fixedBaseSectionsFunctor Z (φ ≫ f.appTop) ⊤).obj N
  let T := (fixedBaseSectionsFunctor Z ψ ⊤).obj N
  letI : Module R K := K.isModule
  letI : Module R ((ModuleCat.restrictScalars a.hom).obj T) :=
    ((ModuleCat.restrictScalars a.hom).obj T).isModule
  exact ModuleCat.ofHom (X := K) (Y := (ModuleCat.restrictScalars a.hom).obj T)
    { toFun := fun x => x
      map_add' := by intros; rfl
      map_smul' := by
        intro r x
        change (K.smul r).hom x =
          (T.smul (a.hom r)).hom x
        have hK := modulesToFixedBaseSheaf_smul Z (φ ≫ f.appTop) N ⊤ r x
        have hT := modulesToFixedBaseSheaf_smul Z ψ N ⊤ (a.hom r) x
        change (K.smul r).hom x = _ at hK
        change (T.smul (a.hom r)).hom x = _ at hT
        rw [hK, hT]
        have htop : (⊤ : Z.Opens).leTop = 𝟙 _ := Subsingleton.elim _ _
        simp [htop]
        change ((φ ≫ f.appTop).hom r) • (show Γ(N, ⊤) from x) =
          ((a ≫ ψ).hom r) • (show Γ(N, ⊤) from x)
        rw [compat] }

/-- Extend scalars in the actual top-section pullback unit along a compatible
base-ring map. The result is the unique `A`-linear map whose value on
`1 ⊗ x` is the ordinary pullback-unit section of `x`. -/
noncomputable def fixedBasePullbackTopAfterExtension
    (compat : φ ≫ f.appTop = a ≫ ψ) :
    (ModuleCat.extendScalars a.hom).obj
        ((fixedBaseSectionsFunctor Y φ ⊤).obj M) ⟶
      (fixedBaseSectionsFunctor Z ψ ⊤).obj ((pullback f).obj M) := by
  let N := (pullback f).obj M
  let k := fixedBaseSections_restrictScalars φ f a ψ compat N
  exact ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars a.hom
    (fixedBasePullbackTop φ f M ≫ k)

/-- Scalar extension sends a pure generator to the actual top component of
the pullback adjunction unit. -/
theorem fixedBasePullbackTopAfterExtension_one_tmul
    (compat : φ ≫ f.appTop = a ≫ ψ) (x : Γ(M, ⊤)) :
    (fixedBasePullbackTopAfterExtension φ f M a ψ compat).hom
        ((1 : A) ⊗ₜ[R,(a.hom)] x) =
      (((pullbackPushforwardAdjunction f).unit.app M).app ⊤) x := by
  let T := (fixedBaseSectionsFunctor Z ψ ⊤).obj ((pullback f).obj M)
  letI : Module R A := Module.compHom A a.hom
  letI : Module R T := Module.compHom T a.hom
  unfold fixedBasePullbackTopAfterExtension
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
  erw [TensorProduct.lift.tmul]
  change (1 : A) • ((fixedBasePullbackTop φ f M ≫
    fixedBaseSections_restrictScalars φ f a ψ compat ((pullback f).obj M)).hom x) = _
  rw [one_smul]
  simp only [ModuleCat.comp_apply, fixedBasePullbackTop_apply]
  rfl

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.FixedBaseOpenSections
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Scalar extension of the pullback unit on open sections

For compatible maps `R ⟶ Γ(Y, ⊤)` and `A ⟶ Γ(Z, ⊤)`, the actual
pullback adjunction unit on an arbitrary open `U` transposes to an
`A`-linear map from extended sections of `M` on `U` to sections of
`f⁺ M` on `f ⁻¹ᵁ U`. This is an underived map; no localization or
isomorphism assertion is made.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped ChangeOfRings TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R A : CommRingCat.{u}} {Y Z : Scheme.{u}}
  (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
  (a : R ⟶ A) (ψ : A ⟶ Γ(Z, ⊤))

private noncomputable def fixedBaseOpenSections_restrictScalars
    (U : Y.Opens) (compat : φ ≫ f.appTop = a ≫ ψ) (N : Z.Modules) :
    (fixedBaseSectionsFunctor Z (φ ≫ f.appTop) (f ⁻¹ᵁ U)).obj N ⟶
      (ModuleCat.restrictScalars a.hom).obj
        ((fixedBaseSectionsFunctor Z ψ (f ⁻¹ᵁ U)).obj N) := by
  let K := (fixedBaseSectionsFunctor Z (φ ≫ f.appTop) (f ⁻¹ᵁ U)).obj N
  let T := (fixedBaseSectionsFunctor Z ψ (f ⁻¹ᵁ U)).obj N
  letI : Module R K := K.isModule
  letI : Module R ((ModuleCat.restrictScalars a.hom).obj T) :=
    ((ModuleCat.restrictScalars a.hom).obj T).isModule
  exact ModuleCat.ofHom (X := K) (Y := (ModuleCat.restrictScalars a.hom).obj T)
    { toFun := fun x => x
      map_add' := by intros; rfl
      map_smul' := by
        intro r x
        change (K.smul r).hom x = (T.smul (a.hom r)).hom x
        have hK := modulesToFixedBaseSheaf_smul Z (φ ≫ f.appTop) N
          (f ⁻¹ᵁ U) r x
        have hT := modulesToFixedBaseSheaf_smul Z ψ N (f ⁻¹ᵁ U) (a.hom r) x
        change (K.smul r).hom x = _ at hK
        change (T.smul (a.hom r)).hom x = _ at hT
        rw [hK, hT]
        change (N.smul (Z.presheaf.map (f ⁻¹ᵁ U).leTop.op
          ((φ ≫ f.appTop).hom r))).hom (show Γ(N, f ⁻¹ᵁ U) from x) =
          (N.smul (Z.presheaf.map (f ⁻¹ᵁ U).leTop.op
            ((a ≫ ψ).hom r))).hom (show Γ(N, f ⁻¹ᵁ U) from x)
        rw [compat] }

/-- The actual open-section pullback unit, transposed across extension of scalars. -/
noncomputable def fixedBasePullbackOpenAfterExtension (U : Y.Opens)
    (compat : φ ≫ f.appTop = a ≫ ψ) :
    (ModuleCat.extendScalars a.hom).obj
        ((fixedBaseSectionsFunctor Y φ U).obj M) ⟶
      (fixedBaseSectionsFunctor Z ψ (f ⁻¹ᵁ U)).obj ((pullback f).obj M) := by
  let N := (pullback f).obj M
  let k := fixedBaseOpenSections_restrictScalars φ f a ψ U compat N
  exact ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars a.hom
    (fixedBasePullbackOpen φ f M U ≫ k)

/-- On `1 ⊗ x`, the extended map is literally the ordinary pullback unit at `U`. -/
theorem fixedBasePullbackOpenAfterExtension_one_tmul (U : Y.Opens)
    (compat : φ ≫ f.appTop = a ≫ ψ) (x : Γ(M, U)) :
    (fixedBasePullbackOpenAfterExtension φ f M a ψ U compat).hom
        ((1 : A) ⊗ₜ[R,(a.hom)] x) =
      (((pullbackPushforwardAdjunction f).unit.app M).app U) x := by
  let T := (fixedBaseSectionsFunctor Z ψ (f ⁻¹ᵁ U)).obj ((pullback f).obj M)
  letI : Module R A := Module.compHom A a.hom
  letI : Module R T := Module.compHom T a.hom
  unfold fixedBasePullbackOpenAfterExtension
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
  erw [TensorProduct.lift.tmul]
  change (1 : A) • ((fixedBasePullbackOpen φ f M U ≫
    fixedBaseOpenSections_restrictScalars φ f a ψ U compat ((pullback f).obj M)).hom x) = _
  rw [one_smul]
  simp only [ModuleCat.comp_apply, fixedBasePullbackOpen_apply]
  rfl

end AlgebraicGeometry.Scheme.Modules

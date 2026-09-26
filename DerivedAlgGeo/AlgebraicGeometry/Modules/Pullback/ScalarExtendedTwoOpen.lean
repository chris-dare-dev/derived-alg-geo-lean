/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.ScalarExtendedOpenSections
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Two-open gluing of an actual scalar-extended pullback unit

The scalar-extended pullback unit is an isomorphism on a two-open union when
it is an isomorphism on both opens and their intersection, provided extension
of scalars preserves finite limits. This is an underived gluing step. The
open-section isomorphism hypotheses are not established here.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R A : CommRingCat.{u}} {Y Z : Scheme.{u}}
  (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
  (a : R ⟶ A) (ψ : A ⟶ Γ(Z, ⊤))

/-- If the actual extended pullback unit is invertible on two opens and
their intersection, it is invertible on their union. The only algebraic
hypothesis is finite-limit preservation of scalar extension. -/
theorem fixedBasePullbackOpenAfterExtension_isIso_sup
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u,u,u} a.hom)]
    (U V : Y.Opens) (compat : φ ≫ f.appTop = a ≫ ψ)
    [IsIso (fixedBasePullbackOpenAfterExtension φ f M a ψ U compat)]
    [IsIso (fixedBasePullbackOpenAfterExtension φ f M a ψ V compat)]
    [IsIso (fixedBasePullbackOpenAfterExtension φ f M a ψ (U ⊓ V) compat)] :
    IsIso (fixedBasePullbackOpenAfterExtension φ f M a ψ (U ⊔ V) compat) := by
  let FY := (modulesToFixedBaseSheaf Y φ).obj M
  let FZ := (modulesToFixedBaseSheaf Z ψ).obj ((pullback f).obj M)
  let E := ModuleCat.extendScalars.{u,u,u} a.hom
  letI : PreservesFiniteLimits E := inferInstance
  let cYE := E.mapCone (TopCat.Sheaf.interUnionPullbackCone FY U V)
  let cZ := TopCat.Sheaf.interUnionPullbackCone FZ (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
  have hcYE : IsLimit cYE :=
    isLimitOfPreserves (ModuleCat.extendScalars.{u,u,u} a.hom)
      (fixedBaseSectionsTwoOpenLimit Y φ M U V)
  have hcZ : IsLimit cZ := fixedBaseSectionsTwoOpenLimit Z ψ ((pullback f).obj M)
    (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
  let qU := fixedBasePullbackOpenAfterExtension φ f M a ψ U compat
  let qV := fixedBasePullbackOpenAfterExtension φ f M a ψ V compat
  let qI := fixedBasePullbackOpenAfterExtension φ f M a ψ (U ⊓ V) compat
  let qS := fixedBasePullbackOpenAfterExtension φ f M a ψ (U ⊔ V) compat
  letI : IsIso qU := inferInstance
  letI : IsIso qV := inferInstance
  letI : IsIso qI := inferInstance
  let iU := asIso qU
  let iV := asIso qV
  let iI := asIso qI
  let α : (cospan
      (FY.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op)
      (FY.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op) ⋙ E) ≅
      cospan
        (FZ.presheaf.map (homOfLE inf_le_left : (f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ U).op)
        (FZ.presheaf.map (homOfLE inf_le_right : (f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ V).op) :=
    cospanIsoMk iI iU iV
      (by exact (fixedBasePullbackOpenAfterExtension_restrict φ f M a ψ inf_le_left compat).symm)
      (by exact (fixedBasePullbackOpenAfterExtension_restrict φ f M a ψ inf_le_right compat).symm)
  let cYE' := (Cone.postcompose α.hom).obj cYE
  have hcYE' : IsLimit cYE' := (IsLimit.postcomposeHomEquiv α cYE).symm hcYE
  have hleft : qS ≫ cZ.π.app .left = cYE'.π.app .left := by
    change qS ≫ FZ.presheaf.map
        (homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))).op =
      E.map (FY.presheaf.map
        (homOfLE (le_sup_left : U ≤ U ⊔ V)).op) ≫ qU
    exact fixedBasePullbackOpenAfterExtension_restrict φ f M a ψ
      (le_sup_left : U ≤ U ⊔ V) compat
  have hright : qS ≫ cZ.π.app .right = cYE'.π.app .right := by
    change qS ≫ FZ.presheaf.map
        (homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V))).op =
      E.map (FY.presheaf.map
        (homOfLE (le_sup_right : V ≤ U ⊔ V)).op) ≫ qV
    exact fixedBasePullbackOpenAfterExtension_restrict φ f M a ψ
      (le_sup_right : V ≤ U ⊔ V) compat
  let cm := hcZ.liftConeMorphism cYE'
  have hcm : cm.hom = qS := by
    apply PullbackCone.IsLimit.hom_ext hcZ
    · exact (hcZ.fac cYE' .left).trans hleft.symm
    · exact (hcZ.fac cYE' .right).trans hright.symm
  haveI : IsIso cm := IsLimit.hom_isIso hcYE' hcZ cm
  change IsIso qS
  rw [← hcm]
  change IsIso (asIso cm).hom.hom
  infer_instance

end AlgebraicGeometry.Scheme.Modules

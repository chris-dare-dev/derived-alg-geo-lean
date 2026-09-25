/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.RelativeLocalizationScalars
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FlatPullback
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.RingTheory.Flat.Localization

/-!
# Linearity of relative bounded-coherent pullback under affine localization

For any scheme over Spec R, including a non-affine one, pullback along the
base-change map to Spec A is R-linear for the explicit affine-base actions
when A is a localization of R. The proof uses the cartesian square to identify
the two global-section scalars, proves linearity of module-sheaf pullback via
its adjunction, then transports this through exact derived pullback and the
quasi-coherent and bounded-coherent full subcategories.

The supplied derived pullback must preserve the bounded-coherent locus. This
does not establish localized Hom sets, object descent, fixed-target arrow
extension, or an arbitrary non-flat base-change theorem.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.DerivedCategory

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u

private def baseToGlobal {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A)) : R →+* Γ(Y, ⊤) :=
  p.appTop.hom.comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp φ)

@[reducible] private def modulesLinear {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A)) : Linear R Y.Modules := by
  letI : Linear Γ(Y, (⊤ : Y.Opens)) Y.Modules := Scheme.modulesLinearGlobal Y
  exact Linear.ofRingMorphism ((Linear.toCatCenter Γ(Y, (⊤ : Y.Opens)) Y.Modules).comp
    (baseToGlobal φ p))

private theorem baseToGlobal_comp {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (CommRingCat.of A)) (r : R) :
    baseToGlobal φ (f ≫ p) r = f.appTop.hom (baseToGlobal φ p r) := by
  rw [baseToGlobal, Scheme.Hom.comp_appTop]
  rfl

private theorem baseToGlobal_specMap {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A)) (r : R) :
    baseToGlobal (RingHom.id R)
        (p ≫ Spec.map (CommRingCat.ofHom φ)) r =
      baseToGlobal φ p r := by
  rw [baseToGlobal_comp]
  simp only [baseToGlobal, RingHom.comp_apply, RingHom.id_apply]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  exact (congrArg (fun q : CommRingCat.of R ⟶ Γ(Spec (CommRingCat.of A), ⊤) =>
    p.appTop.hom (q.hom r)) h).symm

private theorem pushforward_scalar {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (CommRingCat.of A)) (M : X.Modules) (r : R) :
    (Scheme.Modules.pushforward f).map
        (AlgebraicGeometry.Cohomology.globalSectionSmul M (baseToGlobal φ (f ≫ p) r)) =
      AlgebraicGeometry.Cohomology.globalSectionSmul
        ((Scheme.Modules.pushforward f).obj M) (baseToGlobal φ p r) := by
  open AlgebraicGeometry.Cohomology in
  ext U m
  change ((globalSectionSmul M (baseToGlobal φ (f ≫ p) r)).val.app
      (op (f ⁻¹ᵁ U))).hom m =
    ((globalSectionSmul ((Scheme.Modules.pushforward f).obj M)
      (baseToGlobal φ p r)).val.app (op U)).hom m
  rw [globalSectionSmul_app, globalSectionSmul_app, baseToGlobal_comp]
  exact congrArg (fun s : X.presheaf.obj (op (f ⁻¹ᵁ U)) =>
    s • (show Γ(M, f ⁻¹ᵁ U) from m))
    (ConcreteCategory.congr_hom (f.naturality (homOfLE (le_top (a := U))).op)
      (baseToGlobal φ p r)).symm

private theorem pullback_scalar {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (CommRingCat.of A)) (M : Y.Modules) (r : R) :
    (Scheme.Modules.pullback f).map
      (AlgebraicGeometry.Cohomology.globalSectionSmul M (baseToGlobal φ p r)) =
      AlgebraicGeometry.Cohomology.globalSectionSmul
        ((Scheme.Modules.pullback f).obj M) (baseToGlobal φ (f ≫ p) r) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  apply (adj.homEquiv M ((Scheme.Modules.pullback f).obj M)).injective
  simp only [adj.homEquiv_unit]
  have hnat := adj.unit_naturality
    (AlgebraicGeometry.Cohomology.globalSectionSmul M (baseToGlobal φ p r))
  have hcent := AlgebraicGeometry.Cohomology.globalSectionSmul_naturality
    (adj.unit.app M) (baseToGlobal φ p r)
  have hpush := congrArg (fun g => adj.unit.app M ≫ g)
    (pushforward_scalar φ f p ((Scheme.Modules.pullback f).obj M) r).symm
  exact hnat.trans (hcent.trans hpush)

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

private theorem baseChangeSquare {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (X : SchemeBaseChange (Spec (CommRingCat.of R))) :
    let T := affineAlgebraBaseChange (R := R) (A := A)
    let f := baseChangeMap X (toIdentityBaseChange T)
    f.left ≫ (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left =
      (baseChangeSnd X T).left ≫ (toIdentityBaseChange T).left := by
  let T := affineAlgebraBaseChange (R := R) (A := A)
  have h := (baseChangeMap_isPullback X (toIdentityBaseChange T)).w
  have hleft := congrArg Over.Hom.left h
  change (baseChangeSnd X T).left ≫ (toIdentityBaseChange T).left =
    (baseChangeMap X (toIdentityBaseChange T)).left ≫
      (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left at hleft
  exact hleft.symm

private theorem relative_baseToGlobal {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (X : SchemeBaseChange (Spec (CommRingCat.of R))) (r : R) :
    let T := affineAlgebraBaseChange (R := R) (A := A)
    let f := baseChangeMap X (toIdentityBaseChange T)
    baseToGlobal (RingHom.id R)
        (f.left ≫ (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left) r =
      baseToGlobal (algebraMap R A) (baseChangeSnd X T).left r := by
  let T := affineAlgebraBaseChange (R := R) (A := A)
  let f := baseChangeMap X (toIdentityBaseChange T)
  calc
    baseToGlobal (RingHom.id R)
        (f.left ≫ (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left) r =
      baseToGlobal (RingHom.id R)
        ((baseChangeSnd X T).left ≫ (toIdentityBaseChange T).left) r :=
      congrArg (fun p => baseToGlobal (RingHom.id R) p r) (baseChangeSquare X)
    _ = baseToGlobal (algebraMap R A) (baseChangeSnd X T).left r := by
      change baseToGlobal (RingHom.id R)
        ((baseChangeSnd X T).left ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) r = _
      exact baseToGlobal_specMap (algebraMap R A) (baseChangeSnd X T).left r

private theorem relativeModulesPullback_linear {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (X : SchemeBaseChange (Spec (CommRingCat.of R))) :
    let T := affineAlgebraBaseChange (R := R) (A := A)
    let f := baseChangeMap X (toIdentityBaseChange T)
    let pSource := (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left
    let pTarget := (baseChangeSnd X T).left
    letI : Linear R (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left.Modules :=
      modulesLinear (RingHom.id R) pSource
    letI : Linear R (X ⨯ T).left.Modules := modulesLinear (algebraMap R A) pTarget
    Functor.Linear R (Scheme.Modules.pullback f.left) := by
  let T := affineAlgebraBaseChange (R := R) (A := A)
  let f := baseChangeMap X (toIdentityBaseChange T)
  let pSource := (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left
  let pTarget := (baseChangeSnd X T).left
  letI : Linear R (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left.Modules :=
    modulesLinear (RingHom.id R) pSource
  letI : Linear R (X ⨯ T).left.Modules := modulesLinear (algebraMap R A) pTarget
  apply (Functor.linear_iff R (Scheme.Modules.pullback f.left)).2
  intro E r
  change (Scheme.Modules.pullback f.left).map
      (AlgebraicGeometry.Cohomology.globalSectionSmul E (baseToGlobal (RingHom.id R) pSource r)) =
    AlgebraicGeometry.Cohomology.globalSectionSmul
      ((Scheme.Modules.pullback f.left).obj E) (baseToGlobal (algebraMap R A) pTarget r)
  exact (pullback_scalar (RingHom.id R) f.left pSource E r).trans
    (congrArg (AlgebraicGeometry.Cohomology.globalSectionSmul
      ((Scheme.Modules.pullback f.left).obj E)) (relative_baseToGlobal X r))

private theorem relativeFlat {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A]
    (X : SchemeBaseChange (Spec (CommRingCat.of R))) :
    Flat (baseChangeMap X
      (toIdentityBaseChange (affineAlgebraBaseChange (R := R) (A := A)))).left := by
  let T := affineAlgebraBaseChange (R := R) (A := A)
  have hf : Flat (toIdentityBaseChange T).left := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    apply Flat.SpecMap_iff.mpr
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A M)
  exact MorphismProperty.of_isPullback (P := @Flat)
    ((Over.forget (Spec (CommRingCat.of R))).map_isPullback
      (baseChangeMap_isPullback X (toIdentityBaseChange T))) hf

private theorem relativeAmbientPullback_linear {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (X : SchemeBaseChange (Spec (CommRingCat.of R)))
    (P : DqcLeftDerivedPullback (baseChangeMap X
      (toIdentityBaseChange (affineAlgebraBaseChange (R := R) (A := A)))))
    [IsExactPullback (baseChangeMap X
      (toIdentityBaseChange (affineAlgebraBaseChange (R := R) (A := A))))] :
    let T := affineAlgebraBaseChange (R := R) (A := A)
    let pSource := (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left
    let pTarget := (baseChangeSnd X T).left
    letI : Linear R (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left.Modules :=
      modulesLinear (RingHom.id R) pSource
    letI : Linear R (X ⨯ T).left.Modules := modulesLinear (algebraMap R A) pTarget
    letI : Linear R (SchemeDerivedCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) := inferInstance
    letI : Linear R (SchemeDerivedCategory (X ⨯ T).left) := inferInstance
    Functor.Linear R P.ambient.functor := by
  let T := affineAlgebraBaseChange (R := R) (A := A)
  let f := baseChangeMap X (toIdentityBaseChange T)
  let pSource := (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left
  let pTarget := (baseChangeSnd X T).left
  letI : Linear R (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left.Modules :=
    modulesLinear (RingHom.id R) pSource
  letI : Linear R (X ⨯ T).left.Modules := modulesLinear (algebraMap R A) pTarget
  letI : Linear R (SchemeDerivedCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) := inferInstance
  letI : Linear R (SchemeDerivedCategory (X ⨯ T).left) := inferInstance
  letI : Functor.Linear R (modulePullback f) := relativeModulesPullback_linear X
  letI : Functor.Linear R (derivedPullback f) := by
    change Functor.Linear R ((modulePullback f).mapDerivedCategory)
    infer_instance
  exact Functor.linear_of_iso R (P.ambient.exactComparison).symm

private theorem relativeDqcPullback_linear {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (X : SchemeBaseChange (Spec (CommRingCat.of R)))
    (P : DqcLeftDerivedPullback (baseChangeMap X
      (toIdentityBaseChange (affineAlgebraBaseChange (R := R) (A := A)))))
    [IsExactPullback (baseChangeMap X
      (toIdentityBaseChange (affineAlgebraBaseChange (R := R) (A := A))))] :
    let T := affineAlgebraBaseChange (R := R) (A := A)
    let pSource := (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left
    let pTarget := (baseChangeSnd X T).left
    letI : Linear R (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left.Modules :=
      modulesLinear (RingHom.id R) pSource
    letI : Linear R (X ⨯ T).left.Modules := modulesLinear (algebraMap R A) pTarget
    letI : Linear R (SchemeDerivedCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) := inferInstance
    letI : Linear R (SchemeDerivedCategory (X ⨯ T).left) := inferInstance
    letI : Linear R (Dqc.SchemeQuasicoherentDerivedCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) := inferInstance
    letI : Linear R (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) := inferInstance
    Functor.Linear R P.functor := by
  let T := affineAlgebraBaseChange (R := R) (A := A)
  let pSource := (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left
  let pTarget := (baseChangeSnd X T).left
  letI : Linear R (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left.Modules :=
    modulesLinear (RingHom.id R) pSource
  letI : Linear R (X ⨯ T).left.Modules := modulesLinear (algebraMap R A) pTarget
  letI : Linear R (SchemeDerivedCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) := inferInstance
  letI : Linear R (SchemeDerivedCategory (X ⨯ T).left) := inferInstance
  letI : Linear R (Dqc.SchemeQuasicoherentDerivedCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) := inferInstance
  letI : Linear R (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) := inferInstance
  letI : Functor.Linear R P.ambient.functor := relativeAmbientPullback_linear X P
  apply (Functor.linear_iff R P.functor).2
  intro E r
  apply ObjectProperty.hom_ext
  change P.ambient.functor.map (r • 𝟙 E.obj) =
    r • 𝟙 (P.ambient.functor.obj E.obj)
  exact (Functor.linear_iff R P.ambient.functor).1 inferInstance E.obj r

private theorem relativeBoundedPullback_linear {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (X : SchemeBaseChange (Spec (CommRingCat.of R)))
    (P : DqcLeftDerivedPullback (baseChangeMap X
      (toIdentityBaseChange (affineAlgebraBaseChange (R := R) (A := A)))))
    (h : P.PreservesBoundedCoherent)
    [IsExactPullback (baseChangeMap X
      (toIdentityBaseChange (affineAlgebraBaseChange (R := R) (A := A))))] :
    let T := affineAlgebraBaseChange (R := R) (A := A)
    let pSource := (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left
    let pTarget := (baseChangeSnd X T).left
    letI : Linear R (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left.Modules :=
      modulesLinear (RingHom.id R) pSource
    letI : Linear R (X ⨯ T).left.Modules := modulesLinear (algebraMap R A) pTarget
    letI : Linear R (SchemeDerivedCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) := inferInstance
    letI : Linear R (SchemeDerivedCategory (X ⨯ T).left) := inferInstance
    letI : Linear R (Dqc.SchemeQuasicoherentDerivedCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) := inferInstance
    letI : Linear R (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) := inferInstance
    letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) := inferInstance
    letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) := inferInstance
    Functor.Linear R (P.boundedFunctor h) := by
  let T := affineAlgebraBaseChange (R := R) (A := A)
  let pSource := (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left
  let pTarget := (baseChangeSnd X T).left
  letI : Linear R (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left.Modules :=
    modulesLinear (RingHom.id R) pSource
  letI : Linear R (X ⨯ T).left.Modules := modulesLinear (algebraMap R A) pTarget
  letI : Linear R (SchemeDerivedCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) := inferInstance
  letI : Linear R (SchemeDerivedCategory (X ⨯ T).left) := inferInstance
  letI : Linear R (Dqc.SchemeQuasicoherentDerivedCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) := inferInstance
  letI : Linear R (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) := inferInstance
  letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) := inferInstance
  letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) := inferInstance
  letI : Functor.Linear R P.functor := relativeDqcPullback_linear X P
  apply (Functor.linear_iff R (P.boundedFunctor h)).2
  intro E r
  apply ObjectProperty.hom_ext
  change P.functor.map (r • 𝟙 E.obj) = r • 𝟙 (P.functor.obj E.obj)
  exact (Functor.linear_iff R P.functor).1 inferInstance E.obj r

/-- Relative bounded-coherent derived pullback is linear for the two affine-base
actions when the base is localized and pullback preserves the bounded-coherent locus. -/
theorem boundedFunctor_linearOfLocalization {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A]
    (X : SchemeBaseChange (Spec (CommRingCat.of R)))
    (P : DqcLeftDerivedPullback (baseChangeMap X
      (toIdentityBaseChange (affineAlgebraBaseChange (R := R) (A := A)))))
    (h : P.PreservesBoundedCoherent) :
    let T := affineAlgebraBaseChange (R := R) (A := A)
    let pSource := (baseChangeSnd X (identityBaseChange (Spec (CommRingCat.of R)))).left
    let pTarget := (baseChangeSnd X T).left
    letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) :=
      Dqc.boundedCoherentLinearOfAffineMap (RingHom.id R) pSource
    letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) :=
      Dqc.boundedCoherentLinearOfAffineMap (algebraMap R A) pTarget
    Functor.Linear R (P.boundedFunctor h) := by
  let T := affineAlgebraBaseChange (R := R) (A := A)
  let f := baseChangeMap X (toIdentityBaseChange T)
  letI : Flat f.left := relativeFlat M X
  letI : IsExactPullback f := isExactPullback_of_flat f
  exact relativeBoundedPullback_linear X P h

/-- Relative bounded-coherent pullback along an affine localization is additive.
Together with `boundedFunctor_linearOfLocalization`, this makes its actual
action on Hom groups available as `Functor.mapLinearMap` for the affine-base
scalar actions. This does not assert that those Hom maps are localizations. -/
theorem boundedFunctor_additiveOfLocalization {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A]
    (X : SchemeBaseChange (Spec (CommRingCat.of R)))
    (P : DqcLeftDerivedPullback (baseChangeMap X
      (toIdentityBaseChange (affineAlgebraBaseChange (R := R) (A := A)))))
    (h : P.PreservesBoundedCoherent) :
    (P.boundedFunctor h).Additive := by
  let T := affineAlgebraBaseChange (R := R) (A := A)
  let f := baseChangeMap X (toIdentityBaseChange T)
  letI : Flat f.left := relativeFlat M X
  letI : IsExactPullback f := isExactPullback_of_flat f
  letI : P.ambient.functor.Additive := by
    letI : (derivedPullback f).Additive := by
      change ((modulePullback f).mapDerivedCategory).Additive
      infer_instance
    exact Functor.additive_of_iso (P.ambient.exactComparison).symm
  letI : P.functor.Additive := by
    dsimp [DqcLeftDerivedPullback.functor]
    infer_instance
  dsimp [DqcLeftDerivedPullback.boundedFunctor]
  infer_instance

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

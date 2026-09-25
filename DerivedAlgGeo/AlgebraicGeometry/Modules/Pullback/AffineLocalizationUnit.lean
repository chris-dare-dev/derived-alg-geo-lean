/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.AffineSpec
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.FixedBaseSections
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.ScalarExtendedOpenSections
import DerivedAlgGeo.Algebra.Category.ModuleCat.Localization

/-!
# The affine pullback unit as localization

For a multiplicative set in a commutative ring, the actual top sections of
the pullback of a tilde module to the localized affine spectrum are naturally
the localization of its top sections. The comparison carries the localization
generator to the actual scheme-module pullback unit.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (S : Submonoid R)

/-- The localization of fixed-base top sections of a tilde module is naturally
the actual top sections of its scheme-module pullback to the localized spectrum. -/
def affineLocalizationTopNatIso :
    let A := CommRingCat.of (Localization S)
    let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization S))
    ((AlgebraicGeometry.tilde.functor R ⋙
        AlgebraicGeometry.fixedBaseSectionsFunctor (Spec R) (Scheme.ΓSpecIso R).inv ⊤) ⋙
      ModuleCat.localizedModuleFunctor S) ≅
    ((AlgebraicGeometry.tilde.functor R ⋙ pullback (Spec.map f)) ⋙
      AlgebraicGeometry.fixedBaseSectionsFunctor (Spec A) (Scheme.ΓSpecIso A).inv ⊤) := by
  let A := CommRingCat.of (Localization S)
  let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization S))
  let T := AlgebraicGeometry.tilde.functor R
  let G := AlgebraicGeometry.moduleSpecΓFunctor (R := R)
  let H := ModuleCat.localizedModuleFunctor S
  let E := ModuleCat.extendScalars f.hom
  let T' := AlgebraicGeometry.tilde.functor A
  let G' := AlgebraicGeometry.moduleSpecΓFunctor (R := A)
  let P := pullback (Spec.map f)
  change (T ⋙ G) ⋙ H ≅ (T ⋙ P) ⋙ G'
  calc
    (T ⋙ G) ⋙ H ≅ (𝟭 (ModuleCat.{u} R)) ⋙ H :=
      Functor.isoWhiskerRight (AlgebraicGeometry.tilde.toTildeΓNatIso (R := R)).symm H
    _ ≅ H := Functor.leftUnitor H
    _ ≅ E := (ModuleCat.extendScalarsLocalizationNatIso S).symm
    _ ≅ E ⋙ (𝟭 (ModuleCat.{u} A)) := (Functor.rightUnitor E).symm
    _ ≅ E ⋙ (T' ⋙ G') :=
      Functor.isoWhiskerLeft E (AlgebraicGeometry.tilde.toTildeΓNatIso (R := A))
    _ ≅ (E ⋙ T') ⋙ G' := (Functor.associator E T' G').symm
    _ ≅ (T ⋙ P) ⋙ G' :=
      Functor.isoWhiskerRight (pullbackSpecMapTildeIso f).symm G'

private theorem affineLocalizationTopNatIso_hom_app (M : ModuleCat.{u} R) :
    let A := CommRingCat.of (Localization S)
    let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization S))
    let H := ModuleCat.localizedModuleFunctor S
    let E := ModuleCat.extendScalars f.hom
    let G' := AlgebraicGeometry.moduleSpecΓFunctor (R := A)
    (affineLocalizationTopNatIso S).hom.app M =
      H.map (AlgebraicGeometry.tilde.isoTop M).inv ≫
      (ModuleCat.extendScalarsLocalizationNatIso S).inv.app M ≫
      (AlgebraicGeometry.tilde.isoTop (E.obj M)).hom ≫
      G'.map ((pullbackSpecMapTildeIso f).inv.app M) := by
  rfl

/-- The natural isomorphism sends the localization generator of a tilde section
to that section's image under the actual pullback adjunction unit. -/
theorem affineLocalizationTopNatIso_hom_localizedMk (M : ModuleCat.{u} R) (m : M) :
    let A := CommRingCat.of (Localization S)
    let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization S))
    ((affineLocalizationTopNatIso S).hom.app M).hom
        (((AlgebraicGeometry.fixedBaseSectionsFunctor (Spec R)
          (Scheme.ΓSpecIso R).inv ⊤).obj (AlgebraicGeometry.tilde M)).localizedModuleMkLinearMap S
          ((AlgebraicGeometry.tilde.isoTop M).hom m)) =
      (fixedBasePullbackTop (Scheme.ΓSpecIso R).inv (Spec.map f)
        (AlgebraicGeometry.tilde M)).hom ((AlgebraicGeometry.tilde.isoTop M).hom m) := by
  let A := CommRingCat.of (Localization S)
  let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization S))
  let G' := AlgebraicGeometry.moduleSpecΓFunctor (R := A)
  let β := pullbackSpecMapTildeIso f
  let q := G'.mapIso (β.app M)
  apply q.toLinearEquiv.injective
  change q.hom.hom
      (((affineLocalizationTopNatIso S).hom.app M).hom
        (((AlgebraicGeometry.fixedBaseSectionsFunctor (Spec R)
          (Scheme.ΓSpecIso R).inv ⊤).obj (AlgebraicGeometry.tilde M)).localizedModuleMkLinearMap S
          ((AlgebraicGeometry.tilde.isoTop M).hom m))) =
    q.hom.hom
      ((fixedBasePullbackTop (Scheme.ΓSpecIso R).inv (Spec.map f)
        (AlgebraicGeometry.tilde M)).hom ((AlgebraicGeometry.tilde.isoTop M).hom m))
  have hmate := pullbackSpecMapTildeIso_unit_apply f M m
  change q.hom.hom
      ((fixedBasePullbackTop (Scheme.ΓSpecIso R).inv (Spec.map f)
        (AlgebraicGeometry.tilde M)).hom ((AlgebraicGeometry.tilde.isoTop M).hom m)) =
    (AlgebraicGeometry.tilde.isoTop ((ModuleCat.extendScalars f.hom).obj M)).hom
      ((1 : A) ⊗ₜ[R] m) at hmate
  rw [hmate]
  have hloc :
      ((ModuleCat.localizedModuleFunctor S).map (AlgebraicGeometry.tilde.isoTop M).inv).hom
        (((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj
          (AlgebraicGeometry.tilde M)).localizedModuleMkLinearMap S
          ((AlgebraicGeometry.tilde.isoTop M).hom m)) =
      M.localizedModuleMkLinearMap S m := by
    change (IsLocalizedModule.mapExtendScalars S
      (((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj
        (AlgebraicGeometry.tilde M)).localizedModuleMkLinearMap S)
      (M.localizedModuleMkLinearMap S) (Localization S)
      (AlgebraicGeometry.tilde.isoTop M).inv.hom)
        (((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj
          (AlgebraicGeometry.tilde M)).localizedModuleMkLinearMap S
          ((AlgebraicGeometry.tilde.isoTop M).hom m)) = _
    rw [IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]
    change M.localizedModuleMkLinearMap S
      ((AlgebraicGeometry.tilde.isoTop M).inv.hom
        ((AlgebraicGeometry.tilde.isoTop M).hom m)) = _
    rw [Iso.hom_inv_id_apply]
  have hγ :
      ((ModuleCat.extendScalarsLocalizationNatIso S).inv.app M).hom
        (M.localizedModuleMkLinearMap S m) =
          (show (ModuleCat.extendScalars (algebraMap R (Localization S))).obj M from
            (1 : Localization S) ⊗ₜ[R] m) := by
    change (ModuleCat.extendScalarsLocalizationIso S M).inv.hom
      (M.localizedModuleMkLinearMap S m) = _
    rw [← ModuleCat.extendScalarsLocalizationIso_hom_tmul S M m]
    exact Iso.hom_inv_id_apply (ModuleCat.extendScalarsLocalizationIso S M) _
  rw [affineLocalizationTopNatIso_hom_app]
  change q.hom.hom (q.inv.hom
      ((AlgebraicGeometry.tilde.isoTop ((ModuleCat.extendScalars f.hom).obj M)).hom
        (((ModuleCat.extendScalarsLocalizationNatIso S).inv.app M).hom
          (((ModuleCat.localizedModuleFunctor S).map
            (AlgebraicGeometry.tilde.isoTop M).inv).hom
            (((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj
              (AlgebraicGeometry.tilde M)).localizedModuleMkLinearMap S
              ((AlgebraicGeometry.tilde.isoTop M).hom m)))))) = _
  rw [Iso.inv_hom_id_apply, hloc, hγ]

/-- The compatibility holds for every top section, since `tilde.isoTop` is an
isomorphism. Thus the actual pullback unit is the localization generator under
the natural isomorphism, rather than only on a chosen presentation of sections. -/
theorem affineLocalizationTopNatIso_hom_localizedMk_section
    (M : ModuleCat.{u} R)
    (x : (AlgebraicGeometry.fixedBaseSectionsFunctor (Spec R)
      (Scheme.ΓSpecIso R).inv ⊤).obj (AlgebraicGeometry.tilde M)) :
    let A := CommRingCat.of (Localization S)
    let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization S))
    ((affineLocalizationTopNatIso S).hom.app M).hom
        (((AlgebraicGeometry.fixedBaseSectionsFunctor (Spec R)
          (Scheme.ΓSpecIso R).inv ⊤).obj (AlgebraicGeometry.tilde M)).localizedModuleMkLinearMap S
          x) =
      (fixedBasePullbackTop (Scheme.ΓSpecIso R).inv (Spec.map f)
        (AlgebraicGeometry.tilde M)).hom x := by
  let m : M := (AlgebraicGeometry.tilde.isoTop M).inv.hom x
  have hx : (AlgebraicGeometry.tilde.isoTop M).hom m = x :=
    Iso.inv_hom_id_apply (AlgebraicGeometry.tilde.isoTop M) x
  simpa only [hx] using affineLocalizationTopNatIso_hom_localizedMk S M m

/-- On a localization square of affine spectra, the localization generator
comparison is the square-specialized actual pullback unit on top sections. -/
theorem affineLocalizationTopNatIso_hom_localizedMk_square
    (M : ModuleCat.{u} R)
    (x : (AlgebraicGeometry.fixedBaseSectionsFunctor (Spec R)
      (Scheme.ΓSpecIso R).inv ⊤).obj (AlgebraicGeometry.tilde M)) :
    let A := CommRingCat.of (Localization S)
    let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization S))
    ((affineLocalizationTopNatIso S).hom.app M).hom
        (((AlgebraicGeometry.fixedBaseSectionsFunctor (Spec R)
          (Scheme.ΓSpecIso R).inv ⊤).obj (AlgebraicGeometry.tilde M)).localizedModuleMkLinearMap S
          x) =
      (fixedBasePullbackOpenOfIsPullback (Spec.map f) (AlgebraicGeometry.tilde M) f
        (𝟙 (Spec R)) (𝟙 (Spec A)) IsPullback.of_id_snd ⊤).hom
          ((1 : A) ⊗ₜ[R] x) := by
  let A := CommRingCat.of (Localization S)
  let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization S))
  calc
    _ = (fixedBasePullbackTop (Scheme.ΓSpecIso R).inv (Spec.map f)
          (AlgebraicGeometry.tilde M)).hom x :=
      affineLocalizationTopNatIso_hom_localizedMk_section S M x
    _ = (((pullbackPushforwardAdjunction (Spec.map f)).unit.app
          (AlgebraicGeometry.tilde M)).app ⊤) x :=
      fixedBasePullbackTop_apply (Scheme.ΓSpecIso R).inv (Spec.map f)
        (AlgebraicGeometry.tilde M) x
    _ = _ := by
      exact (fixedBasePullbackOpenOfIsPullback_one_tmul
        (Spec.map f) (AlgebraicGeometry.tilde M) f
        (𝟙 (Spec R)) (𝟙 (Spec A)) IsPullback.of_id_snd ⊤ x).symm

end AlgebraicGeometry.Scheme.Modules

end

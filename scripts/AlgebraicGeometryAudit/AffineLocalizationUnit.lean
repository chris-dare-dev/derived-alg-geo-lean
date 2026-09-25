import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.AffineLocalizationUnit

/-!
# Affine localization of the actual top-section pullback unit

The natural comparison is functorial in the module and carries the canonical
localization generator to the actual pullback unit. No Noetherian, finiteness,
or derived hypothesis is used.
-/

open CategoryTheory AlgebraicGeometry

universe u

#print axioms AlgebraicGeometry.Scheme.Modules.affineLocalizationTopNatIso
#print axioms AlgebraicGeometry.Scheme.Modules.affineLocalizationTopNatIso_hom_localizedMk
#print axioms AlgebraicGeometry.Scheme.Modules.affineLocalizationTopNatIso_hom_localizedMk_section
#print axioms AlgebraicGeometry.Scheme.Modules.affineLocalizationTopNatIso_hom_localizedMk_square

-- `CommRingCat` ranges over arbitrary commutative rings, without finiteness assumptions.
example {R : CommRingCat.{u}} (S : Submonoid R)
    (M : ModuleCat.{u} R) (m : M) :
    let A := CommRingCat.of (Localization S)
    let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization S))
    ((Scheme.Modules.affineLocalizationTopNatIso (R := R) S).hom.app M).hom
        (((fixedBaseSectionsFunctor (Spec R) (Scheme.ΓSpecIso R).inv ⊤).obj
          (tilde M)).localizedModuleMkLinearMap S ((tilde.isoTop M).hom m)) =
      (Scheme.Modules.fixedBasePullbackTop (Scheme.ΓSpecIso R).inv
        (Spec.map f) (tilde M)).hom ((tilde.isoTop M).hom m) := by
  exact Scheme.Modules.affineLocalizationTopNatIso_hom_localizedMk S M m

-- The comparison is natural, not a family of unrelated object isomorphisms.
example {R : CommRingCat.{u}} (S : Submonoid R)
    {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    let A := CommRingCat.of (Localization S)
    let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization S))
    ((tilde.functor R ⋙ fixedBaseSectionsFunctor (Spec R)
      (Scheme.ΓSpecIso R).inv ⊤) ⋙ ModuleCat.localizedModuleFunctor S).map g ≫
      (Scheme.Modules.affineLocalizationTopNatIso S).hom.app N =
    (Scheme.Modules.affineLocalizationTopNatIso S).hom.app M ≫
      ((tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f)) ⋙
        fixedBaseSectionsFunctor (Spec A) (Scheme.ΓSpecIso A).inv ⊤).map g := by
  exact (Scheme.Modules.affineLocalizationTopNatIso S).hom.naturality g

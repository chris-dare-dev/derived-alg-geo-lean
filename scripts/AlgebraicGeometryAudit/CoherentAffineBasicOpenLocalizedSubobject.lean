import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenLocalizedSubobject

/-! # Actual-basic-open coherent localized-subobject audit and direct clients -/

open CategoryTheory AlgebraicGeometry

universe u

#print axioms AlgebraicGeometry.Coh.basicOpenCoherentSubobject
#print axioms AlgebraicGeometry.Coh.basicOpenCoherentSubobject_eq_localizedSpectrum
#print axioms AlgebraicGeometry.Coh.basicOpenCoherentSubobject_subobjectModule

-- The chosen presentation may be the canonical affine global sections of E.
-- The affine-equivalence unit supplies the comparison with its coherent tilde.
example {R : CommRingCat.{u}} [IsNoetherianRing R] (r : R)
    (E : Coh (Spec R)) :
    let M : FGModuleCat.{u} R := (Coh.affineEquivalence (R := R)).functor.obj E
    ∀ (N : Submodule R M.obj) (hN : N.FG),
      ModuleCat.subobjectModule
          ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj)
          (Coh.basicOpenCoherentSubobject r M E
            ((Coh.affineEquivalence (R := R)).unitIso.app E) N hN) =
        N.localized' (Localization.Away r) (Submonoid.powers r)
          (M.obj.localizedModuleMkLinearMap (Submonoid.powers r)) := by
  intro M N hN
  exact Coh.basicOpenCoherentSubobject_subobjectModule r M E
    ((Coh.affineEquivalence (R := R)).unitIso.app E) N hN

-- The comparison is callable through ordinary imported API, not a scoped instance.
example {R : CommRingCat.{u}} [IsNoetherianRing R] (r : R)
    (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    Coh.basicOpenCoherentSubobject r M E cR N hN =
      Coh.localizedSpectrumCoherentSubobject r M E cR N hN := by
  exact Coh.basicOpenCoherentSubobject_eq_localizedSpectrum r M E cR N hN

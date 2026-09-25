import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.LocalizedSubobject

/-! # Localized-spectrum coherent subobject audit and direct clients -/

open CategoryTheory AlgebraicGeometry

universe u

#print axioms AlgebraicGeometry.Coh.localizedSpectrumGlobalSectionsNatIso
#print axioms AlgebraicGeometry.Coh.localizedSpectrumGlobalSectionsIso
#print axioms AlgebraicGeometry.Coh.coherentTildeSubobject
#print axioms AlgebraicGeometry.Coh.localizedSpectrumSubobject
#print axioms AlgebraicGeometry.Coh.localizedSpectrumSubobject_subobjectModule
#print axioms AlgebraicGeometry.Coh.localizedSpectrumCoherentSubobject
#print axioms AlgebraicGeometry.Coh.localizedSpectrumCoherentSubobject_subobjectModule
#print axioms AlgebraicGeometry.Coh.localizedSpectrumCoherentSubobject_globalSections

-- Canonical `M = Γ(E)` client. The affine-equivalence unit, not a carrier cast,
-- identifies the coherent target with the tilde of its finite global sections.
example {R : CommRingCat.{u}} [IsNoetherianRing R] (r : R)
    (E : Coh (Spec R)) :
    let M : FGModuleCat.{u} R := (Coh.affineEquivalence (R := R)).functor.obj E
    ∀ (N : Submodule R M.obj) (hN : N.FG),
      ModuleCat.subobjectModule
          ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj)
          (Coh.localizedSpectrumCoherentSubobject r M E
            ((Coh.affineEquivalence (R := R)).unitIso.app E) N hN) =
        N.localized' (Localization.Away r) (Submonoid.powers r)
          (M.obj.localizedModuleMkLinearMap (Submonoid.powers r)) := by
  exact Coh.localizedSpectrumCoherentSubobject_globalSections r E

-- A chosen affine presentation has a coherent mono before pullback, and the
-- localized-spectrum result is callable without opening any scoped instances.
example {R : CommRingCat.{u}} [IsNoetherianRing R] (r : R)
    (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    Nonempty (Subobject E) ∧
      ModuleCat.subobjectModule
          ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj)
          (Coh.localizedSpectrumCoherentSubobject r M E cR N hN) =
        N.localized' (Localization.Away r) (Submonoid.powers r)
          (M.obj.localizedModuleMkLinearMap (Submonoid.powers r)) := by
  exact ⟨⟨Coh.coherentTildeSubobject M E cR N hN⟩,
    Coh.localizedSpectrumCoherentSubobject_subobjectModule r M E cR N hN⟩

import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenSubobjectClassification

/-! # SF11.4bp one-chart arbitrary-mono classification audit and clients -/

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

#print axioms AlgebraicGeometry.Coh.basicOpenGlobalSectionsIso
#print axioms AlgebraicGeometry.Coh.exists_tilde_subobject_pullbackBasicOpen
#print axioms AlgebraicGeometry.Coh.exists_coherentTildeSubobject_pullbackBasicOpen
#print axioms AlgebraicGeometry.Coh.exists_coherentTildeSubobject_pullbackBasicOpen_globalSections

-- The target transport is available from the ordinary imported owner leaf.
example {R : CommRingCat.{u}} [IsNoetherianRing R] (r : R)
    (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M) :
    let A := Localization.Away r
    let e := basicOpenIsoSpecAway r
    let β := Coh.pullbackEquivalence e
    let j := Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)
    let G := Coh.pullback j
    let EA := Coh.affineEquivalence (R := CommRingCat.of A)
    let J : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := (ModuleCat.isFG A).ι
    let Hloc : ModuleCat.{u} R ⥤ ModuleCat.{u} A :=
      ModuleCat.localizedModuleFunctor (Submonoid.powers r)
    J.obj (EA.functor.obj (β.inverse.obj (G.obj E))) ≅ Hloc.obj M.obj :=
  Coh.basicOpenGlobalSectionsIso r M E cR

-- A prescribed mono, with no regularity assumption on r, is represented by
-- the restriction of a concrete tilde subobject of canonical Γ(E).
example {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (E : Coh (Spec R))
    (Z : Coh (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)))
    (β : Z ⟶ (Coh.pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj E)
    [Mono β] :
    let ER := Coh.affineEquivalence (R := R)
    let M : FGModuleCat.{u} R := ER.functor.obj E
    let G := Coh.pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))
    ∃ (N : Submodule R M.obj) (hN : N.FG),
      let P := Coh.coherentTildeSubobject M E (ER.unitIso.app E) N hN
      (∃ e : Z ≅ G.obj P, β = e.hom ≫ G.map P.arrow) ∧
        ModuleCat.subobjectModule
            ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj)
            (Coh.basicOpenCoherentSubobject r M E (ER.unitIso.app E) N hN) =
          N.localized' (Localization.Away r) (Submonoid.powers r)
            (M.obj.localizedModuleMkLinearMap (Submonoid.powers r)) :=
  Coh.exists_coherentTildeSubobject_pullbackBasicOpen_globalSections r E Z β

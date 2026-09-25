import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ModuleCatLocalization

/-! Axiom audit and direct clients for the exact derived ModuleCat localization mate. -/

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

#print axioms ModuleCat.extendScalarsLocalizationDerived
#print axioms ModuleCat.localizedModuleDerived
#print axioms ModuleCat.extendScalarsLocalizationDerivedNatIso
#print axioms ModuleCat.extendScalarsLocalizationDerivedNatIso_naturality

noncomputable section

universe u

variable {R : Type u} [CommRing R] (S : Submonoid R)
  {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y)

-- The comparison accepts an arbitrary derived arrow, not only a complex map.
example :
    (ModuleCat.extendScalarsLocalizationDerived S).map f ≫
        (ModuleCat.extendScalarsLocalizationDerivedNatIso S).hom.app Y =
      (ModuleCat.extendScalarsLocalizationDerivedNatIso S).hom.app X ≫
        (ModuleCat.localizedModuleDerived S).map f :=
  ModuleCat.extendScalarsLocalizationDerivedNatIso_naturality S f

-- A downstream client can use the isomorphism on an arbitrary derived object.
example :
    (ModuleCat.extendScalarsLocalizationDerived S).obj X ≅
      (ModuleCat.localizedModuleDerived S).obj X :=
  (ModuleCat.extendScalarsLocalizationDerivedNatIso S).app X

end

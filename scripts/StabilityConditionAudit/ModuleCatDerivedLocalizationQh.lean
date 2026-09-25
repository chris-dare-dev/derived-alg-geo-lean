import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ModuleCatLocalizationQh
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyLocalization

/-! Axiom audit and direct client for the `Qh` module-localization mate. -/

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

#print axioms ModuleCat.extendScalarsLocalizationDerivedFactorsh
#print axioms ModuleCat.extendScalarsLocalizationDerivedNatIso_Qh

noncomputable section

universe u

variable {R : Type u} [CommRing R] (S : Submonoid R)
  (K : CochainComplex (ModuleCat.{u} R) ℤ)

-- The Hom-complex comparison is the localization factorsh component.
example :
    (ModuleCat.extendScalarsLocalizationDerivedNatIso S).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫
      (CochainComplex.HomComplex.derivedLocalizationComparison S K).hom =
    (ModuleCat.extendScalarsLocalizationDerivedFactorsh S K).hom ≫
      DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((ModuleCat.extendScalarsLocalizationCochainNatIso S).hom.app K)) :=
  ModuleCat.extendScalarsLocalizationDerivedNatIso_Qh S K

end

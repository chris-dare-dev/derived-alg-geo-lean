/-
Audit and direct clients for the canonical `ModuleCat` scalar-extension/
localized-module functor comparison.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat
import Mathlib.Algebra.Homology.DerivedCategory.Basic

#print axioms ModuleCat.extendScalarsLocalizationIso
#print axioms ModuleCat.extendScalarsLocalizationIso_hom_tmul
#print axioms ModuleCat.extendScalarsLocalizationNatIso
#print axioms ModuleCat.extendScalarsLocalizationCochainNatIso

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

variable {R : Type u} [CommRing R] (S : Submonoid R)

-- A direct client of the natural transformation on the localization generator.
example (M : ModuleCat.{u} R) (m : M) :
    (ModuleCat.extendScalarsLocalizationNatIso S).hom.app M
        ((1 : Localization S) ⊗ₜ[R] m) =
      M.localizedModuleMkLinearMap S m :=
  ModuleCat.extendScalarsLocalizationIso_hom_tmul S M m

-- The same comparison is available to an arbitrary cochain complex.
example (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars (algebraMap R (Localization S))).mapHomologicalComplex
      (.up ℤ)).obj K ≅
      ((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex (.up ℤ)).obj K :=
  (ModuleCat.extendScalarsLocalizationCochainNatIso S).app K

-- Applying ordinary functors to the complex isomorphism gives a derived-object
-- isomorphism. This does not compare derived-category Hom localization maps.
example (K : CochainComplex (ModuleCat.{u} R) ℤ)
    [HasDerivedCategory (ModuleCat.{u} (Localization S))] :
    (DerivedCategory.Qh).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((ModuleCat.extendScalars (algebraMap R (Localization S))).mapHomologicalComplex
            (.up ℤ)).obj K)) ≅
      (DerivedCategory.Qh).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex (.up ℤ)).obj K)) := by
  exact (DerivedCategory.Qh).mapIso
    ((HomotopyCategory.quotient _ (.up ℤ)).mapIso
      ((ModuleCat.extendScalarsLocalizationCochainNatIso S).app K))

end

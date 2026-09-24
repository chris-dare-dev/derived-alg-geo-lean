/-
Generic module-localization slice of the AlgebraicGeometry audit. Despite the
audit's historical name, `EnumDecls` routes the repository's `Algebra` root to
this audit.
-/
import DerivedAlgGeo.Algebra.Module.Localization
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! ## Localization and kernels of modules -/

#print axioms LinearMap.kerMap
#print axioms IsLocalizedModule.kerMap
#print axioms IsLocalizedModule.kernelMap
#print axioms IsLocalizedModule.kernelNatTrans

/-! ## Finite module descent through localization -/

#print axioms Module.exists_finite_submodule_of_isLocalization
#print axioms Module.exists_finitely_presented_submodule_of_isLocalization
#print axioms Module.exists_finite_submodule_of_isLocalization_containing
#print axioms Module.exists_finitely_presented_submodule_of_isLocalization_containing
#print axioms Module.exists_finite_submodules_of_isLocalization_map
#print axioms Module.exists_finite_submodules_of_isLocalization_two_maps

/-! ## Fixed-target arrows over a localized ring -/

#print axioms Module.exists_finitely_presented_fixedTargetArrow_of_isLocalization

/-! ## Three-term descent with a fixed terminal module -/

#print axioms Module.exists_finitely_presented_fixedTerminalThreeTerm_of_isLocalization

/-! ## Cohomology of a localized three-term complex -/

#print axioms IsLocalizedModule.boundaryToCycles
#print axioms IsLocalizedModule.localizedDifferential
#print axioms IsLocalizedModule.localizedCyclesMap
#print axioms IsLocalizedModule.localizedBoundaryToCycles
#print axioms IsLocalizedModule.cohomologyMap
#print axioms IsLocalizedModule.cohomologyMap_isLocalized

/-! ## Tensor extension versus canonical module localization -/

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

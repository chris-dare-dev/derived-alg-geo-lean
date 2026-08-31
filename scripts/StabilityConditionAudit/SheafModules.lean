/-
Generic module-sheaf slice of the StabilityCondition audit. Despite the audit's
historical name, this slice covers category-theoretic infrastructure independent
of schemes.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules

/-! ## Transporting finite presentations on a ringed site -/

#print axioms SheafOfModules.Presentation.isFinite_of_isIso
#print axioms SheafOfModules.Presentation.isFinite_map
#print axioms SheafOfModules.Presentation.isFinitePresentation_quasicoherentData
#print axioms SheafOfModules.IsFinitePresentation.of_presentation

/-! ## Exactness of the forgetful functor to abelian sheaves -/

#print axioms SheafOfModules.preservesFiniteColimits_toSheaf
#print axioms SheafOfModules.preservesFiniteColimits_toSheaf'
#print axioms SheafOfModules.preservesEpimorphisms_toSheaf
#print axioms SheafOfModules.shortExact_map_toSheaf
#print axioms SheafOfModules.epi_of_isLocallySurjective
#print axioms SheafOfModules.reflectsEpimorphisms_toSheaf

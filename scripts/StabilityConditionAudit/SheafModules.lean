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

/-! ## Restricting presentations on over sites -/

#print axioms SheafOfModules.Presentation.over
#print axioms SheafOfModules.GeneratingSections.over
#print axioms SheafOfModules.GeneratingSections.isFiniteType_over
#print axioms SheafOfModules.QuasicoherentData.presentationOver
#print axioms SheafOfModules.QuasicoherentData.presentationOver_generators_I
#print axioms SheafOfModules.QuasicoherentData.presentationOver_relations_I
#print axioms SheafOfModules.QuasicoherentData.over
#print axioms SheafOfModules.instHasBinaryProductsOver_derivedAlgGeo

/-! ## Isomorphism invariance and locality of finite presentation -/

#print axioms SheafOfModules.QuasicoherentData.ofIso
#print axioms SheafOfModules.QuasicoherentData.isFinitePresentation_ofIso
#print axioms SheafOfModules.IsFinitePresentation.of_iso
#print axioms SheafOfModules.isFinitePresentation_isClosedUnderIsomorphisms
#print axioms SheafOfModules.QuasicoherentData.isFinitePresentation_over
#print axioms SheafOfModules.IsFinitePresentation.over
#print axioms SheafOfModules.IsFinitePresentation.of_coversTop
#print axioms SheafOfModules.instHasBinaryProductsOver_derivedAlgGeo_1

/-! ## Exactness of the forgetful functor to abelian sheaves -/

#print axioms SheafOfModules.preservesFiniteColimits_toSheaf
#print axioms SheafOfModules.preservesFiniteColimits_toSheaf'
#print axioms SheafOfModules.preservesEpimorphisms_toSheaf
#print axioms SheafOfModules.shortExact_map_toSheaf
#print axioms SheafOfModules.epi_of_isLocallySurjective
#print axioms SheafOfModules.reflectsEpimorphisms_toSheaf

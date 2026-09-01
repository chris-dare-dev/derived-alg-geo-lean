/-
Generic module-sheaf slice of the StabilityCondition audit. Despite the audit's
historical name, this slice covers category-theoretic infrastructure independent
of schemes.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules

/-! ## Generating sections from free epimorphisms -/

#print axioms SheafOfModules.GeneratingSections.ofFreeEpi
#print axioms SheafOfModules.GeneratingSections.isFiniteType_ofFreeEpi
#print axioms SheafOfModules.GeneratingSections.ofFreeEpi_π

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

/-! ## Zero objects and short-exact extensions of finite presentation -/

#print axioms SheafOfModules.isFinitePresentation_containsZero
#print axioms SheafOfModules.simultaneousImageCover
#print axioms SheafOfModules.simultaneousImageCover_mem
#print axioms SheafOfModules.simultaneousImageCoverObjects
#print axioms SheafOfModules.simultaneousImageCoverObjects_coversTop
#print axioms SheafOfModules.sectionOfInitial
#print axioms SheafOfModules.sectionOfInitial_eval
#print axioms SheafOfModules.overSection
#print axioms SheafOfModules.overSection_eval_mkId
#print axioms SheafOfModules.overSection_ext
#print axioms SheafOfModules.overUnitIso
#print axioms SheafOfModules.unitToPushforwardObjUnit_over
#print axioms SheafOfModules.freeHomEquiv_mapFree_over
#print axioms SheafOfModules.localLift
#print axioms SheafOfModules.localLift_comp
#print axioms SheafOfModules.Presentation.mapOver
#print axioms SheafOfModules.Presentation.mapOver_isFinite
#print axioms SheafOfModules.Presentation.relationMap
#print axioms SheafOfModules.Presentation.relationMap_presentationOfIsCokernelFree
#print axioms SheafOfModules.Presentation.relationMap_mapOver
#print axioms SheafOfModules.Presentation.freeMap_inl_freeSumIso_inv
#print axioms SheafOfModules.Presentation.freeMap_inl_freeSumIso_inv_assoc
#print axioms SheafOfModules.Presentation.freeMap_inr_freeSumIso_inv
#print axioms SheafOfModules.Presentation.freeMap_inr_freeSumIso_inv_assoc
#print axioms SheafOfModules.Presentation.correction
#print axioms SheafOfModules.Presentation.correction_comp
#print axioms SheafOfModules.Presentation.correction_comp_assoc
#print axioms SheafOfModules.Presentation.extensionGeneratorsMap
#print axioms SheafOfModules.Presentation.extensionRelationLeft
#print axioms SheafOfModules.Presentation.extensionRelationRight
#print axioms SheafOfModules.Presentation.extensionRelationsMap
#print axioms SheafOfModules.Presentation.epi_extensionGeneratorsMap
#print axioms SheafOfModules.Presentation.extensionKernelToRightRelations
#print axioms SheafOfModules.Presentation.extensionRelationRight_comp_kernelToRightRelations
#print axioms SheafOfModules.Presentation.extensionLeftRelationsToKernel
#print axioms SheafOfModules.Presentation.extensionLeftRelationsToKernel_comp_kernelToRightRelations
#print axioms SheafOfModules.Presentation.extensionKernelOfRightRelationsToLeftRelations
#print axioms SheafOfModules.Presentation.extensionKernelOfRightRelationsToLeftRelations_comp
#print axioms SheafOfModules.Presentation.extensionRelationLeft_eq
#print axioms SheafOfModules.Presentation.epi_extensionKernelToRightRelations
#print axioms SheafOfModules.Presentation.epi_extensionRelationsMap
#print axioms SheafOfModules.Presentation.extension
#print axioms SheafOfModules.Presentation.extension_isFinite
#print axioms SheafOfModules.overFunctor_preservesZeroMorphisms
#print axioms SheafOfModules.ShortExact.map_over
#print axioms SheafOfModules.Presentation.correction_mapOver
#print axioms SheafOfModules.mapOver_lift_comp
#print axioms SheafOfModules.localLift_comp_mapOver
#print axioms SheafOfModules.localLift_mapOver_generators_comp
#print axioms SheafOfModules.IsFinitePresentation.middle_of_presentations_of_generatorLift
#print axioms SheafOfModules.IsFinitePresentation.middle_of_presentations
#print axioms SheafOfModules.IsFinitePresentation.middle_of_shortExact
#print axioms SheafOfModules.isFinitePresentation_isClosedUnderExtensions
#print axioms SheafOfModules.instAbelianSheafAddCommGrpCat_derivedAlgGeo
#print axioms SheafOfModules.instNonPreadditiveAbelianSheafAddCommGrpCat_derivedAlgGeo
#print axioms SheafOfModules.Presentation.instNonPreadditiveAbelian_derivedAlgGeo
#print axioms SheafOfModules.instHasBinaryProductsOver_derivedAlgGeo_2

/-! ## Exactness of the forgetful functor to abelian sheaves -/

#print axioms SheafOfModules.preservesFiniteColimits_toSheaf
#print axioms SheafOfModules.preservesFiniteColimits_toSheaf'
#print axioms SheafOfModules.preservesEpimorphisms_toSheaf
#print axioms SheafOfModules.shortExact_map_toSheaf
#print axioms SheafOfModules.epi_of_isLocallySurjective
#print axioms SheafOfModules.reflectsEpimorphisms_toSheaf

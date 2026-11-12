/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites

/-!
Audit records for the generic stack-in-groupoids root.

The module, declarations, and audit ownership are neutral category theory.
-/

#print axioms CategoryTheory.StackInGroupoids
#print axioms CategoryTheory.StackInGroupoids.CechDescent
#print axioms CategoryTheory.StackInGroupoids.Cover
#print axioms CategoryTheory.StackInGroupoids.Cover.hom
#print axioms CategoryTheory.StackInGroupoids.Cover.index
#print axioms CategoryTheory.StackInGroupoids.Cover.mem
#print axioms CategoryTheory.StackInGroupoids.Cover.mk.inj
#print axioms CategoryTheory.StackInGroupoids.Cover.mk.sizeOf_spec
#print axioms CategoryTheory.StackInGroupoids.Cover.obj
#print axioms CategoryTheory.StackInGroupoids.cechDescentEquivalence
#print axioms CategoryTheory.StackInGroupoids.essSurjToCechDescent
#print axioms CategoryTheory.StackInGroupoids.fiberIsGroupoid
#print axioms CategoryTheory.StackInGroupoids.fullyFaithfulToCechDescent
#print axioms CategoryTheory.StackInGroupoids.presheaf_obj_isGroupoid
#print axioms CategoryTheory.StackInGroupoids.presheaf_isStack
#print axioms CategoryTheory.StackInGroupoids.isStack
#print axioms CategoryTheory.StackInGroupoids.mk.inj
#print axioms CategoryTheory.StackInGroupoids.mk.sizeOf_spec
#print axioms CategoryTheory.StackInGroupoids.ofEquivalence
#print axioms CategoryTheory.StackInGroupoids.presheaf
#print axioms CategoryTheory.StackInGroupoids.toCechDescent
#print axioms CategoryTheory.StackMorphism
#print axioms CategoryTheory.StackMorphism.FiberCategory
#print axioms CategoryTheory.StackMorphism.FiberRepresentation
#print axioms CategoryTheory.StackMorphism.FiberRepresentation.fiberEquivalence
#print axioms CategoryTheory.StackMorphism.FiberRepresentation.mk.inj
#print axioms CategoryTheory.StackMorphism.FiberRepresentation.mk.sizeOf_spec
#print axioms CategoryTheory.StackMorphism.FiberRepresentation.representing
#print axioms CategoryTheory.StackMorphism.IsRepresentable
#print axioms CategoryTheory.StackMorphism.IsRepresentable.representation
#print axioms CategoryTheory.StackMorphism.app
#print axioms CategoryTheory.StackMorphism.comp
#print axioms CategoryTheory.StackMorphism.id
#print axioms CategoryTheory.StackMorphism.Modification
#print axioms CategoryTheory.StackMorphism.pullbackIso
#print axioms CategoryTheory.discretePseudofunctor
#print axioms CategoryTheory.discretePseudofunctor_isStack
#print axioms CategoryTheory.discretePseudofunctor_obj_isDiscrete
#print axioms CategoryTheory.discretePseudofunctor_obj_isGroupoid
#print axioms CategoryTheory.stackInGroupoidsOfSheaf
#print axioms CategoryTheory.Pseudofunctor.IsStack.of_le
#print axioms CategoryTheory.StackInGroupoids.ofLE
#print axioms CategoryTheory.StackInGroupoids.ofLE_presheaf
#print axioms CategoryTheory.StackInGroupoids.Cover.ofLE
#print axioms CategoryTheory.StackInGroupoids.Cover.ofLE_index
#print axioms CategoryTheory.StackInGroupoids.Cover.ofLE_obj
#print axioms CategoryTheory.StackInGroupoids.Cover.ofLE_hom

#print axioms CategoryTheory.discretePseudofunctorMap
#print axioms CategoryTheory.StackInGroupoids.discreteMap
#print axioms CategoryTheory.StackInGroupoids.representable
#print axioms CategoryTheory.StackInGroupoids.representableMap
#print axioms CategoryTheory.StackInGroupoids.representableMap_app_obj
#print axioms CategoryTheory.StackInGroupoids.representable_ofLE
#print axioms CategoryTheory.stackInGroupoidsOfSheaf_ofLE
#print axioms CategoryTheory.StackInGroupoids.discreteMap_app_obj

#print axioms CategoryTheory.Pseudofunctor.DescentData.map
#print axioms CategoryTheory.Pseudofunctor.DescentData.map_obj_obj
#print axioms CategoryTheory.Pseudofunctor.DescentData.map_obj_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.map_map_hom
#print axioms CategoryTheory.Pseudofunctor.toDescentDataCompMapIso
#print axioms CategoryTheory.Pseudofunctor.toDescentDataCompMapIso_hom_app_hom
#print axioms CategoryTheory.Pseudofunctor.toDescentDataCompMapIso_inv_app_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.mapId
#print axioms CategoryTheory.Pseudofunctor.DescentData.mapId_hom_app_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.mapId_inv_app_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.mapComp
#print axioms CategoryTheory.Pseudofunctor.DescentData.mapComp_hom_app_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.mapComp_inv_app_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.mapIso
#print axioms CategoryTheory.Pseudofunctor.DescentData.mapIso_hom_app_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.mapIso_inv_app_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.faithful_map
#print axioms CategoryTheory.Pseudofunctor.DescentData.full_map
#print axioms CategoryTheory.Pseudofunctor.DescentData.isEquivalence_map
#print axioms CategoryTheory.Pseudofunctor.isPrestack_iff_of_isEquivalence
#print axioms CategoryTheory.Pseudofunctor.isStack_iff_of_isEquivalence
#print axioms CategoryTheory.Pseudofunctor.isStack_iff_of_equivalence

#print axioms CategoryTheory.Pseudofunctor.DescentData.coreEquivalence
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreEquivalence_counitIso
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreEquivalence_functor
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreEquivalence_inverse
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreEquivalence_unitIso
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreFunctor
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreFunctor_map_iso
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreFunctor_obj_of_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreFunctor_obj_of_obj
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreInverse
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreInverse_map_hom_iso_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreInverse_map_hom_iso_inv
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreInverse_obj_hom_iso
#print axioms CategoryTheory.Pseudofunctor.DescentData.coreInverse_obj_obj_of
#print axioms CategoryTheory.Pseudofunctor.DescentData.toDescentDataCompCoreEquivalenceFunctorIso
#print axioms CategoryTheory.Pseudofunctor.DescentData.toDescentDataCompCoreEquivalenceFunctorIso_hom_app_iso_hom_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.toDescentDataCompCoreEquivalenceFunctorIso_hom_app_iso_inv_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.toDescentDataCompCoreEquivalenceFunctorIso_inv_app_iso_hom_hom
#print axioms CategoryTheory.Pseudofunctor.DescentData.toDescentDataCompCoreEquivalenceFunctorIso_inv_app_iso_inv_hom
#print axioms CategoryTheory.Pseudofunctor.isStack_core
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.IsLocal
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.IsLocal.of_le
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.IsLocal.of_sieve
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.IsLocal.toIsClosedUnderMapObj
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.core_isLocal
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.isLocal_top
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.isStack_fullsubcategory

#print axioms CategoryTheory.StackInGroupoids.ofStack
#print axioms CategoryTheory.StackInGroupoids.ofStack_presheaf
#print axioms CategoryTheory.StackInGroupoids.ofObjectProperty
#print axioms CategoryTheory.StackInGroupoids.ofObjectProperty_presheaf
#print axioms CategoryTheory.StackInGroupoids.ofObjectPropertyι
#print axioms CategoryTheory.StackInGroupoids.ofObjectPropertyMap

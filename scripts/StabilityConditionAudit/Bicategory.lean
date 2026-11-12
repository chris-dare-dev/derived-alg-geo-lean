/-
Higher-categorical slice of the StabilityCondition audit. Despite the audit's
historical name, this slice covers generic bicategorical infrastructure.
-/
import DerivedAlgGeo.CategoryTheory.Bicategory

/-! ## Ordinary adjoint functors as adjunctions in `Cat` -/

#print axioms CategoryTheory.Adjunction.bicategoricalEquiv

#print axioms CategoryTheory.NatTrans.toStrongTrans
#print axioms CategoryTheory.NatTrans.toStrongTrans_app

/-! ## Two-fibre products of Cat-valued pseudofunctors -/

#print axioms CategoryTheory.Pseudofunctor.diagonal
#print axioms CategoryTheory.Pseudofunctor.fiberProduct
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.comm
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.comm_hom_as_app_toNatTrans_app
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.comm_inv_as_app_toNatTrans_app
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.fst
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.fst_app
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.fst_naturality
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.isGroupoid_obj
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.lift
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftApp
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftApp_map_fst
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftApp_map_snd
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftApp_obj_fst
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftApp_obj_iso_hom
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftApp_obj_iso_inv
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftApp_obj_snd
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftFst
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftFst_hom_as_app_toNatTrans_app
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftFst_inv_as_app_toNatTrans_app
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftNaturality
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftNaturality_hom_app_fst
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftNaturality_hom_app_snd
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftNaturality_inv_app_fst
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftNaturality_inv_app_snd
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftSnd
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftSnd_hom_as_app_toNatTrans_app
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.liftSnd_inv_as_app_toNatTrans_app
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.lift_app
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.lift_comm
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.lift_naturality
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.map
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.mapComp
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.mapComp_hom_app_fst
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.mapComp_hom_app_snd
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.mapComp_inv_app_fst
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.mapComp_inv_app_snd
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.mapId
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.mapId_hom_app_fst
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.mapId_hom_app_snd
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.mapId_inv_app_fst
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.mapId_inv_app_snd
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.map_map_fst
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.map_map_snd
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.map_obj_fst
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.map_obj_iso_hom
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.map_obj_iso_inv
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.map_obj_snd
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.snd
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.snd_app
#print axioms CategoryTheory.Pseudofunctor.fiberProduct.snd_naturality
#print axioms CategoryTheory.Pseudofunctor.fiberProduct_map
#print axioms CategoryTheory.Pseudofunctor.fiberProduct_mapComp
#print axioms CategoryTheory.Pseudofunctor.fiberProduct_mapId
#print axioms CategoryTheory.Pseudofunctor.fiberProduct_obj
#print axioms CategoryTheory.Pseudofunctor.terminal
#print axioms CategoryTheory.Pseudofunctor.toTerminal

/-! ## The core of a Cat-valued pseudofunctor -/

#print axioms CategoryTheory.Pseudofunctor.core
#print axioms CategoryTheory.Pseudofunctor.core_map
#print axioms CategoryTheory.Pseudofunctor.core_mapComp
#print axioms CategoryTheory.Pseudofunctor.core_mapComp'_hom_toNatTrans_app_iso_hom
#print axioms CategoryTheory.Pseudofunctor.core_mapComp'_inv_toNatTrans_app_iso_hom
#print axioms CategoryTheory.Pseudofunctor.core_mapId
#print axioms CategoryTheory.Pseudofunctor.core_obj
#print axioms CategoryTheory.Pseudofunctor.core_obj_isGroupoid
#print axioms CategoryTheory.Pseudofunctor.coreι
#print axioms CategoryTheory.Pseudofunctor.coreι_app
#print axioms CategoryTheory.Pseudofunctor.coreι_naturality

/-! ## Object properties of the core, and inclusions of full sub-pseudofunctors -/

#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.core
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.core_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.core_isClosedUnderMapObj
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.core_prop
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.ιOfLE
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.ιOfLECompι
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.ιOfLECompι_hom_as_app_toNatTrans_app
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.ιOfLECompι_inv_as_app_toNatTrans_app
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.ιOfLE_app_toFunctor
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.ιOfLE_naturality

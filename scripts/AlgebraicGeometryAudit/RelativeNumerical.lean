/-
The algebraic and relative-numerical roots introduced for Definition 8.7 of
arXiv:2607.28411. These declarations are audited here because the audit routes
the Algebra subject with its numerical consumers; no scheme-bearing adapter is
claimed by this slice.
-/
import DerivedAlgGeo.Algebra.RelativeNumerical.Overlattice

-- Neutral algebraic root: saturation and its torsion-free universal property.
#print axioms AddSubgroup.saturation
#print axioms AddSubgroup.mem_saturation
#print axioms AddSubgroup.le_saturation
#print axioms AddSubgroup.saturation_le
#print axioms AddSubgroup.saturation_nsmulSaturated
#print axioms AddSubgroup.saturation_eq_self
#print axioms AddSubgroup.SaturatedQuotient
#print axioms AddSubgroup.saturatedQuotient_isAddTorsionFree
#print axioms AddSubgroup.saturatedQuotientMk
#print axioms AddSubgroup.saturatedQuotientMk_eq_zero_iff
#print axioms AddSubgroup.saturatedQuotientLift
#print axioms AddSubgroup.saturatedQuotientLift_mk
#print axioms AddSubgroup.saturatedQuotientMap
#print axioms AddSubgroup.saturatedQuotientMap_mk
#print axioms AddSubgroup.saturatedQuotientHom_ext
#print axioms AddSubgroup.saturatedQuotientHom_ext_iff
#print axioms AddSubgroup.saturatedQuotientMap_id
#print axioms AddSubgroup.saturatedQuotientMap_comp

-- Relative numerical algebraic core: indexed groups, relations, quotient, and tests.
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FiberSum
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.fiberInclusion
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.fiberwiseHom
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.fiberwiseHom_fiberInclusion
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.relationSubgroup
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.Group
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.of
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.of_apply
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.relation_eq_zero
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.of_eq_of
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.lift
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.lift_of
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.map
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.map_mk
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.mapOfRelations
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.map_id
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.map_comp
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.hom_ext
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.hom_ext_iff
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.mk.inj
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.mk.sizeOf_spec
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.Family
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.Point
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.index
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.classValue
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.relation
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.relations
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.relation_mem
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.RelativeGroup
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.pointClass
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.pointClass_eq
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.lift
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.lift_pointClass
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.singletonFold
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.singletonFold_of
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.singletonEquiv
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.singletonEquiv_of

-- Images, specialization factorization, and the family adapter.
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.EtaImage
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.etaClass
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.etaClass_coe
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.IsFiniteIndexOverlattice
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.specializationMap
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.specializationMap_coe
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.specializationMap_self
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.ofEta
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.FamilyRelationSystem.ofEta_classValue_coe
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.etaImageIdEquiv
#print axioms DerivedAlgGeo.Algebra.RelativeNumerical.etaImageIdEquiv_etaClass

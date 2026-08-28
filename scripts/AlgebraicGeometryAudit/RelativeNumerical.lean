/-
The algebraic and relative-numerical roots introduced for Definition 8.7 of
arXiv:2607.28411.  Saturation is audited here beside its first geometric
consumer so the abstraction boundary remains visible.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Relative

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
#print axioms AddSubgroup.saturatedQuotientMap_id
#print axioms AddSubgroup.saturatedQuotientMap_comp

-- Relative numerical algebraic core: fibres, relations, quotient, and tests.
#print axioms AlgebraicGeometry.Numerical.Relative.FiberSum
#print axioms AlgebraicGeometry.Numerical.Relative.fiberInclusion
#print axioms AlgebraicGeometry.Numerical.Relative.fiberwiseHom
#print axioms AlgebraicGeometry.Numerical.Relative.fiberwiseHom_fiberInclusion
#print axioms AlgebraicGeometry.Numerical.Relative.relationSubgroup
#print axioms AlgebraicGeometry.Numerical.Relative.Group
#print axioms AlgebraicGeometry.Numerical.Relative.of
#print axioms AlgebraicGeometry.Numerical.Relative.of_apply
#print axioms AlgebraicGeometry.Numerical.Relative.relation_eq_zero
#print axioms AlgebraicGeometry.Numerical.Relative.of_eq_of
#print axioms AlgebraicGeometry.Numerical.Relative.lift
#print axioms AlgebraicGeometry.Numerical.Relative.lift_of
#print axioms AlgebraicGeometry.Numerical.Relative.map
#print axioms AlgebraicGeometry.Numerical.Relative.map_mk
#print axioms AlgebraicGeometry.Numerical.Relative.mapOfRelations
#print axioms AlgebraicGeometry.Numerical.Relative.map_id
#print axioms AlgebraicGeometry.Numerical.Relative.map_comp
#print axioms AlgebraicGeometry.Numerical.Relative.hom_ext
#print axioms AlgebraicGeometry.Numerical.Relative.singletonFold
#print axioms AlgebraicGeometry.Numerical.Relative.singletonFold_of
#print axioms AlgebraicGeometry.Numerical.Relative.singletonEquiv
#print axioms AlgebraicGeometry.Numerical.Relative.singletonEquiv_of

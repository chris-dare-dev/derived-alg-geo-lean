/-
TStructureCore slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.Bounded
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearYoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearCoyoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.LinearAlgebra
open CategoryTheory.Triangulated

/-! ## Cohomology exactness (#146) -/

#print axioms CategoryTheory.Triangulated.Tilting.originalHeartCoh_exact_of_distTriang
#print axioms CategoryTheory.Triangulated.Tilting.originalHeartCoh_isZero_of_isZero
#print axioms CategoryTheory.Triangulated.Tilting.heart_map_originalHeartCoh

/-! ## TStructure — bounded t-structures and t-exact functors (#146) -/

#print axioms CategoryTheory.Triangulated.TStructure.IsBounded
#print axioms CategoryTheory.Triangulated.TStructure.isBounded_iff
#print axioms CategoryTheory.Triangulated.TStructure.exists_isLE
#print axioms CategoryTheory.Triangulated.TStructure.exists_isGE
#print axioms CategoryTheory.Triangulated.TStructure.IsNondegenerate
#print axioms CategoryTheory.Triangulated.TStructure.isNondegenerate_of_isBounded
#print axioms CategoryTheory.Functor.IsRightTExact
#print axioms CategoryTheory.Functor.IsLeftTExact
#print axioms CategoryTheory.Functor.IsTExact
#print axioms CategoryTheory.Functor.isLE_map_of_isRightTExact
#print axioms CategoryTheory.Functor.isGE_map_of_isLeftTExact
#print axioms CategoryTheory.Functor.isTExact_of
#print axioms CategoryTheory.Functor.isRightTExact_of_isLE_zero
#print axioms CategoryTheory.Functor.isLeftTExact_of_isGE_zero
#print axioms CategoryTheory.Functor.isLeftTExact_rightAdjoint
#print axioms CategoryTheory.Functor.isRightTExact_leftAdjoint
#print axioms CategoryTheory.Functor.mapTriangleLEGEIso
#print axioms CategoryTheory.Functor.mapTruncLEIso
#print axioms CategoryTheory.Functor.mapTruncGEIso
#print axioms CategoryTheory.Functor.isLE_iff_of_reflectsZeroObjects
#print axioms CategoryTheory.Functor.isGE_iff_of_reflectsZeroObjects
#print axioms CategoryTheory.Functor.isBounded_of_target
#print axioms CategoryTheory.Functor.heart_map_of_isTExact
#print axioms CategoryTheory.Functor.isRightTExact_comp
#print axioms CategoryTheory.Functor.isLeftTExact_comp
#print axioms CategoryTheory.Functor.isTExact_comp
#print axioms CategoryTheory.Functor.isRightTExact_id
#print axioms CategoryTheory.Functor.isLeftTExact_id
#print axioms CategoryTheory.Functor.isTExact_id

/-! ## SF7.2 compact generation, Ind-extension, and A.17 core (#477) -/

#print axioms CategoryTheory.Functor.PreservesSmallCoproducts
#print axioms CategoryTheory.IsCompactObject
#print axioms CategoryTheory.IsCompactObject.coproductComparisonIso
#print axioms CategoryTheory.IsCompactObject.coproductComparisonIso.congr_simp
#print axioms CategoryTheory.IsCompactObject.map_ι_coproductComparisonIso_hom
#print axioms CategoryTheory.IsCompactObject.map_ι_coproductComparisonIso_hom_assoc
#print axioms CategoryTheory.IsCompactObject.exists_finite_sum
#print axioms CategoryTheory.IsCompactObject.shift
#print axioms CategoryTheory.ObjectProperty.compactObjects
#print axioms CategoryTheory.ObjectProperty.isCompactObject_of_iso
#print axioms CategoryTheory.ObjectProperty.coprodClosure
#print axioms CategoryTheory.ObjectProperty.coprodClosure.below.of_coproduct
#print axioms CategoryTheory.ObjectProperty.coprodClosure.below.of_extension
#print axioms CategoryTheory.ObjectProperty.coprodClosure.below.of_iso
#print axioms CategoryTheory.ObjectProperty.coprodClosure.below.of_mem
#print axioms CategoryTheory.ObjectProperty.coprodClosure.of_coproduct
#print axioms CategoryTheory.ObjectProperty.coprodClosure.of_extension
#print axioms CategoryTheory.ObjectProperty.coprodClosure.of_iso
#print axioms CategoryTheory.ObjectProperty.coprodClosure.of_mem
#print axioms CategoryTheory.ObjectProperty.instIsClosedUnderColimitsOfShapeCoprodClosureDiscrete
#print axioms CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsCompactObjects
#print axioms CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsCoprodClosure
#print axioms CategoryTheory.ObjectProperty.instIsTriangulatedClosed₂CoprodClosure
#print axioms CategoryTheory.ObjectProperty.le_coprodClosure
#print axioms CategoryTheory.ObjectProperty.coprodClosure_le
#print axioms CategoryTheory.ObjectProperty.coprodClosure_map_obj
#print axioms CategoryTheory.Adjunction.isCompactObject_leftAdjoint_obj
#print axioms CategoryTheory.Adjunction.compactObjects_map_leftAdjoint
#print axioms CategoryTheory.Triangulated.TStructure.IsCompactlyGeneratedBy
#print axioms CategoryTheory.Triangulated.TStructure.IsCompactlyGeneratedBy.compact
#print axioms CategoryTheory.Triangulated.TStructure.IsCompactlyGeneratedBy.le_zero_eq
#print axioms CategoryTheory.Triangulated.TStructure.IsCompactlyGeneratedBy.isLE_zero_of_generator
#print axioms CategoryTheory.Triangulated.TStructure.AisleData
#print axioms CategoryTheory.Triangulated.MappingTelescope.shiftMap
#print axioms CategoryTheory.Triangulated.MappingTelescope.ι_shiftMap
#print axioms CategoryTheory.Triangulated.MappingTelescope.ι_shiftMap_assoc
#print axioms CategoryTheory.Triangulated.MappingTelescope.map
#print axioms CategoryTheory.Triangulated.MappingTelescope.ι_map
#print axioms CategoryTheory.Triangulated.MappingTelescope.ι_map_assoc
#print axioms CategoryTheory.Triangulated.MappingTelescope.projection
#print axioms CategoryTheory.Triangulated.MappingTelescope.ι_projection
#print axioms CategoryTheory.Triangulated.MappingTelescope.ι_projection_self
#print axioms CategoryTheory.Triangulated.MappingTelescope.shiftMap_projection_zero
#print axioms CategoryTheory.Triangulated.MappingTelescope.shiftMap_projection_succ
#print axioms CategoryTheory.Triangulated.MappingTelescope.map_projection_zero
#print axioms CategoryTheory.Triangulated.MappingTelescope.map_projection_succ
#print axioms CategoryTheory.Triangulated.MappingTelescope.comp_projection_eq_zero_of_comp_map_eq_zero
#print axioms CategoryTheory.Triangulated.MappingTelescope.eq_zero_of_comp_map_eq_zero
#print axioms CategoryTheory.Triangulated.MappingTelescope.hom_map_injective
#print axioms CategoryTheory.Triangulated.MappingTelescope.transition
#print axioms CategoryTheory.Triangulated.MappingTelescope.transition.congr_simp
#print axioms CategoryTheory.Triangulated.MappingTelescope.transition_self
#print axioms CategoryTheory.Triangulated.MappingTelescope.transition_succ
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.mk.inj
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.obj
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.hom
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.connecting
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.distinguished
#print axioms CategoryTheory.Triangulated.MappingTelescope.chosen
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.exists_desc
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.exists_desc_comp_ι
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.inclusion
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.f_comp_inclusion
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.transition_comp_inclusion
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.comp_connecting_eq_zero
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.exists_lift_coproduct
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.exists_factor_stage
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.exists_transition_comp_eq_zero
#print axioms CategoryTheory.Triangulated.MappingTelescope.Data.exists_transition_comp_eq
#print axioms CategoryTheory.Triangulated.TStructure.ApproximationMap
#print axioms CategoryTheory.Triangulated.TStructure.ApproximationMap.left
#print axioms CategoryTheory.Triangulated.TStructure.ApproximationMap.left_mem
#print axioms CategoryTheory.Triangulated.TStructure.ApproximationMap.hom
#print axioms CategoryTheory.Triangulated.TStructure.ApproximationMap.hom_surjective
#print axioms CategoryTheory.Triangulated.TStructure.ApproximationMap.mk.inj
#print axioms CategoryTheory.Triangulated.TStructure.ApproximationMap.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.TStructure.ApproximationMap.shift_hom_injective
#print axioms CategoryTheory.Triangulated.TStructure.AisleData.shift
#print axioms CategoryTheory.Triangulated.TStructure.AisleData.exists_triangle
#print axioms CategoryTheory.Triangulated.TStructure.AisleData.ofApproximationMaps
#print axioms CategoryTheory.Triangulated.TStructure.AisleData.rightOrthogonal_le_shift
#print axioms CategoryTheory.Triangulated.TStructure.AisleData.tStructure
#print axioms CategoryTheory.Triangulated.TStructure.AisleData.tStructure.congr_simp
#print axioms CategoryTheory.Triangulated.TStructure.AisleData.tStructure_le_zero
#print axioms CategoryTheory.Triangulated.TStructure.AisleData.tStructure_ge_one
#print axioms CategoryTheory.ObjectProperty.coprodClosure_le_shift
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorApproximation
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorApproximation.generator_shift
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorApproximation.exists_triangle
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorApproximation.aisleData
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorApproximation.tStructure
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorApproximation.tStructure_le_zero
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorApproximation.tStructure_ge_one
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorApproximation.isCompactlyGeneratedBy
#print axioms CategoryTheory.Triangulated.TStructure.GeneratorApproximationMap
#print axioms CategoryTheory.Triangulated.TStructure.GeneratorApproximationMap.mk.inj
#print axioms CategoryTheory.Triangulated.TStructure.GeneratorApproximationMap.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.TStructure.GeneratorApproximationMap.left
#print axioms CategoryTheory.Triangulated.TStructure.GeneratorApproximationMap.left_mem
#print axioms CategoryTheory.Triangulated.TStructure.GeneratorApproximationMap.hom
#print axioms CategoryTheory.Triangulated.TStructure.GeneratorApproximationMap.hom_surjective
#print axioms CategoryTheory.Triangulated.TStructure.GeneratorApproximationMap.shift_hom_injective
#print axioms CategoryTheory.Triangulated.TStructure.GeneratorApproximationMap.exists_triangle
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorApproximation.ofGeneratorApproximationMaps
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.GeneratorIndex
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.generator
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.generator_mem
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.EvaluationIndex
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.evaluationSource
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.evaluationMap
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.initialObject
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.initialHom
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.initialObject_mem
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.initialHom_surjective
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.Stage
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.Stage.mk.inj
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.Stage.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.Stage.obj
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.Stage.mem
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.Stage.hom
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.initialStage
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.KernelIndex
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.kernelSource
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.kernelMap
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.kernelObject
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.kernelHom
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.kernelHom_comp_stageHom
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.kernelHom_comp_stageHom_assoc
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.kernelObject_shift_mem
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.StepData
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.StepData.mk.inj
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.StepData.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.StepData.next
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.StepData.transition
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.StepData.connecting
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.StepData.distinguished
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.StepData.transition_hom
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.StepData.kills
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.stepData_nonempty
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.step
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.tower
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.towerTransition
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.towerTransition_comp_hom
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.towerTransition_comp_hom_assoc
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.towerTransition_kills
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.towerObject
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.telescope
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.limitHom
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.inclusion_comp_limitHom
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.inclusion_comp_limitHom_assoc
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.telescope_mem
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.limitHom_surjective
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.limitHom_shift_injective
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.generatorApproximationMap
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.compactGeneratorApproximation
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.tStructure
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.tStructure_isCompactlyGeneratedBy
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.tStructure_le_zero
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorBrown.tStructure_ge_one
#print axioms CategoryTheory.Triangulated.TStructure.CompactGeneratorApproximation.ofApproximationMaps
#print axioms CategoryTheory.Functor.isRightTExact_of_compactlyGenerated
#print axioms CategoryTheory.Adjunction.isTExact_of_compactlyGenerated
#print axioms CategoryTheory.ObjectProperty.hasInducedTStructure_of_preimage
#print axioms CategoryTheory.ObjectProperty.preimageLift
#print axioms CategoryTheory.ObjectProperty.tStructure_isLE_iff_map
#print axioms CategoryTheory.ObjectProperty.tStructure_isGE_iff_map
#print axioms CategoryTheory.Triangulated.TStructure.boundedAisle
#print axioms CategoryTheory.Triangulated.TStructure.IndExtensionData
#print axioms CategoryTheory.Triangulated.TStructure.IndExtensionData.small_isBounded
#print axioms CategoryTheory.Triangulated.TStructure.IndExtensionData.largeAisle
#print axioms CategoryTheory.Triangulated.TStructure.IndExtensionData.compactlyGenerated
#print axioms CategoryTheory.Triangulated.TStructure.IndExtensionData.hasInduced
#print axioms CategoryTheory.Triangulated.TStructure.IndExtensionData.isLE_iff
#print axioms CategoryTheory.Triangulated.TStructure.IndExtensionData.isGE_iff
#print axioms CategoryTheory.Triangulated.Polishchuk.InducedTStructureData
#print axioms CategoryTheory.Triangulated.Polishchuk.InducedTStructureData.tStructure
#print axioms CategoryTheory.Triangulated.Polishchuk.InducedTStructureData.isBounded
#print axioms CategoryTheory.Triangulated.Polishchuk.InducedTStructureData.isLE_iff
#print axioms CategoryTheory.Triangulated.Polishchuk.InducedTStructureData.isGE_iff
#print axioms CategoryTheory.Triangulated.Polishchuk.induce
#print axioms CategoryTheory.Triangulated.Polishchuk.induceOfApproximation
#print axioms CategoryTheory.Triangulated.Polishchuk.induceOfBrown
#print axioms CategoryTheory.Triangulated.Polishchuk.induceOfApproximationMaps
#print axioms CategoryTheory.Triangulated.TStructure.coprodBoundedAisle_rightOrthogonal_of_isGE
#print axioms CategoryTheory.Triangulated.TStructure.boundedAisle_le_large
#print axioms CategoryTheory.Triangulated.TStructure.large_isLE_zero_iff
#print axioms CategoryTheory.Triangulated.TStructure.large_isGE_one_iff
#print axioms CategoryTheory.Triangulated.TStructure.boundedAisle_le_shift
#print axioms CategoryTheory.Triangulated.TStructure.large_isLE_iff
#print axioms CategoryTheory.Triangulated.TStructure.large_isGE_iff
#print axioms CategoryTheory.Triangulated.TStructure.hasInducedTStructure_of_largeAisle
#print axioms CategoryTheory.Triangulated.TStructure.IndExtensionData.ofCompactGenerators
#print axioms CategoryTheory.Triangulated.TStructure.IndExtensionData.ofApproximation
#print axioms CategoryTheory.Triangulated.TStructure.IndExtensionData.ofBrown

/-! ## Repository-owned t-structure heart bridges -/


/-! ## ForMathlib — results Mathlib lacks at the pin -/

#print axioms Matrix.polarFactor

-- `R`-linearity of the opposite category and of the opposite shift (#469).
-- Each is the linear counterpart of an additive declaration Mathlib already
-- has; `shiftFunctorOppositeLinear` is DERIVED from linearity of the shift on
-- `C`, which stays a hypothesis because additivity does not imply linearity.
#print axioms CategoryTheory.homModuleOpposite
#print axioms CategoryTheory.linearOpposite
#print axioms CategoryTheory.unop_smul
#print axioms CategoryTheory.op_smul
#print axioms CategoryTheory.Functor.op_linear
#print axioms CategoryTheory.shiftFunctorOppositeLinear
#print axioms CategoryTheory.ShiftedHom.opEquiv_symm_smul
#print axioms CategoryTheory.ShiftedHom.opEquiv'_symm_smul

-- Repository-owned heart results used by weak-tilting cohomology.
#print axioms CategoryTheory.ObjectProperty.FullSubcategory.isZero_of_obj_isZero
#print axioms CategoryTheory.Triangulated.TStructure.heart_hι
#print axioms CategoryTheory.Triangulated.TStructure.heart_containsZero
#print axioms CategoryTheory.Triangulated.TStructure.heart_closedUnderBinaryProducts
#print axioms CategoryTheory.Triangulated.TStructure.heart_closedUnderFiniteProducts
#print axioms CategoryTheory.Triangulated.TStructure.heart_hasFiniteProducts
#print axioms CategoryTheory.Triangulated.TStructure.heart_admissible
#print axioms CategoryTheory.Triangulated.TStructure.heartAbelian
#print axioms CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian
#print axioms CategoryTheory.Triangulated.TStructure.exists_image_factorisation_epi_triangle
#print axioms CategoryTheory.Triangulated.TStructure.exists_distinguished_triangle_of_heart_mono
#print axioms CategoryTheory.Triangulated.TStructure.exists_image_factorisation_triangles
#print axioms CategoryTheory.Triangulated.TStructure.heartFullSubcategory_shortExact_of_distTriang
#print axioms CategoryTheory.Triangulated.TStructure.heartFullSubcategory_shortExact_triangle
#print axioms CategoryTheory.Triangulated.TStructure.truncGE_map_comp_descTruncGE
#print axioms CategoryTheory.Triangulated.TStructure.exists_truncLT_octahedral_split
#print axioms Matrix.polarFactor_posSemidef
#print axioms Matrix.polarFactor_mul_self
#print axioms Matrix.polarFactor_isHermitian
#print axioms Matrix.det_polarFactor_ne_zero
#print axioms Matrix.isUnit_det_polarFactor
#print axioms Matrix.polarFactor_posDef
#print axioms Matrix.polarUnitary
#print axioms Matrix.polarUnitary_mul_polarFactor
#print axioms Matrix.polarUnitary_mem_unitaryGroup
#print axioms Matrix.exists_polarDecomposition
#print axioms Matrix.eq_polarFactor_of_mul
#print axioms Matrix.eq_polarUnitary_of_mul
#print axioms Matrix.existsUnique_polarDecomposition

/-! ## ForMathlib — the bounded homotopy category (#543 substrate)

`HomotopyCategory.Bounded C`, mirroring Mathlib's `HomotopyCategory.Plus`
declaration by declaration; upstreamable as written. Category plumbing only:
the `HomFiniteBounded` model built on it is audited with the Euler form. -/

#print axioms CochainComplex.bounded
#print axioms CochainComplex.bounded_iff
#print axioms CochainComplex.isStrictlyLE_mappingCone
#print axioms HomotopyCategory.bounded
#print axioms HomotopyCategory.bounded_quotient_obj_iff
#print axioms HomotopyCategory.bounded_iff_exists
#print axioms HomotopyCategory.bounded_containsZero
#print axioms HomotopyCategory.bounded_isStableUnderShift
#print axioms HomotopyCategory.bounded_isTriangulatedClosed₃
#print axioms HomotopyCategory.bounded_isTriangulated
#print axioms HomotopyCategory.Bounded
#print axioms HomotopyCategory.Bounded.ι
#print axioms HomotopyCategory.Bounded.fullyFaithfulι

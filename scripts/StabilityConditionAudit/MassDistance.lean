/-
MassDistance slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearYoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearCoyoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.LinearAlgebra
open CategoryTheory.Triangulated

/-! ## StabilityMass — choice-free HN mass envelope -/

#print axioms CategoryTheory.Triangulated.HNFiltration.mass
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.charge_ne_zero_of_semistable
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_pos
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_ofIso
#print axioms CategoryTheory.Triangulated.stabilityMass
#print axioms CategoryTheory.Triangulated.stabilityMass_pos
#print axioms CategoryTheory.Triangulated.stabilityMass_congr
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_eq_zero_of_isZero
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_eq_mass
#print axioms CategoryTheory.Triangulated.stabilityMass_eq_mass
#print axioms CategoryTheory.Triangulated.classCharge
#print axioms CategoryTheory.Triangulated.HNFiltration.classMass
#print axioms CategoryTheory.Triangulated.Slicing.classMass
#print axioms CategoryTheory.Triangulated.HNFiltration.classMass_eq_zero_of_isZero
#print axioms CategoryTheory.Triangulated.HNFiltration.classMass_eq_classMass
#print axioms CategoryTheory.Triangulated.Slicing.classMass_eq_classMass
#print axioms CategoryTheory.Triangulated.Slicing.classMass_ne_top
#print axioms CategoryTheory.Triangulated.Slicing.classMass_lt_top
#print axioms CategoryTheory.Triangulated.Slicing.classMass_toReal_eq_sum
#print axioms CategoryTheory.Triangulated.Slicing.classMass_eq_ofReal_norm_classCharge
#print axioms CategoryTheory.Triangulated.Slicing.exists_headTail_classMass
#print axioms CategoryTheory.Triangulated.HNFiltration.exists_headTail_classMass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.hnMass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.stabilityMass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.hnMass_eq_hnMass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.stabilityMass_eq_hnMass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.stabilityMass_ne_top
#print axioms CategoryTheory.Triangulated.stabilityMass_ne_top
#print axioms CategoryTheory.Triangulated.stabilityMass_lt_top
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_sum
#print axioms CategoryTheory.Triangulated.stabilityMass_eq_zero_iff
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_pos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_charge
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.mass_map_inverse
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.mass_map_functor
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_stabilityMass
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_stabilityMass_functor_obj

/-! ## HNPolygon — abelian HN paths and positive-angle support -/

#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.factorObj
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.hnPolygon_le_of_polygonVertex_isMax
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.last_le_phase
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.last_prefix_le_quotient_phase
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.mass
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.norm_charge_le_mass
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.norm_charge_le_polygonLength
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phase_last_prefix_le_of_ne_zero_to_semistable
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phase_le_first
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonEdge
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonEdge_arg
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonEdge_arg_strictAnti
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonEdge_mem_semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonLength
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonLength_eq_mass
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex_exists_strict_support
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex_exists_strict_support_hnPolygon
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex_last
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex_mem_hnPolygon
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex_succ_sub
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex_zero
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.quotientHNFiltration
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.quotientInfToCokernel
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.quotientInfToCokernel_mono
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.quotient_inf_phase_le
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.semistable_le_chain_of_phase_gt
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.semistable_phase_le_first
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.subobjectCharge_exists_strict_support
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.subobjectCharge_le_of_polygonVertex_isMax
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.subobject_phase_le_first
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.arg_last_edge_le_arg_last_sub_zero
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.arg_last_sub_zero_le_arg_first
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.arg_unitRay
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossFunctional
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossFunctional_apply
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossFunctional_neg_of_arg_lt
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossFunctional_pos_of_arg_lt
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.exists_strict_support_at_interior
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.length
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.norm_last_sub_zero_le_length
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.sum_edges_eq_last_sub_zero
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.unitRay
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.unitRay_im
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.unitRay_mem_semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.unitRay_re
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnPolygon
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnPolygon_mono
#print axioms CategoryTheory.Triangulated.StabilityFunction.subobjectCharge_mem_hnPolygon

/-! ## ConvexPolygonPerimeter — finite perimeter and short-exact mass bounds -/

#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.mass_eq_mass
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.mass_le_add_norm_cokernel_of_mono
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.mass_le_add_norm_of_shortExact
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonLength_le_add_norm_charge_sub_of_mono
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonLength_le_of_vertexHull_subset
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength_comp_monotone_le
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength_cons_cons
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength_mono_sublist
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength_nil
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength_ofFn_eq_length
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength_singleton
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedEdge
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedLength
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedLength_comp_monotone_le
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedLength_eq_length_add_chord
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedLength_eq_sum_turning
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedLength_le_of_monotone_support
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedTangent
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossMaxIndex
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossMaxIndex_max
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossMaxIndex_mono_of_angle_gt
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional_apply
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional_le_norm_mul
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional_sub_left
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional_sub_right
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional_unitDirection_self
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional_unitRay_sub
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorBisector
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorBisector_mem_Ioo
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorBisector_strictAnti
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorNextEdge
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorPrevEdge
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorTurnScale
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorTurnScale_pos
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.last_sub_zero_mem_semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.length_le_of_convexHull_subset
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.length_snoc
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.norm_unitDirection_le_one
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.sub_mem_semiClosedUpperHalfPlane_of_lt
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.turningFunctional
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.turningFunctional_interior_eq_cross
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.unitDirection
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.unitDirection_eq_unitRay_arg

/-! ## StabilityDistance — the three-coordinate extended pseudodistance -/

#print axioms CategoryTheory.Triangulated.logMassDist
#print axioms CategoryTheory.Triangulated.logMassDist_self
#print axioms CategoryTheory.Triangulated.logMassDist_comm
#print axioms CategoryTheory.Triangulated.logMassDist_triangle
#print axioms CategoryTheory.Triangulated.logMassDist_eq_of_ne_top
#print axioms CategoryTheory.Triangulated.phiPlusDist
#print axioms CategoryTheory.Triangulated.phiMinusDist
#print axioms CategoryTheory.Triangulated.massDist
#print axioms CategoryTheory.Triangulated.stabilityDistTerm
#print axioms CategoryTheory.Triangulated.stabilityDist
#print axioms CategoryTheory.Triangulated.phiPlusDist_self
#print axioms CategoryTheory.Triangulated.phiMinusDist_self
#print axioms CategoryTheory.Triangulated.massDist_self
#print axioms CategoryTheory.Triangulated.phiPlusDist_comm
#print axioms CategoryTheory.Triangulated.phiMinusDist_comm
#print axioms CategoryTheory.Triangulated.massDist_comm
#print axioms CategoryTheory.Triangulated.phiPlusDist_triangle
#print axioms CategoryTheory.Triangulated.phiMinusDist_triangle
#print axioms CategoryTheory.Triangulated.massDist_triangle
#print axioms CategoryTheory.Triangulated.massDist_eq_abs_log
#print axioms CategoryTheory.Triangulated.massDist_eq_abs_log_ratio
#print axioms CategoryTheory.Triangulated.stabilityDist_self
#print axioms CategoryTheory.Triangulated.stabilityDist_comm
#print axioms CategoryTheory.Triangulated.stabilityDist_triangle
#print axioms CategoryTheory.Triangulated.slicingDist_le_stabilityDist
#print axioms CategoryTheory.Triangulated.stabilityDistTerm_le_stabilityDist
#print axioms CategoryTheory.Triangulated.phiPlusDist_le_stabilityDist
#print axioms CategoryTheory.Triangulated.phiMinusDist_le_stabilityDist
#print axioms CategoryTheory.Triangulated.massDist_le_stabilityDist

/-! ## StabilityDistanceSeparation — identity of indiscernibles -/

#print axioms CategoryTheory.Triangulated.stabilityDistTerm_eq_zero_of_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_norm_charge
#print axioms CategoryTheory.Triangulated.phiPlus_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.phiMinus_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.slicing_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.charge_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.charge_comp_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityDist_eq_zero_iff
#print axioms CategoryTheory.Triangulated.stabilityConditionDist_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityConditionDist_eq_zero_iff

/-! ## StabilityDistanceTopology — Proposition 8.1 topology comparison -/

#print axioms CategoryTheory.Triangulated.abs_phiPlus_sub_lt_of_stabilityDist
#print axioms CategoryTheory.Triangulated.abs_phiMinus_sub_lt_of_stabilityDist
#print axioms CategoryTheory.Triangulated.abs_log_mass_ratio_lt_of_stabilityDist
#print axioms CategoryTheory.Triangulated.exp_neg_lt_mass_ratio_and_lt_exp_of_stabilityDist
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_lt_exp_mul_of_stabilityDist
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_lt_exp_mul_of_stabilityDist'
#print axioms CategoryTheory.Triangulated.norm_phaseExp_sub_phaseExp_le
#print axioms CategoryTheory.Triangulated.norm_sum_phaseExp_sub_centralRay_le
#print axioms CategoryTheory.Triangulated.charge_eq_stabilityMass_mul_phaseExp
#print axioms CategoryTheory.Triangulated.norm_charge_sub_mass_phaseExp_le_of_stabilityDist
#print axioms CategoryTheory.Triangulated.cos_mul_stabilityMass_le_norm_charge_of_width
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_le_of_mem_basisNhd_of_semistable
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_le_of_mem_basisNhd_of_semistable'
#print axioms CategoryTheory.Triangulated.StabilityMassTriangleInequality
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_congr
#print axioms CategoryTheory.Triangulated.stabilityMass_chain_le_partial_sum
#print axioms CategoryTheory.Triangulated.stabilityMass_le_sum_postnikov_factors
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_le_of_mem_basisNhd
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_le_of_mem_basisNhd'
#print axioms CategoryTheory.Triangulated.basisForwardMassFactor
#print axioms CategoryTheory.Triangulated.basisReverseMassFactor
#print axioms CategoryTheory.Triangulated.basisMassControl
#print axioms CategoryTheory.Triangulated.basisForwardMassFactor_zero
#print axioms CategoryTheory.Triangulated.basisReverseMassFactor_zero
#print axioms CategoryTheory.Triangulated.basisMassControl_zero
#print axioms CategoryTheory.Triangulated.abs_log_mass_ratio_le_of_mem_basisNhd
#print axioms CategoryTheory.Triangulated.exists_basisMassControl_lt
#print axioms CategoryTheory.Triangulated.exists_basisNhd_subset_stabilityDist_ball
#print axioms CategoryTheory.Triangulated.stabilityChargeControl
#print axioms CategoryTheory.Triangulated.stabilityChargeControl_zero
#print axioms CategoryTheory.Triangulated.norm_charge_sub_charge_lt_of_stabilityDist
#print axioms CategoryTheory.Triangulated.stabilitySeminorm_le_of_stabilityDist_lt
#print axioms CategoryTheory.Triangulated.exists_stabilityChargeControl_lt
#print axioms CategoryTheory.Triangulated.exists_stabilityDist_ball_subset_basisNhd
#print axioms CategoryTheory.Triangulated.nhds_hasBasis_basisNhd
#print axioms CategoryTheory.Triangulated.StabilityDistanceTopologyCompatible
#print axioms CategoryTheory.Triangulated.stabilityDistanceTopologyCompatible_of_mass_triangle
#print axioms CategoryTheory.Triangulated.stabilityPseudoEMetricSpace
#print axioms CategoryTheory.Triangulated.stabilityPseudoEMetricSpace_toTopologicalSpace
#print axioms CategoryTheory.Triangulated.stabilityPseudoEMetricSpace_edist
#print axioms CategoryTheory.Triangulated.stabilityEMetricSpace
#print axioms CategoryTheory.Triangulated.stabilityEMetricSpace_toTopologicalSpace
#print axioms CategoryTheory.Triangulated.stabilityPseudoEMetricSpaceOfMassTriangle
#print axioms CategoryTheory.Triangulated.stabilityEMetricSpaceOfMassTriangle

/-! ## The octahedral reduction of the mass triangle inequality -/

#print axioms CategoryTheory.Triangulated.stabilityMass_eq_ofReal_norm_charge
#print axioms CategoryTheory.Triangulated.exists_headTail_stabilityMass
#print axioms CategoryTheory.Triangulated.HNFiltration.exists_headTail_mass
#print axioms CategoryTheory.Triangulated.StabilityMassSemistableLeftTriangleInequality
#print axioms CategoryTheory.Triangulated.stabilityMassTriangleInequality_of_semistable_obj₁
#print axioms CategoryTheory.Triangulated.stabilityMassSemistableLeftTriangleInequality
#print axioms CategoryTheory.Triangulated.stabilityMassTriangleInequality
#print axioms CategoryTheory.Triangulated.stabilityDistanceTopologyCompatible
#print axioms CategoryTheory.Triangulated.stabilityMassBoundaryHeartInequality
#print axioms CategoryTheory.Triangulated.stabilityMass_H0FunctorShift_negOne_zero_triangle_le_of_obj₁_phase_one
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_shift_one
#print axioms CategoryTheory.Triangulated.HNFiltration.unrotateStability
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_appendFactor
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_triangle_eq_add_of_same_phase
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.charge_triangle
#print axioms CategoryTheory.Triangulated.StabilityMassBoundaryHeartInequality
#print axioms CategoryTheory.Triangulated.stabilityMass_liftedRotation
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observable_charge
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart
#print axioms CategoryTheory.Triangulated.phaseOne_endpoints_of_heart_shortExact
#print axioms CategoryTheory.Triangulated.stabilityMass_shift_neg_one
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_rotateStability
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_unrotateStability
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observable
#print axioms CategoryTheory.Triangulated.StabilityMassHeartShortExactInequality
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.mem_slicing_of_heart_isSemistable
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_obj₁_phase_one_of_amplitude
#print axioms CategoryTheory.Triangulated.HNFiltration.rotateStability
#print axioms CategoryTheory.Triangulated.stabilityMass_heart_shortExact_le_of_obj₂_semistable
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_charge
#print axioms CategoryTheory.Triangulated.heartShortExact_exists_distinguished_triangle
#print axioms CategoryTheory.Triangulated.norm_charge_le_stabilityMass_toReal
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_shift_neg_one
#print axioms CategoryTheory.Triangulated.norm_actC_rotationGLPos
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_appendFactor
#print axioms CategoryTheory.Triangulated.actC_rotationGLPos
#print axioms CategoryTheory.Triangulated.stabilityMassHeartShortExactInequality_of_triangle
#print axioms CategoryTheory.Triangulated.stabilityMass_heartCoh_negOne_zero_triangle_le_of_obj₁_phase_one
#print axioms CategoryTheory.Triangulated.stabilityMass_shift_one
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_obj₂_semistable
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_heartCoh_negOne_add_zero
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_obj₁_phase_one
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_triangle_eq_add_of_hn_separated
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_hasHN
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.mass_eq_stabilityMass_toReal
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_obj₁_phase_one_of_obj₃_le_one
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_same_phase
#print axioms CategoryTheory.Triangulated.stabilityMass_heart_shortExact_le_of_same_phase
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observable_slicing

/-! ## AutFullIsometry — invariance of all three coordinates -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_phiPlusDist
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_phiMinusDist
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_massDist
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_stabilityDistTerm
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_stabilityDistTerm_functor_obj
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_stabilityDist
#print axioms CategoryTheory.Triangulated.AutPairQuot_smul_stabilityDist

/-! ## Group-law spot checks

`#print axioms` audits the proof term; these check the instance actually
computes the intended composition rather than some other group structure that
happens to typecheck. Both are `rfl`, so a wrong `mul` would fail here.
-/

section SpotChecks

open CategoryTheory.Triangulated.StabilityCondition.GroupAction

example (f g : NormalizedShift) (φ : ℝ) :
    (f * g).toOrderIso φ = f.toOrderIso (g.toOrderIso φ) := rfl

example (φ : ℝ) : (1 : NormalizedShift).toOrderIso φ = φ := rfl

example (f : NormalizedShift) (φ : ℝ) :
    (f⁻¹ * f).toOrderIso φ = φ := by simp

/-- `GLTilde` multiplication must compose the shift factors in the SAME order
as `NormalizedShift` does. An order flip here would typecheck and be wrong. -/
example (x y : GLTilde) (φ : ℝ) :
    (x * y).shift.toOrderIso φ = x.shift.toOrderIso (y.shift.toOrderIso φ) :=
  rfl

/-- The projections agree with the field accessors. -/
example (x : GLTilde) : GLTilde.toMatHom x = x.mat := rfl
example (x : GLTilde) : GLTilde.toShiftHom x = x.shift := rfl

/-- The identity really is a compatible pair, so `GLTilde` is inhabited and
the group is not vacuous. -/
example : (1 : GLTilde).mat = 1 ∧ (1 : GLTilde).shift = 1 := ⟨rfl, rfl⟩

/-- Phase `+1` is the antipodal ray — the shift functor `[1]`. -/
example (φ : ℝ) : rayVec (φ + 1) = -rayVec φ := rayVec_add_one φ

end SpotChecks

/-! ## Step-3a convention checks

The slicing action relabels by `f⁻¹`, not `f`. With `f` the definition still
typechecks and `mul_smul` fails, so the `MulAction` laws below are the real
guard; these `example`s pin the surface convention that goes with them.
-/

section SlicingChecks

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
  CategoryTheory.Triangulated.StabilityCondition.GroupAction

-- Declared explicitly. `lake env lean` does not apply the package's
-- `[leanOptions]`, so under a bare `lean` invocation `u` and `v` were
-- auto-bound and this section elaborated by accident. Under the repo's actual
-- settings (`autoImplicit = false`) it did not compile at all -- which is
-- exactly the rot that covering this file with a `lean_lib` is meant to catch.
universe u v

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

example (f : NormalizedShift) (s : Slicing C) (φ : ℝ) :
    (f • s).P φ = s.P (f⁻¹.toOrderIso φ) := rfl

/-- `GLTilde` acts through its shift factor only — the matrix factor is not
consulted. -/
example (x : GLTilde) (s : Slicing C) (φ : ℝ) :
    (x • s).P φ = (x.shift • s).P φ := rfl

/-! Step 3b: both factors act, each on its own component. -/

variable {Λ : Type*} [AddCommGroup Λ] (v : K₀ C →+ Λ)

example (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) :
    (x • σ).slicing = x • σ.slicing := rfl

example (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) (a : Λ) :
    (x • σ).Z a = actC x.mat (σ.Z a) := rfl

/-! Step 3c: the action reaches full stability conditions. -/

section StabChecks

variable [IsTriangulated C]

example (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) :
    (x • σ).slicing = x • σ.slicing := rfl

example (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) (a : Λ) :
    (x • σ).Z a = actC x.mat (σ.Z a) := rfl

end StabChecks

/-! The `Aut` half, now a `MulAction`.

Both components reverse under `*`, and they reverse in *opposite* syntactic
directions — the auto-equivalences compose contravariantly, the lattice maps
covariantly. Getting one of the two backwards typechecks and is wrong, so both
are pinned by `rfl` here. -/

section AutPairChecks

variable [IsTriangulated C]

/-- `a * b` applies `b`'s lattice automorphism FIRST. -/
example (a b : AutPair v) (σ : StabilityCondition.WithClassMap C v) (x : Λ) :
    ((AutPairQuot.mk a * AutPairQuot.mk b) • σ).Z x = σ.Z (b.lam (a.lam x)) := rfl

/-- ...and correspondingly applies `a`'s inverse equivalence first on objects. -/
example (a b : AutPair v) (σ : StabilityCondition.WithClassMap C v) (φ : ℝ) (X : C) :
    ((AutPairQuot.mk a * AutPairQuot.mk b) • σ).slicing.P φ X
      = σ.slicing.P φ (b.Φ.e.inverse.obj (a.Φ.e.inverse.obj X)) := rfl

/-- The identity acts as the identity, definitionally on both components. -/
example (σ : StabilityCondition.WithClassMap C v) (x : Λ) :
    ((1 : AutPairQuot v) • σ).Z x = σ.Z x := rfl

/-- The forgetful map really does forget only the lattice datum. -/
example (a : AutPair v) : AutPairQuot.toAutQuot (AutPairQuot.mk a) = AutQuot.mk a.Φ := rfl

/-- The quotient relation is normalized: only the forward functor is part of
the relation; inverse isomorphisms are derived from adjoint uniqueness. -/
example (a b : AutPair v) :
    a ≈ b ↔ (Nonempty (a.Φ.e.functor ≅ b.Φ.e.functor) ∧ a.lam = b.lam) := Iff.rfl

/-- The two §8 factors commute on stability conditions. -/
example (x : GLTilde) (a : AutPair v) (σ : StabilityCondition.WithClassMap C v) :
    x • (AutPairQuot.mk a • σ) = AutPairQuot.mk a • (x • σ) :=
  gltilde_autPair_smul_comm x a σ

/-- All three fixed-element continuity instances are found by typeclass search. -/
example (x : GLTilde) :
    Continuous fun σ : StabilityCondition.WithClassMap C v ↦ x • σ :=
  continuous_const_smul x

example (q : AutPairQuot v) :
    Continuous fun σ : StabilityCondition.WithClassMap C v ↦ q • σ :=
  continuous_const_smul q

example (p : GLTilde × AutPairQuot v) :
    Continuous fun σ : StabilityCondition.WithClassMap C v ↦ p • σ :=
  continuous_const_smul p

/-- The corresponding joint-continuity instances are also available. -/
example : Continuous fun p : GLTilde × StabilityCondition.WithClassMap C v ↦
    p.1 • p.2 :=
  continuous_smul

example : Continuous fun p : AutPairQuot v × StabilityCondition.WithClassMap C v ↦
    p.1 • p.2 :=
  continuous_smul

example : Continuous fun p : (GLTilde × AutPairQuot v) ×
    StabilityCondition.WithClassMap C v ↦ p.1 • p.2 :=
  continuous_smul

end AutPairChecks

end SlicingChecks


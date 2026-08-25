/-
Lattice slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearYoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearCoyoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.LinearAlgebra
open CategoryTheory.Triangulated

/-! ## Lattice lane -/

#print axioms IntegralLattice.NumLattice
#print axioms IntegralLattice.eq_zero_of_zsmul_eq_zero
#print axioms IntegralLattice.eq_zero_of_two_zsmul_eq_zero
#print axioms IntegralLattice.zsmul_injective
#print axioms IntegralLattice.zsmul_left_cancel
#print axioms IntegralLattice.finrank_numLattice
#print axioms IntegralLattice.ne_zero_of_apply_ne_zero
#print axioms IntegralLattice.eq_zero_of_two_zsmul_eq_zero_num

/-! ## Mukai lane — the extension `ℤ ⊕ N ⊕ ℤ` of a symmetric bilinear lattice

Pure lattice arithmetic. Nothing here is a statement about a K3 surface, a
Mukai lattice of a variety, or any geometric object; see the module docstrings
in `DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/`. -/

#print axioms Mukai.MukaiLattice
#print axioms Mukai.pairing
#print axioms Mukai.pairing_mk
#print axioms Mukai.pairing_add_left
#print axioms Mukai.pairing_add_right
#print axioms Mukai.pairing_smul_left
#print axioms Mukai.pairing_smul_right
#print axioms Mukai.pairing_neg_left
#print axioms Mukai.pairing_neg_right
#print axioms Mukai.pairing_sub_left
#print axioms Mukai.pairing_sub_right
#print axioms Mukai.pairing_zero_left
#print axioms Mukai.pairing_zero_right
#print axioms Mukai.pairing_comm
#print axioms Mukai.selfPairing
#print axioms Mukai.selfPairing_eq_pairing
#print axioms Mukai.selfPairing_mk
#print axioms Mukai.selfPairing_smul
#print axioms Mukai.selfPairing_zero
#print axioms Mukai.selfPairing_neg
#print axioms Mukai.even_selfPairing
#print axioms Mukai.IsSpherical
#print axioms Mukai.IsIsotropic
#print axioms Mukai.isSpherical_iff
#print axioms Mukai.isIsotropic_iff
#print axioms Mukai.IsSpherical.neg
#print axioms Mukai.IsIsotropic.neg
#print axioms Mukai.not_isSpherical_and_isIsotropic
#print axioms Mukai.expectedDim
#print axioms Mukai.expectedDim_eq_zero_iff
#print axioms Mukai.expectedDim_eq_two_iff
#print axioms Mukai.rankUnit
#print axioms Mukai.corankUnit
#print axioms Mukai.pairing_outer
#print axioms Mukai.isIsotropic_rankUnit
#print axioms Mukai.isIsotropic_corankUnit
#print axioms Mukai.pairing_rankUnit_corankUnit
#print axioms Mukai.pairingBilin
#print axioms Mukai.pairingBilin_apply

/-! ## Mukai lane — rank-two subpairs -/

#print axioms Mukai.gram
#print axioms Mukai.gram_comm
#print axioms Mukai.gram_zero_left
#print axioms Mukai.gram_zero_right
#print axioms Mukai.pairing_lincomb
#print axioms Mukai.selfPairing_lincomb
#print axioms Mukai.gram_lincomb
#print axioms Mukai.IsHyperbolicPair
#print axioms Mukai.isHyperbolicPair_iff
#print axioms Mukai.discr_pos_of_isHyperbolicPair
#print axioms Mukai.gram_ne_zero_of_isHyperbolicPair
#print axioms Mukai.ne_zero_left_of_isHyperbolicPair
#print axioms Mukai.ne_zero_right_of_isHyperbolicPair
#print axioms Mukai.isHyperbolicPair_comm
#print axioms Mukai.isHyperbolicPair_lincomb
#print axioms Mukai.orthWitness
#print axioms Mukai.pairing_orthWitness
#print axioms Mukai.selfPairing_orthWitness
#print axioms Mukai.selfPairing_orthWitness_neg
#print axioms Mukai.orthWitness_ne_zero
#print axioms Mukai.pairSpan
#print axioms Mukai.mem_pairSpan_left
#print axioms Mukai.mem_pairSpan_right
#print axioms Mukai.orthWitness_mem_pairSpan
#print axioms Mukai.HasSphericalClass
#print axioms Mukai.HasIsotropicClass
#print axioms Mukai.exists_neg_selfPairing_of_isHyperbolicPair


/-! ## Mukai lane — reflection in a spherical class

Still pure lattice arithmetic. `reflect` is a map of the abstract Mukai
extension; it is **not** the Seidel–Thomas spherical twist, and no autoequivalence
of any derived category is constructed or asserted. -/

#print axioms Mukai.reflect
#print axioms Mukai.reflect_apply
#print axioms Mukai.reflect_zero
#print axioms Mukai.reflect_add
#print axioms Mukai.reflect_smul
#print axioms Mukai.reflect_neg
#print axioms Mukai.reflectHom
#print axioms Mukai.reflectHom_apply
#print axioms Mukai.pairing_reflect_right
#print axioms Mukai.reflect_reflect
#print axioms Mukai.reflect_involutive
#print axioms Mukai.reflect_bijective
#print axioms Mukai.reflectEquiv
#print axioms Mukai.reflectEquiv_apply
#print axioms Mukai.reflectEquiv_symm_apply
#print axioms Mukai.reflect_self
#print axioms Mukai.reflect_of_pairing_eq_zero
#print axioms Mukai.pairing_reflect_eq_zero_iff
#print axioms Mukai.pairing_reflect_reflect
#print axioms Mukai.selfPairing_reflect
#print axioms Mukai.reflectIsometry
#print axioms Mukai.reflectIsometry_apply
#print axioms Mukai.IsSpherical.reflect
#print axioms Mukai.IsIsotropic.reflect
#print axioms Mukai.expectedDim_reflect
#print axioms Mukai.reflect_neg_left

/-! ## Period-domain lane — a real quadratic space of signature `(2, n - 2)`

Pure signature theory of a real quadratic space, in the discipline of the Mukai
lane above: nothing here is a statement about a K3 surface, its numerical
Grothendieck group or its period domain. See the module docstring of
`DerivedAlgGeo/LinearAlgebra/QuadraticForm/PeriodDomain.lean`. -/

#print axioms PeriodDomain.IsPositivePlane
#print axioms PeriodDomain.IsPositivePlane.finrank_eq
#print axioms PeriodDomain.IsPositivePlane.posDef
#print axioms PeriodDomain.HasSignatureTwo
#print axioms PeriodDomain.HasSignatureTwo.sigPos_eq
#print axioms PeriodDomain.HasSignatureTwo.sigNeg_add_two
#print axioms PeriodDomain.IsSphericalClass
#print axioms PeriodDomain.orthogonal
#print axioms PeriodDomain.wall
#print axioms PeriodDomain.periodDomain
#print axioms PeriodDomain.sphericalClasses
#print axioms PeriodDomain.periodDomain₀
#print axioms PeriodDomain.periodDomain₀_sphericalClasses_univ_eq_empty
#print axioms PeriodDomain.polarBilin_isRefl
#print axioms PeriodDomain.mem_orthogonal_iff
#print axioms PeriodDomain.isSphericalClass_iff_apply
#print axioms PeriodDomain.mem_wall_iff_mem_orthogonal
#print axioms PeriodDomain.notMem_of_isSphericalClass
#print axioms PeriodDomain.restrict_nondegenerate_of_isPositivePlane
#print axioms PeriodDomain.nondegenerate
#print axioms PeriodDomain.isCompl_orthogonal
#print axioms PeriodDomain.nonpos_of_mem_orthogonal
#print axioms PeriodDomain.neg_of_mem_orthogonal
#print axioms PeriodDomain.negDef_orthogonal
#print axioms PeriodDomain.finrank_orthogonal
#print axioms PeriodDomain.exists_isPositivePlane
#print axioms PeriodDomain.periodDomain_nonempty
#print axioms PeriodDomain.stdForm
#print axioms PeriodDomain.stdForm_hasSignatureTwo

/-! ### Wall finiteness — coercivity, bounded level sets, and the lattice count

The `QuadraticMap` records extend Mathlib's own API and are stated for an
arbitrary finite-dimensional real normed space; the `PeriodDomain` records are
the pointwise wall count. Neither says anything about a K3 surface. -/

#print axioms QuadraticMap.continuous_polar
#print axioms QuadraticMap.continuous_of_finiteDimensional
#print axioms QuadraticMap.PosDef.exists_pos_mul_norm_sq_le
#print axioms QuadraticMap.PosDef.isBounded_setOf_eq
#print axioms PeriodDomain.sphericalOrthogonal
#print axioms PeriodDomain.isBounded_sphericalOrthogonal
#print axioms PeriodDomain.finite_sphericalOrthogonal_inter
#print axioms PeriodDomain.finite_walls_through

/-! ### Regions of positive planes — the uniform constant and the wall count

`PlaneRegion` carries its coercivity constant as a field because a bounded
family of planes does not supply one; `ofCompactPairs` is the criterion that
inhabits the field, and `empty` is the degenerate witness kept for contrast. -/

#print axioms PeriodDomain.mem_orthogonal_span_pair_iff
#print axioms PeriodDomain.exists_uniform_coercivity
#print axioms PeriodDomain.PlaneRegion
#print axioms PeriodDomain.PlaneRegion.mk.inj
#print axioms PeriodDomain.PlaneRegion.mk.sizeOf_spec
#print axioms PeriodDomain.PlaneRegion.carrier
#print axioms PeriodDomain.PlaneRegion.isPositivePlane
#print axioms PeriodDomain.PlaneRegion.coercivity
#print axioms PeriodDomain.PlaneRegion.coercivity_pos
#print axioms PeriodDomain.PlaneRegion.uniform
#print axioms PeriodDomain.PlaneRegion.wallClasses
#print axioms PeriodDomain.PlaneRegion.isBounded_wallClasses
#print axioms PeriodDomain.PlaneRegion.finite_wallClasses_inter
#print axioms PeriodDomain.PlaneRegion.ofCompactPairs
#print axioms PeriodDomain.PlaneRegion.empty

/-! ### Oriented positive pairs — the sign invariant that models `P⁺`

The ordered form of the period domain and the two halves the pairing determinant
cuts it into. "Component" is modeled by the sign, not proved to be one; see the
module docstring of `QuadraticForm/Orientation.lean`. -/

#print axioms PeriodDomain.pairSpan
#print axioms PeriodDomain.IsPositivePair
#print axioms PeriodDomain.pairingDet
#print axioms PeriodDomain.isPositivePlane_pairSpan
#print axioms PeriodDomain.combination_ne_zero
#print axioms PeriodDomain.pairingDet_ne_zero
#print axioms PeriodDomain.pairingDet_swap
#print axioms PeriodDomain.pairingDet_swap_ref
#print axioms PeriodDomain.SameOrientation
#print axioms PeriodDomain.sameOrientation_refl
#print axioms PeriodDomain.sameOrientation_symm
#print axioms PeriodDomain.sameOrientation_trans
#print axioms PeriodDomain.periodDomainPlus
#print axioms PeriodDomain.periodDomainMinus
#print axioms PeriodDomain.disjoint_periodDomainPlus_minus
#print axioms PeriodDomain.union_periodDomainPlus_minus
#print axioms PeriodDomain.swap_mem_of_mem_periodDomainPlus

/-! ### The real Mukai extension, bundled — and the exponential chart

The bridge from the bare pairing of the Mukai lane to the bundled quadratic form
the period domain is stated over. `realForm` is HALF the self-pairing, which is
what makes `polar (realForm b) = realPairing b` and keeps `⟪δ,δ⟫ = -2` reading as
it does in the source; see the module docstring of `Mukai/RealForm.lean`. -/

#print axioms Mukai.RealExtension
#print axioms Mukai.realPairing
#print axioms Mukai.realPairing_apply
#print axioms Mukai.realPairing_comm
#print axioms Mukai.realBilin
#print axioms Mukai.realBilin_apply
#print axioms Mukai.realForm
#print axioms Mukai.realForm_apply
#print axioms Mukai.realForm_mk
#print axioms Mukai.polar_realForm
#print axioms Mukai.expRe
#print axioms Mukai.expIm
#print axioms Mukai.realPairing_expRe_expRe
#print axioms Mukai.realPairing_expIm_expIm
#print axioms Mukai.realPairing_expRe_expIm
#print axioms Mukai.realPairing_expIm_expRe
#print axioms Mukai.realForm_smul_add_smul
#print axioms Mukai.expRe_ne_zero
#print axioms Mukai.isPositivePair_exp
#print axioms Mukai.pairingDet_exp_self
#print axioms Mukai.mem_periodDomainPlus_exp

/-! ### Additivity of the signature over an orthogonal decomposition

Missing from Mathlib at the pin. Only the easy inequality is proved, twice; the
counting identity turns it into an equality. See the module docstring of
`QuadraticForm/SignatureAdditive.lean`. -/

#print axioms QuadraticMap.sigPos_add_le
#print axioms QuadraticMap.sigNeg_add_le
#print axioms QuadraticMap.nondegenerate_of_isCompl
#print axioms QuadraticMap.sigPos_eq_add

/-! ### The signature of the real Mukai extension

`HasSignatureTwo` for `realForm b` from the signature of `b` — with
`V = NS(X) ⊗ ℝ` that is the Hodge index theorem, so the hypothesis every
period-domain result carries stops being an assumption about the Mukai lattice.
Step 2 of the additivity work. -/

#print axioms QuadraticMap.rangeIsometry
#print axioms QuadraticMap.sigPos_smul_of_pos
#print axioms QuadraticMap.sigNeg_smul_of_pos
#print axioms Mukai.hyperbolicIncl
#print axioms Mukai.middleIncl
#print axioms Mukai.hyperbolicIncl_injective
#print axioms Mukai.middleIncl_injective
#print axioms Mukai.hyperbolic
#print axioms Mukai.middle
#print axioms Mukai.mem_hyperbolic_iff
#print axioms Mukai.mem_middle_iff
#print axioms Mukai.isCompl_hyperbolic_middle
#print axioms Mukai.orthogonal_hyperbolic_middle
#print axioms Mukai.comp_hyperbolicIncl_apply
#print axioms Mukai.comp_middleIncl_apply
#print axioms Mukai.hasSignatureTwo_realForm

/-! ### `P⁺` is named by the cone, not by a class inside it

The case of the projection-sign cocycle that route (A) needs, proved by a path
along the segment rather than by the cocycle itself. See the module docstring of
`Mukai/ExponentialOrientation.lean` for what is and is not settled. -/

#print axioms Mukai.continuous_bilin
#print axioms Mukai.pairingDet_exp
#print axioms Mukai.segment
#print axioms Mukai.segment_zero
#print axioms Mukai.segment_one
#print axioms Mukai.pos_segment
#print axioms Mukai.pathDet
#print axioms Mukai.continuous_pathDet
#print axioms Mukai.pathDet_zero
#print axioms Mukai.pathDet_one
#print axioms Mukai.mem_periodDomainPlus_exp_of_sameCone
#print axioms Mukai.mem_periodDomainPlus_exp_of_sameCone_of_sigPos

/-! ### The integral Mukai lattice inside the real extension

The `ℤ`-span of the extended basis is the integral Mukai extension, and the two
pairings agree under a map of middles — so wall finiteness is a statement about
integral classes rather than about an abstract `ZSpan`. -/

#print axioms Mukai.extendBasis
#print axioms Mukai.integralExtension
#print axioms Mukai.span_range_extendBasis
#print axioms Mukai.extendMap
#print axioms Mukai.realPairing_extendMap
#print axioms Mukai.isSphericalClass_extendMap
#print axioms Mukai.finite_sphericalOrthogonal_integralExtension
#print axioms Mukai.finite_wallClasses_integralExtension

/-! ### The central charge of a positive pair

Route (A) re-read in the language stability conditions are stated in: the kernel
of `Z` is the orthogonal complement, and negative definiteness there is the
support property. `expCharge` is Bridgeland's `Z(β,ω)`. -/

#print axioms PeriodDomain.centralCharge
#print axioms PeriodDomain.centralCharge_re
#print axioms PeriodDomain.centralCharge_im
#print axioms PeriodDomain.centralCharge_add
#print axioms PeriodDomain.centralCharge_smul
#print axioms PeriodDomain.centralCharge_zero
#print axioms PeriodDomain.centralCharge_eq_zero_iff
#print axioms PeriodDomain.ker_centralCharge_eq
#print axioms PeriodDomain.neg_of_centralCharge_eq_zero
#print axioms PeriodDomain.centralCharge_ne_zero_of_nonneg
#print axioms PeriodDomain.mem_wall_iff_centralCharge_eq_zero
#print axioms PeriodDomain.isCompl_ker_centralCharge
#print axioms PeriodDomain.mem_periodDomain₀_iff_centralCharge_ne_zero
#print axioms Mukai.expCharge
#print axioms Mukai.expCharge_apply
#print axioms Mukai.neg_of_expCharge_eq_zero
#print axioms Mukai.expCharge_ne_zero_of_nonneg
#print axioms Mukai.mem_wall_iff_expCharge_eq_zero
#print axioms Mukai.mem_periodDomain₀_iff_expCharge_ne_zero

/-! ### The cut period domain is nonempty

A Sylvester criterion makes the positive pairs an open set; each wall of a
nonzero class is a proper closed subspace of `M × M`; Baire avoids countably many
of them at once. This answers the question #700 left open. -/

#print axioms PeriodDomain.apply_smul_add_smul
#print axioms PeriodDomain.isPositivePair_iff
#print axioms PeriodDomain.isOpen_setOf_isPositivePair
#print axioms PeriodDomain.exists_isPositivePair
#print axioms PeriodDomain.wallPairs
#print axioms PeriodDomain.mem_wallPairs_iff
#print axioms PeriodDomain.wallPairs_ne_top
#print axioms PeriodDomain.dense_compl_wallPairs
#print axioms PeriodDomain.nonempty_periodDomain₀

#print axioms Mukai.extendMap_add

/-! ## The projection-sign cocycle

The orientation partition of `Orientation.lean` does not depend on its
reference pair. The proof interpolates a positive pair into the reference plane
along a segment that stays positive, so the only analytic input is the
intermediate value theorem on a quadratic polynomial — connectedness of the
Grassmannian of positive planes is not used. -/

#print axioms PeriodDomain.pairingDet_comm
#print axioms PeriodDomain.pairingDet_ref_comb
#print axioms PeriodDomain.pairingDet_self
#print axioms PeriodDomain.pairingDet_self_pos
#print axioms PeriodDomain.isPositivePair_iff_forall_combination
#print axioms PeriodDomain.projCoeffFst
#print axioms PeriodDomain.projCoeffSnd
#print axioms PeriodDomain.proj
#print axioms PeriodDomain.polar_proj_fst
#print axioms PeriodDomain.polar_proj_snd
#print axioms PeriodDomain.proj_mem_pairSpan
#print axioms PeriodDomain.sub_proj_mem_orthogonal
#print axioms PeriodDomain.pairingDet_proj
#print axioms PeriodDomain.pos_mul_endpoints_of_ne_zero
#print axioms PeriodDomain.isPositivePair_interp
#print axioms PeriodDomain.pairingDet_proj_mul_pos
#print axioms PeriodDomain.pairingDet_cocycle
#print axioms PeriodDomain.sameOrientation_iff_of_reference
#print axioms PeriodDomain.nonpos_of_sigPos_eq_one
#print axioms Mukai.im_expCharge
#print axioms Mukai.apply_sub_smul_eq_zero_of_im_eq_zero
#print axioms Mukai.two_mul_re_expCharge
#print axioms Mukai.two_mul_re_expCharge_ge
#print axioms Mukai.re_expCharge_pos_of_nonneg
#print axioms Mukai.re_expCharge_pos_of_neg_one

/-
SupportWalls slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearYoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearCoyoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.LinearAlgebra
open CategoryTheory.Triangulated

/-! ## Support lane — the Kontsevich-Soibelman quadratic-form reformulation

The basic statements are linear algebra plus one compactness argument over a
finite-dimensional real normed space and keep `S` arbitrary. The later
genuine/uniform/quotient declarations add bundled quadratic forms, a saturated
integral quotient, and a weak-stability adapter whose selected loci are actual
nonzero weak-semistable heart classes. The adapter still supplies no geometric
family, HN structure over a curve, boundedness, or moduli theory. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.IsHomogTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.IsCompatible
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.slice
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.isCompact_slice
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.norm_inv_smul_mem_slice
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.hasSupportProperty_of_isCompatible
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.exists_isCompatible_of_hasSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.hasSupportProperty_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasSupportProperty.mono
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasSupportProperty.eq_zero_of_charge_eq_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.hasSupportProperty_of_norm_sub_le
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasSupportProperty.exists_tolerance
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.isOpen_hasSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.quadraticForm_isHomogTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasQuadraticSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasQuadraticSupportProperty.hasSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasQuadraticSupportProperty.mono
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.familyLocus
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasUniformQuadraticSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasUniformQuadraticSupportProperty.fiber
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.hasUniformQuadraticSupportProperty_of_union
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.hasUniformQuadraticSupportProperty_iff_union
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasUniformQuadraticSupportProperty.reindex
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasQuadraticSupportProperty.constant
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.hasUniformQuadraticSupportProperty_constant_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.transportQuadraticForm
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.transportQuadraticForm_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.isCompatible_transport
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasUniformQuadraticSupportProperty.transport
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.hasUniformQuadraticSupportProperty_transport_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.quotientCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.quotientCharge_mkQ
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.quotientFamilyLocus
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasUniformQuadraticSupportPropertyModulo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.hasUniformQuadraticSupportPropertyModulo_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasUniformQuadraticSupportPropertyModulo.fiber
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasUniformQuadraticSupportPropertyModulo.hasSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.mkQ_eq_zero_of_mem
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasQuadraticSupportProperty.constant_modulo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.IsSaturated
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.saturatedClosure
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.subset_saturatedClosure
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.isSaturated_saturatedClosure
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.saturatedClosure_le
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.neg_mem_saturatedClosure_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.Quotient
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.quotientClass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.quotientClass_eq_zero_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.quotient_isAddTorsionFree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.quotient_moduleFinite
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.quotient_moduleFree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.saturatedClosure_le_ker
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.quotientCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.quotientCharge_quotientClass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.quotientToRealQuotient
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.quotientToRealQuotient.congr_simp
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.quotientToRealQuotient_quotientClass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.RealScalarExtension
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.scalarExtensionComparison
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.scalarExtensionComparison_tmul
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.scalarExtensionComparison_quotientClass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.exists_scalarExtensionEquiv_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.scalarExtensionEquiv
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.Support.ZeroChargeLattice.scalarExtensionEquiv_apply

/-! ## FiniteLength lane — charges on the free lattice of simples

`Fin n -> Z` is a MODEL of `K_0(A)` for a finite-length abelian category, not
an identification: that is Jordan-Holder, which exists in neither Mathlib nor
the foundational library. Every result is a theorem about `Fin n -> Z`. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength.mem_cone_smul
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength.mem_cone_sum
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength.chargeOf
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength.chargeOf_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength.chargeOf_single
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength.eq_chargeOf
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength.existsUnique_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength.mem_cone_natCombination
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength.chargeOf_mem_cone
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength.chargeOf_ne_zero

/-! ## Wall lane — numerical walls in the (s, t) half plane

Arithmetic on triples of reals. There is NO surface: no coherent sheaf, no
Chern character, no polarisation, and no Bogomolov-Gieseker inequality -- and
none is axiomatised, because the wall equation is an identity and needs none. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.NumClass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.NumClass.rk
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.NumClass.deg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.NumClass.ch2
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.reZ
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.imZ
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.minA
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.minB
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.minC
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wallExpr
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wallExpr_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wall_iff_circle
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wall_circle_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wall_line_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.shift
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.minA_shift
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.minB_shift
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.minC_shift
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wallExpr_shift
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.charge_eq_zero_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.eq_of_two_walls

/-! ### Wall lane — the nested wall theorem

Still the same arithmetic: `wall_eq_of_meet` is a statement about triples of
reals and says nothing about sheaves. In particular it is NOT the geometric
nested-wall theorem, which additionally asserts that the walls it orders are
walls of actual stability, and that is not expressible at the pin.

`wall_eq_of_meet_needs_charge` is a counterexample, not a theorem about walls:
it exhibits two genuinely different walls meeting at the one point where `v`'s
charge degenerates, which is what makes the charge hypothesis load-bearing
rather than decorative. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.minor_orth
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.crossAB
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.crossAC
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.crossBC
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.crossAB_swap
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.crossAC_swap
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.crossBC_swap
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.minorCross_eq_zero_of_two_walls
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wall_subset_of_crossZero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wall_eq_of_meet
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.degV
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.degV_charge_eq_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wall_eq_of_meet_needs_charge


/-! ## Spherical walls — the `exp(β + iω)` chart

Real arithmetic in a vector space with a symmetric bilinear form. Nothing here
is a statement about a K3 surface: no Néron--Severi group, no ample cone, no
Hodge index theorem, no stability condition. A separate structure from the
tilt-stability walls above, sharing no declaration with them; see the module
docstrings in
`DerivedAlgGeo/CategoryTheory/Triangulated/WeakStabilityCondition/StabilityCondition/Walls/`. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.pairing
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.pairing_mk
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.selfPairing
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.selfPairing_eq_pairing
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.selfPairing_mk
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.chartRe
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.chartIm
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.pairingRe
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.pairingIm
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.pairingRe_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.pairingIm_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.pairingIm_eq_of_symm
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.two_mul_rk_mul_pairingRe
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.pairingRe_eq_of_rk_ne_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.two_mul_rk_mul_pairingRe_of_rk_eq_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.pairingRe_of_rk_eq_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.IsSpherical
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.isSpherical_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.sphericalPlus
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.mem_sphericalPlus_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.isSpherical_of_mem_sphericalPlus
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.rk_pos_of_mem_sphericalPlus
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.corank_eq_of_isSpherical
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.wall
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.mem_wall_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.chamber
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.mem_chamber_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.chamber_antitone
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.chamber_eq_compl_iUnion
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.mem_wall_iff_of_isSpherical
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.IntegralComparison
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.IntegralComparison.toFun
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.IntegralComparison.compat
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.IntegralComparison.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.IntegralComparison.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.IntegralComparison.map
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.IntegralComparison.map_fst
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.pairing_map
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.selfPairing_map
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.isSpherical_map_iff

/-! ## Spherical walls — local finiteness

Bridgeland's Proposition 11.2. Still no K3 surface, no Néron--Severi group, no
ample cone and no Hodge index theorem: the negative-definiteness that the
geometric theory would get from Hodge index, and the positive lower bound on
`q(ω,ω)` that its "bounded region" wording leaves implicit, are both fields of
`BoundedRegion` and are supplied by the caller. Nothing here constructs one. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.carrier
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.bounded
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.ampleLower
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.ampleLower_pos
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.ample_le
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.coercivity
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.coercivity_pos
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.neg_definite
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.key
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.rk_sq_le
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.normSq_sub_smul_le
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.reconstruct
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.wallCandidates
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.exists_norm_fst_le
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.wallCandidates_subset
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical.BoundedRegion.finite_wallCandidates

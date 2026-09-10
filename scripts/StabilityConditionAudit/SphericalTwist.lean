/-
Spherical-twist slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist
open CategoryTheory.Triangulated

/-! ## Spherical twist lane — `τ_E` on `K₀`

Pure `K₀` arithmetic against the Euler form. Nothing here is a statement about
a spherical object, a K3 surface, or the autoequivalence `T_E`; see the module
docstring in `DerivedAlgGeo/CategoryTheory/Triangulated/SphericalTwist/`. -/

#print axioms SphericalTwist.twistK₀
#print axioms SphericalTwist.twistK₀_apply
#print axioms SphericalTwist.twistK₀_zero
#print axioms SphericalTwist.twistK₀_of
#print axioms SphericalTwist.chiK₀_twistK₀_left
#print axioms SphericalTwist.twistK₀_twistK₀
#print axioms SphericalTwist.twistK₀_involutive
#print axioms SphericalTwist.twistK₀_bijective
#print axioms SphericalTwist.twistK₀Equiv
#print axioms SphericalTwist.twistK₀Equiv_apply
#print axioms SphericalTwist.twistK₀Equiv_symm_apply
#print axioms SphericalTwist.twistK₀_self
#print axioms SphericalTwist.twistK₀_of_chi_eq_zero
#print axioms SphericalTwist.chiK₀_twistK₀_eq_zero_iff
#print axioms SphericalTwist.chiK₀_twistK₀_twistK₀

/-! ## Mukai lane — `τ_E` transported to the lattice

`MukaiRealization` is SUPPLIED data and nothing constructs one; its
`chi_eq_neg_pairing` field is Mukai's theorem / HRR. See the module docstring in
`SphericalTwist/Mukai.lean`. -/

#print axioms SphericalTwist.MukaiRealization
#print axioms SphericalTwist.MukaiRealization.mk.inj
#print axioms SphericalTwist.MukaiRealization.mk.sizeOf_spec
#print axioms SphericalTwist.MukaiRealization.v
#print axioms SphericalTwist.MukaiRealization.symm
#print axioms SphericalTwist.MukaiRealization.chi_eq_neg_pairing
#print axioms SphericalTwist.MukaiRealization.isSpherical_of_chi_eq_two
#print axioms SphericalTwist.MukaiRealization.map_twistK₀
#print axioms SphericalTwist.MukaiRealization.isSpherical_map_twistK₀
#print axioms SphericalTwist.MukaiRealization.isIsotropic_map_twistK₀
#print axioms SphericalTwist.MukaiRealization.expectedDim_map_twistK₀
#print axioms SphericalTwist.MukaiRealization.map_twistK₀Equiv
#print axioms SphericalTwist.MukaiRealization.chiK₀_twistK₀_twistK₀
#print axioms SphericalTwist.MukaiRealization.chiK₀_comm

/-! ## Braid lane — `τ_A τ_B τ_A = τ_B τ_A τ_B` on `K₀`

`SphericalPairData` is a `Prop` structure, so it has no `mk.inj` /
`mk.sizeOf_spec` to audit. The identity is the `K₀` shadow of Seidel--Thomas and
does NOT imply the functorial braid relation; see the module docstring in
`SphericalTwist/Braid.lean`. -/

#print axioms SphericalTwist.chiK₀_twistK₀_right
#print axioms SphericalTwist.SphericalPairData
#print axioms SphericalTwist.SphericalPairData.chi_A
#print axioms SphericalTwist.SphericalPairData.chi_B
#print axioms SphericalTwist.SphericalPairData.a_two
#print axioms SphericalTwist.SphericalPairData.symm
#print axioms SphericalTwist.braid_expand
#print axioms SphericalTwist.twistK₀_braid_apply
#print axioms SphericalTwist.twistK₀_braid
#print axioms SphericalTwist.MukaiRealization.reflect_braid

-- Enhanced spherical-functor lane: the four adjunction-map cone choices for a
-- dg functor with left and right dg adjoints, and the explicit twist/cotwist
-- equivalence conditions. No sphericality theorem is recorded.
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.chosen
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistCone
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistConeFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualCotwist
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualCotwistFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistCone
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistConeFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.leftAdj
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.mk.inj
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.rightAdj

-- Anno--Logvinenko's four triangles, read as functors into triangles of `H⁰`.
-- Each is one line over the generic cone-triangle layer, every value is
-- distinguished, and each first map is the corresponding unit or counit on
-- `H⁰`.  Two of the four are the UNSHIFTED cones: the conventional dual twist
-- and cotwist are their `⟦-1⟧` shifts, which are not taken here.  Nothing
-- claims sphericality or any relation among the four.
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.twistTriangleFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.twistTriangleFunctor_obj_mem_distinguishedTriangles
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.twistTriangleFunctor_obj_mor₁
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistConeTriangleFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistConeTriangleFunctor_obj_mem_distinguishedTriangles
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistConeTriangleFunctor_obj_mor₁
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistConeTriangleFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistConeTriangleFunctor_obj_mem_distinguishedTriangles
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistConeTriangleFunctor_obj_mor₁
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualCotwistTriangleFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualCotwistTriangleFunctor_obj_mem_distinguishedTriangles
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualCotwistTriangleFunctor_obj_mor₁

-- The conventional dual twist and cotwist: the inverse rotations of the two
-- unshifted cone triangles.  `invRotate` applies the `⟦-1⟧` shift and reorders
-- in one step, and the first vertex is the value of the dg shifted cone
-- functor on the nose rather than up to isomorphism.
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistTriangleFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistTriangleFunctor_obj_mem_distinguishedTriangles
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistTriangleFunctor_obj_obj₁
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistTriangleFunctor_obj_obj₂
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistTriangleFunctor_obj_obj₃
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistTriangleFunctor_obj_mor₂
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistTriangleFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistTriangleFunctor_obj_mem_distinguishedTriangles
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistTriangleFunctor_obj_obj₁
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistTriangleFunctor_obj_obj₂
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistTriangleFunctor_obj_obj₃
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistTriangleFunctor_obj_mor₂

-- Exactness for the twist: it preserves shifts and chosen cones, so `H⁰` of it
-- commutes with the shift and is a triangulated functor.  Not sphericality:
-- that needs all four Anno--Logvinenko conditions and Morita quasi-functors.
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.twistPreservesShifts
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistConePreservesShifts
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.twistH0CommShift
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.twistPreservesChosenCones
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistConePreservesChosenCones
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.twistH0IsTriangulated
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.twist
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.twistFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistCotwistEquivalenceConditions
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistCotwistEquivalenceConditions.cotwist
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistCotwistEquivalenceConditions.twist

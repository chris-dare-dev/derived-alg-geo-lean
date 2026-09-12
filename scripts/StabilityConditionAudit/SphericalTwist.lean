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
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualCotwist
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualCotwistFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistCone
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistConeFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.leftAdj
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.mk.inj
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.rightAdj

-- Anno--Logvinenko's four triangles, read as functors into triangles of `H⁰`.
-- Each is one line over the generic cone-triangle layer, every value is
-- distinguished, and each first map is the corresponding unit or counit on
-- `H⁰`.  Two of the four are the UNSHIFTED cones: the conventional dual twist
-- and cotwist are their separately named `⟦-1⟧` shifts.  The triangle
-- construction performs the same shift by inverse rotation.  Nothing claims
-- sphericality or any relation among the four.
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
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.dualTwistFunctorH0Iso
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistTriangleFunctor
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistTriangleFunctor_obj_mem_distinguishedTriangles
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistTriangleFunctor_obj_obj₁
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistTriangleFunctor_obj_obj₂
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistTriangleFunctor_obj_obj₃
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistTriangleFunctor_obj_mor₂
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistFunctorH0Iso

-- The equivalence conditions, spent: the twist and the unshifted cotwist cone
-- are autoequivalences of `H⁰`.  This is the first categorical invertibility
-- statement about a twist here; everything earlier was numerical, on `K₀`, or
-- a construction with no invertibility attached.  Exactness is the next block;
-- sphericality is still out of reach.
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.twistH0Equivalence
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistConeH0Equivalence
#print axioms CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionCones.cotwistH0Equivalence

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

/-! ## Spherical objects without a Serre functor (#888)

`SerreFunctor/Objects.lean` already carried `SerreFunctor.IsSphericalObject`, relative to a chosen
Serre functor and with a fourth clause `S(E) ≅ E⟦n⟧`. This predicate is deliberately WEAKER: a
general k-linear pretriangulated category has no Serre functor, and the Euler computation needs
none. `of_serreFunctor` projects the Serre-relative one onto this one, so the two are related
rather than parallel; the projection is one-way and nothing here reconstructs a Serre functor.

TRAP recorded in the module docstring: `chiHom_self_eq` needs `n ≠ 0`. The structure IS inhabitable
at `n = 0`, where the support collapses to `{0}` and chi is 1 while `1 + (-1)^0` is 2 -- so without
the hypothesis the statement is FALSE rather than vacuous. The degenerate value is recorded
separately.

TRAP, second: `vanishing` reads "every morphism is zero", never `IsZero (E ⟶ E⟦i⟧)`. That Hom is a
bare Type and `IsZero` there is unsatisfiable, which would make the structure uninhabitable and
every theorem vacuously true while still compiling.

`finrank_shift_zero` exists because the zero shift is not syntactically the identity, so the
endomorphism statement does not apply to `Hom(E, E⟦0⟧)` directly. -/

#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject
#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject.vanishing
#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject.end_one
#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject.top_one
#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject.not_isZero
#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject.finrank_end
#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject.finrank_top
#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject.finrank_hom_eq_zero
#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject.finrank_shift_zero
#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject.of_iso
#print axioms CategoryTheory.Triangulated.SphericalTwist.chiHom_self_eq
#print axioms CategoryTheory.Triangulated.SphericalTwist.chiHom_self_eq_one_of_zero
#print axioms CategoryTheory.Triangulated.SphericalTwist.chiK₀_of_self_eq_two
#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject.twistK₀_involutive
#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject.twistK₀_bijective
#print axioms CategoryTheory.Triangulated.SphericalTwist.IsSphericalObject.of_serreFunctor

/-! ## A twist-shaped autoequivalence acts on stability conditions (#890)

Connects the lattice half of the lane to the stability machinery: an autoequivalence whose action
on K0 is the twist becomes a group element acting on `WithClassMap`, and that action is transport
along the Mukai reflection. This is the precise form of "the spherical twist acts on Stab through
the reflection" available BEFORE the twist is constructed.

NOTHING HERE CONSTRUCTS A TWIST. `TwistShaped` is supplied data and is named to say so: it asserts
that its K0 action IS `twistK₀`. No inhabitant is produced.

TWO THINGS NOT TO CONCLUDE, both recorded in the module docstring.

`AutPairQuot` is NOT `Aut(D)`. It quotients by a bare natural isomorphism of underlying functors
and leaves the CommShift datum unconstrained, so it is a priori COARSER than exact autoequivalences
up to isomorphism of exact functors.

`lam_lam` is about the LATTICE, not the functor. The reflection is an involution, so the lattice
part of the square is the identity -- but the twist does NOT have order two in any automorphism
group; it has infinite order. Being an involution on K0 says nothing about the functor.

`map_inverse_eq` is the step the issue warned not to wave at: `K₀.map_congr` on the unit
isomorphism upgrades a natural isomorphism to an equality of maps on K0, and involutivity of the
twist then identifies the inverse's action. -/

#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.Φ
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.mk.inj
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.map_eq
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.chi_self
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.map_inverse_eq
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.isSpherical_v
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.lam
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.compat
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.toAutPair
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.toAutPair_lam
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.toAutPair_Φ
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.act_eq
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.act_slicing
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.act_Z
#print axioms CategoryTheory.Triangulated.SphericalTwist.TwistShaped.lam_lam

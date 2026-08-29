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

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

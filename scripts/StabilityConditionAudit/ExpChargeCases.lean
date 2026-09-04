/-
ExpChargeCases slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition
open CategoryTheory.Triangulated

/-! ## Lemma 6.2 — the four cases, at the level of the charge

Arithmetic on a triple of reals and a vector carrying a symmetric bilinear
form. There is NO sheaf, no tilted heart, no torsion pair, and no K3 surface.

This is NOT Lemma 6.2 and is deliberately not wired into MukaiChargeData:
bundling these case discriminants as fields of that structure would make its
`nonzero_mem` a one-line case split over invented assumptions, which would
compile, pass every gate, and prove nothing. Deciding WHICH objects of the
tilted heart fall into which case is the other half, and it is not here.

The shifted statements are stated on `-v` on purpose. Bridgeland states every
sign of section 6 for the SHEAF, while the object of the tilted heart in the
boundary case is its shift; `Re Z(E) > 0` is therefore exactly what puts the
heart object on the NEGATIVE real axis. The two reversals cancel, and getting
it backwards yields a false statement that compiles. No gate catches that. -/

#print axioms CategoryTheory.Triangulated.expCharge_neg
#print axioms CategoryTheory.Triangulated.mem_semiClosedUpperHalfPlane_of_im_pos
#print axioms CategoryTheory.Triangulated.mem_semiClosedUpperHalfPlane_of_im_zero_of_re_neg
#print axioms CategoryTheory.Triangulated.mem_semiClosedUpperHalfPlane_of_apply_sub_smul_pos
#print axioms CategoryTheory.Triangulated.mem_semiClosedUpperHalfPlane_of_dimension_zero
#print axioms CategoryTheory.Triangulated.neg_mem_semiClosedUpperHalfPlane_of_apply_sub_smul_neg
#print axioms CategoryTheory.Triangulated.neg_mem_semiClosedUpperHalfPlane_of_boundary_of_nonneg
#print axioms CategoryTheory.Triangulated.neg_mem_semiClosedUpperHalfPlane_of_boundary_of_neg_one

/-
ChargeFamily slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls
open CategoryTheory.Triangulated

/-! ## The dimension- and geometry-independent wall root

ChargeFamily P N is a family of additive complex charges on an additive group
N, indexed by an arbitrary type P: no heart, slicing, support property,
half-plane, or topology. wallValue is the determinant
Re Z(v) Im Z(w) - Im Z(v) Re Z(w), equal to minus the imaginary part of
Z(v) conj Z(w), and wall is its zero locus: the NUMERICAL wall, which is the
whole parameter space when w is an integral multiple of v or Z(v) = 0.
Symmetry, bi-additivity, integral-shift invariance, and preservation under
reindex and pullback are proved; the functoriality laws are definitional. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.ext
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.ext_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.im
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.im_add
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.im_neg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.im_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.im_zsmul
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.mem_wall
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.pullback
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.pullback_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.pullback_id
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.pullback_pullback
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.pullback_reindex
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.pullback_wall
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.pullback_wallValue
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.re
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.re_add
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.re_neg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.re_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.re_zsmul
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.reindex
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.reindex_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.reindex_id
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.reindex_pullback_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.reindex_reindex
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.reindex_wall
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wall
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_add_left
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_add_nsmul_right
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_add_right
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_add_zsmul_right
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_eq_neg_im_mul_conj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_neg_left
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_neg_right
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_self
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_swap
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_zero_left
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_zero_right
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_zsmul_right
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wall_add_zsmul_right
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wall_self
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wall_swap

/-! ## The (s,t) polynomial as one child

stChargeFamily packages reZ and imZ as a ChargeFamily on the (s,t) plane and
NumClass, and stChargeFamily_wallValue proves the generic determinant is exactly
wallExpr. Circle, line, disjointness, and nesting therefore stay theorems about
this child and are NOT assumptions of the root. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.mem_stChargeFamily_wall
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.stCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.stChargeFamily
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.stChargeFamily_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.stChargeFamily_wallValue
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.stCharge_im
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.stCharge_re

/-! ## The real-linear action on charges

A stability condition may be post-composed with a real-linear automorphism of
the complex numbers; the universal cover of GL+(2, R) acts that way and the
numerical wall is one of the things it preserves. realDet is the determinant in
the basis 1, I; wallValue_linearAct is the determinant law, wallValue being the
determinant of the 2x2 matrix of real and imaginary parts. wall_linearAct and
wall_smul need only invertibility, NOT orientation: the wall is preserved by
every invertible real-linear map, while the phase is not, which is why GL+
rather than GL appears downstream. Only the numerical half of the action is
here; no heart or slicing is transported. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.linearAct
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.linearAct_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.map_eq_smul_add_smul
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.realDet
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.realDet_mulLeft
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.smul
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.smul_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_linearAct
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wallValue_smul
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wall_linearAct
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.wall_smul

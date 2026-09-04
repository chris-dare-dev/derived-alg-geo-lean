/-
WallDiscriminant slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition
open CategoryTheory.Triangulated

/-! ## Wall lane — the Bogomolov discriminant

`discr` is a real-valued function of a triple of reals. There is NO surface: no
coherent sheaf, no Chern character, no polarisation, and in particular the
Bogomolov-Gieseker inequality is NOT proved and NOT axiomatised here.
`0 <= discr v` is a hypothesis wherever it appears.

What the lane buys is `wall_eq_of_meet_of_discr_nonneg`: the disjointness
statement of `Basic.lean` with its charge hypothesis -- a condition on a point
of the half plane -- replaced by a condition on the class alone. The exchange
is exact, via `discr_eq_neg_of_charge_eq_zero`, which pins the discriminant to
`-(r^2 t^2)` wherever the charge degenerates.

`discr_degV = -4` records that `Basic.lean`'s counterexample class sits
strictly in the negative regime, so `wall_eq_of_meet_needs_charge` and
`wall_eq_of_meet_of_discr_nonneg` are compatible rather than contradictory. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.NumClass.discr
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.NumClass.discr_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.NumClass.discr_of_rk_eq_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.NumClass.scale
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.NumClass.scale_rk
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.NumClass.scale_deg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.NumClass.scale_ch2
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.NumClass.discr_scale
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.discr_eq_neg_of_charge_eq_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.charge_ne_zero_of_discr_nonneg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wall_eq_of_meet_of_discr_nonneg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.discr_degV

/-! ### Wall lane — nesting, the ordering half of Bertram's theorem

Still arithmetic on triples of reals. `walls_nested_of_discr_nonneg` is NOT the
geometric nested-wall theorem: it orders circles in the (s, t) half plane and
says nothing about semistable objects, which is not expressible at the pin.

The same-family hypothesis is load-bearing, and
`walls_not_nested_of_opposite_offset` is the counterexample that shows it --
two walls of a class with nonnegative discriminant, disjoint but side by side
across the vertical wall. Dropping the hypothesis makes the theorem false, not
merely unproved. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wallCentre
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wallRadiusSq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wallOffset
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wallCentre_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wallRadiusSq_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wallOffset_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wallCentre_eq_sub_offset
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.wallRadiusSq_eq_offset
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.nesting_identity
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.nested_of_offsets
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.walls_nested_of_discr_nonneg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.walls_not_nested_of_opposite_offset

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

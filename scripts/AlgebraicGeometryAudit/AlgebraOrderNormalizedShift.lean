/-
Order-automorphism slice of the AlgebraicGeometry audit. Despite the audit's
historical name, `EnumDecls` routes the repository's `Algebra` root to this
audit, and MO1.12 (#1323) moved `NormalizedShift` -- the group of order
automorphisms of `R` commuting with unit translation -- out of the stability
tree to `Algebra/Order/NormalizedShift/`. These records were in the
GroupAction slice of the StabilityCondition audit until that move; the
declaration names are unchanged, only the lane that owns them.

The five names the GroupAction slice never listed -- `toOrderIso`,
`map_add_one`, `ext'_iff` and the two `mk` lemmas -- are audited here rather
than carried onward as backlog, so the move lowers the total unaudited count
instead of relocating it.
-/
import DerivedAlgGeo.Algebra.Order.NormalizedShift

/-! ## The group of `+1`-equivariant order automorphisms of `R` -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.toOrderIso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.toOrderIso_injective
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.map_add_one
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.ext'
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.ext'_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.symm_map_add_one
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.group
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.mul_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.one_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.inv_apply

/-! ## Uniform continuity, forced by `+1`-equivariance -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.map_add_nat
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.map_sub_nat
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.map_add_int
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.uniformContinuous
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift.exists_radius

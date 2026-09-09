/-
Axiom audit records for extensions of Mathlib's `CategoryTheory/Shift/`.
Run with `lake env lean scripts/StabilityConditionAudit/Shift.lean`.
-/
import DerivedAlgGeo.CategoryTheory.Shift

/-! ## The pointwise shift on a functor category

A shift on `Y` induces one on `X ⥤ Y` by postcomposition.  Mathlib has no such
instance at the pin; every comparison it needs is an identity of functors
there, so the construction is the image of `shiftFunctorZero` and
`shiftFunctorAdd` under `whiskeringRight`.  The evaluation functors then
commute with it on the nose. -/

#print axioms CategoryTheory.functorCategoryShiftMkCore
#print axioms CategoryTheory.functorCategoryHasShift
#print axioms CategoryTheory.functorCategory_shiftFunctor_obj
#print axioms CategoryTheory.functorCategory_shiftFunctor_obj_obj
#print axioms CategoryTheory.functorCategory_shiftFunctor_map_app
#print axioms CategoryTheory.functorCategory_shiftFunctorZero_hom_app
#print axioms CategoryTheory.functorCategory_shiftFunctorAdd_hom_app
#print axioms CategoryTheory.evaluationCommShift
#print axioms CategoryTheory.evaluationCommShift_iso_hom_app

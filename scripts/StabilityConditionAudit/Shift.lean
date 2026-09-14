/-
Axiom audit records for extensions of Mathlib's `CategoryTheory/Shift/`.
Run with `lake env lean scripts/StabilityConditionAudit/Shift.lean`.
-/
import DerivedAlgGeo.CategoryTheory.Shift
import DerivedAlgGeo.CategoryTheory.Triangulated.ShiftFunctor

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
#print axioms CategoryTheory.functorCategory_shiftFunctorZero_inv_app
#print axioms CategoryTheory.functorCategory_shiftFunctorAdd_hom_app
#print axioms CategoryTheory.functorCategory_shiftFunctorAdd_inv_app
#print axioms CategoryTheory.evaluationCommShift
#print axioms CategoryTheory.evaluationCommShift_iso_hom_app
#print axioms CategoryTheory.Functor.CommShift.ext
#print axioms CategoryTheory.Functor.CommShift.ext_iff
#print axioms CategoryTheory.Functor.CommShift₂.firstFamilyCommShift
#print axioms CategoryTheory.Functor.CommShift₂.firstFamilyCommShift_iso_hom_app_app
#print axioms CategoryTheory.Functor.CommShift₂.firstFamilyEvaluationCommShift
#print axioms CategoryTheory.Functor.CommShift₂.firstFamilyEvaluationCommShift_eq
#print axioms CategoryTheory.Functor.CommShift₂.secondFamilyCommShift
#print axioms CategoryTheory.Functor.CommShift₂.secondFamilyCommShift_iso_hom_app_app
#print axioms CategoryTheory.Functor.CommShift₂.secondFamilyEvaluationCommShift
#print axioms CategoryTheory.Functor.CommShift₂.secondFamilyEvaluationCommShift_eq

/-! ## Integral shifts as triangulated functors

Both `CommShift` packages are explicit.  The signed package is triangulated
for every integer; the unsigned package is triangulated only at even shifts
and remains available for compatibility and object-only uses. -/

#print axioms CategoryTheory.Pretriangulated.signedShiftFunctorCommIso
#print axioms CategoryTheory.Pretriangulated.shiftFunctorUnsignedCommShift
#print axioms CategoryTheory.Pretriangulated.shiftFunctorCommShift
#print axioms CategoryTheory.Pretriangulated.shiftFunctorCommShift_commShiftIso_hom_app
#print axioms CategoryTheory.Pretriangulated.commShiftIso_commShift
#print axioms CategoryTheory.Pretriangulated.shiftSignIso
#print axioms CategoryTheory.Pretriangulated.shiftFunctorMapTriangleIso
#print axioms CategoryTheory.Pretriangulated.shiftFunctorIsTriangulated
#print axioms CategoryTheory.Pretriangulated.shiftFunctorUnsignedMapTriangleIso
#print axioms CategoryTheory.Pretriangulated.shiftFunctorUnsignedIsTriangulated

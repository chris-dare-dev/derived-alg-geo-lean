/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Transferring triangulatedness across shift-compatible isomorphisms

This file packages the selected source and target shift structures for an
isomorphism of functors and transfers triangulatedness across that isomorphism.
It is generic in the functors and is consumed by Fourier--Mukai comparisons
and other presentations.

## Main definitions

`CategoryTheory.Triangulated.FunctorIsoShiftCompatibility` stores a selected
target shift structure and the compatibility of a supplied comparison with
the caller-selected source structure.

## Main results

`CategoryTheory.Triangulated.FunctorIsoShiftCompatibility.is_triangulated_of_iso`
transfers triangulatedness across the comparison.
`CategoryTheory.Triangulated.FunctorIsoShiftCompatibility.is_triangulated_of_equivalence_functor_eq`
applies this transfer to an equivalence whose forward functor is the target.

## Implementation notes

The source `CategoryTheory.Functor.CommShift` remains an input, so a
specialization can preserve a shift structure already chosen by its
presentation instead of replacing it with one transported across the
isomorphism.

## References

The transfer uses Mathlib's
`CategoryTheory.Functor.isTriangulated_of_iso` and
`CategoryTheory.Equivalence.IsTriangulated.mk'`.

## Tags

triangulated functor, shift compatibility, natural isomorphism, equivalence
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CategoryTheory.Triangulated

/-- Shift compatibility of a supplied natural isomorphism, relative to the
source functor's selected shift structure and an independently selected shift
structure on the target functor.

The source `CategoryTheory.Functor.CommShift` is an input to this record.
Specializations must preserve the shift structure already chosen by their
presentation rather than replacing it with one transported from the target. -/
structure FunctorIsoShiftCompatibility
    {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ]
    (G F : C ⥤ D) [G.CommShift ℤ] (α : G ≅ F) where
  /-- The target's chosen presentation is kept independent of transport from the source. -/
  targetCommShift : F.CommShift ℤ
  /-- This compatibility lets Mathlib transport distinguished triangles across the isomorphism. -/
  hom_commShift :
    letI : F.CommShift ℤ := targetCommShift
    NatTrans.CommShift α.hom ℤ

namespace FunctorIsoShiftCompatibility

variable {C D : Type*} [Category* C] [Category* D]
  [HasShift C ℤ] [HasShift D ℤ]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {G F : C ⥤ D} [G.CommShift ℤ] {α : G ≅ F}
  (h : FunctorIsoShiftCompatibility G F α)

/-- Install the selected target shift and supplied compatibility so that
`CategoryTheory.Functor.isTriangulated_of_iso` can transport distinguished
triangles from the source functor. The source shift remains caller-selected,
which preserves presentation-specific conventions such as the cotwist sign. -/
theorem is_triangulated_of_iso [G.IsTriangulated] :
    letI : F.CommShift ℤ := h.targetCommShift
    F.IsTriangulated := by
  letI : F.CommShift ℤ := h.targetCommShift
  letI : NatTrans.CommShift α.hom ℤ := h.hom_commShift
  exact Functor.isTriangulated_of_iso α

/-- Transfer triangulatedness to an equivalence whose forward functor is the
comparison target. Mathlib derives the inverse and equivalence shift structures
from the selected forward structure before constructing the triangulated
equivalence. -/
theorem is_triangulated_of_equivalence_functor_eq {E : C ≌ D}
    (hEF : E.functor = F) [G.IsTriangulated] :
    letI : E.functor.CommShift ℤ := hEF ▸ h.targetCommShift
    letI : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
    letI : E.CommShift ℤ := E.commShift_of_functor ℤ
    E.IsTriangulated := by
  cases hEF
  letI : E.functor.CommShift ℤ := h.targetCommShift
  letI : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
  letI : E.CommShift ℤ := E.commShift_of_functor ℤ
  exact Equivalence.IsTriangulated.mk' E h.is_triangulated_of_iso

end FunctorIsoShiftCompatibility

end CategoryTheory.Triangulated

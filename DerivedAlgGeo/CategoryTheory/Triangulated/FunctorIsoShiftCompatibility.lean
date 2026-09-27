/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Shift-compatible isomorphisms of triangulated functors

This file packages the selected source and target `CommShift` structures for
an isomorphism of functors and transfers triangulatedness across that
isomorphism. The package is generic in the functors and is consumed by
Fourier--Mukai comparisons and other presentations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CategoryTheory.Triangulated

/-- Shift compatibility of a supplied natural isomorphism, relative to the
source functor's selected shift structure and an independently selected shift
structure on the target functor.

The source `CommShift` instance is an input to this record. Specializations
must preserve the shift structure already chosen by their presentation rather
than replacing it with one transported from the target. -/
structure FunctorIsoShiftCompatibility
    {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ]
    (G F : C ⥤ D) [G.CommShift ℤ] (α : G ≅ F) where
  /-- The independently selected shift structure on the target functor. -/
  targetCommShift : F.CommShift ℤ
  /-- The supplied isomorphism respects the selected source and target shifts. -/
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

/-- Transfer triangulatedness across the supplied isomorphism using the
selected source and target shift structures. -/
theorem targetIsTriangulated [G.IsTriangulated] :
    letI : F.CommShift ℤ := h.targetCommShift
    F.IsTriangulated := by
  letI : F.CommShift ℤ := h.targetCommShift
  letI : NatTrans.CommShift α.hom ℤ := h.hom_commShift
  exact Functor.isTriangulated_of_iso α

/-- Transfer triangulatedness to an equivalence whose functor is the target
of the supplied comparison, deriving the inverse and equivalence shift
structures from the selected forward structure. -/
theorem equivalenceIsTriangulatedOfEq {E : C ≌ D}
    (hEF : E.functor = F) [G.IsTriangulated] :
    letI : E.functor.CommShift ℤ := hEF ▸ h.targetCommShift
    letI : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
    letI : E.CommShift ℤ := E.commShift_of_functor ℤ
    E.IsTriangulated := by
  cases hEF
  letI : E.functor.CommShift ℤ := h.targetCommShift
  letI : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
  letI : E.CommShift ℤ := E.commShift_of_functor ℤ
  exact Equivalence.IsTriangulated.mk' E h.targetIsTriangulated

end FunctorIsoShiftCompatibility

end CategoryTheory.Triangulated

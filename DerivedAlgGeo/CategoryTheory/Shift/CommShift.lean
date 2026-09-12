/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Extensionality for functors commuting with shifts

Mathlib's `Functor.CommShift` is data: two structures on the same functor need
not agree by proof irrelevance.  They do agree when their family of
commutation isomorphisms agrees, because the zero and addition fields are
propositions.  This is the data-level comparison used when a shift structure
is assembled through two categorical presentations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v v' u u' w

namespace CategoryTheory.Functor.CommShift

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {A : Type w} [AddMonoid A] [HasShift C A] [HasShift D A]
  {F : C ⥤ D}

/-- Two `CommShift` structures on one functor agree when all their
commutation isomorphisms agree. -/
@[ext]
theorem ext (h h' : F.CommShift A)
    (w : ∀ n : A, h.commShiftIso n = h'.commShiftIso n) : h = h' := by
  cases h
  cases h'
  congr
  funext n
  exact w n

end CategoryTheory.Functor.CommShift

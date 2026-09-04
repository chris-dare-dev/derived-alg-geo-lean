/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.Orthogonal

/-!
# Left orthogonals are closed under colimits

A map out of a colimit is determined by its components, so if every object of a diagram is left
orthogonal to `P`, so is the colimit: the induced map and the zero map agree on every leg.

Mathlib's `Mathlib/CategoryTheory/ObjectProperty/Orthogonal.lean` gives both orthogonals
`IsClosedUnderIsomorphisms` and `ContainsZero`, and its `Triangulated/Orthogonal.lean` gives them
`IsTriangulatedClosed₂`. Closure under colimits is the one hypothesis of
`ObjectProperty.coprodClosure_le` that neither file supplies, which is why two compactly-generated
t-structure proofs each re-derived it by hand as three branches of an induction over
`coprodClosure`. With this instance both collapse to a single `coprodClosure_le` application.

The statement is for an arbitrary shape `J`, not just `Discrete ι`, because nothing in the argument
uses the shape: `IsColimit.hom_ext` is the whole proof. There is no dual instance for
`rightOrthogonal` under limits here, because no consumer needs one yet.
-/

universe v' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : ObjectProperty C)

instance instIsClosedUnderColimitsOfShapeLeftOrthogonal
    (J : Type u') [Category.{v'} J] :
    P.leftOrthogonal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨h⟩ Y f hY
    refine h.isColimit.hom_ext fun j => ?_
    rw [comp_zero]
    exact h.prop_diag_obj j _ hY

end CategoryTheory.ObjectProperty

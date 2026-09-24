/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Exactness

/-!
# Truncation finiteness along a t-exact functor

The component predicates `A` and `B` and the finiteness predicates `P` and `Q`
are independent. An object of `B` must lift, up to isomorphism, from an object
of `A`. Source truncations must satisfy `P`, and `F` must carry `P` into `Q`.
T-exactness then transports finiteness of each coconnective truncation.

This theorem neither constructs either t-structure nor supplies component
object descent or t-exactness. In particular, a lift only for a base-changed
component does not prove truncation finiteness on an entire ambient category.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u v' u'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Transfer a finiteness property of coconnective truncations across a
t-exact functor for objects in a chosen target component that lift from a
chosen source component. The lift and preservation of finiteness are inputs,
not conclusions about a geometric pullback. -/
theorem truncLE_mem_of_component_lift (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    (t : TStructure C) (t' : TStructure D) [F.IsTExact t t']
    (A P : ObjectProperty C) (B Q : ObjectProperty D)
    [Q.IsClosedUnderIsomorphisms]
    (hLift : ∀ Y : D, B Y → ∃ X : C, A X ∧ Nonempty (F.obj X ≅ Y))
    (hSource : ∀ X : C, A X → ∀ n : ℤ, P ((t.truncLE n).obj X))
    (hPres : ∀ X : C, P X → Q (F.obj X)) :
    ∀ Y : D, B Y → ∀ n : ℤ, Q ((t'.truncLE n).obj Y) := by
  intro Y hY n
  obtain ⟨X, hX, ⟨e⟩⟩ := hLift Y hY
  exact Q.prop_of_iso
    ((F.mapTruncLEIso t t' n X).trans ((t'.truncLE n).mapIso e))
    (hPres _ (hSource X hX n))

end CategoryTheory.Functor

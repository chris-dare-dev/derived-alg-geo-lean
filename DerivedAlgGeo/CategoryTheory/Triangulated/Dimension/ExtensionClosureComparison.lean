/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.GenerationTime
import DerivedAlgGeo.CategoryTheory.Triangulated.ExtensionClosure

/-!
# Extension closure and triangulated envelopes

This file compares `CategoryTheory.Triangulated.ExtensionClosure` with
Mathlib's `CategoryTheory.ObjectProperty.extensionProductIter` and
`CategoryTheory.ObjectProperty.triangEnvelope` without adding closure
operations or strengthening the owner extension closure. Every finite iterate
of `CategoryTheory.ObjectProperty.extensionProduct` lies in the owner
extension closure. Conversely, the whole owner extension closure lies in the
triangulated envelope when the generators are nonempty and the category is
triangulated.

## Main definitions

This file introduces no definitions. It reuses the owner extension closure
and Mathlib's extension-product and triangulated-envelope constructions.

## Main results

| Declaration | Role |
|---|---|
| `CategoryTheory.Triangulated.ExtensionClosure.extensionProductIter_le` | Finite iterates lie in the owner closure. |
| `CategoryTheory.Triangulated.ExtensionClosure.le_triangEnvelope` | Compares the owner closure and Mathlib's envelope under nonemptiness. |
| `CategoryTheory.Triangulated.ExtensionClosure.eq_iSup_extensionProductIter` | Identifies the owner closure with the supremum after adjoining zero objects. |
| `CategoryTheory.Triangulated.ExtensionClosure.extensionProductIter_le_triangEnvelopeIter` | Preserves the finite stage index. |
| `CategoryTheory.Triangulated.ExtensionClosure.generationTime_singleton_le_of_mem_extensionProductIter` | Converts a finite stage into a generation-time bound. |

## Implementation notes

The nonemptiness assumption in the envelope comparison is essential: for
`P = ⊥`, `CategoryTheory.Triangulated.ExtensionClosure P` contains every zero
object by its zero constructor, while
`CategoryTheory.ObjectProperty.triangEnvelope ⊥` is bottom. The supremum
equality adjoins `IsZero` because the owner closure contains zero objects even
when `P` is empty. For the numerical bound, a direct inclusion into
`triangEnvelopeIter n` preserves the stage index; passing through the whole
triangulated envelope would lose that bound.

The typeclass restatement of
`CategoryTheory.Triangulated.ExtensionClosure.le_of_closed` uses
`CategoryTheory.ObjectProperty.ContainsZero` together with closure under
isomorphisms: `ContainsZero` gives one zero object, and
`CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms` transfers membership
to every zero object.

## References

* `Mathlib.CategoryTheory.Triangulated.Subcategory`
* `Mathlib.CategoryTheory.Triangulated.Generators`
* `Mathlib.CategoryTheory.ObjectProperty.ContainsZero`

## Tags

extension closure, triangulated envelope, generation time
-/

universe v u

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace ExtensionClosure

/-- Every finite iterate of Mathlib's extension product is contained in the
repository's owner extension closure. The triangle in
`CategoryTheory.ObjectProperty.extensionProduct` has the orientation used by
`CategoryTheory.Triangulated.ExtensionClosure.ext`, so no rotation is needed. -/
theorem extensionProductIter_le (P : ObjectProperty C) (n : ℕ) :
    P.extensionProductIter n ≤ ExtensionClosure P := by
  induction n with
  | zero =>
      rw [ObjectProperty.extensionProductIter_zero]
      exact fun _ hP => .mem hP
  | succ n ih =>
      rw [ObjectProperty.extensionProductIter_succ]
      intro E hE
      obtain ⟨X, Y, f, g, h, hT, hX, hY⟩ :=
        (ObjectProperty.extensionProduct_iff P (P.extensionProductIter n) E).mp hE
      exact .ext hT (.mem hX) (ih Y hY)

/-- Induction into an isomorphism-closed property containing a zero object and
closed under distinguished extensions. The
`CategoryTheory.ObjectProperty.ContainsZero` witness is enough because
`CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms` transfers it to every
zero object. -/
theorem le_of_closed_under_isomorphisms {P Q : ObjectProperty C}
    [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] [Q.IsTriangulatedClosed₂]
    (hPQ : P ≤ Q) : ExtensionClosure P ≤ Q := by
  refine ExtensionClosure.le_of_closed (hzero := ?_) hPQ ?_
  · intro E hE
    exact Q.prop_of_isZero hE
  · intro X E Y f g h hT hX hY
    exact Q.ext_of_isTriangulatedClosed₂ (Triangle.mk f g h) hT hX hY

/-- If the generators are nonempty and the category is triangulated, the owner
extension closure is contained in Mathlib's triangulated envelope. The
`CategoryTheory.IsTriangulated` hypothesis supplies closure under distinguished
extensions, and nonemptiness supplies zero objects to that envelope.
Nonemptiness is essential: for `P = ⊥`, the owner closure contains zero
objects, but `CategoryTheory.ObjectProperty.triangEnvelope ⊥ = ⊥`. -/
theorem le_triangEnvelope (P : ObjectProperty C) [P.Nonempty] [IsTriangulated C] :
    ExtensionClosure P ≤ P.triangEnvelope := by
  exact le_of_closed_under_isomorphisms (P := P) (Q := P.triangEnvelope)
    (ObjectProperty.le_triangEnvelope P)

/-- The owner extension closure is exactly the supremum of Mathlib extension
iterates generated by `P` together with the zero-object property. The zero
property is needed because
`CategoryTheory.Triangulated.ExtensionClosure` contains zero objects even when
the original generator property is empty. -/
theorem eq_iSup_extensionProductIter (P : ObjectProperty C) [IsTriangulated C] :
    ExtensionClosure P =
      ⨆ n : ℕ, (P ⊔ (IsZero (C := C))).extensionProductIter n := by
  let P₀ : ObjectProperty C := P ⊔ (IsZero (C := C))
  apply le_antisymm
  · intro E hE
    induction hE with
    | zero hzero =>
        rw [ObjectProperty.prop_iSup_iff]
        refine ⟨0, ?_⟩
        simp only [ObjectProperty.extensionProductIter_zero,
          ObjectProperty.prop_sup_iff]
        exact Or.inr hzero
    | mem hP =>
        rw [ObjectProperty.prop_iSup_iff]
        refine ⟨0, ?_⟩
        simp only [ObjectProperty.extensionProductIter_zero,
          ObjectProperty.prop_sup_iff]
        exact Or.inl hP
    | ext hT _ _ ihX ihY =>
        rw [ObjectProperty.prop_iSup_iff] at ihX ihY ⊢
        obtain ⟨n, hn⟩ := ihX
        obtain ⟨m, hm⟩ := ihY
        refine ⟨n + (m + 1), ?_⟩
        rw [ObjectProperty.extensionProductIter_add' P₀ rfl]
        exact (ObjectProperty.extensionProduct_iff (P₀.extensionProductIter n)
          (P₀.extensionProductIter m) _).2 ⟨_, _, _, _, _, hT, hn, hm⟩
  · have hP₀ : P₀ ≤ ExtensionClosure P := by
        intro E hE
        rcases (ObjectProperty.prop_sup_iff P (IsZero (C := C)) E).mp hE with hP | hzero
        · exact .mem hP
        · exact .zero hzero
    have hIter : ∀ n, P₀.extensionProductIter n ≤ ExtensionClosure P := by
      intro n
      induction n with
      | zero =>
          rw [ObjectProperty.extensionProductIter_zero]
          exact hP₀
      | succ n ih =>
          rw [ObjectProperty.extensionProductIter_succ]
          intro E hE
          obtain ⟨X, Y, f, g, h, hT, hX, hY⟩ :=
            (ObjectProperty.extensionProduct_iff P₀
              (P₀.extensionProductIter n) E).mp hE
          exact .ext hT (hP₀ X hX) (ih Y hY)
    refine iSup_le fun n => ?_
    exact hIter n

/-- Mathlib's extension iterate at stage `n` lies in the corresponding
triangulated-envelope stage. This direct comparison preserves the finite step
bound used by `CategoryTheory.ObjectProperty.generationTime`. -/
theorem extensionProductIter_le_triangEnvelopeIter (P : ObjectProperty C) (n : ℕ) :
    P.extensionProductIter n ≤ P.triangEnvelopeIter n := by
  rw [ObjectProperty.triangEnvelopeIter]
  refine (ObjectProperty.monotone_extensionProductIter ?_ n).trans
    (ObjectProperty.le_retractClosure _)
  calc
    P ≤ P.shiftClosure ℤ := ObjectProperty.le_shiftClosure _
    _ ≤ (P.shiftClosure ℤ).binaryProductsClosure := ObjectProperty.le_limitsClosure _ _
    _ ≤ (P.shiftClosure ℤ).binaryProductsClosure.retractClosure :=
      ObjectProperty.le_retractClosure _

/-- An object in the `n`th extension-product iterate has generation time at
most `n`, by its direct inclusion into the `n`th triangulated-envelope stage. -/
theorem generationTime_singleton_le_of_mem_extensionProductIter
    (P : ObjectProperty C) {X : C} (n : ℕ)
    (hX : P.extensionProductIter n X) :
    P.generationTime (ObjectProperty.singleton X) ≤ (n : ℕ∞) := by
  apply (ObjectProperty.generationTime_le_coe_iff P (ObjectProperty.singleton X) n).2
  rw [ObjectProperty.singleton_le_iff]
  exact extensionProductIter_le_triangEnvelopeIter P n X hX

end ExtensionClosure

end CategoryTheory.Triangulated

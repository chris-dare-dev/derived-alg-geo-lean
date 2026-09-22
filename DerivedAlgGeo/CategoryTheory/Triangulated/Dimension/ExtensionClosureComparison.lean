/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.ExtensionClosure
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.GenerationTime
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Comparing extension closures

Downstream comparisons connect the repository's extension closure with Mathlib's
finite extension products, triangulated envelope, and generation-time API.

## Main definitions

This module adds no carrier or closure operation. The owner presentation remains
`CategoryTheory.Triangulated.ExtensionClosure`.

## Main results

| Declaration | Statement |
| --- | --- |
| `CategoryTheory.Triangulated.ExtensionClosure.le_of_closed_of_isTriangulatedClosed₂` | Repackages the raw closure hypotheses as typeclasses. |
| `CategoryTheory.Triangulated.ExtensionClosure.extensionProductIter_le` | Embeds every finite extension product in the owner closure. |
| `CategoryTheory.Triangulated.ExtensionClosure.le_triangEnvelope_of_isTriangulatedClosed₂` | Compares the owner closure with an envelope supplied with extension closure. |
| `CategoryTheory.Triangulated.ExtensionClosure.le_triangEnvelope` | Compares the owner closure with Mathlib's envelope in a triangulated category. |
| `CategoryTheory.Triangulated.ExtensionClosure.not_le_triangEnvelope_bot` | Records the empty-property counterexample. |
| `CategoryTheory.Triangulated.ExtensionClosure.eq_iSup_extensionProductIter` | Presents the owner closure as the supremum of zero-augmented finite iterates. |
| `CategoryTheory.Triangulated.ExtensionClosure.generationTime_singleton_le_of_mem_extensionProductIter` | Bounds singleton generation time by the iterate index. |

## Implementation notes

The finite-iterate comparison uses a local `IsTriangulatedClosed₂` witness, so
it adds no stronger public instance to the owner module. The supremum equality
adjoins `IsZero` to cover empty generators and uses associativity in its reverse
inclusion.

## References

`Mathlib.CategoryTheory.Triangulated.Subcategory` supplies the extension-product
and envelope APIs compared here.

## Tags

extension closure, extension products, triangulated envelope, generation time
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.ObjectProperty
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated.ExtensionClosure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {P Q : ObjectProperty C}

/-- The class-vocabulary form of
`CategoryTheory.Triangulated.ExtensionClosure.le_of_closed`.

These assumptions repackage the raw induction hypotheses: the typeclasses say
that `Q` contains zero objects, is closed under isomorphisms, and is closed
under distinguished extensions.  In the raw form, closure under zero objects
and distinguished extensions already implies isomorphism closure, so this
corollary does not assert strictly weaker hypotheses. -/
theorem le_of_closed_of_isTriangulatedClosed₂ [Q.ContainsZero]
    [Q.IsClosedUnderIsomorphisms] [Q.IsTriangulatedClosed₂] (h : P ≤ Q) :
    ExtensionClosure P ≤ Q := by
  apply ExtensionClosure.le_of_closed (Q := Q)
  · intro E hE
    exact Q.prop_of_isZero hE
  · exact h
  · intro X E Y f g k hT hX hY
    exact Q.ext_of_isTriangulatedClosed₂ _ hT hX hY

/-- Every Mathlib iterated extension product of `P` lies in the owner closure.

The local closure witness is exactly closure under distinguished extensions;
the owner module intentionally exports no such stronger instance. -/
theorem extensionProductIter_le (P : ObjectProperty C) (n : ℕ) :
    P.extensionProductIter n ≤ ExtensionClosure P := by
  letI : (ExtensionClosure P).IsTriangulatedClosed₂ := {
    ext₂' := fun T hT h₁ h₃ =>
      (ExtensionClosure P).le_isoClosure _ (ExtensionClosure.ext hT h₁ h₃) }
  exact P.extensionProductIter_le_of_isTriangulatedClosed₂
    (fun _ hP => ExtensionClosure.mem hP) n

/-- The owner closure is contained in the triangulated envelope when that
particular envelope is closed under distinguished extensions.

This form needs only `[P.Nonempty]` and
`[P.triangEnvelope.IsTriangulatedClosed₂]`; it does not require an ambient
`IsTriangulated C` instance. Mathlib's ambient triangulated instance is one way
to supply the local closure hypothesis. -/
theorem le_triangEnvelope_of_isTriangulatedClosed₂ (P : ObjectProperty C)
    [P.Nonempty] [P.triangEnvelope.IsTriangulatedClosed₂] :
    ExtensionClosure P ≤ P.triangEnvelope := by
  exact le_of_closed_of_isTriangulatedClosed₂ (Q := P.triangEnvelope)
    P.le_triangEnvelope

/-- The owner closure is contained in Mathlib's triangulated envelope when the
generator set is nonempty and the ambient category is triangulated.

The nonemptiness is necessary: for `P = ⊥`, the owner closure contains every
zero object while the triangulated envelope is bottom. -/
theorem le_triangEnvelope (P : ObjectProperty C) [P.Nonempty]
    [IsTriangulated C] :
    ExtensionClosure P ≤ P.triangEnvelope := by
  exact le_triangEnvelope_of_isTriangulatedClosed₂ P

/-- The reverse envelope comparison fails for the empty property: the owner
closure contains zero objects, whereas the empty property's triangulated
envelope is bottom. -/
theorem not_le_triangEnvelope_bot :
    ¬ ExtensionClosure (⊥ : ObjectProperty C) ≤
      (⊥ : ObjectProperty C).triangEnvelope := by
  intro h
  have hzero := h (0 : C) (ExtensionClosure.zero (isZero_zero C))
  simp [ObjectProperty.triangEnvelope, ObjectProperty.triangEnvelopeIter] at hzero

/-- The owner closure is the supremum of the finite extension iterates of
`P ⊔ IsZero` in a triangulated category.

Adjoining zero objects makes the statement valid even when `P` is empty.  The
reverse inclusion combines two finite iterates using the pinned Mathlib
associativity theorem, which is where `[IsTriangulated C]` is used. -/
theorem eq_iSup_extensionProductIter (P : ObjectProperty C)
    [IsTriangulated C] :
    ExtensionClosure P = ⨆ n, (P ⊔ IsZero).extensionProductIter n := by
  apply le_antisymm
  · intro E hE
    induction hE with
    | zero hZ =>
        exact (prop_iSup_iff _ _).2 ⟨0, Or.inr hZ⟩
    | mem hP =>
        exact (prop_iSup_iff _ _).2 ⟨0, Or.inl hP⟩
    | ext hT _ _ ihX ihY =>
        obtain ⟨n, hn⟩ := (prop_iSup_iff _ _).1 ihX
        obtain ⟨m, hm⟩ := (prop_iSup_iff _ _).1 ihY
        apply (prop_iSup_iff _ _).2
        refine ⟨n + (m + 1), ?_⟩
        rw [extensionProductIter_add' _ rfl]
        exact ⟨_, _, _, _, _, hT, hn, hm⟩
  · apply iSup_le
    intro n
    refine le_trans (extensionProductIter_le (P := P ⊔ IsZero) n) ?_
    apply ExtensionClosure.le_of_closed (P := P ⊔ IsZero) (Q := ExtensionClosure P)
      (fun hZ => ExtensionClosure.zero hZ)
    · intro X hX
      rcases hX with hP | hZ
      · exact ExtensionClosure.mem hP
      · exact ExtensionClosure.zero hZ
    · exact fun hT hX hY => ExtensionClosure.ext hT hX hY

/-- An object in the `n`th extension product of `P` has singleton generation
time at most `n`.

Starting from `P ≤ P.triangEnvelopeIter 0`, monotonicity of extension products
and retract closure place the `n`-fold extension product inside
`P.triangEnvelopeIter n`. This argument avoids the associativity step, so it
works under the pretriangulated assumptions alone. -/
theorem generationTime_singleton_le_of_mem_extensionProductIter
    (P : ObjectProperty C) (n : ℕ) {X : C}
    (hX : P.extensionProductIter n X) :
    P.generationTime (ObjectProperty.singleton X) ≤ (n : ℕ∞) := by
  apply (P.generationTime_le_coe_iff _ n).2
  rw [ObjectProperty.singleton_le_iff]
  have hP : P ≤ (P.shiftClosure ℤ).binaryProductsClosure.retractClosure := by
    simpa only [ObjectProperty.triangEnvelopeIter_zero] using P.le_triangEnvelopeIter 0
  exact le_retractClosure _ _ ((monotone_extensionProductIter hP n) X hX)

end CategoryTheory.Triangulated.ExtensionClosure

end

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.ExtensionClosure
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.GenerationTime
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Comparing extension closures

Downstream comparison lemmas between the repository's owner `ExtensionClosure`
and Mathlib's iterated extension products and triangulated envelope.  The
owner closure remains an `ObjectProperty` with only its proved properties.
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

/-- The class-vocabulary form of `ExtensionClosure.le_of_closed`.

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

/-- The owner closure is contained in Mathlib's triangulated envelope when the
generator set is nonempty and the ambient category is triangulated.

The nonemptiness is necessary: for `P = ⊥`, the owner closure contains every
zero object while the triangulated envelope is bottom. -/
theorem le_triangEnvelope (P : ObjectProperty C) [P.Nonempty]
    [IsTriangulated C] :
    ExtensionClosure P ≤ P.triangEnvelope := by
  exact le_of_closed_of_isTriangulatedClosed₂ (Q := P.triangEnvelope)
    P.le_triangEnvelope

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

This bound needs only the pretriangulated hypotheses of the generation-time
API; no ambient triangulatedness or nonempty-generator assumption is used. -/
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

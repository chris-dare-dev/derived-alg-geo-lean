/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Quasi-isomorphisms in short exact sequences of complexes

For a morphism of short exact sequences of integer-indexed cochain complexes
in an abelian category, quasi-isomorphisms on the outer terms imply one on
the middle term.

## Main results

* `HomologicalComplex.HomologySequence.quasiIso_τ₂` gives the middle-term
  quasi-isomorphism without choosing a model for the abelian category.

## Implementation notes

The long exact homology sequences supply two five-object windows. The four
lemma gives monicity in the window ending at the current degree and epicity
in the window beginning there. These combine into an isomorphism on each
homology object.

## References

This extends Mathlib's `HomologicalComplex.HomologySequence.quasiIso_τ₃`
and uses its exact five-object homology sequence and the abelian four lemmas.
-/

open CategoryTheory Category Limits

namespace HomologicalComplex

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
  (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

include hS₁ hS₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If the outer maps in a morphism of short exact sequences of cochain
complexes are quasi-isomorphisms, then so is the middle map. -/
lemma HomologySequence.quasiIso_τ₂
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (homologyMap φ.τ₂ i) := by
    have hi : (ComplexShape.up ℤ).Rel (i - 1) i := by simp
    apply Abelian.mono_of_epi_of_mono_of_mono'' (n := 5) (k := 2) (by omega)
      (HomologySequence.composableArrows₅_exact hS₁ (i - 1) i hi)
      (HomologySequence.composableArrows₅_exact hS₂ (i - 1) i hi)
      (HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ (i - 1) i hi)
      2 3 4 5 rfl rfl rfl rfl
    all_goals dsimp
    all_goals infer_instance
  have hepi : Epi (homologyMap φ.τ₂ i) := by
    have hi : (ComplexShape.up ℤ).Rel i (i + 1) := by simp
    apply Abelian.epi_of_epi_of_epi_of_mono'' (n := 5) (k := 0) (by omega)
      (HomologySequence.composableArrows₅_exact hS₁ i (i + 1) hi)
      (HomologySequence.composableArrows₅_exact hS₂ i (i + 1) hi)
      (HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ i (i + 1) hi)
      0 1 2 3 rfl rfl rfl rfl
    all_goals dsimp
    all_goals infer_instance
  exact isIso_of_mono_of_epi _

end HomologicalComplex

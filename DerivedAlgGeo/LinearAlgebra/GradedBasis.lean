/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Graded pieces determined by a weighted basis

Given a basis-like family `b : ι → A` and a weight `w : ι → ℕ`, this file
defines the weight-`k` submodule as the span of the corresponding basis
vectors. It proves that a linearly independent spanning family gives an
internal direct-sum decomposition and that multiplicativity may be checked on
basis vectors.

The construction is independent of numerical intersection rings and algebraic
geometry. Geometric numerical-ring constructors consume it from
`AlgebraicGeometry/Numerical/Core/GradedBasis.lean`.
-/

universe u v

open Submodule Set

namespace DerivedAlgGeo.LinearAlgebra

variable {ι : Type v} {A : Type u} [CommRing A] [Algebra ℚ A]

/-- The span of the vectors of weight `k`. -/
def gradedPiece (b : ι → A) (w : ι → ℕ) (k : ℕ) : Submodule ℚ A :=
  span ℚ (b '' (w ⁻¹' {k}))

variable {b : ι → A} {w : ι → ℕ} {n : ℕ}

/-- Every vector of the indexed family lies in its own graded piece. -/
theorem mem_gradedPiece (i : ι) : b i ∈ gradedPiece b w (w i) :=
  subset_span ⟨i, rfl, rfl⟩

/-- If all weights are at most `n`, every graded piece above `n` vanishes. -/
theorem gradedPiece_eq_bot (hw : ∀ i, w i ≤ n) {k : ℕ} (hk : n < k) :
    gradedPiece b w k = ⊥ := by
  have hempty : w ⁻¹' {k} = (∅ : Set ι) := by
    ext i
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    intro h
    have := hw i
    omega
  rw [gradedPiece, hempty, image_empty, span_empty]

/-- Graded pieces cut out by distinct weights are independent. -/
theorem gradedPiece_iSupIndep (hb : LinearIndependent ℚ b) :
    iSupIndep (gradedPiece b w) := by
  intro k
  have key : Disjoint (span ℚ (b '' (w ⁻¹' {k}))) (span ℚ (b '' (w ⁻¹' {k})ᶜ)) :=
    hb.disjoint_span_image disjoint_compl_right
  refine Disjoint.mono_right ?_ key
  refine iSup_le fun j => iSup_le fun hj => span_mono (image_mono ?_)
  intro i hi
  simp only [mem_preimage, mem_singleton_iff] at hi
  simp only [mem_compl_iff, mem_preimage, mem_singleton_iff]
  rw [hi]
  exact hj

/-- The graded pieces span whenever the indexed family spans. -/
theorem gradedPiece_iSup_eq_top (hsp : span ℚ (range b) = ⊤) :
    ⨆ k, gradedPiece b w k = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hsp, span_le]
  rintro _ ⟨i, rfl⟩
  exact Submodule.mem_iSup_of_mem (w i) (mem_gradedPiece i)

/-- A linearly independent spanning family decomposes the module as the
direct sum of its weight pieces. -/
theorem gradedPiece_isInternal (hb : LinearIndependent ℚ b)
    (hsp : span ℚ (range b) = ⊤) :
    DirectSum.IsInternal (gradedPiece b w) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradedPiece_iSupIndep hb) (gradedPiece_iSup_eq_top hsp)

/-- Multiplicativity of the grading, promoted from indexed vectors to all
elements of their weight pieces. -/
theorem gradedPiece_mul_mem
    (hmul : ∀ p q : ι, b p * b q ∈ gradedPiece b w (w p + w q))
    {i j : ℕ} {x y : A} (hx : x ∈ gradedPiece b w i)
    (hy : y ∈ gradedPiece b w j) :
    x * y ∈ gradedPiece b w (i + j) := by
  have hle : gradedPiece b w i * gradedPiece b w j ≤ gradedPiece b w (i + j) := by
    rw [gradedPiece, gradedPiece, Submodule.span_mul_span, span_le]
    rintro _ ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩
    simp only [mem_preimage, mem_singleton_iff] at hp hq
    rw [← hp, ← hq]
    exact hmul p q
  exact hle (Submodule.mul_mem_mul hx hy)

end DerivedAlgGeo.LinearAlgebra

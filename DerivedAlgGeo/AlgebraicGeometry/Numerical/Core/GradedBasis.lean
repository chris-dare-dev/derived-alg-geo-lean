/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Core.Definitions
import DerivedAlgGeo.LinearAlgebra.GradedBasis

/-!
# Constructing a `NumericalRingData` from a graded basis

The generic weighted-basis decomposition belongs to
`DerivedAlgGeo.LinearAlgebra.GradedBasis`. This geometric consumer combines
that decomposition with a top-degree functional to construct the numerical
intersection-ring presentation `NumericalRingData`.

Given a basis `b : Module.Basis ι ℚ A` and a weight `w : ι → ℕ` bounded by
`n`, the caller supplies three finite checks: that `1` lies in weight zero,
that products of basis vectors respect weights, and that the degree map kills
every basis vector outside top weight. The generic linear-algebra root supplies
internality and vanishing above `n`.
-/

universe u v

open Submodule Set

namespace AlgebraicGeometry.Numerical

open DerivedAlgGeo.LinearAlgebra

variable {ι : Type v} {A : Type u} [CommRing A] [Algebra ℚ A]

/-- **Build a `NumericalRingData` from a graded basis.**

The caller supplies the basis, the weight function, and three finite checks:
that `1` sits in codimension zero, that products of basis vectors respect the
grading, and that the degree map kills every piece but the top one. -/
@[reducible]
noncomputable def NumericalRingData.ofGradedBasis (n : ℕ)
    (b : Module.Basis ι ℚ A) (w : ι → ℕ)
    (hw : ∀ i, w i ≤ n)
    (hone : (1 : A) ∈ gradedPiece (b : ι → A) w 0)
    (hmul : ∀ p q : ι, (b : ι → A) p * (b : ι → A) q ∈
      gradedPiece (b : ι → A) w (w p + w q))
    (deg : A →ₗ[ℚ] ℚ)
    (hdeg : ∀ i : ι, w i ≠ n → deg (b i) = 0) :
    NumericalRingData n A where
  piece := gradedPiece (b : ι → A) w
  isInternal := gradedPiece_isInternal b.linearIndependent b.span_eq
  piece_eq_bot_of_lt _ hk := gradedPiece_eq_bot hw hk
  one_mem_piece_zero := hone
  mul_mem_piece hx hy := gradedPiece_mul_mem hmul hx hy
  degree := deg
  degree_eq_zero_of_mem := by
    intro k x hk hx
    have hsub : gradedPiece (b : ι → A) w k ≤ LinearMap.ker deg := by
      rw [gradedPiece, span_le]
      rintro _ ⟨i, hi, rfl⟩
      simp only [mem_preimage, mem_singleton_iff] at hi
      exact hdeg i (hi ▸ hk)
    exact hsub hx

/-! ### Smoke test

This exercises every hypothesis of `ofGradedBasis` on the dimension-zero
intersection ring `ℚ` of a point. The exported point presentation is built
independently in `Numerical/Examples/DimensionZero/Point.lean`. -/

section SmokeTest

private noncomputable def pointBasis : Module.Basis Unit ℚ ℚ :=
  Module.Basis.singleton Unit ℚ

private theorem pointGradedPiece_zero :
    gradedPiece (⇑pointBasis) (fun _ : Unit => (0 : ℕ)) 0 = ⊤ := by
  have hpre : (fun _ : Unit => (0 : ℕ)) ⁻¹' {0} = (univ : Set Unit) := by
    ext i
    simp
  rw [gradedPiece, hpre, image_univ, pointBasis.span_eq]

@[reducible]
private noncomputable def pointRingViaGradedBasis : NumericalRingData 0 ℚ :=
  NumericalRingData.ofGradedBasis 0 pointBasis (fun _ => 0)
    (fun _ => le_refl 0)
    (by rw [pointGradedPiece_zero]; trivial)
    (fun p q => by
      have h : gradedPiece (⇑pointBasis) (fun _ : Unit => (0 : ℕ))
          ((fun _ : Unit => (0 : ℕ)) p + (fun _ : Unit => (0 : ℕ)) q) = ⊤ :=
        pointGradedPiece_zero
      rw [h]
      trivial)
    LinearMap.id
    (fun _ hi => absurd rfl hi)

end SmokeTest

end AlgebraicGeometry.Numerical

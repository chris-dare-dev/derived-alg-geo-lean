/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PositiveFrame
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.Continuous

/-!
# A Sylvester criterion for a positive frame, and openness

`IsPositiveFrame` is stated as a condition on the plane a pair spans. This file
gives the equivalent condition on the pair itself,

```
IsPositiveFrame Q x y ↔ 0 < Q x ∧ 0 < 4 * Q x * Q y - (polar Q x y) ^ 2,
```

which is Sylvester's criterion for the `2 × 2` Gram matrix, and which subsumes
independence: a pair satisfying it spans a plane rather than a line, so the
`finrank = 2` clause comes free.

Both sides of the criterion are continuous, so **the positive frames form an open
set** — the fact a genericity argument needs, and the reason this file exists.
-/

open QuadraticMap Bornology

namespace PeriodDomain

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}

/-- The value of `Q` on a combination, in terms of the pair's Gram data. -/
theorem apply_smul_add_smul (x y : M) (a b : ℝ) :
    Q (a • x + b • y) = a * a * Q x + a * b * polar (⇑Q) x y + b * b * Q y := by
  have h₁ : polar (⇑Q) (a • x) (b • y) = a * b * polar (⇑Q) x y := by
    rw [polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul]
    ring
  have h₂ : polar (⇑Q) (a • x) (b • y) = Q (a • x + b • y) - Q (a • x) - Q (b • y) := rfl
  rw [QuadraticMap.map_smul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul] at h₂
  rw [h₁] at h₂
  linarith

/-- **Sylvester's criterion for a pair.** The `2 × 2` Gram matrix of `(x, y)` is
positive definite exactly when `Q x` and the discriminant are positive, and that
is exactly the condition that the pair spans a positive plane. -/
theorem isPositiveFrame_iff (x y : M) :
    IsPositiveFrame Q x y ↔
      0 < Q x ∧ 0 < 4 * Q x * Q y - (polar (⇑Q) x y) ^ 2 := by
  constructor
  · intro h
    have hx : x ∈ pairSpan x y := Submodule.subset_span (by simp)
    have hy : y ∈ pairSpan x y := Submodule.subset_span (by simp)
    have hxne : x ≠ 0 := by
      intro hx0
      have := combination_ne_zero h (a := 1) (b := 0) (Or.inl one_ne_zero)
      simp [hx0] at this
    have hQx : 0 < Q x := by
      have := h.posDef ⟨x, hx⟩ (by simpa using hxne)
      rwa [restrict_apply] at this
    refine ⟨hQx, ?_⟩
    -- the quadratic `t ↦ Q (t • x + y)` is positive, so its discriminant is negative
    by_contra hdisc
    push Not at hdisc
    set t : ℝ := -(polar (⇑Q) x y) / (2 * Q x) with ht
    have hcomb : Q (t • x + (1 : ℝ) • y)
        = 0 + (4 * Q x * Q y - (polar (⇑Q) x y) ^ 2) / (4 * Q x) := by
      rw [apply_smul_add_smul, ht]
      field_simp
      ring
    have hne : t • x + (1 : ℝ) • y ≠ 0 := combination_ne_zero h (Or.inr one_ne_zero)
    have hmem : t • x + (1 : ℝ) • y ∈ pairSpan x y :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ hy)
    have hpos := h.posDef ⟨_, hmem⟩ (by simpa using hne)
    rw [restrict_apply, hcomb] at hpos
    have hquot : (4 * Q x * Q y - (polar (⇑Q) x y) ^ 2) / (4 * Q x) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hdisc (by linarith)
    linarith
  · rintro ⟨hQx, hdisc⟩
    have hvals : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → 0 < Q (a • x + b • y) := by
      intro a b hab
      rw [apply_smul_add_smul]
      rcases eq_or_ne b 0 with rfl | hb
      · have ha : a ≠ 0 := by tauto
        have : 0 < a * a := mul_self_pos.mpr ha
        simpa using mul_pos this hQx
      · nlinarith [sq_nonneg (2 * Q x * a + polar (⇑Q) x y * b), mul_self_pos.mpr hb, hQx, hdisc]
    have hne : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → a • x + b • y ≠ 0 := by
      intro a b hab h0
      have := hvals a b hab
      rw [h0, map_zero] at this
      exact lt_irrefl _ this
    -- the pair is independent, so its span is a plane
    have hindep : LinearIndependent ℝ ![x, y] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_contra hcon
      have hor : s ≠ 0 ∨ t ≠ 0 := by
        rcases eq_or_ne s 0 with rfl | hs
        · exact Or.inr fun h => hcon ⟨rfl, h⟩
        · exact Or.inl hs
      exact hne s t hor hst
    constructor
    · have hrange : ({x, y} : Set M) = Set.range ![x, y] := by
        ext z
        simp
        tauto
      rw [pairSpan, hrange]
      simpa using finrank_span_eq_card hindep
    · rintro ⟨v, hv⟩ hv0
      rw [pairSpan, Submodule.mem_span_pair] at hv
      obtain ⟨a, b, rfl⟩ := hv
      rw [restrict_apply]
      refine hvals a b ?_
      by_contra hcon
      push Not at hcon
      exact hv0 (by simp [hcon.1, hcon.2])

section Topology

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
variable (Q : QuadraticForm ℝ N)

/-- **The positive frames form an open set.** Both halves of the Sylvester
criterion are continuous. -/
theorem isOpen_setOf_isPositiveFrame :
    IsOpen {p : N × N | IsPositiveFrame Q p.1 p.2} := by
  have hQ := continuous_of_finiteDimensional Q
  have hpolar := continuous_polar Q
  have hset : {p : N × N | IsPositiveFrame Q p.1 p.2}
      = {p : N × N | 0 < Q p.1} ∩
        {p : N × N | 0 < 4 * Q p.1 * Q p.2 - (polar (⇑Q) p.1 p.2) ^ 2} := by
    ext p
    exact isPositiveFrame_iff p.1 p.2
  rw [hset]
  refine IsOpen.inter ?_ ?_
  · exact isOpen_lt continuous_const (hQ.comp continuous_fst)
  · refine isOpen_lt continuous_const ?_
    exact ((continuous_const.mul (hQ.comp continuous_fst)).mul
      (hQ.comp continuous_snd)).sub (hpolar.pow 2)

end Topology

end PeriodDomain

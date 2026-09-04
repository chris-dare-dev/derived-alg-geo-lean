/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# The support property and its quadratic form

Kontsevich–Soibelman's *support property* for a central charge asks for a
uniform comparison `‖v‖ ≤ C ‖Z v‖` over a distinguished set of classes. The
formulation used throughout the modern literature replaces that estimate by a
**quadratic form** `Q` which is nonnegative on the distinguished set and
negative definite on `ker Z`. This file proves the two are equivalent.

## What this is a theorem about

`S` here is **an arbitrary subset** of a finite-dimensional real normed space.
In the intended application it is the set of classes of `σ`-semistable objects,
but that identification needs a stability condition and is not made here: no
declaration below mentions a triangulated category, a slicing, or anything
else in `StabilityCondition/`. Every statement is linear algebra plus one
compactness argument, and
would hold verbatim for any other choice of `S`.

The intended `W` is `ℂ`; the proofs never use anything about the target beyond
its norm, so it is left general.

## Why the hypotheses on `Q` are what they are

The proofs use exactly two properties of a quadratic form: continuity and
degree-two homogeneity. Both directions are therefore stated for
`IsHomogTwo`, which is strictly weaker than being a quadratic form — see its
docstring. This makes both theorems stronger and costs nothing, since every
quadratic form on a finite-dimensional real space satisfies it.

## Main results

* `hasSupportProperty_of_isCompatible` — the compactness direction.
* `exists_isCompatible_of_hasSupportProperty` — the explicit direction, via
  `Q v = C² ‖Z v‖² - ‖v‖²`.
* `hasSupportProperty_iff` — the equivalence.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.Support

open Metric

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

variable (Z : V →ₗ[ℝ] W) (S : Set V)

/-- The support property: a uniform linear comparison of the norm of a class
with the norm of its charge, over the distinguished set `S`. -/
def HasSupportProperty : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ v ∈ S, ‖v‖ ≤ C * ‖Z v‖

/-- The two properties of a quadratic form that the equivalence below actually
uses: continuity and homogeneity of degree two.

**This is deliberately weaker than being a quadratic form.** Continuity plus
`Q (a • v) = a² Q v` does not imply bilinearity: `Q (x, y) = |x * y|` on `ℝ²`
satisfies both and is not a quadratic form. Stating the hypothesis this way
makes both directions stronger theorems and costs nothing, because every
quadratic form on a finite-dimensional real space satisfies it. -/
structure IsHomogTwo (Q : V → ℝ) : Prop where
  /-- `Q` is continuous -/
  continuous : Continuous Q
  /-- `Q` is homogeneous of degree two -/
  smul : ∀ (a : ℝ) (v : V), Q (a • v) = a ^ 2 * Q v

/-- Compatibility of a form with the pair `(Z, S)`: nonnegative on `S`, and
negative definite on `ker Z`. -/
structure IsCompatible (Q : V → ℝ) : Prop where
  /-- `Q` is nonnegative on the distinguished set -/
  nonneg_of_mem : ∀ v ∈ S, 0 ≤ Q v
  /-- `Q` is negative definite on the kernel of the charge -/
  neg_of_ker : ∀ v : V, Z v = 0 → v ≠ 0 → Q v < 0

variable {Z S}

/-- The compact slice the argument runs on: the unit sphere cut by `Q ≥ 0`. -/
def slice (Q : V → ℝ) : Set V := Metric.sphere (0 : V) 1 ∩ {v | 0 ≤ Q v}

theorem isCompact_slice {Q : V → ℝ} (hQ : IsHomogTwo Q) : IsCompact (slice Q) :=
  (isCompact_sphere (0 : V) 1).inter_right (isClosed_le continuous_const hQ.continuous)

omit [FiniteDimensional ℝ V] in
/-- Normalising a nonzero vector on which `Q` is nonnegative lands in the
slice. This is the only place degree-two homogeneity is used. -/
theorem norm_inv_smul_mem_slice {Q : V → ℝ} (hQ : IsHomogTwo Q) {v : V} (hv : v ≠ 0)
    (hQv : 0 ≤ Q v) : ‖v‖⁻¹ • v ∈ slice Q := by
  have hn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  refine ⟨?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
    field_simp
  · show 0 ≤ Q (‖v‖⁻¹ • v)
    rw [hQ.smul]
    exact mul_nonneg (sq_nonneg _) hQv

/-- **The support property follows from a compatible form.**

The slice is compact and `Z` does not vanish on it, so `‖Z ·‖` attains a
positive minimum there; the comparison constant is its reciprocal. -/
theorem hasSupportProperty_of_isCompatible {Q : V → ℝ}
    (hQ : IsHomogTwo Q) (hc : IsCompatible Z S Q) :
    HasSupportProperty Z S := by
  have hZcont : Continuous fun v : V => ‖Z v‖ := Z.continuous_of_finiteDimensional.norm
  rcases (slice Q).eq_empty_or_nonempty with hempty | hne
  · -- The slice is empty, so `S` contains only zero and any constant works.
    refine ⟨1, one_pos, fun v hv => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    · exfalso
      have hmem := norm_inv_smul_mem_slice hQ hv0 (hc.nonneg_of_mem v hv)
      rw [hempty] at hmem
      exact hmem
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_slice hQ).exists_isMinOn hne hZcont.continuousOn
  have hv₀ne : v₀ ≠ 0 := by
    intro h
    have := hv₀.1
    rw [mem_sphere_zero_iff_norm, h, norm_zero] at this
    exact zero_ne_one this
  have hm : 0 < ‖Z v₀‖ := by
    rw [norm_pos_iff]
    intro h
    exact absurd hv₀.2 (not_le.mpr (hc.neg_of_ker v₀ h hv₀ne))
  refine ⟨‖Z v₀‖⁻¹, inv_pos.mpr hm, fun v hv => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  have hmem := norm_inv_smul_mem_slice hQ hv0 (hc.nonneg_of_mem v hv)
  have hle : ‖Z v₀‖ ≤ ‖Z (‖v‖⁻¹ • v)‖ := isMinOn_iff.mp hmin _ hmem
  rw [map_smul, norm_smul, norm_inv, norm_norm] at hle
  rw [inv_mul_eq_div, le_div_iff₀ hn, ← le_div_iff₀' hm] at hle
  rwa [div_eq_inv_mul] at hle

/-- **A compatible form follows from the support property.**

The witness is explicit: `Q v = C² ‖Z v‖² - ‖v‖²`. On `S` it is nonnegative by
squaring the support estimate, and on `ker Z` it is `-‖v‖²`. -/
theorem exists_isCompatible_of_hasSupportProperty (h : HasSupportProperty Z S) :
    ∃ Q : V → ℝ, IsHomogTwo Q ∧ IsCompatible Z S Q := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨fun v => C ^ 2 * ‖Z v‖ ^ 2 - ‖v‖ ^ 2, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (continuous_const.mul (Z.continuous_of_finiteDimensional.norm.pow 2)).sub
      (continuous_norm.pow 2)
  · intro a v
    simp only [map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  · intro v hv
    have hb := hbound v hv
    have key : ‖v‖ ^ 2 ≤ (C * ‖Z v‖) ^ 2 := by
      refine sq_le_sq' ?_ hb
      have h1 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
      have h2 : (0 : ℝ) ≤ C * ‖Z v‖ := mul_nonneg hC.le (norm_nonneg _)
      linarith
    rw [mul_pow] at key
    linarith
  · intro v hZ hv
    have : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
    simp only [hZ, norm_zero]
    nlinarith

/-- **The support property is exactly the existence of a compatible form.**

This is the Kontsevich–Soibelman reformulation, at the level of the numerical
data it is a statement about. -/
theorem hasSupportProperty_iff :
    HasSupportProperty Z S ↔ ∃ Q : V → ℝ, IsHomogTwo Q ∧ IsCompatible Z S Q :=
  ⟨exists_isCompatible_of_hasSupportProperty,
    fun ⟨_, hQ, hc⟩ => hasSupportProperty_of_isCompatible hQ hc⟩

/-! ### Elementary consequences

Both are immediate from the definition and are stated because they are the
sanity checks a reader will want: the property is monotone in `S`, and it
forces the charge to be injective on the span of `S` in the strong pointwise
sense. -/

omit [FiniteDimensional ℝ V] in
theorem HasSupportProperty.mono {S' : Set V} (h : HasSupportProperty Z S)
    (hS : S' ⊆ S) : HasSupportProperty Z S' := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun v hv => hb v (hS hv)⟩

omit [FiniteDimensional ℝ V] in
/-- A class in `S` with vanishing charge is zero. -/
theorem HasSupportProperty.eq_zero_of_charge_eq_zero (h : HasSupportProperty Z S)
    {v : V} (hv : v ∈ S) (hZ : Z v = 0) : v = 0 := by
  obtain ⟨C, _, hb⟩ := h
  have := hb v hv
  rw [hZ, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.mp this

/-! ### Stability under perturbation of the charge

The support property is an **open** condition on `Z`. That is what makes it the
right hypothesis for a deformation argument: a charge that has it keeps it under
any sufficiently small change, so the property propagates along a path rather
than having to be re-established at every point.

None of this uses compactness, the quadratic form, or finite-dimensionality —
only the triangle inequality and one division — so all three are stated with
`FiniteDimensional` omitted. The topological statement at the end is the only
one that needs a norm on the space of charges, and it is a corollary of the
other two rather than a separate argument. -/

omit [FiniteDimensional ℝ V] in
/-- **The support property survives a small perturbation of the charge.**

Both the constant and the closeness bound are explicit, because the admissible
size of the perturbation depends on `C`: an estimate that is only barely true
tolerates only a barely nonzero change. The perturbed constant is
`C / (1 - Cε)`, which degrades to `+∞` exactly as `Cε → 1`. -/
theorem hasSupportProperty_of_norm_sub_le {Z' : V →ₗ[ℝ] W} {C ε : ℝ}
    (hC : 0 < C) (hb : ∀ v ∈ S, ‖v‖ ≤ C * ‖Z v‖)
    (hε : ∀ v : V, ‖Z' v - Z v‖ ≤ ε * ‖v‖) (hCε : C * ε < 1) :
    HasSupportProperty Z' S := by
  have hden : 0 < 1 - C * ε := by linarith
  refine ⟨C / (1 - C * ε), div_pos hC hden, fun v hv => ?_⟩
  have h1 : ‖v‖ ≤ C * ‖Z v‖ := hb v hv
  have h3 : ‖Z v - Z' v‖ ≤ ε * ‖v‖ := by
    rw [norm_sub_rev]; exact hε v
  have h2 : ‖Z v‖ ≤ ‖Z' v‖ + ε * ‖v‖ := by
    calc ‖Z v‖ = ‖Z' v + (Z v - Z' v)‖ := by congr 1; abel
      _ ≤ ‖Z' v‖ + ‖Z v - Z' v‖ := norm_add_le _ _
      _ ≤ ‖Z' v‖ + ε * ‖v‖ := by linarith
  have h4 : C * ‖Z v‖ ≤ C * (‖Z' v‖ + ε * ‖v‖) := mul_le_mul_of_nonneg_left h2 hC.le
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [h1, h4]

omit [FiniteDimensional ℝ V] in
/-- **Openness, stated without a topology on the space of charges.**

Every charge with the support property admits a positive tolerance inside which
every other charge still has it. `isOpen_hasSupportProperty` is this made
topological; this form is separated out because it needs no norm on the space of
maps and so applies to plain linear maps. -/
theorem HasSupportProperty.exists_tolerance (h : HasSupportProperty Z S) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Z' : V →ₗ[ℝ] W,
      (∀ v : V, ‖Z' v - Z v‖ ≤ ε * ‖v‖) → HasSupportProperty Z' S := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨(2 * C)⁻¹, by positivity, fun Z' hZ' => ?_⟩
  refine hasSupportProperty_of_norm_sub_le hC hb hZ' ?_
  rw [inv_eq_one_div, mul_one_div, div_lt_one (by positivity)]
  linarith

omit [FiniteDimensional ℝ V] in
variable (S) in
/-- **The charges with the support property form an open set.**

`S` is fixed and the charges are topologized by the operator norm. This is the
`IsOpen` form of `HasSupportProperty.exists_tolerance`; the mathematical content
is entirely in that lemma, and the only step here is `le_opNorm`. -/
theorem isOpen_hasSupportProperty :
    IsOpen {Z : V →L[ℝ] W | HasSupportProperty (Z : V →ₗ[ℝ] W) S} := by
  rw [Metric.isOpen_iff]
  rintro Z (hZ : HasSupportProperty _ S)
  obtain ⟨ε, hε, hmain⟩ := hZ.exists_tolerance
  refine ⟨ε, hε, fun Z' hZ' => ?_⟩
  refine hmain (Z' : V →ₗ[ℝ] W) fun v => ?_
  have hle : ‖Z' - Z‖ ≤ ε := (mem_ball_iff_norm.mp hZ').le
  calc ‖(Z' : V →ₗ[ℝ] W) v - (Z : V →ₗ[ℝ] W) v‖
      = ‖(Z' - Z) v‖ := by simp
    _ ≤ ‖Z' - Z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg v)

end CategoryTheory.Triangulated.WeakStabilityCondition.Support

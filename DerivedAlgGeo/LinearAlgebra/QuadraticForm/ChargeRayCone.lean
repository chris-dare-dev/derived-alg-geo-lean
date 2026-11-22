/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The cone of a quadratic form over a ray of charges

Let `Q` be a quadratic form on a real vector space `V` and `Z : V →ₗ[ℝ] ℂ` a charge
whose kernel is negative semidefinite for `Q`. Fix `ζ : ℂ`. The classes `x` with
`0 ≤ Q x` and charge on the open ray `ℝ_{>0} ζ`, together with `0`, form a convex
cone. This is Lemma A.7 of Bayer–Macrì–Stellari, arXiv:1410.1585.

It is the numerical half of the statement that the support property survives
wall-crossing: Jordan--Hölder factors of a semistable object have charges on one
ray, so `0 ≤ Q` on the factors gives `0 ≤ Q` on the object.

Convexity fails for a sector of positive angle, even a small one. Take a normalized
pair, `Q v = ‖Z v‖ ^ 2 - ‖p v‖ ^ 2`, and two classes with `‖p v‖ = ‖Z v‖`, equal
kernel directions and different charge directions. Their sum has `Q < 0`.

## Main definitions

* `QuadraticMap.chargeRayCone Q Z ζ`: `0` together with the classes `x` with
  `0 ≤ Q x` and `Z x ∈ ℝ_{>0} ζ`.

## Main results

* `QuadraticMap.polar_nonneg_of_charge_eq`: two classes with `0 ≤ Q` and charges on
  one open ray have nonnegative polar form.
* `QuadraticMap.add_mem_chargeRayCone`, `QuadraticMap.smul_mem_chargeRayCone`,
  `QuadraticMap.convex_chargeRayCone`: the set is a convex cone (BMS16, Lemma A.7).

## Implementation notes

The source argues by counting sign changes of `t ↦ Q (x + t y)`. Here the argument
is shorter: if `Z x = r ζ` and `Z y = s ζ` with `r, s > 0`, then `s x - r y` lies in
`ker Z`. So `0 ≥ Q (s x - r y) = s² Q x + r² Q y - s r · polar Q x y`, hence
`polar Q x y ≥ 0` and `Q (x + y) = Q x + Q y + polar Q x y ≥ 0`.

Only semidefiniteness on the kernel is used. The open ray matters: with `Z y = 0`
allowed, `Q (x, y) = x y` and `Z (x, y) = x` give `Q ((1, 0) + (0, -1)) < 0`.

## References

* Bayer, Macrì, Stellari, *The space of stability conditions on abelian threefolds,
  and on some Calabi-Yau threefolds*, arXiv:1410.1585, Lemmas A.6 and A.7.
* Bayer, *A short proof of the deformation property of Bridgeland stability
  conditions*, arXiv:1606.02169, Lemma 6.1.
-/

namespace QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {Q : QuadraticForm ℝ V} {Z : V →ₗ[ℝ] ℂ}

/-- **Classes on one ray have nonnegative polar form.** If the kernel of `Z` is
negative semidefinite for `Q`, then two classes with `0 ≤ Q` whose charges lie on one
open ray `ℝ_{>0} ζ` have `0 ≤ polar Q x y`. -/
theorem polar_nonneg_of_charge_eq (hker : ∀ k, Z k = 0 → Q k ≤ 0) {x y : V}
    (hx : 0 ≤ Q x) (hy : 0 ≤ Q y) {ζ : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hZx : Z x = (r : ℂ) * ζ) (hZy : Z y = (s : ℂ) * ζ) :
    0 ≤ polar Q x y := by
  have hk : Z (s • x - r • y) = 0 := by
    rw [map_sub, map_smul, map_smul, hZx, hZy, Complex.real_smul, Complex.real_smul]
    ring
  have hle := hker _ hk
  have hexp : Q (s • x - r • y) = s ^ 2 * Q x + r ^ 2 * Q y - s * r * polar Q x y := by
    have h1 : Q (s • x - r • y) = Q (s • x) + Q (r • y) - polar Q (s • x) (r • y) := by
      rw [sub_eq_add_neg, show Q (s • x + -(r • y)) =
          Q (s • x) + Q (-(r • y)) + polar Q (s • x) (-(r • y)) by rw [polar]; ring,
        polar_neg_right, QuadraticMap.map_neg]
      ring
    rw [h1, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left, polar_smul_right,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  rw [hexp] at hle
  have hsr : 0 < s * r := mul_pos hs hr
  by_contra hneg
  push Not at hneg
  nlinarith [mul_neg_of_pos_of_neg hsr hneg, sq_nonneg s, sq_nonneg r,
    mul_nonneg (sq_nonneg s) hx, mul_nonneg (sq_nonneg r) hy]

variable (Q Z) in
/-- The cone of a quadratic form over the open ray `ℝ_{>0} ζ`: the class `0`, and
the classes `x` with `0 ≤ Q x` and `Z x = r ζ` for some `r > 0`. -/
def chargeRayCone (ζ : ℂ) : Set V :=
  {x | x = 0 ∨ (0 ≤ Q x ∧ ∃ r : ℝ, 0 < r ∧ Z x = (r : ℂ) * ζ)}

variable {ζ : ℂ}

theorem zero_mem_chargeRayCone : (0 : V) ∈ chargeRayCone Q Z ζ :=
  Or.inl rfl

/-- A class with `0 ≤ Q` and charge on the ray lies in the cone. -/
theorem mem_chargeRayCone_of_charge_eq {x : V} (hx : 0 ≤ Q x) {r : ℝ} (hr : 0 < r)
    (hZx : Z x = (r : ℂ) * ζ) : x ∈ chargeRayCone Q Z ζ :=
  Or.inr ⟨hx, r, hr, hZx⟩

/-- Every class of the cone has `0 ≤ Q`. -/
theorem apply_nonneg_of_mem_chargeRayCone {x : V} (hx : x ∈ chargeRayCone Q Z ζ) :
    0 ≤ Q x := by
  rcases hx with rfl | ⟨hx, -⟩
  · simp
  · exact hx

/-- **The cone is closed under addition** (BMS16, Lemma A.7). -/
theorem add_mem_chargeRayCone (hker : ∀ k, Z k = 0 → Q k ≤ 0) {x y : V}
    (hx : x ∈ chargeRayCone Q Z ζ) (hy : y ∈ chargeRayCone Q Z ζ) :
    x + y ∈ chargeRayCone Q Z ζ := by
  rcases hx with rfl | ⟨hQx, r, hr, hZx⟩
  · simpa using hy
  rcases hy with rfl | ⟨hQy, s, hs, hZy⟩
  · rw [add_zero]
    exact mem_chargeRayCone_of_charge_eq hQx hr hZx
  refine Or.inr ⟨?_, r + s, add_pos hr hs, ?_⟩
  · have hP := polar_nonneg_of_charge_eq hker hQx hQy hr hs hZx hZy
    have : Q (x + y) = Q x + Q y + polar Q x y := by rw [polar]; ring
    rw [this]
    positivity
  · rw [map_add, hZx, hZy]
    push_cast
    ring

/-- The cone is closed under multiplication by nonnegative scalars. -/
theorem smul_mem_chargeRayCone {x : V} (hx : x ∈ chargeRayCone Q Z ζ) {a : ℝ}
    (ha : 0 ≤ a) : a • x ∈ chargeRayCone Q Z ζ := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using zero_mem_chargeRayCone
  rcases hx with rfl | ⟨hQx, r, hr, hZx⟩
  · simpa using zero_mem_chargeRayCone
  refine Or.inr ⟨?_, a * r, mul_pos ha hr, ?_⟩
  · rw [QuadraticMap.map_smul, smul_eq_mul]
    positivity
  · rw [map_smul, hZx, Complex.real_smul]
    push_cast
    ring

/-- **The cone is convex** (BMS16, Lemma A.7). -/
theorem convex_chargeRayCone (hker : ∀ k, Z k = 0 → Q k ≤ 0) :
    Convex ℝ (chargeRayCone Q Z ζ) :=
  fun _ hx _ hy _ _ ha hb _ =>
    add_mem_chargeRayCone hker (smul_mem_chargeRayCone hx ha) (smul_mem_chargeRayCone hy hb)

/-- A finite sum of classes in the cone lies in the cone. -/
theorem sum_mem_chargeRayCone (hker : ∀ k, Z k = 0 → Q k ≤ 0) {ι : Type*} (s : Finset ι)
    {x : ι → V} (hx : ∀ i ∈ s, x i ∈ chargeRayCone Q Z ζ) :
    ∑ i ∈ s, x i ∈ chargeRayCone Q Z ζ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_chargeRayCone
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add_mem_chargeRayCone hker (hx i (Finset.mem_insert_self i s))
      (ih fun j hj => hx j (Finset.mem_insert_of_mem hj))

end QuadraticMap

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.ComplexRepresentation
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Covering.Fibre

/-!
# Surjectivity of the lifted matrix projection

Every `T ∈ GL⁺(2, ℝ)` admits a compatible phase relabelling, so `toMatHom`
is onto.

Together with `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Covering/Fibre.lean` this closes the algebraic exact sequence.
`WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Covering/SourceTopology.lean` now supplies a topology, continuity of the projection,
and simple connectedness; `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Covering/Map.lean` proves the covering-map property.

## The construction, and why it needs no branch cut

Write `T` acting on `ℂ` in the form `z ↦ a z + b z̄`. This is possible for any
real-linear map, and the determinant comes out as `‖a‖² - ‖b‖²`, so **`det T > 0`
says exactly `‖b‖ < ‖a‖`**. That single inequality is what makes the whole
construction work.

On the unit circle,

```
T (e^{iπφ}) = a e^{iπφ} + b e^{-iπφ} = e^{iπφ} · a · (1 + (b/a) e^{-2iπφ})
```

and the last factor `W φ` has **real part at least `1 - ‖b/a‖ > 0`**. So `W φ`
never leaves the right half-plane, `arg (W φ)` is continuous with no branch-cut
trouble at all, and the lift can simply be written down:

```
lift φ = φ + arg a / π + arg (W φ) / π
```

No covering-space machinery, no path lifting, no monodromy. The branch cut is
avoided by construction rather than worked around.

## Monotonicity without differentiating

The obvious route is to differentiate: `lift' φ = (1 - ‖b/a‖²) / ‖W φ‖² > 0`.
That is true and is the reason the result holds, but it costs a chain rule
through `Complex.arg`.

The cheaper route used here is the **2×2 cross product** `v × w = v₀w₁ - v₁w₀`:

* `rayVec φ × rayVec ψ = sin (π (ψ - φ))`, and
* `(M *ᵥ v) × (M *ᵥ w) = det M · (v × w)`.

So for `0 < ψ - φ < 1` the image cross product is `det T · sin (π (ψ - φ)) > 0`,
which forces `sin (π (lift ψ - lift φ)) > 0`. That alone leaves the difference
ambiguous modulo 2 — but `arg (W ·)` lands in `(-π/2, π/2)`, so
`lift ψ - lift φ` is pinned inside `(-1, 2)`, and on that interval
`sin (π x) > 0` has the unique solution set `(0, 1)`.

Positivity of `det` is used **twice**, and differently: once to put `W` in the
right half-plane, once to sign the cross product.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open Matrix Real Complex

/-! ## The unit-circle exponential -/

/-- `cexpI x = e^{ix}`. Mathlib has no `Complex.cis` at the pinned revision. -/
noncomputable def cexpI (x : ℝ) : ℂ := Complex.exp (↑x * Complex.I)

@[simp] theorem cexpI_re (x : ℝ) : (cexpI x).re = Real.cos x :=
  Complex.exp_ofReal_mul_I_re x

@[simp] theorem cexpI_im (x : ℝ) : (cexpI x).im = Real.sin x :=
  Complex.exp_ofReal_mul_I_im x

theorem cexpI_add (x y : ℝ) : cexpI (x + y) = cexpI x * cexpI y := by
  simp only [cexpI, Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] theorem norm_cexpI (x : ℝ) : ‖cexpI x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

theorem cexpI_ne_zero (x : ℝ) : cexpI x ≠ 0 := by
  intro h; have := norm_cexpI x; rw [h] at this; simp at this

/-- Coordinates of a complex number in the `1, I` basis. -/
theorem cplxCoord_apply (z : ℂ) : cplxCoord z = ![z.re, z.im] := by
  show ⇑(Complex.basisOneI.repr z) = _
  rw [Complex.coe_basisOneI_repr]

theorem cplxCoord_cexpI (φ : ℝ) : cplxCoord (cexpI (π * φ)) = rayVec φ := by
  rw [cplxCoord_apply]; ext i; fin_cases i <;> simp [rayVec]

/-! ## `T` as `z ↦ a z + b z̄` -/

variable (T : Matrix.GLPos (Fin 2) ℝ)

/-- The holomorphic part of `T`. -/
noncomputable def cA : ℂ :=
  ⟨(toMat T 0 0 + toMat T 1 1) / 2, (toMat T 1 0 - toMat T 0 1) / 2⟩

/-- The antiholomorphic part of `T`. -/
noncomputable def cB : ℂ :=
  ⟨(toMat T 0 0 - toMat T 1 1) / 2, (toMat T 1 0 + toMat T 0 1) / 2⟩

/-- **The circle map, in closed form.** -/
theorem mulVec_rayVec_eq (φ : ℝ) :
    toMat T *ᵥ rayVec φ
      = cplxCoord (cA T * cexpI (π * φ) + cB T * cexpI (-(π * φ))) := by
  rw [cplxCoord_apply]
  ext i
  fin_cases i <;>
    simp [rayVec, cA, cB, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Real.cos_neg, Real.sin_neg] <;> ring

/-- **`det T = ‖a‖² - ‖b‖²`.** This is the identity that turns the hypothesis
`det T > 0` into the inequality `‖b‖ < ‖a‖` the construction runs on. -/
theorem normSq_cA_sub_normSq_cB :
    normSq (cA T) - normSq (cB T) = (toMat T).det := by
  simp [Complex.normSq_apply, cA, cB, Matrix.det_fin_two]
  ring

theorem det_toMat_pos : 0 < (toMat T).det := T.2

theorem normSq_cB_lt_normSq_cA : normSq (cB T) < normSq (cA T) := by
  have := normSq_cA_sub_normSq_cB T
  have := det_toMat_pos T
  linarith

theorem cA_ne_zero : cA T ≠ 0 := by
  intro h
  have hlt := normSq_cB_lt_normSq_cA T
  rw [h, Complex.normSq_zero] at hlt
  exact absurd (Complex.normSq_nonneg (cB T)) (by linarith)

theorem norm_cB_lt_norm_cA : ‖cB T‖ < ‖cA T‖ := by
  have h := normSq_cB_lt_normSq_cA T
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (cA T), norm_nonneg (cB T)]

/-! ## The right-half-plane factor -/

/-- `b / a`, of norm `< 1`. -/
noncomputable def ratio : ℂ := cB T / cA T

theorem norm_ratio_lt_one : ‖ratio T‖ < 1 := by
  have hA : 0 < ‖cA T‖ := norm_pos_iff.mpr (cA_ne_zero T)
  rw [ratio, norm_div, div_lt_one hA]
  exact norm_cB_lt_norm_cA T

/-- The factor that carries all the `φ`-dependence.

Its real part is bounded below by `1 - ‖b/a‖ > 0`, which is the whole reason
this construction needs no branch cut. -/
noncomputable def Wmap (φ : ℝ) : ℂ := 1 + ratio T * cexpI (-(2 * π * φ))

theorem Wmap_re_pos (φ : ℝ) : 0 < (Wmap T φ).re := by
  have hnorm : ‖ratio T * cexpI (-(2 * π * φ))‖ = ‖ratio T‖ := by
    rw [norm_mul, norm_cexpI, mul_one]
  have hre : |(ratio T * cexpI (-(2 * π * φ))).re| ≤ ‖ratio T‖ := by
    rw [← hnorm]; exact Complex.abs_re_le_norm _
  have := norm_ratio_lt_one T
  have habs := abs_le.mp hre
  simp only [Wmap, Complex.add_re, Complex.one_re]
  linarith [habs.1]

theorem Wmap_ne_zero (φ : ℝ) : Wmap T φ ≠ 0 := by
  intro h
  have := Wmap_re_pos T φ
  rw [h] at this
  simp at this

theorem cexpI_neg_two_pi : cexpI (-(2 * π)) = 1 := by
  simp only [cexpI]
  rw [show ((-(2 * π) : ℝ) : ℂ) * Complex.I = -(2 * ↑π * Complex.I) by push_cast; ring,
    Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

theorem Wmap_add_one (φ : ℝ) : Wmap T (φ + 1) = Wmap T φ := by
  have hsplit : -(2 * π * (φ + 1)) = -(2 * π * φ) + -(2 * π) := by ring
  rw [Wmap, Wmap, hsplit, cexpI_add, cexpI_neg_two_pi, mul_one]

/-! ## The lift -/

/-- **The phase relabelling attached to `T`.**

`arg (cA T)` is a constant; all the motion is in `arg (Wmap T φ)`, which is
continuous because `Wmap T φ` never leaves the right half-plane. -/
noncomputable def lift (φ : ℝ) : ℝ := φ + (cA T).arg / π + (Wmap T φ).arg / π

theorem pi_mul_lift (φ : ℝ) :
    π * lift T φ = π * φ + (cA T).arg + (Wmap T φ).arg := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  simp only [lift]
  field_simp

/-- **The defining property of the lift.** `T` carries the ray at phase `φ` to
the ray at phase `lift T φ`, scaled by `‖a‖ ‖W φ‖ > 0`. -/
theorem mulVec_rayVec_lift (φ : ℝ) :
    toMat T *ᵥ rayVec φ = (‖cA T‖ * ‖Wmap T φ‖) • rayVec (lift T φ) := by
  have hfactor : cA T * cexpI (π * φ) + cB T * cexpI (-(π * φ))
      = cexpI (π * φ) * cA T * Wmap T φ := by
    have hinv : cexpI (-(π * φ)) = cexpI (π * φ) * cexpI (-(2 * π * φ)) := by
      rw [← cexpI_add]; congr 1; ring
    rw [Wmap, ratio, hinv]
    field_simp [cA_ne_zero T]
  have hpolarA : (‖cA T‖ : ℂ) * cexpI (cA T).arg = cA T :=
    Complex.norm_mul_exp_arg_mul_I (cA T)
  have hpolarW : (‖Wmap T φ‖ : ℂ) * cexpI (Wmap T φ).arg = Wmap T φ :=
    Complex.norm_mul_exp_arg_mul_I (Wmap T φ)
  have hcomplex : cA T * cexpI (π * φ) + cB T * cexpI (-(π * φ))
      = ((‖cA T‖ * ‖Wmap T φ‖ : ℝ) : ℂ) * cexpI (π * lift T φ) := by
    rw [hfactor, pi_mul_lift, cexpI_add, cexpI_add]
    calc cexpI (π * φ) * cA T * Wmap T φ
        = cexpI (π * φ) * ((‖cA T‖ : ℂ) * cexpI (cA T).arg)
            * ((‖Wmap T φ‖ : ℂ) * cexpI (Wmap T φ).arg) := by
          rw [hpolarA, hpolarW]
      _ = ((‖cA T‖ * ‖Wmap T φ‖ : ℝ) : ℂ)
            * (cexpI (π * φ) * cexpI (cA T).arg * cexpI (Wmap T φ).arg) := by
          push_cast; ring
  rw [mulVec_rayVec_eq, hcomplex]
  rw [show (((‖cA T‖ * ‖Wmap T φ‖ : ℝ) : ℂ) * cexpI (π * lift T φ))
      = (‖cA T‖ * ‖Wmap T φ‖ : ℝ) • cexpI (π * lift T φ) from (Complex.real_smul ..).symm]
  rw [map_smul, cplxCoord_cexpI]

theorem lift_scale_pos (φ : ℝ) : 0 < ‖cA T‖ * ‖Wmap T φ‖ :=
  mul_pos (norm_pos_iff.mpr (cA_ne_zero T)) (norm_pos_iff.mpr (Wmap_ne_zero T φ))

theorem compatible_lift (φ : ℝ) :
    OnRay (toMat T *ᵥ rayVec φ) (rayVec (lift T φ)) :=
  ⟨_, lift_scale_pos T φ, mulVec_rayVec_lift T φ⟩

theorem lift_add_one (φ : ℝ) : lift T (φ + 1) = lift T φ + 1 := by
  simp only [lift, Wmap_add_one]
  ring

/-! ## The 2×2 cross product -/

/-- The signed area `v₀w₁ - v₁w₀`. -/
def cross (v w : Fin 2 → ℝ) : ℝ := v 0 * w 1 - v 1 * w 0

theorem cross_rayVec (φ ψ : ℝ) :
    cross (rayVec φ) (rayVec ψ) = Real.sin (π * (ψ - φ)) := by
  simp only [cross, rayVec, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show π * (ψ - φ) = π * ψ - π * φ by ring, Real.sin_sub]
  ring

theorem cross_mulVec (M : Matrix (Fin 2) (Fin 2) ℝ) (v w : Fin 2 → ℝ) :
    cross (M *ᵥ v) (M *ᵥ w) = M.det * cross v w := by
  simp only [cross, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem cross_smul (a b : ℝ) (v w : Fin 2 → ℝ) :
    cross (a • v) (b • w) = a * b * cross v w := by
  simp only [cross, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Strict monotonicity -/

/-- `arg (Wmap T φ)` is confined to `(-π/2, π/2)`, because `Wmap T φ` has
positive real part. This is what pins the ambiguity the cross product leaves. -/
theorem abs_arg_Wmap_lt (φ : ℝ) : |(Wmap T φ).arg| < π / 2 :=
  Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (Wmap_re_pos T φ))

private theorem sin_pos_unique {x : ℝ} (hx : -1 < x) (hx2 : x < 2)
    (hsin : 0 < Real.sin (π * x)) : 0 < x ∧ x < 1 := by
  have hπ := Real.pi_pos
  refine ⟨?_, ?_⟩
  · rcases le_or_gt x 0 with hle | hpos
    · exfalso
      -- `π x ∈ (-π, 0]`, where `sin ≤ 0`.
      have h1 : 0 ≤ -(π * x) := by nlinarith
      have h2 : -(π * x) ≤ π := by nlinarith
      have hnn := Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
      rw [Real.sin_neg] at hnn
      linarith
    · exact hpos
  · rcases lt_or_ge x 1 with hlt | hge
    · exact hlt
    · exfalso
      -- `π x ∈ [π, 2π)`, where `sin ≤ 0`.
      have h1 : 0 ≤ π * x - π := by nlinarith
      have h2 : π * x - π ≤ π := by nlinarith
      have hnn := Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
      have hkey : Real.sin (π * x) = -Real.sin (π * x - π) := by
        conv_lhs => rw [show π * x = (π * x - π) + π by ring]
        rw [Real.sin_add_pi]
      rw [hkey] at hsin
      linarith

/-- Strict monotonicity on a unit window. -/
theorem lift_lt_lift_of_lt_of_sub_lt_one {φ ψ : ℝ} (h1 : φ < ψ) (h2 : ψ - φ < 1) :
    lift T φ < lift T ψ := by
  -- The image cross product is positive, by `det T > 0`.
  have hsin : 0 < Real.sin (π * (ψ - φ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [Real.pi_pos]
  have himg : 0 < cross (toMat T *ᵥ rayVec φ) (toMat T *ᵥ rayVec ψ) := by
    rw [cross_mulVec, cross_rayVec]
    exact mul_pos (det_toMat_pos T) hsin
  -- Read the same number off the lift.
  rw [mulVec_rayVec_lift, mulVec_rayVec_lift, cross_smul, cross_rayVec] at himg
  have hscale : 0 < (‖cA T‖ * ‖Wmap T φ‖) * (‖cA T‖ * ‖Wmap T ψ‖) :=
    mul_pos (lift_scale_pos T φ) (lift_scale_pos T ψ)
  have hsin2 : 0 < Real.sin (π * (lift T ψ - lift T φ)) := by
    rcases le_or_gt (Real.sin (π * (lift T ψ - lift T φ))) 0 with hle | hpos
    · nlinarith [himg, hscale]
    · exact hpos
  -- The difference is trapped in `(-1, 2)` by the `arg` bound.
  have hbound : -1 < lift T ψ - lift T φ ∧ lift T ψ - lift T φ < 2 := by
    have ha := abs_lt.mp (abs_arg_Wmap_lt T φ)
    have hb := abs_lt.mp (abs_arg_Wmap_lt T ψ)
    have hπ : 0 < π := Real.pi_pos
    have hdiff : lift T ψ - lift T φ
        = (ψ - φ) + ((Wmap T ψ).arg - (Wmap T φ).arg) / π := by
      simp only [lift]; field_simp; ring
    rw [hdiff]
    constructor
    · have : ((Wmap T ψ).arg - (Wmap T φ).arg) / π > -1 := by
        rw [gt_iff_lt, lt_div_iff₀ hπ]; linarith [ha.2, hb.1]
      linarith
    · have : ((Wmap T ψ).arg - (Wmap T φ).arg) / π < 1 := by
        rw [div_lt_one hπ]; linarith [ha.1, hb.2]
      linarith
  have := sin_pos_unique hbound.1 hbound.2 hsin2
  linarith [this.1]

theorem lift_add_nat (φ : ℝ) (n : ℕ) : lift T (φ + n) = lift T φ + n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have : φ + (k + 1 : ℕ) = (φ + k) + 1 := by push_cast; ring
    rw [this, lift_add_one, ih]
    push_cast; ring

private theorem lift_lt_of_sub_lt_nat (n : ℕ) :
    ∀ φ ψ : ℝ, φ < ψ → ψ - φ < n → lift T φ < lift T ψ := by
  induction n with
  | zero => intro φ ψ h1 h2; simp only [Nat.cast_zero] at h2; linarith
  | succ k ih =>
    intro φ ψ h1 h2
    rcases lt_or_ge (ψ - φ) 1 with hsmall | hbig
    · exact lift_lt_lift_of_lt_of_sub_lt_one T h1 hsmall
    · -- Cross one unit, where `lift` shifts by exactly one, then recurse.
      have hstep : lift T φ < lift T (φ + 1) := by rw [lift_add_one]; linarith
      rcases eq_or_lt_of_le (by linarith : φ + 1 ≤ ψ) with heq | hlt
      · rwa [heq] at hstep
      · refine hstep.trans (ih (φ + 1) ψ hlt ?_)
        push_cast at h2
        linarith

theorem lift_strictMono : StrictMono (lift T) := by
  intro φ ψ hlt
  obtain ⟨n, hn⟩ := exists_nat_gt (ψ - φ)
  exact lift_lt_of_sub_lt_nat T n φ ψ hlt hn

/-! ## Continuity and surjectivity -/

theorem lift_continuous : Continuous (lift T) := by
  have hW : Continuous (Wmap T) := by
    apply continuous_const.add
    exact continuous_const.mul
      (Complex.continuous_exp.comp (by fun_prop))
  refine continuous_iff_continuousAt.mpr fun φ => ?_
  refine (continuousAt_id.add continuousAt_const).add ?_
  exact ((Complex.continuousAt_arg
    (Complex.mem_slitPlane_iff.mpr (Or.inl (Wmap_re_pos T φ)))).comp
      hW.continuousAt).div_const π

theorem lift_surjective : Function.Surjective (lift T) := by
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt (|y - lift T 0| + 1)
  have hup : y < lift T ((0 : ℝ) + n) := by
    rw [lift_add_nat]
    have := le_abs_self (y - lift T 0)
    linarith
  have hdown : lift T ((0 : ℝ) - n) < y := by
    have hkey : lift T ((0 : ℝ) - n) + n = lift T 0 := by
      have : ((0 : ℝ) - n) + n = 0 := by ring
      rw [← lift_add_nat T ((0:ℝ) - n) n, this]
    have := neg_abs_le (y - lift T 0)
    linarith
  have hle : (0 : ℝ) - n ≤ (0 : ℝ) + n := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hmem : y ∈ Set.Icc (lift T ((0:ℝ) - n)) (lift T ((0:ℝ) + n)) :=
    ⟨hdown.le, hup.le⟩
  obtain ⟨φ, _, hφ⟩ :=
    intermediate_value_Icc hle (lift_continuous T).continuousOn hmem
  exact ⟨φ, hφ⟩

/-! ## The result -/

/-- The phase relabelling attached to `T`, as a `NormalizedShift`. -/
noncomputable def liftShift : NormalizedShift where
  toOrderIso := (lift_strictMono T).orderIsoOfSurjective _ (lift_surjective T)
  map_add_one := lift_add_one T

@[simp] theorem liftShift_apply (φ : ℝ) : (liftShift T).toOrderIso φ = lift T φ := rfl

theorem compatible_liftShift : Compatible T (liftShift T) := compatible_lift T

/-- **`G̃L⁺(2, ℝ) → GL⁺(2, ℝ)` is surjective.**

Every matrix of positive determinant carries a compatible phase relabelling,
so it lies in the image of the projection. -/
theorem toMatHom_surjective : Function.Surjective GLTilde.toMatHom :=
  fun T => ⟨⟨T, liftShift T, compatible_liftShift T⟩, rfl⟩

/-! ## The canonical section, and the `ℤ`-torsor structure

What surjectivity gives beyond a bare existence statement: `lift` is *canonical*
— it is written down, not chosen — so it is a genuine **section** of the
projection, and every element of `G̃L⁺(2, ℝ)` factors uniquely through it.

This is concrete algebraic data supporting the later covering-map proof. What
it is **not** by itself is a topological statement; see
`exact_deckHom_toMatHom`. -/

/-- The canonical section of the projection, given by the explicit lift. -/
noncomputable def sect (T : Matrix.GLPos (Fin 2) ℝ) : GLTilde :=
  ⟨T, liftShift T, compatible_liftShift T⟩

@[simp] theorem sect_mat (T : Matrix.GLPos (Fin 2) ℝ) : (sect T).mat = T := rfl

theorem toMatHom_comp_sect (T : Matrix.GLPos (Fin 2) ℝ) :
    GLTilde.toMatHom (sect T) = T := rfl

theorem deck_injective : Function.Injective deck := by
  intro m n h
  have : deckHom (Multiplicative.ofAdd m) = deckHom (Multiplicative.ofAdd n) := h
  simpa using deckHom_injective this

/-- **Unique factorisation.** Every element is a deck transformation composed
with the canonical lift of its own matrix part.

No group-homomorphism property is claimed for `sect`, so this is a bijection
of sets with a canonical section, not a claimed semidirect-product
decomposition. -/
theorem existsUnique_deck_mul_sect (x : GLTilde) :
    ∃! n : ℤ, x = deck n * sect x.mat := by
  have hker : x * (sect x.mat)⁻¹ ∈ GLTilde.toMatHom.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, toMatHom_comp_sect]
    show x.mat * x.mat⁻¹ = 1
    exact mul_inv_cancel _
  rw [← range_deckHom_eq_ker] at hker
  obtain ⟨m, hm⟩ := hker
  refine ⟨Multiplicative.toAdd m, ?_, ?_⟩
  · show x = deck (Multiplicative.toAdd m) * sect x.mat
    have hd : deck (Multiplicative.toAdd m) = x * (sect x.mat)⁻¹ := hm
    rw [hd, inv_mul_cancel_right]
  · intro n hn
    refine deck_injective ?_
    -- Rewriting with `hn` directly would also hit the `x` inside `x.mat`.
    have h1 : x * (sect x.mat)⁻¹ = deck n := mul_inv_eq_iff_eq_mul.mpr hn
    have h2 : deck (Multiplicative.toAdd m) = x * (sect x.mat)⁻¹ := hm
    rw [h2, h1]

/-- **The algebraic covering-space facts, together.**

`1 → ℤ → G̃L⁺(2, ℝ) → GL⁺(2, ℝ) → 1` is exact: `deckHom` is injective, its
range is exactly the kernel of the projection, and the projection is onto.

This theorem packages the extension, not the topology.  The covering-map and
simple-connectedness properties are packaged separately by
`GLTilde.universalCoverData` in `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Covering/Map.lean`. -/
theorem exact_deckHom_toMatHom :
    Function.Injective deckHom
      ∧ deckHom.range = GLTilde.toMatHom.ker
      ∧ Function.Surjective GLTilde.toMatHom :=
  ⟨deckHom_injective, range_deckHom_eq_ker, toMatHom_surjective⟩

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

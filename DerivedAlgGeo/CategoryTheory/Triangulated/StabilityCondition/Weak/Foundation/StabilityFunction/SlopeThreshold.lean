/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.SlopeCutoff

/-!
# A phase cutoff, read as a slope cutoff

`Cutoff.lean` cuts by a **phase** `β : ℝ`; Bridgeland's §6 cuts by a **slope**, `μ_ω(E)`
against `β·ω`.  `Slope.lean` relates the two orders — `phase_le_iff_slope_le` — but only
between two *objects*.  Nothing turned a cutoff into a slope, and every case of Lemma 6.2
needs exactly that.

`slopeOfPhase` is the translation, and `lt_phase_iff_slopeOfPhase_lt` is that it is correct.

## Where the formula comes from

The charge is `-degree + i·rank`, so an object of positive rank has its charge in the open
upper half plane, and the phase cutoff `β` is the ray at angle `π·β`.  Testing against that
ray is `phaseCross` with the unit vector `cos(πβ) + sin(πβ)·i`, which computes to

```
rank · cos(πβ) + degree · sin(πβ)
```

and dividing by `rank · sin(πβ) > 0` turns its positivity into `-cot(πβ) < degree/rank`.
Hence `slopeOfPhase β = -(cos(πβ)/sin(πβ))`.

## The hypotheses are exactly what the geometry has

`0 < β` and `β < 1` are not technical: `sin(πβ) > 0` is what makes the division sign-preserving,
and it is also what makes `β` an interior phase.  At `β = 1` the cutoff is the negative real axis,
where `SlopeCutoff.lean` puts every rank-zero object — the reason that file restricts to `β < 1`.
`0 < rank` is likewise real: at rank zero the slope is not defined, and those objects are handled
by `mem_hnTors_of_rank_zero` instead of by any slope comparison.

## Both statements hold on a surface

Neither proof touches `SlopeData.degree_pos_of_rank_zero`: `0 < rank` already puts the charge in
the *open* upper half plane, which is all `phaseCross_pos_of_arg_lt` and `arg_lt_of_phaseCross_pos`
need.  So both are stated on `WeakSlopeData` — the surface structure, where a rank-zero object may
have degree `0` — and `SlopeData` inherits them through `SlopeData.toWeakSlopeData`.

The rank-zero half does **not** carry over.  `mem_hnTors_of_rank_zero` is a `SlopeData` theorem and
has no weak counterpart: on a surface a rank-zero object of degree `0` has charge `0`, hence no
phase at all, so no cutoff comparison places it.  See `WeakSlope.lean`.
-/

noncomputable section

open CategoryTheory Complex Real

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **The slope that a phase cutoff corresponds to**, `-cot(πβ)`.

Meaningful for `β ∈ (0,1)`; outside that range `sin(πβ)` vanishes or changes sign and the
translation below does not hold. -/
def slopeOfPhase (β : ℝ) : ℝ := -(Real.cos (π * β) / Real.sin (π * β))

namespace WeakSlopeData

variable (D : WeakSlopeData A)

/-- **A phase cutoff is a slope cutoff**, on a surface as on a curve.

For an object of positive rank and an interior cutoff, exceeding the cutoff in phase is
exceeding `slopeOfPhase β` in slope.  This is the object-versus-threshold companion of
`phase_le_iff_slope_le`, which compares two objects.

`0 < rank` puts the charge in the *open* upper half plane, so the degree hypothesis plays no
part and this holds for the weak structure.  `SlopeData` inherits it below. -/
theorem lt_phase_iff_slopeOfPhase_lt {E : A} (hE : 0 < D.rank E) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    β < D.phase E ↔ slopeOfPhase β < D.slope E := by
  have hpi := Real.pi_pos
  have hmem : π * β ∈ Set.Ioc (-π) π :=
    Set.mem_Ioc.mpr ⟨by nlinarith, by nlinarith⟩
  set z : ℂ := Complex.cos ((π * β : ℝ) : ℂ) + Complex.sin ((π * β : ℝ) : ℂ) * Complex.I
    with hz_def
  have hargz : Complex.arg z = π * β := Complex.arg_cos_add_sin_mul_I hmem
  have hsin : 0 < Real.sin (π * β) := Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  have hr : (0 : ℝ) < (D.rank E : ℝ) := by exact_mod_cast hE
  have hwne : D.charge E ≠ 0 := D.charge_ne_zero_of_rank_pos hE
  have hwarg : 0 < Complex.arg (D.charge E) := D.arg_pos_of_rank_pos hE
  have hzne : z ≠ 0 := by
    intro h
    rw [h, Complex.arg_zero] at hargz
    nlinarith
  have hcross : phaseCross z (D.charge E)
      = (D.rank E : ℝ) * Real.cos (π * β) + (D.degree E : ℝ) * Real.sin (π * β) := by
    simp only [phaseCross, hz_def, WeakSlopeData.charge_re, WeakSlopeData.charge_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
      Complex.sin_ofReal_re, Complex.I_re, Complex.I_im, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im]
    ring
  have harith : (0 : ℝ) < (D.rank E : ℝ) * Real.cos (π * β) + (D.degree E : ℝ) * Real.sin (π * β)
      ↔ slopeOfPhase β < D.slope E := by
    rw [slopeOfPhase, WeakSlopeData.slope, ← neg_div, div_lt_div_iff₀ hsin hr]
    constructor <;> intro h <;> nlinarith
  rw [← harith, ← hcross]
  rw [WeakSlopeData.phase, lt_div_iff₀ hpi]
  constructor
  · intro h
    refine phaseCross_pos_of_arg_lt (by rw [hargz]; nlinarith) hzne hwne ?_
    rw [hargz]; linarith [h]
  · intro h
    have := arg_lt_of_phaseCross_pos hzne hwne hwarg h
    rw [hargz] at this
    linarith

/-- **The torsion-free side**, by negation.

`Cutoff.lean`'s two classes are complementary at each phase, and so are the two slope
conditions; no second argument is needed. -/
theorem phase_le_iff_le_slopeOfPhase {E : A} (hE : 0 < D.rank E) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    D.phase E ≤ β ↔ D.slope E ≤ slopeOfPhase β := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact D.lt_phase_iff_slopeOfPhase_lt hE hβ0 hβ1

end WeakSlopeData

namespace SlopeData

variable (D : SlopeData A)

/-- **A phase cutoff is a slope cutoff.**

For an object of positive rank and an interior cutoff, exceeding the cutoff in phase is
exceeding `slopeOfPhase β` in slope.  This is the object-versus-threshold companion of
`phase_le_iff_slope_le`, which compares two objects.

Inherited from `WeakSlopeData.lt_phase_iff_slopeOfPhase_lt` along `toWeakSlopeData`. -/
theorem lt_phase_iff_slopeOfPhase_lt {E : A} (hE : 0 < D.rank E) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    β < D.toStabilityFunction.phase E ↔ slopeOfPhase β < D.slope E := by
  rw [toStabilityFunction_phase]
  simpa using D.toWeakSlopeData.lt_phase_iff_slopeOfPhase_lt hE hβ0 hβ1

/-- **The torsion-free side**, by negation.

`Cutoff.lean`'s two classes are complementary at each phase, and so are the two slope
conditions; no second argument is needed. -/
theorem phase_le_iff_le_slopeOfPhase {E : A} (hE : 0 < D.rank E) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    D.toStabilityFunction.phase E ≤ β ↔ D.slope E ≤ slopeOfPhase β := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact D.lt_phase_iff_slopeOfPhase_lt hE hβ0 hβ1

end SlopeData

end CategoryTheory.Triangulated

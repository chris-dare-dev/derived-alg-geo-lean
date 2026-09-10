/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Threefold.CalabiYau
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.ThreefoldWallTransport

/-!
# The threefold wall transport, on the quintic

`Examples/Threefold/ProjectiveSpaceWalls.lean` connected the transport of
`Stability/ThreefoldWallTransport.lean` to the `ℙ³` model.  This file does the
same for the quintic Calabi--Yau threefold, which was in the same position: a
model referenced only inside its own file, with no polarization defined for it.

## Why the second threefold is worth doing

`ℙ³` and the quintic differ in exactly the two places the transport touches.

* **The degree.** `∫H³ = 5` rather than `1`, so every one of the four degrees
  carries a factor the `ℙ³` computation could not see.  A transport that
  silently assumed unit degree would pass on `ℙ³` and fail here.
* **The Todd class.** The quintic has `td₁ = 0` and `∫td₃ = χ(O) = 0`, where
  `ℙ³` has every coefficient nonzero.  The transport does not read the Todd
  class, and these statements are the check that it does not: the four degrees
  below depend on the Chern coefficients and the degree alone.

## The coordinates

With `∫H³ = 5` and linear-section coordinates `(a, b, c, e)`,

```text
∫H³ch₀ = 5a,   ∫H²ch₁ = 5b,   ∫H·ch₂ = 5(-b/2 + c),   ∫ch₃ = 5b/6 - 5c + e,
```

the last because `threefoldChCoeff 5` divides the point coordinate by the
degree, which the integral then undoes.  That cancellation is the one place the
quintic computation is not the `ℙ³` one with a factor of five.

## No second sanity witness

`ProjectiveSpaceWalls.p3BMTSanity` already shows `BMTData` is inhabitable, and a
second tautological witness would add nothing.  `quintic_Q_toNumClass_nonneg`
therefore takes a supplied `BMTData` as a hypothesis, which is the honest shape:
the Bayer--Macrì--Toda inequality is **not** proved here for the quintic or for
anything else, and it is false for some threefolds.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition

namespace AlgebraicGeometry.Numerical

namespace Examples

noncomputable section

/-! ### The polarization -/

/-- `∫_X H³ = 5` on the quintic. -/
theorem quintic_degree_H_pow_three :
    quinticNumericalVariety.ring.degree (rankOneH 3 ^ 3) = 5 := by
  show rankOneDegree 3 5 (rankOneH 3 ^ 3) = 5
  rw [rankOneDegree_pow]
  norm_num

/-- **The hyperplane class as a polarization of the quintic.** -/
def quinticPolarization : Polarization quinticNumericalVariety.ring where
  cls := rankOneH 3
  cls_mem := by
    have h := rankOneH_pow_mem_piece 3 1
    rwa [pow_one] at h
  degree_pow_pos := by
    rw [quintic_degree_H_pow_three]
    norm_num

@[simp]
theorem quinticPolarization_cls : quinticPolarization.cls = rankOneH 3 := rfl

/-! ### The transported class -/

/-- Integration of a Chern-character component against a power of `H`: only the
total codimension three survives, and it survives with the degree `5`. -/
private theorem quintic_degree_chComp_mul (i k : ℕ) (E : ThreefoldNum) :
    quinticNumericalVariety.ring.degree
        (quinticNumericalVariety.chComp E i * rankOneH 3 ^ k)
      = threefoldChCoeff 5 E i * (if i + k = 3 then 5 else 0) := by
  show rankOneDegree 3 5
      (algebraMap ℚ (RankOneRing 3) (threefoldChCoeff 5 E i) * rankOneH 3 ^ i
        * rankOneH 3 ^ k) = _
  rw [mul_assoc, ← pow_add, rankOneDegree_algebraMap_mul_pow]

/-- Integration of a Chern-character component with no extra factor. -/
private theorem quintic_degree_chComp (i : ℕ) (E : ThreefoldNum) :
    quinticNumericalVariety.ring.degree (quinticNumericalVariety.chComp E i)
      = threefoldChCoeff 5 E i * (if i = 3 then 5 else 0) := by
  show rankOneDegree 3 5
      (algebraMap ℚ (RankOneRing 3) (threefoldChCoeff 5 E i) * rankOneH 3 ^ i) = _
  rw [rankOneDegree_algebraMap_mul_pow]

/-! ### The four degrees of a class on the quintic

The transport of `(a, b, c, e)` is `(5a, 5b, 5(-b/2 + c), 5b/6 - 5c + e)`. -/

/-- Not a `simp` lemma: the generic `Threefold.toNumClass_deg*` projections are
already `simp` and rewrite the left-hand side first, so the normal-form linter
rejects the attribute.  `quintic_reZ` and `quintic_imZ` name these explicitly. -/
theorem quintic_toNumClass_deg0 (E : ThreefoldNum) :
    (Threefold.toNumClass quinticNumericalVariety quinticPolarization E).deg0
      = ((5 * (E 0 : ℚ) : ℚ) : ℝ) := by
  rw [Threefold.toNumClass_deg0, quinticPolarization_cls, quintic_degree_H_pow_three]
  norm_num
  rfl

/-- Not a `simp` lemma, for the reason given at `quintic_toNumClass_deg0`. -/
theorem quintic_toNumClass_deg1 (E : ThreefoldNum) :
    (Threefold.toNumClass quinticNumericalVariety quinticPolarization E).deg1
      = ((5 * (E 1 : ℚ) : ℚ) : ℝ) := by
  rw [Threefold.toNumClass_deg1, quinticPolarization_cls, quintic_degree_chComp_mul]
  norm_num
  simp only [threefoldChCoeff]
  push_cast
  ring

/-- Not a `simp` lemma, for the reason given at `quintic_toNumClass_deg0`. -/
theorem quintic_toNumClass_deg2 (E : ThreefoldNum) :
    (Threefold.toNumClass quinticNumericalVariety quinticPolarization E).deg2
      = ((5 * (-(E 1 : ℚ) / 2 + (E 2 : ℚ)) : ℚ) : ℝ) := by
  rw [Threefold.toNumClass_deg2, quinticPolarization_cls]
  have h : quinticNumericalVariety.chComp E 2 * rankOneH 3
      = quinticNumericalVariety.chComp E 2 * rankOneH 3 ^ 1 := by rw [pow_one]
  rw [h, quintic_degree_chComp_mul]
  norm_num
  simp only [threefoldChCoeff]
  push_cast
  ring

/-- Not a `simp` lemma, for the reason given at `quintic_toNumClass_deg0`.

The degree cancels the `/5` that `threefoldChCoeff 5` puts on the point
coordinate, which is why this one is not the `ℙ³` answer times five. -/
theorem quintic_toNumClass_deg3 (E : ThreefoldNum) :
    (Threefold.toNumClass quinticNumericalVariety quinticPolarization E).deg3
      = ((5 * (E 1 : ℚ) / 6 - 5 * (E 2 : ℚ) + (E 3 : ℚ) : ℚ) : ℝ) := by
  rw [Threefold.toNumClass_deg3, quintic_degree_chComp]
  norm_num
  simp only [threefoldChCoeff]
  push_cast
  ring

/-! ### The charge family on the model -/

/-- The threefold charge family of the quintic, indexed by `(α, β)`. -/
def quinticWallChargeFamily : Wall.ChargeFamily (ℝ × ℝ) ThreefoldNum :=
  Threefold.wallChargeFamily quinticNumericalVariety quinticPolarization

@[simp]
theorem quinticWallChargeFamily_charge (p : ℝ × ℝ) (E : ThreefoldNum) :
    quinticWallChargeFamily.charge p E =
      Wall.Threefold.charge p.1 p.2
        (Threefold.toNumClass quinticNumericalVariety quinticPolarization E) := rfl

/-- The real part of the quintic charge, in linear-section coordinates. -/
theorem quintic_reZ (α β : ℝ) (E : ThreefoldNum) :
    Wall.Threefold.reZ α β
        (Threefold.toNumClass quinticNumericalVariety quinticPolarization E)
      = -((5 * (E 1 : ℚ) / 6 - 5 * (E 2 : ℚ) + (E 3 : ℚ) : ℚ) : ℝ)
        + β * ((5 * (-(E 1 : ℚ) / 2 + (E 2 : ℚ)) : ℚ) : ℝ)
        - (β ^ 2 - α ^ 2) / 2 * ((5 * (E 1 : ℚ) : ℚ) : ℝ)
        + (β ^ 3 - 3 * β * α ^ 2) / 6 * ((5 * (E 0 : ℚ) : ℚ) : ℝ) := by
  simp only [Wall.Threefold.reZ, quintic_toNumClass_deg0, quintic_toNumClass_deg1,
    quintic_toNumClass_deg2, quintic_toNumClass_deg3]

/-- The imaginary part of the quintic charge, in linear-section coordinates. -/
theorem quintic_imZ (α β : ℝ) (E : ThreefoldNum) :
    Wall.Threefold.imZ α β
        (Threefold.toNumClass quinticNumericalVariety quinticPolarization E)
      = α * (((5 * (-(E 1 : ℚ) / 2 + (E 2 : ℚ)) : ℚ) : ℝ)
        - β * ((5 * (E 1 : ℚ) : ℚ) : ℝ)
        + (3 * β ^ 2 - α ^ 2) / 6 * ((5 * (E 0 : ℚ) : ℚ) : ℝ)) := by
  simp only [Wall.Threefold.imZ, quintic_toNumClass_deg0, quintic_toNumClass_deg1,
    quintic_toNumClass_deg2]

/-! ### The transported Bayer--Macrì--Toda inequality -/

/-- The transported inequality on the quintic, taking the datum as a hypothesis.

**No witness is constructed here.**  `ProjectiveSpaceWalls.p3BMTSanity` already
shows the structure is inhabitable, and a second tautological witness would add
nothing.  The inequality itself is not proved for the quintic or for anything
else, and it is false for some threefolds. -/
theorem quintic_Q_toNumClass_nonneg
    (B : Threefold.BMTData quinticNumericalVariety quinticPolarization)
    {α β : ℚ} {E : ThreefoldNum} (hα : 0 < α) (hE : B.TiltSemistable α β E) :
    0 ≤ Wall.Threefold.Q (α : ℝ) (β : ℝ)
      (Threefold.toNumClass quinticNumericalVariety quinticPolarization E) :=
  Threefold.Q_toNumClass_nonneg quinticNumericalVariety quinticPolarization B hα hE

end

end Examples

end AlgebraicGeometry.Numerical

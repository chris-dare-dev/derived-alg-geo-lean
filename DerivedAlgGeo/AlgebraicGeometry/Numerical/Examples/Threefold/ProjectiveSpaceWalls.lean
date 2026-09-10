/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Threefold.ProjectiveSpace
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.ThreefoldWallTransport

/-!
# The threefold wall transport, on `ℙ³`

`Stability/ThreefoldWallTransport.lean` carries a polarised threefold class into
the four-coordinate `(α, β)` charge plane, and `Examples/Threefold/ProjectiveSpace.lean`
builds the `ℙ³` model.  Nothing connected them: the model was referenced only
inside its own file, and no polarization was defined for it at all.  So the
threefold charge arithmetic had no worked example, exactly as the surface
arithmetic had none before `Examples/Surface/RankOneRealization.lean`.

This file supplies the polarization and evaluates the transport.

## The coordinates

With `∫H³ = 1` and linear-section coordinates `(a, b, c, e)`, the four degrees
come out as

```text
∫H³ch₀ = a,   ∫H²ch₁ = b,   ∫H·ch₂ = -b/2 + c,   ∫ch₃ = b/6 - c + e,
```

which is `threefoldChCoeff` read against `∫H³ = 1`.  The four
`p3_toNumClass_deg*` lemmas are that computation, and everything else in the file is a consequence of it together
with the general theorems of the transport.

## The Bayer--Macrì--Toda datum, and what a witness can honestly be

`BMTData` has no witness anywhere in the tree, so every consequence of it is
vacuous.  It cannot be given an honest one by proving the inequality: the
conjecture is **false for some threefolds** — the blow-up of `ℙ³` at a point,
Schmidt — and true for `ℙ³` itself only by a real theorem this repository does
not contain.

`p3BMTSanity` is therefore a sanity witness in the exact style of
`k3BogomolovSanity`: its `TiltSemistable` predicate is *defined* to be the
conclusion, so `nonneg` holds tautologously.  **It asserts nothing whatsoever
about sheaves or about tilt stability**, and must not be read as the
Bayer--Macrì--Toda inequality for `ℙ³`.  What it buys is that the transported
statements below are about an inhabited structure.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition

namespace AlgebraicGeometry.Numerical

namespace Examples

noncomputable section

/-! ### The polarization -/

/-- `∫_{ℙ³} H³ = 1`. -/
theorem p3_degree_H_pow_three :
    p3NumericalVariety.ring.degree (rankOneH 3 ^ 3) = 1 := by
  show rankOneDegree 3 1 (rankOneH 3 ^ 3) = 1
  rw [rankOneDegree_pow]
  norm_num

/-- **The hyperplane class as a polarization of `ℙ³`.**  The first polarization
of a threefold model in the repository. -/
def p3Polarization : Polarization p3NumericalVariety.ring where
  cls := rankOneH 3
  cls_mem := by
    have h := rankOneH_pow_mem_piece 3 1
    rwa [pow_one] at h
  degree_pow_pos := by
    rw [p3_degree_H_pow_three]
    norm_num

@[simp]
theorem p3Polarization_cls : p3Polarization.cls = rankOneH 3 := rfl

/-! ### The transported class -/

/-- Integration of a Chern-character component against a power of `H`: only the
total codimension three survives. -/
private theorem p3_degree_chComp_mul (i k : ℕ) (E : ThreefoldNum) :
    p3NumericalVariety.ring.degree (p3NumericalVariety.chComp E i * rankOneH 3 ^ k)
      = threefoldChCoeff 1 E i * (if i + k = 3 then 1 else 0) := by
  show rankOneDegree 3 1
      (algebraMap ℚ (RankOneRing 3) (threefoldChCoeff 1 E i) * rankOneH 3 ^ i
        * rankOneH 3 ^ k) = _
  rw [mul_assoc, ← pow_add, rankOneDegree_algebraMap_mul_pow]

/-- Integration of a Chern-character component with no extra factor. -/
private theorem p3_degree_chComp (i : ℕ) (E : ThreefoldNum) :
    p3NumericalVariety.ring.degree (p3NumericalVariety.chComp E i)
      = threefoldChCoeff 1 E i * (if i = 3 then 1 else 0) := by
  show rankOneDegree 3 1
      (algebraMap ℚ (RankOneRing 3) (threefoldChCoeff 1 E i) * rankOneH 3 ^ i) = _
  rw [rankOneDegree_algebraMap_mul_pow]

/-! ### The four degrees of a class on `ℙ³`

The transport of `(a, b, c, e)` is `(a, b, -b/2 + c, b/6 - c + e)`.  These four
lemmas are the computation the rest of the file rests on. -/

/-- Not a `simp` lemma: the generic `Threefold.toNumClass_deg*` projections are
already `simp` and rewrite the left-hand side first, so the normal-form linter
rejects the attribute.  `p3_reZ` and `p3_imZ` name these explicitly. -/
theorem p3_toNumClass_deg0 (E : ThreefoldNum) :
    (Threefold.toNumClass p3NumericalVariety p3Polarization E).deg0 = ((E 0 : ℤ) : ℝ) := by
  rw [Threefold.toNumClass_deg0, p3Polarization_cls, p3_degree_H_pow_three, one_mul]
  norm_num
  rfl

/-- Not a `simp` lemma: the generic `Threefold.toNumClass_deg*` projections are
already `simp` and rewrite the left-hand side first, so the normal-form linter
rejects the attribute.  `p3_reZ` and `p3_imZ` name these explicitly. -/
theorem p3_toNumClass_deg1 (E : ThreefoldNum) :
    (Threefold.toNumClass p3NumericalVariety p3Polarization E).deg1 = ((E 1 : ℤ) : ℝ) := by
  rw [Threefold.toNumClass_deg1, p3Polarization_cls, p3_degree_chComp_mul]
  norm_num
  rfl

/-- Not a `simp` lemma: the generic `Threefold.toNumClass_deg*` projections are
already `simp` and rewrite the left-hand side first, so the normal-form linter
rejects the attribute.  `p3_reZ` and `p3_imZ` name these explicitly. -/
theorem p3_toNumClass_deg2 (E : ThreefoldNum) :
    (Threefold.toNumClass p3NumericalVariety p3Polarization E).deg2
      = ((-(E 1 : ℚ) / 2 + (E 2 : ℚ) : ℚ) : ℝ) := by
  rw [Threefold.toNumClass_deg2, p3Polarization_cls]
  have h : p3NumericalVariety.chComp E 2 * rankOneH 3
      = p3NumericalVariety.chComp E 2 * rankOneH 3 ^ 1 := by rw [pow_one]
  rw [h, p3_degree_chComp_mul]
  norm_num
  simp only [threefoldChCoeff]
  push_cast
  ring

/-- Not a `simp` lemma: the generic `Threefold.toNumClass_deg*` projections are
already `simp` and rewrite the left-hand side first, so the normal-form linter
rejects the attribute.  `p3_reZ` and `p3_imZ` name these explicitly. -/
theorem p3_toNumClass_deg3 (E : ThreefoldNum) :
    (Threefold.toNumClass p3NumericalVariety p3Polarization E).deg3
      = (((E 1 : ℚ) / 6 - (E 2 : ℚ) + (E 3 : ℚ) : ℚ) : ℝ) := by
  rw [Threefold.toNumClass_deg3, p3_degree_chComp]
  norm_num
  show ((threefoldChCoeff 1 E 3 : ℚ) : ℝ) = _
  simp only [threefoldChCoeff]
  norm_num

/-! ### The charge family on the model -/

/-- The threefold charge family of `ℙ³`, indexed by `(α, β)`. -/
def p3WallChargeFamily : Wall.ChargeFamily (ℝ × ℝ) ThreefoldNum :=
  Threefold.wallChargeFamily p3NumericalVariety p3Polarization

@[simp]
theorem p3WallChargeFamily_charge (p : ℝ × ℝ) (E : ThreefoldNum) :
    p3WallChargeFamily.charge p E =
      Wall.Threefold.charge p.1 p.2
        (Threefold.toNumClass p3NumericalVariety p3Polarization E) := rfl

/-- The real part of the `ℙ³` charge, in linear-section coordinates. -/
theorem p3_reZ (α β : ℝ) (E : ThreefoldNum) :
    Wall.Threefold.reZ α β (Threefold.toNumClass p3NumericalVariety p3Polarization E)
      = -(((E 1 : ℚ) / 6 - (E 2 : ℚ) + (E 3 : ℚ) : ℚ) : ℝ)
        + β * (((-(E 1 : ℚ) / 2 + (E 2 : ℚ) : ℚ) : ℝ))
        - (β ^ 2 - α ^ 2) / 2 * ((E 1 : ℤ) : ℝ)
        + (β ^ 3 - 3 * β * α ^ 2) / 6 * ((E 0 : ℤ) : ℝ) := by
  simp only [Wall.Threefold.reZ, p3_toNumClass_deg0, p3_toNumClass_deg1,
    p3_toNumClass_deg2, p3_toNumClass_deg3]

/-- The imaginary part of the `ℙ³` charge, in linear-section coordinates. -/
theorem p3_imZ (α β : ℝ) (E : ThreefoldNum) :
    Wall.Threefold.imZ α β (Threefold.toNumClass p3NumericalVariety p3Polarization E)
      = α * ((((-(E 1 : ℚ) / 2 + (E 2 : ℚ) : ℚ) : ℝ)) - β * ((E 1 : ℤ) : ℝ)
        + (3 * β ^ 2 - α ^ 2) / 6 * ((E 0 : ℤ) : ℝ)) := by
  simp only [Wall.Threefold.imZ, p3_toNumClass_deg0, p3_toNumClass_deg1,
    p3_toNumClass_deg2]

/-! ### A sanity witness for the Bayer--Macrì--Toda datum -/

/-- **A sanity witness, not geometry.**

`TiltSemistable` is taken to be the conclusion itself, so `nonneg` holds
tautologously.  This asserts **nothing whatsoever about sheaves or about tilt
stability**: it exists only to show `BMTData` is inhabitable and that the
transported theorems fire on a concrete model.  Do not read it as the
Bayer--Macrì--Toda inequality for `ℙ³`, which is a real theorem this repository
does not contain, nor as evidence for the conjecture, which is false for some
threefolds. -/
def p3BMTSanity : Threefold.BMTData p3NumericalVariety p3Polarization where
  TiltSemistable α β E := 0 ≤ Threefold.Q p3NumericalVariety p3Polarization α β E
  nonneg _ _ _ _ h := h

/-- The transported inequality, on the model.  Its content is exactly the
content of `p3BMTSanity`, which is none. -/
theorem p3_Q_toNumClass_nonneg {α β : ℚ} {E : ThreefoldNum} (hα : 0 < α)
    (hE : p3BMTSanity.TiltSemistable α β E) :
    0 ≤ Wall.Threefold.Q (α : ℝ) (β : ℝ)
      (Threefold.toNumClass p3NumericalVariety p3Polarization E) :=
  Threefold.Q_toNumClass_nonneg p3NumericalVariety p3Polarization p3BMTSanity hα hE

end

end Examples

end AlgebraicGeometry.Numerical

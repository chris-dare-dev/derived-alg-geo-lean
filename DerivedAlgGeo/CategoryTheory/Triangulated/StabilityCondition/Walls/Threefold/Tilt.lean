/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Numerical.ChargeFamily
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Rotation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Threefold.Basic

/-!
# The tilt charge family, as the surface family pulled back along a truncation

The `(n, m) = (3, 2)` tilt charge needs **no new polynomial and no kernel**.  It
is `stChargeFamily` -- the existing three-coordinate surface family owned by
`CentralCharge/Numerical/SurfaceFamily.lean` -- reindexed by `Prod.swap` and
pulled back along the four-to-three coordinate drop.

## What is actually new here

`threefoldTruncate` is the only new construction: the additive map that forgets
the fourth compressed degree.  Without it the surface nested-semicircle theorems
cannot be applied to tilt walls at all, because they speak about
`stChargeFamily` and tilt walls do not.

## The chart transposition

The surface family is indexed `(s, t)` and the threefold half plane is indexed
`(alpha, beta)`, with `s = beta` and `t = alpha`.  That transposition lives in
exactly one `reindex Prod.swap` and nowhere else.

## Main results

* `tiltFamily` -- the tilt charge family, definitionally the surface family.
* `rotatedTiltFamily` -- `tiltFamily.phaseRotate (1/2)`, the charge
  Bayer--Lahoz--Macri--Stellari actually induce from.
* `nu_eq_tilt_slope`, `chargeSlope_tilt` -- the tilt slope is `alpha` times the
  charge slope, tying the family to the existing `Threefold.nu`.
* `rotatedTiltFamily_alignmentLocus_eq_preimage` -- every rotated tilt wall is a
  `Prod.swap` preimage of an `stChargeFamily` alignment locus.  This is what
  lets `walls_nested_of_discr_nonneg`, `wall_circle_eq` and `wall_eq_of_meet`
  apply to tilt walls.  The abstraction-audit remediation names this statement
  `rotatedTiltFamily_wall_eq_preimage`; MO1.03 (#1314) renamed the wall locus to
  `alignmentLocus`, and the name here follows the current spelling.

## Two negative results, recorded rather than dropped

* `exists_tilt_alignmentValue_ne_threefold` -- the tilt family is **not** a
  chart change of `Threefold.chargeFamily`.  Their alignment loci genuinely
  differ, and the witness below is computed, not asserted: the truncation
  forgets the fourth degree, which the threefold charge reads.
* `exists_chargeSlope_rotatedTiltFamily_ne` -- the rotation is not cosmetic.
  It fixes every alignment value (`phaseRotate_alignmentValue`) and still moves
  `chargeSlope`, so a construction that keeps the tilt walls and drops the
  rotation is right about the wall locus and wrong about which objects are
  semistable.

The tilt-stability *categorical* content -- a heart, a slicing, or the BMT
inequality -- is asserted nowhere in this file.  This is numerical data only.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

namespace Tilt

open Threefold (betaTwist)

/-! ### The four-to-three coordinate drop -/

/-- **The truncation**: forget the fourth compressed degree, and nothing more.

This is the one new construction of the tilt slice.  It is additive because the
four compressed degrees are additive coordinates on a product of copies of the
reals, and it is not an isomorphism: `exists_tilt_alignmentValue_ne_threefold`
records exactly what it forgets. -/
def threefoldTruncate : Threefold.NumClass →+ NumClass :=
  AddMonoidHom.mk' (fun v => (v.1, v.2.1, v.2.2.1)) (by intro v w; rfl)

-- Deliberately NOT `@[simp]`. It rewrites `threefoldTruncate v` to a raw
-- tuple, which takes the three projection lemmas below out of simp-normal form:
-- simp reaches `NumClass.rk (v.deg0, v.deg1, v.deg2)` and they can never fire.
-- The projections are the useful normal form, so they keep the attribute and
-- this does not. The two `simp only` calls below that want the tuple name this
-- lemma explicitly, so they are unaffected.
theorem threefoldTruncate_apply (v : Threefold.NumClass) :
    threefoldTruncate v =
      (Threefold.NumClass.deg0 v, Threefold.NumClass.deg1 v,
        Threefold.NumClass.deg2 v) := rfl

@[simp]
theorem rk_threefoldTruncate (v : Threefold.NumClass) :
    NumClass.rk (threefoldTruncate v) = Threefold.NumClass.deg0 v := rfl

@[simp]
theorem deg_threefoldTruncate (v : Threefold.NumClass) :
    NumClass.deg (threefoldTruncate v) = Threefold.NumClass.deg1 v := rfl

@[simp]
theorem ch2_threefoldTruncate (v : Threefold.NumClass) :
    NumClass.ch2 (threefoldTruncate v) = Threefold.NumClass.deg2 v := rfl

/-! ### The tilt family -/

/-- **The tilt charge family**, at `(n, m) = (3, 2)`.

The existing surface family, transposed once and pulled back along the
truncation.  No new polynomial and no new kernel: the canonical root is
`stChargeFamily`. -/
def tiltFamily : ChargeFamily (ℝ × ℝ) Threefold.NumClass :=
  (stChargeFamily.reindex _root_.Prod.swap).pullback threefoldTruncate

/-- **The rotated tilt family**, the charge Bayer--Lahoz--Macri--Stellari
induce from.  At `beta = 1/2` the rotation scalar is `-i`, which is the
division by `i` those authors write. -/
def rotatedTiltFamily : ChargeFamily (ℝ × ℝ) Threefold.NumClass :=
  tiltFamily.phaseRotate (1 / 2)

@[simp]
theorem tiltFamily_charge (p : ℝ × ℝ) (v : Threefold.NumClass) :
    tiltFamily.charge p v = stCharge p.2 p.1 (threefoldTruncate v) := rfl

/-- The real part of the tilt charge is the Bayer--Macri--Toda numerator, with
its sign. -/
theorem tiltFamily_re (α β : ℝ) (v : Threefold.NumClass) :
    tiltFamily.re (α, β) v =
      -(Threefold.NumClass.deg2 (betaTwist β v)
        - α ^ 2 / 2 * Threefold.NumClass.deg0 v) := by
  simp only [ChargeFamily.re, tiltFamily_charge, stCharge_re, reZ,
    threefoldTruncate_apply, Threefold.betaTwist, NumClass.rk, NumClass.deg,
    NumClass.ch2, Threefold.NumClass.deg0, Threefold.NumClass.deg1,
    Threefold.NumClass.deg2]
  ring

/-- The imaginary part of the tilt charge is `alpha` times the twisted first
degree. -/
theorem tiltFamily_im (α β : ℝ) (v : Threefold.NumClass) :
    tiltFamily.im (α, β) v = α * Threefold.NumClass.deg1 (betaTwist β v) := by
  simp only [ChargeFamily.im, tiltFamily_charge, stCharge_im, imZ,
    threefoldTruncate_apply, Threefold.betaTwist, NumClass.rk, NumClass.deg,
    Threefold.NumClass.deg0, Threefold.NumClass.deg1]

/-! ### The tilt slope is the charge slope -/

/-- **The tilt slope is `alpha` times the charge slope.**  `Threefold.nu` of
`Walls/Threefold/Basic.lean` is the charge slope of the tilt family, rescaled.

The hypothesis is the one the slope convention needs: `chargeSlope` is the top
element off the open upper half plane, and `Threefold.nu` is junk where its
denominator vanishes, so the two agree exactly where both are defined. -/
theorem nu_eq_tilt_slope (α β : ℝ) (v : Threefold.NumClass)
    (h : 0 < tiltFamily.im (α, β) v) :
    Threefold.nu α β v =
      α * (-(tiltFamily.re (α, β) v) / tiltFamily.im (α, β) v) := by
  rw [tiltFamily_im] at h
  rw [tiltFamily_re, tiltFamily_im]
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact lt_irrefl 0 h
  have hd : Threefold.NumClass.deg1 (betaTwist β v) ≠ 0 := by
    rintro hz
    rw [hz, mul_zero] at h
    exact lt_irrefl 0 h
  rw [Threefold.nu]
  field_simp

/-- The tilt family's `chargeSlope`, in Bayer--Macri--Toda coordinates. -/
theorem chargeSlope_tilt (α β : ℝ) (v : Threefold.NumClass)
    (h : 0 < tiltFamily.im (α, β) v) :
    chargeSlope (tiltFamily.charge (α, β) v)
      = ((Threefold.nu α β v / α : ℝ) : WithTop ℝ) := by
  have him : 0 < (tiltFamily.charge (α, β) v).im := h
  have hα : α ≠ 0 := by
    rintro rfl
    rw [tiltFamily_im, zero_mul] at h
    exact lt_irrefl 0 h
  have key : Threefold.nu α β v / α
      = -(tiltFamily.re (α, β) v) / tiltFamily.im (α, β) v := by
    rw [nu_eq_tilt_slope α β v h]
    field_simp
  rw [chargeSlope_of_im_pos him, key]
  simp only [ChargeFamily.re, ChargeFamily.im]

/-! ### Every rotated tilt wall is a surface wall -/

/-- **The rotated tilt walls are `Prod.swap` preimages of `stChargeFamily`
walls.**

This is the statement that lets the surface nested-semicircle theorems apply to
tilt walls: `walls_nested_of_discr_nonneg`, `wall_circle_eq` and
`wall_eq_of_meet` are about `stChargeFamily`, and this identifies the tilt wall
with one of theirs. -/
theorem rotatedTiltFamily_alignmentLocus_eq_preimage (v w : Threefold.NumClass) :
    rotatedTiltFamily.alignmentLocus v w =
      _root_.Prod.swap ⁻¹'
        stChargeFamily.alignmentLocus (threefoldTruncate v)
          (threefoldTruncate w) := by
  rw [rotatedTiltFamily, ChargeFamily.phaseRotate_alignmentLocus, tiltFamily,
    ChargeFamily.pullback_alignmentLocus, ChargeFamily.reindex_alignmentLocus]

/-- The same statement on the alignment expression itself, which the rotation
also fixes. -/
theorem rotatedTiltFamily_alignmentValue (p : ℝ × ℝ) (v w : Threefold.NumClass) :
    rotatedTiltFamily.alignmentValue p v w =
      stChargeFamily.alignmentValue p.swap (threefoldTruncate v)
        (threefoldTruncate w) := by
  rw [rotatedTiltFamily, ChargeFamily.phaseRotate_alignmentValue, tiltFamily,
    ChargeFamily.pullback_alignmentValue]
  rfl

/-! ### The two negative results -/

/-- At `beta = 1/2` the rotation scalar is `-i`, which is `1/i`.

`Walls/Rotation.lean` proves the same fact for its own use and keeps it private,
so the computation is repeated here rather than reached into. -/
private theorem exp_rotation_one_half :
    Complex.exp (-(Real.pi * (1 / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
  have h : (-(Real.pi * (1 / 2 : ℝ) : ℂ)) * Complex.I
      = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- **The tilt family is not a chart change of the threefold family.**

Their alignment loci genuinely differ, and here is the computed witness: at
`(alpha, beta) = (1, 0)` the classes `(0, 1, 1, 0)` and `(0, 1, 1, 1)` have the
same truncation, so the tilt alignment value vanishes, while the threefold
charge reads the fourth degree and its alignment value is `1`.

This is the content the truncation forgets, stated as a theorem instead of left
as a remark. -/
theorem exists_tilt_alignmentValue_ne_threefold :
    ∃ (p : ℝ × ℝ) (v w : Threefold.NumClass),
      tiltFamily.alignmentValue p v w = 0 ∧
        Threefold.chargeFamily.alignmentValue p v w ≠ 0 := by
  refine ⟨(1, 0), (0, 1, 1, 0), (0, 1, 1, 1), ?_, ?_⟩
  · rw [ChargeFamily.alignmentValue, tiltFamily_re, tiltFamily_im,
      tiltFamily_re, tiltFamily_im]
    norm_num [Threefold.betaTwist, Threefold.NumClass.deg0,
      Threefold.NumClass.deg1, Threefold.NumClass.deg2]
  · rw [Threefold.chargeFamily_alignmentValue]
    norm_num [Threefold.reZ, Threefold.imZ, Threefold.NumClass.deg0,
      Threefold.NumClass.deg1, Threefold.NumClass.deg2, Threefold.NumClass.deg3]

/-- **The rotation is not cosmetic.**

`phaseRotate_alignmentValue` fixes every alignment value, so no tilt wall moves.
`chargeSlope` is a different matter: at `(alpha, beta) = (1, 0)` the class
`(0, 1, 1, 0)` has tilt charge `-1 + i`, of slope `1`, and rotated charge
`1 + i`, of slope `-1`.

Semistability is read off the phase, so a construction that keeps the walls and
drops the rotation is right about the wall locus and wrong about which objects
are semistable. -/
theorem exists_chargeSlope_rotatedTiltFamily_ne :
    ∃ (p : ℝ × ℝ) (v : Threefold.NumClass),
      chargeSlope (rotatedTiltFamily.charge p v)
        ≠ chargeSlope (tiltFamily.charge p v) := by
  refine ⟨(1, 0), (0, 1, 1, 0), ?_⟩
  have hre : (tiltFamily.charge ((1 : ℝ), (0 : ℝ))
      ((0, 1, 1, 0) : Threefold.NumClass)).re = -1 := by
    have := tiltFamily_re 1 0 ((0, 1, 1, 0) : Threefold.NumClass)
    rw [ChargeFamily.re] at this
    rw [this]
    norm_num [Threefold.betaTwist, Threefold.NumClass.deg0,
      Threefold.NumClass.deg1, Threefold.NumClass.deg2]
  have him : (tiltFamily.charge ((1 : ℝ), (0 : ℝ))
      ((0, 1, 1, 0) : Threefold.NumClass)).im = 1 := by
    have := tiltFamily_im 1 0 ((0, 1, 1, 0) : Threefold.NumClass)
    rw [ChargeFamily.im] at this
    rw [this]
    norm_num [Threefold.betaTwist, Threefold.NumClass.deg0,
      Threefold.NumClass.deg1]
  have hz : tiltFamily.charge ((1 : ℝ), (0 : ℝ))
      ((0, 1, 1, 0) : Threefold.NumClass) = -1 + Complex.I := by
    apply Complex.ext
    · rw [hre]; norm_num
    · rw [him]; norm_num
  have hrot : rotatedTiltFamily.charge ((1 : ℝ), (0 : ℝ))
      ((0, 1, 1, 0) : Threefold.NumClass) = 1 + Complex.I := by
    rw [rotatedTiltFamily, ChargeFamily.phaseRotate, ChargeFamily.smul_charge,
      exp_rotation_one_half, hz]
    apply Complex.ext <;> simp
  rw [hrot, hz, chargeSlope_of_im_pos (by simp), chargeSlope_of_im_pos (by simp)]
  have hne : (-(1 + Complex.I).re / (1 + Complex.I).im : ℝ)
      ≠ (-(-1 + Complex.I).re / (-1 + Complex.I).im : ℝ) := by norm_num
  exact_mod_cast hne

end Tilt

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

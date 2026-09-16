/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Alignment
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.SlopeGeometry
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Semistable.TiltGeometry

/-!
# The phase rotation of a charge family

`ChargeFamily.phaseRotate beta` rescales every charge of a family by
`exp (-π β i)`.  It is **not a fifth rotation**: it is the tilt rotation
`WeakPreStabilityCondition.phaseTiltRotation` that
`Weak/Tilting/Semistable/TiltGeometry.lean` already owns, reached through
`ChargeFamily.smul`, and the two bridges below prove that rather than assume
it.  This is the rotation Bayer--Lahoz--Macrì--Stellari apply to the tilt
charge of a cubic threefold, written there as division by `i`; at `beta = 1/2`
the scalar is `-i = 1/i`.

## Main results

* `phaseRotate_charge` — the rotated value **is** `phaseTiltRotation beta` of
  the old value.  `smul` multiplies on the left and `phaseTiltRotation` on the
  right, so the identification is a proved comparison, not a definitional
  accident of how either was written.
* `phaseRotate_constFamily` — on the constant family of a weak prestability
  condition's central charge, `phaseRotate` is that condition's
  `phaseTiltCharge`.  Together with the previous result this is what stops the
  rotation becoming a second spelling of an existing one.
* `phaseRotate_alignmentValue` — the rotation scalar has unit modulus, so it
  fixes the alignment *expression*, not merely its zero set.  No wall radius,
  nesting statement, or semicircle equation changes under it.
* `phaseRotate_alignmentLocus` — alignment loci are invariant.  This is
  `alignmentLocus_smul` at `Complex.exp_ne_zero`.
* `exists_chargeSlope_phaseRotate_ne` — the negative result.  The rotation is
  free on alignment loci and **not** free on phases: `chargeSlope` changes,
  with an explicit witness.  A construction that drops the rotation is
  therefore wrong about semistability even where it is right about walls,
  which is exactly why the rotation is applied in the first place.

## Placement

This file is deliberately **not** merged into `CentralCharge/Family.lean`.
That module owns `ChargeFamily` and imports only Mathlib; giving it a
`Weak/Tilting/` import would make the charge-family root stability-aware and
breach the layering contract that keeps charge construction upstream of walls.
`Walls/Alignment.lean` stays free of the tilt for the same reason, so the
rotation lives here, downstream of both.

The abstraction-audit remediation
(`docs/reviews/2026-09-12-abstraction-audit-remediation.md`, §3.5 and §7 PR-8)
names these statements `phaseRotate_wall` and `phaseRotate_wallValue`.  MO1.03
(#1314) renamed the wall locus and its defining expression to `alignmentLocus`
and `alignmentValue`; the statements below are the ones that remediation
proved, under the current names.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {P : Type u} {N : Type v} [AddCommGroup N]

namespace ChargeFamily

variable (Z : ChargeFamily P N)

/-- Rotate every charge of a family clockwise through `π β`.

This is `ChargeFamily.smul` at the tilt rotation's scalar and not a rotation of
its own: `phaseRotate_charge` proves it is
`WeakPreStabilityCondition.phaseTiltRotation`, and `phaseRotate_constFamily`
proves it is `WeakPreStabilityCondition.phaseTiltCharge` on a constant
family. -/
def phaseRotate (beta : ℝ) : ChargeFamily P N :=
  Z.smul (Complex.exp (-(Real.pi * beta : ℂ) * Complex.I))

/-- **The charge-family rotation is the tilt rotation.**  `smul` multiplies on
the left and `phaseTiltRotation` on the right; `ℂ` is commutative, so the two
agree, and this records that agreement as a theorem. -/
@[simp]
theorem phaseRotate_charge (beta : ℝ) (p : P) (x : N) :
    (Z.phaseRotate beta).charge p x =
      WeakPreStabilityCondition.phaseTiltRotation beta (Z.charge p x) := by
  simp only [phaseRotate, smul_charge,
    WeakPreStabilityCondition.phaseTiltRotation_apply]
  ring

/-- The rotation scalar lies on the unit circle. -/
private theorem normSq_exp_phase (beta : ℝ) :
    Complex.normSq (Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)) = 1 := by
  have h : (-(Real.pi * beta : ℂ)) * Complex.I
      = ((-(Real.pi * beta) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]

/-- **The rotation fixes the alignment expression itself**, and not only its
zero locus, because the rotation scalar has unit modulus.  This is strictly
stronger than `phaseRotate_alignmentLocus`: every quantity computed from
`alignmentValue` — a wall radius, a nesting comparison, a semicircle equation —
is unchanged by the rotation, not merely its vanishing. -/
@[simp]
theorem phaseRotate_alignmentValue (beta : ℝ) (p : P) (x y : N) :
    (Z.phaseRotate beta).alignmentValue p x y = Z.alignmentValue p x y := by
  rw [phaseRotate, alignmentValue_smul, normSq_exp_phase, one_mul]

/-- **Numerical alignment loci are invariant under the phase rotation.**  This
is `alignmentLocus_smul` with the nonvanishing hypothesis discharged by
`Complex.exp_ne_zero`. -/
@[simp]
theorem phaseRotate_alignmentLocus (beta : ℝ) (x y : N) :
    (Z.phaseRotate beta).alignmentLocus x y = Z.alignmentLocus x y :=
  Z.alignmentLocus_smul (Complex.exp_ne_zero _) x y

end ChargeFamily

section Tilt

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Lambda : Type*} [AddCommGroup Lambda] {v : K₀ C →+ Lambda}

namespace ChargeFamily

/-- **No second rotated charge.**  On the constant family of `sigma`'s central
charge, `phaseRotate` is `sigma.phaseTiltCharge` on the nose.  The tilted
charge of `Weak/Tilting/` and the rotated charge family are therefore the same
object read in two vocabularies, not two constructions to be compared later. -/
theorem phaseRotate_constFamily (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (p : P) :
    ((⟨fun _ => sigma.Z.comp v⟩ : ChargeFamily P (K₀ C)).phaseRotate beta).charge p =
      sigma.phaseTiltCharge beta := by
  refine AddMonoidHom.ext fun E => ?_
  exact (⟨fun _ => sigma.Z.comp v⟩ : ChargeFamily P (K₀ C)).phaseRotate_charge beta p E

end ChargeFamily

end Tilt

namespace ChargeFamily

/-- At `beta = 1/2` the rotation scalar is `-i`, which is `1/i`: this is the
rotation Bayer--Lahoz--Macrì--Stellari write as division by `i`. -/
private theorem exp_rotation_one_half :
    Complex.exp (-(Real.pi * (1 / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
  have h : (-(Real.pi * (1 / 2 : ℝ) : ℂ)) * Complex.I
      = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- **The rotation is free on alignment loci and not free on phases.**

`phaseRotate_alignmentValue` fixes every alignment expression, so no wall
moves.  `chargeSlope` is a different matter, and this records the falsification
of "the rotation is cosmetic": on the identity family of `ℂ` at `beta = 1/2`
the class `-1` has charge on the negative real axis, where `chargeSlope` is
`⊤`, while its rotation is `i`, where `chargeSlope` is `0`.

The consequence is the reason the rotation exists.  A construction that keeps
the walls and drops the rotation is right about the wall locus and wrong about
which objects are semistable, because semistability is read off the phase. -/
theorem exists_chargeSlope_phaseRotate_ne :
    ∃ (W : ChargeFamily Unit ℂ) (beta : ℝ) (p : Unit) (x : ℂ),
      chargeSlope ((W.phaseRotate beta).charge p x) ≠ chargeSlope (W.charge p x) := by
  refine ⟨⟨fun _ => AddMonoidHom.id ℂ⟩, 1 / 2, (), -1, ?_⟩
  have hlhs :
      ((⟨fun _ => AddMonoidHom.id ℂ⟩ :
        ChargeFamily Unit ℂ).phaseRotate (1 / 2)).charge () (-1) = Complex.I := by
    rw [phaseRotate, smul_charge, exp_rotation_one_half]
    simp
  have hrhs :
      (⟨fun _ => AddMonoidHom.id ℂ⟩ : ChargeFamily Unit ℂ).charge () (-1)
        = (-1 : ℂ) := rfl
  rw [hlhs, hrhs, chargeSlope_of_im_pos (by simp), chargeSlope_of_im_nonpos (by norm_num)]
  exact WithTop.coe_ne_top

end ChargeFamily

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

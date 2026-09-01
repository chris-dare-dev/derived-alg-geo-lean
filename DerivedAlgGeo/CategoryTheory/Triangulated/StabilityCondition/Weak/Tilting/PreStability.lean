/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.HarderNarasimhan.Ambient
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Basic.ChargeRay
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Assembly

/-!
# Reverse weak heart--slicing assembly for the phase tilt

This module connects the heart-level output of `TiltAssembly` to the reverse
weak heart--slicing foundations.  The analytic ray identity is supplied by
`ChargeRay`: normalized weak slopes give the required heart charge rays, and
integer shifts give the ambient compatibility axiom.

Hom vanishing is discharged by `HeartHomVanishing`, and ambient HN existence
by `AmbientHarderNarasimhan`: boundedness of the tilted t-structure and the
heart HN property extend the towers through the finite t-cohomological
filtration.  Consequently the phase-language weak upper tilt is now packaged
without an external reverse-equivalence premise.  The exact slope-language
adapter and source-normalized theorem are exposed separately by
`Tilting/Source`; this infrastructure alone makes no coverage promotion.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {v : K₀ C →+ V}

namespace WeakPreStabilityCondition

/-- The lattice-level central charge of the phase tilt. -/
noncomputable def phaseTiltLatticeCharge
    (sigma : WeakPreStabilityCondition v) (beta : ℝ) : V →+ ℂ :=
  (phaseTiltRotation beta).comp sigma.Z

omit [IsTriangulated C] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
@[simp]
theorem phaseTiltLatticeCharge_apply
    (sigma : WeakPreStabilityCondition v) (beta : ℝ) (x : V) :
    sigma.phaseTiltLatticeCharge beta x =
      sigma.Z x * Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := rfl

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The normalized ambient weak phase lies on the ray of the rotated lattice
charge. -/
theorem phaseTilt_ambientPhasePredicate_charge_ray
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    ∀ (phi : ℝ) (E : C),
    WeakStabilityFunction.ambientPhasePredicate
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) phi E →
    ¬IsZero E → ∃ m : ℝ, 0 ≤ m ∧
      ((∀ n : ℤ, phi ≠ (n : ℝ)) → 0 < m) ∧
      sigma.phaseTiltLatticeCharge beta (v (K₀.of C E)) =
        (m : ℂ) * Complex.exp ((Real.pi * phi : ℂ) * Complex.I) := by
  intro phi E hP hE0
  simpa only [phaseTiltLatticeCharge_apply,
    phaseTiltWeakStabilityFunction_charge] using
    WeakStabilityFunction.ambientPhasePredicate_charge_ray
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) phi E hP hE0

omit [FiniteDimensional ℝ V] in
/-- The heart-level HN field of the phase-tilt assembly gives ambient HN
towers for all objects already lying in the tilted heart. -/
theorem PhaseTiltHeartObligations.ambientHN_exists_of_mem_tiltedHeart
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (Zlin : V →ₗ[ℝ] ℂ)
    (H : sigma.PhaseTiltHeartObligations beta hbeta0 hbeta1 Zlin)
    (E : C)
    (hE : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E) :
    Nonempty (HNFiltration C
      (WeakStabilityFunction.ambientPhasePredicate
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)) E) :=
  WeakStabilityFunction.ambientHN_exists_of_mem_heart
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) H.hasHN E hE

omit [FiniteDimensional ℝ V] in
/-- The heart HN field of the phase-tilt assembly extends canonically to an
ambient HN filtration for every object.  Boundedness of the original slicing
t-structure is preserved by the HRS tilt, and
`WeakStabilityFunction.ambientHN_exists_of_bounded` performs the finite
t-cohomological assembly. -/
theorem PhaseTiltHeartObligations.ambientHN
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (Zlin : V →ₗ[ℝ] ℂ)
    (H : sigma.PhaseTiltHeartObligations beta hbeta0 hbeta1 Zlin)
    (E : C) :
    Nonempty (HNFiltration C
      (WeakStabilityFunction.ambientPhasePredicate
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)) E) :=
  WeakStabilityFunction.ambientHN_exists_of_bounded
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)
    (heartTorsionPair_tilt_isBounded
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le)
      (sigma.slicing.toTStructure_bounded C))
    H.hasHN E

/-- Package the completed heart-level phase-tilt assembly as an ambient weak
prestability condition.  Both ambient HN existence and charge-ray
compatibility are derived rather than supplied as premises. -/
noncomputable def PhaseTiltHeartObligations.toWeakPreStabilityCondition
    {sigma : WeakPreStabilityCondition v} {beta : ℝ}
    {hbeta0 : 0 ≤ beta} {hbeta1 : beta < 1}
    {Zlin : V →ₗ[ℝ] ℂ}
    (H : sigma.PhaseTiltHeartObligations
      beta hbeta0 hbeta1 Zlin) : WeakPreStabilityCondition v :=
  (WeakStabilityFunction.reverseSlicingObligationsOfHN
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1)
    (fun E ↦ H.ambientHN sigma beta hbeta0 hbeta1 Zlin E)).toWeakPreStabilityCondition
    (sigma.phaseTiltLatticeCharge beta)
    (sigma.phaseTilt_ambientPhasePredicate_charge_ray beta hbeta0 hbeta1)

omit [FiniteDimensional ℝ V] in
@[simp]
theorem PhaseTiltHeartObligations.toWeakPreStabilityCondition_Z
    {sigma : WeakPreStabilityCondition v} {beta : ℝ}
    {hbeta0 : 0 ≤ beta} {hbeta1 : beta < 1}
    {Zlin : V →ₗ[ℝ] ℂ}
    (H : sigma.PhaseTiltHeartObligations beta hbeta0 hbeta1 Zlin) :
    H.toWeakPreStabilityCondition.Z = sigma.phaseTiltLatticeCharge beta := rfl

omit [FiniteDimensional ℝ V] in
@[simp]
theorem PhaseTiltHeartObligations.toWeakPreStabilityCondition_P
    {sigma : WeakPreStabilityCondition v} {beta : ℝ}
    {hbeta0 : 0 ≤ beta} {hbeta1 : beta < 1}
    {Zlin : V →ₗ[ℝ] ℂ}
    (H : sigma.PhaseTiltHeartObligations beta hbeta0 hbeta1 Zlin) :
    H.toWeakPreStabilityCondition.slicing.P =
      WeakStabilityFunction.ambientPhasePredicate
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1) := rfl

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The phase-language weak upper tilt constructed directly from Definition
14.12's tilting property.  The HN and charge-ray inputs are derived directly;
no support-property realization is needed to construct the ambient weak
prestability condition.  This declaration deliberately makes no claim that
the exact slope-language statement of Proposition 14.16 has been reviewed. -/
noncomputable def phaseTiltWeakPreStabilityConditionOfTiltingProperty
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty) : WeakPreStabilityCondition v :=
  (WeakStabilityFunction.reverseSlicingObligationsOfHN
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1)
    (fun E ↦ WeakStabilityFunction.ambientHN_exists_of_bounded
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1)
      (heartTorsionPair_tilt_isBounded
        (slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le)
        (sigma.slicing.toTStructure_bounded C))
      (sigma.phaseTilt_hasHNPropertyOfTiltingProperty
        beta hbeta0 hbeta1 htilt)
      E)).toWeakPreStabilityCondition
    (sigma.phaseTiltLatticeCharge beta)
    (sigma.phaseTilt_ambientPhasePredicate_charge_ray
      beta hbeta0.le hbeta1)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
@[simp]
theorem phaseTiltWeakPreStabilityConditionOfTiltingProperty_Z
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty) :
    (sigma.phaseTiltWeakPreStabilityConditionOfTiltingProperty beta hbeta0 hbeta1
      htilt).Z = sigma.phaseTiltLatticeCharge beta := rfl

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
@[simp]
theorem phaseTiltWeakPreStabilityConditionOfTiltingProperty_P
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty) :
    (sigma.phaseTiltWeakPreStabilityConditionOfTiltingProperty beta hbeta0 hbeta1
      htilt).slicing.P =
      WeakStabilityFunction.ambientPhasePredicate
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1) := rfl

end WeakPreStabilityCondition

end

end CategoryTheory.Triangulated.WeakStabilityCondition

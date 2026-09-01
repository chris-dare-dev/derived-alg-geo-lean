/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Source.Support
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Noetherian

/-!
# Source-facing Proposition 14.16 and Lemma 14.17

This file exposes the completed phase-language infrastructure with the exact
slope cutoff, tilted heart, and central charge used in arXiv:1902.08184v4.
In particular, the output charge is definitionally `Z/(I-b)`, not merely a
unit rotation of `Z`.
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

/-- The conclusions of Proposition 14.16 with the exact source
normalization.  The weak prestability condition supplies the ambient slicing
and HN filtrations; `support` upgrades it to weak stability, and
`zeroChargeNoetherian` records the proposition's final assertion. -/
structure SourceTiltConclusion
    (sigma : WeakPreStabilityCondition v) (b : ℝ)
    (htilt : sigma.TiltingProperty)
    (Zlin : V →ₗ[ℝ] ℂ) where
  /-- The tilted weak prestability condition with charge `Z/(I-b)`. -/
  condition : WeakPreStabilityCondition v
  /-- The condition is the canonical source-normalized construction. -/
  condition_eq : condition =
    sigma.sourceTiltWeakPreStabilityConditionOfTiltingProperty b
      htilt
  /-- The support property for the exact source-normalized heart charge. -/
  support : (sigma.sourceTiltWeakStabilityFunction b).HasSupportProperty v
    (sourceTiltLinearCharge b Zlin)
  /-- The new zero-charge subcategory is noetherian torsion. -/
  zeroChargeNoetherian :
    NoetherianTorsionSubcategory (sigma.slopeTorsionPair b).tilt
  /-- Its torsion class is exactly the source-normalized zero-charge class. -/
  zeroCharge_tors : zeroChargeNoetherian.pair.tors =
    (sigma.sourceTiltWeakStabilityFunction b).zeroCharge

/-- **Proposition 14.16 (source normalization).**

A weak prestability condition with the tilting and support properties tilts
at every finite weak slope `b`.  The returned central charge is exactly
`Z/(I-b)`, and the new zero-charge subcategory is noetherian torsion. -/
noncomputable def sourceTiltConclusion
    (sigma : WeakPreStabilityCondition v) (b : ℝ)
    (htilt : sigma.TiltingProperty)
    (Zlin : V →ₗ[ℝ] ℂ) (hcompat : ∀ x : V, Zlin x = sigma.Z x)
    (hsupport : sigma.weakStabilityFunctionOnHeart.HasSupportProperty v Zlin) :
    sigma.SourceTiltConclusion b htilt Zlin := by
  let theta := slopeCutPhase b
  have htheta := slopeCutPhase_mem_Ioo b
  let N := sigma.phaseTiltNoetherianTorsionSubcategoryOfTiltingEnvelopes
    theta htheta.1.le htheta.2 htilt
  refine
    { condition :=
        sigma.sourceTiltWeakPreStabilityConditionOfTiltingProperty b htilt
      condition_eq := rfl
      support := sigma.sourceTilt_hasSupportProperty b Zlin hcompat hsupport
      zeroChargeNoetherian := ?_
      zeroCharge_tors := ?_ }
  · simpa [slopeTorsionPair, theta] using N
  · change N.pair.tors =
      (sigma.sourceTiltWeakStabilityFunction b).zeroCharge
    calc
      N.pair.tors =
          (sigma.phaseTiltWeakStabilityFunction theta htheta.1.le htheta.2).zeroCharge :=
        rfl
      _ = (sigma.sourceTiltWeakStabilityFunction b).zeroCharge := by
        funext E
        apply propext
        exact (sigma.sourceTiltWeakStabilityFunction_zeroCharge_iff b E).symm

omit [FiniteDimensional ℝ V] in
@[simp]
theorem sourceTiltConclusion_condition_Z
    (sigma : WeakPreStabilityCondition v) (b : ℝ)
    (htilt : sigma.TiltingProperty)
    (Zlin : V →ₗ[ℝ] ℂ) (hcompat : ∀ x : V, Zlin x = sigma.Z x)
    (hsupport : sigma.weakStabilityFunctionOnHeart.HasSupportProperty v Zlin) :
    (sigma.sourceTiltConclusion b htilt Zlin hcompat hsupport).condition.Z =
      sigma.sourceTiltLatticeCharge b := rfl

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Lemma 14.17 (source-normalized semistable classification).**

The semistable objects for `Z/(I-b)` are exactly the two classes constructed
in the phase-language classification.  Here the cutoff inside those classes
is definitionally the normalized phase of the paper's weak slope `b`. -/
theorem sourceTiltWeakStabilityFunction_isSemistable_iff_phaseClassification
    (sigma : WeakPreStabilityCondition v) (b : ℝ) {E : C}
    (hEtilt : ((sigma.slopeTorsionPair b).tilt).heart E)
    (hcharge : (sigma.sourceTiltWeakStabilityFunction b).charge E ≠ 0) :
    (sigma.sourceTiltWeakStabilityFunction b).IsSemistable E ↔
      sigma.IsPhaseTiltTypeOne E ∨
        sigma.IsPhaseTiltTypeTwo (slopeCutPhase b)
          (slopeCutPhase_mem_Ioo b).1.le
          (slopeCutPhase_mem_Ioo b).2 E := by
  let theta := slopeCutPhase b
  have htheta := slopeCutPhase_mem_Ioo b
  have hphaseCharge :
      (sigma.phaseTiltWeakStabilityFunction theta htheta.1.le htheta.2).charge E ≠ 0 := by
    intro hz
    apply hcharge
    rw [sigma.sourceTiltWeakStabilityFunction_charge_eq_scale_phaseTilt b E,
      hz, mul_zero]
  rw [sigma.sourceTiltWeakStabilityFunction_isSemistable_iff_phaseTilt b E]
  exact sigma.phaseTiltWeakStabilityFunction_isSemistable_iff_classification
    theta htheta.1 htheta.2
      (by simpa [slopeTorsionPair, theta] using hEtilt) hphaseCharge

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The first class of Lemma 14.17 has nonnegative original imaginary
charge. -/
theorem sourceTilt_typeOne_im_nonneg
    (sigma : WeakPreStabilityCondition v) (b : ℝ) {E : C}
    (hcharge : (sigma.sourceTiltWeakStabilityFunction b).charge E ≠ 0)
    (hE : sigma.IsPhaseTiltTypeOne E) :
    0 ≤ (sigma.Z (v (K₀.of C E))).im := by
  let W0 := sigma.weakStabilityFunctionOnHeart
  have hE0 : ¬IsZero E := fun hzero =>
    hcharge ((sigma.sourceTiltWeakStabilityFunction b).charge_isZero hzero)
  rcases W0.upper E hE.1.1 hE0 with him | ⟨him, -⟩
  · simpa [W0] using him.le
  · have him' : (sigma.Z (v (K₀.of C E))).im = 0 := by
      simpa [W0] using him
    exact him'.ge

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The extension class of Lemma 14.17 has strictly negative original
imaginary charge. -/
theorem sourceTilt_typeTwo_im_neg
    (sigma : WeakPreStabilityCondition v) (b : ℝ) {E : C}
    (hcharge : (sigma.sourceTiltWeakStabilityFunction b).charge E ≠ 0)
    (hE : sigma.IsPhaseTiltTypeTwo (slopeCutPhase b)
      (slopeCutPhase_mem_Ioo b).1.le (slopeCutPhase_mem_Ioo b).2 E) :
    (sigma.Z (v (K₀.of C E))).im < 0 := by
  let theta := slopeCutPhase b
  let Ws := sigma.sourceTiltWeakStabilityFunction b
  let W0 := sigma.weakStabilityFunctionOnHeart
  have htheta := slopeCutPhase_mem_Ioo b
  obtain ⟨U, V0, hUfree, hUss, hVzero, f, g, d, hdist, -⟩ := hE
  have hVsource : Ws.charge V0 = 0 := by
    rw [sourceTiltWeakStabilityFunction_charge, hVzero.2, zero_div]
  have hsumSource : Ws.charge E = Ws.charge (U⟦(1 : ℤ)⟧) + Ws.charge V0 :=
    Ws.charge_triangle' hdist
  have hUne : ¬IsZero U := by
    intro hzero
    apply hcharge
    rw [hsumSource, hVsource, add_zero]
    exact Ws.charge_isZero ((shiftFunctor C (1 : ℤ)).map_isZero hzero)
  have hUP : sigma.slicing.P (sigma.slicing.phiPlus C U hUne) U :=
    (sigma.weakStabilityFunctionOnHeart_isSemistable_iff U hUss.1 hUne).mp hUss
  have hphi : sigma.slicing.phiPlus C U hUne ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · have hbounds := (sigma.slicing.toTStructure_heart_iff C U).mp hUss.1
      exact lt_of_lt_of_le
        (sigma.slicing.phiMinus_gt_of_gtProp C hUne hbounds.1)
        (sigma.slicing.phiMinus_le_phiPlus C U hUne)
    · exact (sigma.slicing.phiPlus_le_of_leProp C hUne hUfree.2).trans_lt
        htheta.2
  have hUim : 0 < (sigma.Z (v (K₀.of C U))).im := by
    simpa using sigma.charge_im_pos_of_mem_P_phi_lt_one hphi U hUP hUne
  have hsumOld : W0.charge E = W0.charge (U⟦(1 : ℤ)⟧) + W0.charge V0 :=
    W0.charge_triangle' hdist
  have hEcharge : sigma.Z (v (K₀.of C E)) =
      -(sigma.Z (v (K₀.of C U))) := by
    simpa [W0, WeakStabilityFunction.charge, K₀.of_shift_one, hVzero.2] using
      hsumOld
  rw [hEcharge]
  simpa using neg_lt_zero.mpr hUim

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Lemma 14.17 (source-coordinate candidate).**  The two cases are
separated by the sign of the imaginary part of the original charge.  The
second branch retains the phase-free and positive-imaginary Hom fields used
by the constructive phase-language classification; the adversarial review
must determine whether those fields are automatic from the printed v4
hypotheses before any coverage promotion. -/
theorem sourceTiltWeakStabilityFunction_isSemistable_iff_classification
    (sigma : WeakPreStabilityCondition v) (b : ℝ) {E : C}
    (hEtilt : ((sigma.slopeTorsionPair b).tilt).heart E)
    (hcharge : (sigma.sourceTiltWeakStabilityFunction b).charge E ≠ 0) :
    (sigma.sourceTiltWeakStabilityFunction b).IsSemistable E ↔
      (0 ≤ (sigma.Z (v (K₀.of C E))).im ∧ sigma.IsPhaseTiltTypeOne E) ∨
      ((sigma.Z (v (K₀.of C E))).im < 0 ∧
        sigma.IsPhaseTiltTypeTwo (slopeCutPhase b)
          (slopeCutPhase_mem_Ioo b).1.le
          (slopeCutPhase_mem_Ioo b).2 E) := by
  rw [sigma.sourceTiltWeakStabilityFunction_isSemistable_iff_phaseClassification
    b hEtilt hcharge]
  constructor
  · rintro (hE | hE)
    · exact Or.inl ⟨sigma.sourceTilt_typeOne_im_nonneg b hcharge hE, hE⟩
    · exact Or.inr ⟨sigma.sourceTilt_typeTwo_im_neg b hcharge hE, hE⟩
  · rintro (⟨-, hE⟩ | ⟨-, hE⟩)
    · exact Or.inl hE
    · exact Or.inr hE

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The `moreover` clause of Lemma 14.17 for the exact source charge:
positive imaginary part or strict source stability kills every map from an
original zero-charge object. -/
theorem hom_eq_zero_of_zeroCharge_to_sourceTiltSemistable
    (sigma : WeakPreStabilityCondition v) (b : ℝ) {E A0 : C}
    (hE : (sigma.sourceTiltWeakStabilityFunction b).IsSemistable E)
    (hcharge : (sigma.sourceTiltWeakStabilityFunction b).charge E ≠ 0)
    (hA0 : sigma.zeroCharge A0)
    (hrefine : 0 < ((sigma.sourceTiltWeakStabilityFunction b).charge E).im ∨
      (sigma.sourceTiltWeakStabilityFunction b).IsStable E)
    (f : A0 ⟶ E) : f = 0 := by
  let theta := slopeCutPhase b
  let c := sourceTiltScale b
  have htheta := slopeCutPhase_mem_Ioo b
  have hc : 0 < c := sourceTiltScale_pos b
  have hphaseE :
      (sigma.phaseTiltWeakStabilityFunction theta htheta.1.le htheta.2).IsSemistable E :=
    (sigma.sourceTiltWeakStabilityFunction_isSemistable_iff_phaseTilt b E).mp hE
  have hphaseCharge :
      (sigma.phaseTiltWeakStabilityFunction theta htheta.1.le htheta.2).charge E ≠ 0 := by
    intro hz
    apply hcharge
    rw [sigma.sourceTiltWeakStabilityFunction_charge_eq_scale_phaseTilt b E,
      hz, mul_zero]
  have hrefine' :
      0 < ((sigma.phaseTiltWeakStabilityFunction theta htheta.1.le htheta.2).charge E).im ∨
        (sigma.phaseTiltWeakStabilityFunction theta htheta.1.le htheta.2).IsStable E := by
    rcases hrefine with him | hstable
    · left
      have hrel := sigma.sourceTiltWeakStabilityFunction_charge_eq_scale_phaseTilt b E
      rw [hrel] at him
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero] at him
      dsimp [c] at hc
      nlinarith
    · right
      exact (sigma.sourceTiltWeakStabilityFunction_isStable_iff_phaseTilt b E).mp
        hstable
  exact sigma.hom_eq_zero_of_zeroCharge_to_phaseTiltSemistable
    theta htheta.1.le htheta.2 hphaseE hphaseCharge hA0 hrefine' f

end WeakPreStabilityCondition

end

end CategoryTheory.Triangulated.WeakStabilityCondition

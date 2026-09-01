/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Semistable.SemistableTransfer

/-!
# The phase-language classification of tilted semistable objects

This file owns the two source-shaped classes of Lemma 14.17 of
arXiv:1902.08184v4, `IsPhaseTiltTypeOne` and `IsPhaseTiltTypeTwo`, proves each
gives a semistable object of the tilted heart, proves the converse from the
canonical original-cohomology sequence and strict old-HN phase separation, and
records the resulting characterisation.

This is the module a consumer of Lemma 14.17 should import.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated Complex
open CategoryTheory.Triangulated.Tilting
open scoped BigOperators ZeroObject

namespace CategoryTheory.Triangulated.WeakStabilityCondition

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

variable {Lambda : Type*} [AddCommGroup Lambda]
variable {v : K₀ C →+ Lambda}

namespace WeakPreStabilityCondition

/-- The first class in the phase-language form of Lemma 14.17: an original
heart semistable object with no maps from original zero-charge objects. -/
def IsPhaseTiltTypeOne
    (sigma : WeakPreStabilityCondition v) (E : C) : Prop :=
  sigma.weakStabilityFunctionOnHeart.IsSemistable E ∧
    ∀ A0 : C, sigma.zeroCharge A0 → ∀ f : A0 ⟶ E, f = 0

/-- The second class in the phase-language form of Lemma 14.17: an extension
of a zero-charge object by the shift of a semistable torsion-free object.
The final implication is the positive-imaginary part of the lemma's
`moreover` clause; it is exactly what excludes zero-charge subobjects away
from the boundary ray. -/
def IsPhaseTiltTypeTwo
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (E : C) : Prop :=
  ∃ (U V : C), phaseFree sigma.slicing beta U ∧
    sigma.weakStabilityFunctionOnHeart.IsSemistable U ∧
    sigma.zeroCharge V ∧
    ∃ (f : U⟦(1 : ℤ)⟧ ⟶ E) (g : E ⟶ V)
      (d : V ⟶ U⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
      Triangle.mk f g d ∈ distTriang C ∧
        (0 <
            ((sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E).im →
          ∀ V0 : C, sigma.zeroCharge V0 → ∀ a : V0 ⟶ E, a = 0)

/-- Objects of the first class are semistable for the phase-tilted weak
stability function. -/
theorem isSemistable_of_isPhaseTiltTypeOne
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E : C}
    (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E ≠ 0)
    (hE : sigma.IsPhaseTiltTypeOne E) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  have hEnz : ¬IsZero E := fun hzero =>
    hcharge ((W.charge_isZero hzero))
  have hheart := hE.1.1
  have hP :=
    (sigma.weakStabilityFunctionOnHeart_isSemistable_iff E hheart hEnz).mp hE.1
  let phi := sigma.slicing.phiPlus C E hEnz
  have hphi_eq := sigma.slicing.phiPlus_eq_phiMinus_of_semistable C hP hEnz
  have hinterval := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hEtilt
  have hphi_beta : beta < phi := by
    dsimp [phi]
    rw [← hphi_eq.2]
    exact sigma.slicing.phiMinus_gt_of_gtProp C hEnz hinterval.1
  have hphi_one : phi ≤ 1 := by
    exact sigma.slicing.phiPlus_le_of_leProp C hEnz
      ((sigma.slicing.toTStructure_heart_iff C E).mp hheart).2
  obtain ⟨m, hm, -, hmZ⟩ := sigma.compat' phi E hP hEnz
  have hZne : sigma.Z (v (K₀.of C E)) ≠ 0 := by
    intro hZ
    apply hcharge
    simp [hZ]
  have hmpos : 0 < m := by
    apply lt_of_le_of_ne hm
    intro hm0
    apply hZne
    rw [hmZ]
    simp [hm0]
  let theta := phi - beta
  have htheta : theta ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · dsimp [theta]; linarith
    · dsimp [theta]; linarith
  have hrot : W.charge E =
      (m : ℂ) *
        Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I) := by
    rw [show W.charge E = sigma.Z (v (K₀.of C E)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) from rfl, hmZ,
      mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp [theta]
    push_cast
    ring
  have hle : sigma.slicing.leProp C (beta + theta) E := by
    have : sigma.slicing.leProp C phi E :=
      sigma.slicing.leProp_of_semistable C hP le_rfl
    convert this using 1
    all_goals dsimp [theta]
    all_goals ring
  exact sigma.phaseTiltWeakStabilityFunction_isSemistable_of_ray beta hbeta0 hbeta1
    hEtilt htheta hmpos hrot hle (fun _ => hE.2)

/-- Objects of the second class are semistable for the phase-tilted weak
stability function. -/
theorem isSemistable_of_isPhaseTiltTypeTwo
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E : C}
    (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E ≠ 0)
    (hE : sigma.IsPhaseTiltTypeTwo beta hbeta0 hbeta1 E) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  obtain ⟨U, V, hUfree, hUss, hVzero, f, g, d, hdist, hHom⟩ := hE
  have hVtiltZero : W.zeroCharge V :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0 hbeta1 V).mpr
      hVzero
  have hsum : W.charge E = W.charge (U⟦(1 : ℤ)⟧) + W.charge V :=
    W.charge_triangle' hdist
  have hUshiftCharge : W.charge (U⟦(1 : ℤ)⟧) = W.charge E := by
    rw [hsum, hVtiltZero.2, add_zero]
  have hUne : ¬IsZero U := by
    intro hzero
    apply hcharge
    rw [← hUshiftCharge]
    exact W.charge_isZero ((shiftFunctor C (1 : ℤ)).map_isZero hzero)
  have hUheart := hUss.1
  have hUP :=
    (sigma.weakStabilityFunctionOnHeart_isSemistable_iff U hUheart hUne).mp hUss
  let phi := sigma.slicing.phiPlus C U hUne
  have hphi_eq := sigma.slicing.phiPlus_eq_phiMinus_of_semistable C hUP hUne
  have hphi_pos : 0 < phi := by
    dsimp [phi]
    rw [← hphi_eq.2]
    exact sigma.slicing.phiMinus_gt_of_gtProp C hUne hUfree.1
  have hphi_beta : phi ≤ beta := by
    exact sigma.slicing.phiPlus_le_of_leProp C hUne hUfree.2
  obtain ⟨m, hm, -, hmZ⟩ := sigma.compat' phi U hUP hUne
  have hZU_ne : sigma.Z (v (K₀.of C U)) ≠ 0 := by
    intro hZU
    apply hcharge
    rw [← hUshiftCharge]
    simp [W, WeakStabilityFunction.charge, K₀.of_shift_one, hZU]
  have hmpos : 0 < m := by
    apply lt_of_le_of_ne hm
    intro hm0
    apply hZU_ne
    rw [hmZ]
    simp [hm0]
  let theta := phi + 1 - beta
  have htheta : theta ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · dsimp [theta]; linarith
    · dsimp [theta]; linarith
  have hrot : W.charge E =
      (m : ℂ) *
        Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I) := by
    rw [← hUshiftCharge]
    change sigma.Z (v (CategoryTheory.Triangulated.K₀.of C (U⟦(1 : ℤ)⟧))) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) = _
    rw [CategoryTheory.Triangulated.K₀.of_shift_one C U, map_neg, map_neg, hmZ]
    rw [show -((m : ℂ) * Complex.exp (((Real.pi * phi : ℝ) : ℂ) * Complex.I)) =
        (m : ℂ) *
          Complex.exp (((Real.pi * (phi + 1) : ℝ) : ℂ) * Complex.I) by
      rw [show Real.pi * (phi + 1) = Real.pi * phi + Real.pi by ring,
        ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
      ring]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp [theta]
    push_cast
    ring
  have hUshiftLe : sigma.slicing.leProp C (phi + 1) (U⟦(1 : ℤ)⟧) := by
    simpa only [Int.cast_one] using
      sigma.slicing.leProp_shift C phi U 1
        (sigma.slicing.leProp_of_semistable C hUP le_rfl)
  have hVP := sigma.zeroCharge_mem_P_one hVzero.1 hVzero.2
  have hVle : sigma.slicing.leProp C (phi + 1) V :=
    sigma.slicing.leProp_of_semistable C hVP (by linarith)
  have hle : sigma.slicing.leProp C (beta + theta) E := by
    have := sigma.slicing.leProp_of_triangle C (phi + 1) hUshiftLe hVle hdist
    convert this using 1
    all_goals dsimp [theta]
    all_goals ring
  exact sigma.phaseTiltWeakStabilityFunction_isSemistable_of_ray beta hbeta0 hbeta1
    hEtilt htheta hmpos hrot hle hHom

/-- The reverse direction of the phase-language form of Lemma 14.17.  The
canonical original-cohomology sequence splits a tilted-semistable object
into `H⁻¹(E)[1]` and `H⁰(E)`; strict phase separation forces one of those
two terms to have zero charge. -/
theorem phaseTiltClassification_of_isSemistable
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) {E : C}
    (hE :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).IsSemistable E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).charge E ≠ 0) :
    sigma.IsPhaseTiltTypeOne E ∨
      sigma.IsPhaseTiltTypeTwo beta hbeta0.le hbeta1 E := by
  let t := sigma.slicing.toTStructure
  let P := slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le
  let W0 := sigma.weakStabilityFunctionOnHeart
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1
  let U : C := (P.originalHMinusOne hE.1).obj
  let V : C := (P.originalHZero hE.1).obj
  let T := originalCohomologyTriangle t E
  have hT : T ∈ distTriang C := originalCohomologyTriangle_distinguished t E
  have hUfree : phaseFree sigma.slicing beta U := P.originalHMinusOne_free hE.1
  have hVtors : phaseTors sigma.slicing beta V := P.originalHZero_tors hE.1
  have hUheart : sigma.slicing.toTStructure.heart U :=
    mem_heart_of_bounds sigma.slicing hUfree.1
      (sigma.slicing.leProp_mono C hbeta1.le U hUfree.2)
  have hVheart : sigma.slicing.toTStructure.heart V :=
    mem_heart_of_bounds sigma.slicing
      (sigma.slicing.gtProp_anti C hbeta0.le V hVtors.1) hVtors.2
  have hUshiftTilt : P.tilt.heart (U⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hUfree
  have hVtilt : P.tilt.heart V := P.tors_mem_tilt_heart hVtors
  by_cases hUcharge : W.charge (U⟦(1 : ℤ)⟧) = 0
  · have hUshiftZeroCharge : W.zeroCharge (U⟦(1 : ℤ)⟧) :=
      ⟨hUshiftTilt, hUcharge⟩
    have hUshiftOriginalZero :=
      (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0.le hbeta1
        (U⟦(1 : ℤ)⟧)).mp hUshiftZeroCharge
    have hUshiftGt : sigma.slicing.gtProp C 1 (U⟦(1 : ℤ)⟧) := by
      simpa only [Int.cast_one, zero_add] using
        sigma.slicing.gtProp_shift C 0 U 1 hUfree.1
    have hUshiftLe : sigma.slicing.leProp C 1 (U⟦(1 : ℤ)⟧) :=
      ((sigma.slicing.toTStructure_heart_iff C (U⟦(1 : ℤ)⟧)).mp
        hUshiftOriginalZero.1).2
    have hUshiftZero : IsZero (U⟦(1 : ℤ)⟧) := by
      rw [IsZero.iff_id_eq_zero]
      exact sigma.slicing.zero_of_gtProp_leProp_general C 1 hUshiftGt hUshiftLe (𝟙 _)
    haveI : IsIso T.mor₂ :=
      (Triangle.isZero₁_iff_isIso₂ T hT).mp (by
        simpa [T, t, U, P, originalCohomologyTriangle,
          HeartTorsionPair.originalHMinusOne] using hUshiftZero)
    let eEV : E ≅ V := by
      simpa [T, t, V, P, originalCohomologyTriangle,
        HeartTorsionPair.originalHZero] using (asIso T.mor₂)
    have hEtors : phaseTors sigma.slicing beta E := by
      exact ⟨gtProp_of_iso sigma.slicing eEV.symm hVtors.1,
        leProp_of_iso sigma.slicing eEV.symm hVtors.2⟩
    have hEold :=
      sigma.weakStabilityFunctionOnHeart_isSemistable_of_phaseTors_phaseTiltSemistable
        beta hbeta0 hbeta1 hEtors hE hcharge
    have him : 0 < (W.charge E).im := by
      have him' := phaseTiltCharge_im_pos_of_phaseTors sigma hbeta0 hEtors (by
        change phaseTiltRotation beta (W0.charge E) ≠ 0
        simpa [W, W0] using hcharge)
      simpa [W, W0] using him'
    refine Or.inl ⟨hEold, ?_⟩
    intro A0 hA0 f
    exact sigma.hom_eq_zero_of_zeroCharge_to_phaseTiltSemistable beta hbeta0.le hbeta1
      hE hcharge hA0 (Or.inl him) f
  · have hVcharge : W.charge V = 0 := by
      by_contra hVcharge
      have hU0 : ¬IsZero U := by
        intro hzero
        apply hUcharge
        exact W.charge_isZero ((shiftFunctor C (1 : ℤ)).map_isZero hzero)
      have hV0 : ¬IsZero V := fun hzero => hVcharge (W.charge_isZero hzero)
      have hVoldCharge : W0.charge V ≠ 0 := by
        intro hz
        apply hVcharge
        change phaseTiltRotation beta (W0.charge V) = 0
        rw [hz]
        exact map_zero (phaseTiltRotation beta)
      have hUplus : sigma.slicing.phiPlus C U hU0 ≤ beta :=
        sigma.slicing.phiPlus_le_of_leProp C hU0 hUfree.2
      have hVminus : beta < sigma.slicing.phiMinus C V hV0 :=
        sigma.slicing.phiMinus_gt_of_gtProp C hV0 hVtors.1
      have hWU : W.charge (U⟦(1 : ℤ)⟧) =
          phaseTiltRotation beta (-(W0.charge U)) := by
        simp [W, W0, WeakStabilityFunction.charge, phaseTiltRotation, K₀.of_shift_one]
      have hWV : W.charge V = phaseTiltRotation beta (W0.charge V) := by rfl
      have hslopeVU : W.slope V < W.slope (U⟦(1 : ℤ)⟧) :=
        phaseTilt_slope_unshifted_lt_shifted_of_phase_separated sigma W
          hUheart hVheart hUshiftTilt hVtilt hWU hWV hU0 hV0
          (hUplus.trans_lt hVminus) (hUplus.trans_lt hbeta1) hVoldCharge
      have hslopeUV : W.slope (U⟦(1 : ℤ)⟧) ≤ W.slope V := by
        simpa [T, t, U, V, P] using
          hE.2 hUshiftTilt hVtilt
            (fun hzero => hUcharge (W.charge_isZero hzero)) hV0
            T.mor₁ T.mor₂ T.mor₃ hT
      exact (not_lt_of_ge hslopeUV) hslopeVU
    have hVzeroTilt : W.zeroCharge V := ⟨hVtilt, hVcharge⟩
    have hVzero : sigma.zeroCharge V :=
      (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0.le hbeta1 V).mp
        hVzeroTilt
    have hUshiftSemistable : W.IsSemistable (U⟦(1 : ℤ)⟧) := by
      apply sigma.phaseTilt_isSemistable_left_of_zeroCharge_right beta hbeta0.le hbeta1
        hUshiftTilt hVtilt hE hVzeroTilt
      simpa [T, t, U, V, P, originalCohomologyTriangle,
        HeartTorsionPair.originalHMinusOne,
        HeartTorsionPair.originalHZero] using hT
    have hUold : W0.IsSemistable U :=
      sigma.weakStabilityFunctionOnHeart_isSemistable_of_phaseFree_shiftSemistable
        beta hbeta0.le hbeta1 hUfree hUshiftSemistable hUcharge
    refine Or.inr ⟨U, V, hUfree, hUold, hVzero, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [T, t, U, P, originalCohomologyTriangle,
        HeartTorsionPair.originalHMinusOne] using T.mor₁
    · simpa [T, t, V, P, originalCohomologyTriangle,
        HeartTorsionPair.originalHZero] using T.mor₂
    · simpa [T, t, U, V, P, originalCohomologyTriangle,
        HeartTorsionPair.originalHMinusOne,
        HeartTorsionPair.originalHZero] using T.mor₃
    · simpa [T, t, U, V, P, originalCohomologyTriangle,
        HeartTorsionPair.originalHMinusOne,
        HeartTorsionPair.originalHZero] using hT
    · intro him V0 hV0 a
      exact sigma.hom_eq_zero_of_zeroCharge_to_phaseTiltSemistable beta hbeta0.le hbeta1
        hE hcharge hV0 (Or.inl him) a

/-- The constructive direction of the phase-language classification: either
class described in Lemma 14.17 gives a semistable object in the tilted
heart. -/
theorem isSemistable_of_phaseTiltClassification
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E : C}
    (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E ≠ 0)
    (hE : sigma.IsPhaseTiltTypeOne E ∨
      sigma.IsPhaseTiltTypeTwo beta hbeta0 hbeta1 E) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E := by
  rcases hE with hE | hE
  · exact sigma.isSemistable_of_isPhaseTiltTypeOne beta hbeta0 hbeta1
      hEtilt hcharge hE
  · exact sigma.isSemistable_of_isPhaseTiltTypeTwo beta hbeta0 hbeta1
      hEtilt hcharge hE

/-- Full phase-language classification of nonzero-charge semistable objects
after tilting, combining both directions of Lemma 14.17.  The strict lower
bound on `beta` records that a finite slope cutoff corresponds to a phase
cut strictly inside `(0, 1)`. -/
theorem phaseTiltWeakStabilityFunction_isSemistable_iff_classification
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) {E : C}
    (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le).tilt).heart E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).charge E ≠ 0) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).IsSemistable E ↔
      sigma.IsPhaseTiltTypeOne E ∨
        sigma.IsPhaseTiltTypeTwo beta hbeta0.le hbeta1 E := by
  constructor
  · intro hE
    exact sigma.phaseTiltClassification_of_isSemistable beta hbeta0 hbeta1 hE hcharge
  · intro hE
    exact sigma.isSemistable_of_phaseTiltClassification beta hbeta0.le hbeta1
      hEtilt hcharge hE

end WeakPreStabilityCondition

end CategoryTheory.Triangulated.WeakStabilityCondition

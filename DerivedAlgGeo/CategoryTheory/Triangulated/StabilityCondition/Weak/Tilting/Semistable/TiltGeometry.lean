/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Property
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Heart.Equivalence

/-!
# Plane geometry of the phase tilt

This file owns the coordinate facts underlying the tilt of a weak stability
condition: clockwise rotation through `pi * beta` as an additive endomorphism,
the rotated charge, the closed weak upper half plane and its closure and
rigidity properties, the scalar cross product, and the resulting strict slope
comparisons from strict separation of old slicing phases.

`WeakUpperClosed`, `cross`, and the four lemmas exported alongside them are the
shared vocabulary of the rest of `Semistable`; the helpers used only here stay
private.
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

/-- Clockwise rotation through `pi * beta`, as an additive endomorphism of
the complex plane. -/
noncomputable def phaseTiltRotation (beta : ℝ) : ℂ →+ ℂ where
  toFun z := z * Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)
  map_zero' := by simp
  map_add' z w := by rw [add_mul]

@[simp]
theorem phaseTiltRotation_apply (beta : ℝ) (z : ℂ) :
    phaseTiltRotation beta z =
      z * Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := rfl

/-- The central charge rotated clockwise through the phase cutoff. -/
noncomputable def phaseTiltCharge
    (sigma : WeakPreStabilityCondition v) (beta : ℝ) : K₀ C →+ ℂ :=
  (phaseTiltRotation beta).comp (sigma.Z.comp v)

omit [IsTriangulated C] in
@[simp]
theorem phaseTiltCharge_apply
    (sigma : WeakPreStabilityCondition v) (beta : ℝ) (E : C) :
    sigma.phaseTiltCharge beta (K₀.of C E) =
      sigma.Z (v (K₀.of C E)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := rfl

/-- The closed weak upper half plane: nonnegative imaginary part, and on the
real axis only the nonpositive reals.  This is the region in which the charge
of an object of a tilted heart is constrained to lie. -/
def WeakUpperClosed (z : ℂ) : Prop :=
  0 ≤ z.im ∧ (z.im = 0 → z.re ≤ 0)

/-- Zero lies in the closed weak upper half plane. -/
theorem weakUpperClosed_zero : WeakUpperClosed 0 := by
  constructor <;> simp

private theorem weakUpperClosed_add {z w : ℂ}
    (hz : WeakUpperClosed z) (hw : WeakUpperClosed w) :
    WeakUpperClosed (z + w) := by
  constructor
  · simpa using add_nonneg hz.1 hw.1
  · intro him
    have hz_nonneg := hz.1
    have hw_nonneg := hw.1
    have hz0 : z.im = 0 := by
      simp only [Complex.add_im] at him
      linarith
    have hw0 : w.im = 0 := by
      simp only [Complex.add_im] at him
      linarith
    simp only [Complex.add_re]
    exact add_nonpos (hz.2 hz0) (hw.2 hw0)

/-- The closed weak upper half plane is closed under finite sums. -/
theorem weakUpperClosed_sum {I : Type*} [Fintype I] (f : I → ℂ)
    (hf : ∀ i, WeakUpperClosed (f i)) :
    WeakUpperClosed (∑ i, f i) := by
  classical
  exact Finset.sum_induction f WeakUpperClosed
    (fun _ _ => weakUpperClosed_add) weakUpperClosed_zero
    (by intro i _; exact hf i)

/-- If a finite family in the closed weak upper half plane sums to zero, every
member is zero.  This is the rigidity used to detect zero-charge factors. -/
theorem weakUpperClosed_eq_zero_of_sum_eq_zero
    {I : Type*} [Fintype I] (f : I → ℂ)
    (hf : ∀ i, WeakUpperClosed (f i)) (hsum : ∑ i, f i = 0) (i : I) :
    f i = 0 := by
  classical
  have himsum : ∑ j, (f j).im = 0 := by
    have := congrArg Complex.im hsum
    simpa using this
  have him : (f i).im = 0 :=
    congrFun ((Fintype.sum_eq_zero_iff_of_nonneg fun j => (hf j).1).mp himsum) i
  have hre_nonpos : ∀ j, (f j).re ≤ 0 := fun j =>
    (hf j).2 (congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg fun k => (hf k).1).mp himsum) j)
  have hresum : ∑ j, -(f j).re = 0 := by
    have hre := congrArg Complex.re hsum
    have : ∑ j, (f j).re = 0 := by simpa using hre
    simpa using congrArg Neg.neg this
  have hre : -(f i).re = 0 :=
    congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg fun j => neg_nonneg.mpr (hre_nonpos j)).mp
        hresum) i
  apply Complex.ext <;> simp_all

/-- A ray of nonnegative length at a phase in the tilted window lies in the
closed weak upper half plane after the clockwise rotation through `pi * beta`. -/
theorem rotatedRay_weakUpperClosed {beta phi m : ℝ}
    (hm : 0 ≤ m) (hphi : phi ∈ Set.Ioc beta (beta + 1)) :
    WeakUpperClosed
      ((m : ℂ) * Complex.exp (((Real.pi * phi : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((Real.pi : ℂ) * (beta : ℂ)) * Complex.I)) := by
  have hdelta_pos : 0 < phi - beta := by linarith [hphi.1]
  have hdelta_le : phi - beta ≤ 1 := by linarith [hphi.2]
  have hrewrite :
      (m : ℂ) * Complex.exp (((Real.pi * phi : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-((Real.pi : ℂ) * (beta : ℂ)) * Complex.I) =
        (m : ℂ) *
          Complex.exp (((Real.pi * (phi - beta) : ℝ) : ℂ) * Complex.I) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hrewrite, Complex.exp_ofReal_mul_I]
  unfold WeakUpperClosed
  simp only [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im,
    Complex.I_im, Complex.I_re, zero_mul, mul_zero, mul_one, add_zero,
    zero_add, Complex.mul_re, sub_zero]
  change
    0 ≤ m * Real.sin (Real.pi * (phi - beta)) ∧
      (m * Real.sin (Real.pi * (phi - beta)) = 0 →
        m * Real.cos (Real.pi * (phi - beta)) ≤ 0)
  constructor
  · exact mul_nonneg hm
      (Real.sin_nonneg_of_nonneg_of_le_pi
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))
  · intro him
    rcases mul_eq_zero.mp him with hm0 | hsin0
    · simp [hm0]
    have hdelta : phi - beta = 1 := by
      by_contra hne
      have hdelta_lt : phi - beta < 1 := lt_of_le_of_ne hdelta_le hne
      have hsin_pos : 0 < Real.sin (Real.pi * (phi - beta)) :=
        Real.sin_pos_of_pos_of_lt_pi
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      exact (ne_of_gt hsin_pos) hsin0
    rw [hdelta]
    simpa using neg_nonpos.mpr hm

/-- The scalar cross product of two complex numbers, read as plane vectors.
Its sign compares the arguments of `z` and `w`. -/
def cross (z w : ℂ) : ℝ :=
  z.re * w.im - z.im * w.re

private theorem cross_phaseTiltRotation (beta : ℝ) (z w : ℂ) :
    cross (phaseTiltRotation beta z) (phaseTiltRotation beta w) = cross z w := by
  rw [phaseTiltRotation_apply, phaseTiltRotation_apply]
  let c := Real.cos (Real.pi * beta)
  let s := Real.sin (Real.pi * beta)
  have hexp :
      Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) = (c : ℂ) - (s : ℂ) * Complex.I := by
    rw [show -(Real.pi * beta : ℂ) * Complex.I =
        ((-(Real.pi * beta) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I]
    simp [c, s]
    ring
  rw [hexp]
  unfold cross
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, zero_sub]
  have htrig : c ^ 2 + s ^ 2 = 1 := by
    dsimp [c, s]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * beta)]
  rw [show
      (z.re * c - z.im * -(s + 0)) * (w.re * -(s + 0) + w.im * c) -
          (z.re * -(s + 0) + z.im * c) * (w.re * c - w.im * -(s + 0)) =
        (c ^ 2 + s ^ 2) * (z.re * w.im - z.im * w.re) by ring,
    htrig, one_mul]

private theorem cross_phaseTiltRotation_neg_left (beta : ℝ) (z w : ℂ) :
    cross (phaseTiltRotation beta (-z)) (phaseTiltRotation beta w) = -cross z w := by
  rw [cross_phaseTiltRotation]
  simp [cross]
  ring

private theorem cross_phaseTiltRotation_neg_right (beta : ℝ) (z w : ℂ) :
    cross (phaseTiltRotation beta z) (phaseTiltRotation beta (-w)) = -cross z w := by
  rw [cross_phaseTiltRotation]
  simp [cross]
  ring

omit [IsTriangulated C] in
/-- A positive oriented area between two nonzero weak upper-half-plane
charges is the strict slope inequality. -/
private theorem slope_lt_of_cross_pos {t : TStructure C}
    (W : WeakStabilityFunction t) {A B : C}
    (hA : t.heart A) (hB : t.heart B) (hA0 : ¬IsZero A) (hB0 : ¬IsZero B)
    (hcross : 0 < cross (W.charge A) (W.charge B)) :
    W.slope A < W.slope B := by
  have hAim : 0 < (W.charge A).im := by
    rcases W.upper A hA hA0 with him | ⟨him, hre⟩
    · exact him
    · have hBim : 0 ≤ (W.charge B).im := by
        rcases W.upper B hB hB0 with himB | ⟨himB, -⟩
        · exact himB.le
        · exact himB.ge
      unfold cross at hcross
      rw [him] at hcross
      simp only [zero_mul, sub_zero] at hcross
      nlinarith
  by_cases hBim : 0 < (W.charge B).im
  · rw [W.slope_of_im_pos hAim, W.slope_of_im_pos hBim]
    exact_mod_cast (div_lt_div_iff₀ hAim hBim).2 (by
      unfold cross at hcross
      nlinarith)
  · rw [W.slope_of_im_pos hAim, W.slope_of_im_nonpos hBim]
    exact WithTop.coe_lt_top _

/-- The lower HN phase bounds the argument of every nonzero total charge in
the original heart.  This extends the positive-imaginary lemma to the
negative-real boundary ray. -/
private theorem pi_mul_phiMinus_le_charge_arg_of_charge_ne_zero
    (sigma : WeakPreStabilityCondition v) (E : C)
    (hheart : sigma.slicing.toTStructure.heart E)
    (hcharge : sigma.weakStabilityFunctionOnHeart.charge E ≠ 0) :
    Real.pi * sigma.slicing.phiMinus C E
        (fun hE => hcharge (sigma.weakStabilityFunctionOnHeart.charge_isZero hE)) ≤
      Complex.arg (sigma.weakStabilityFunctionOnHeart.charge E) := by
  let W := sigma.weakStabilityFunctionOnHeart
  have hE : ¬IsZero E := fun hE => hcharge (W.charge_isZero hE)
  by_cases him : 0 < (W.charge E).im
  · exact sigma.pi_mul_phiMinus_le_charge_arg_of_im_pos E hheart hE him
  · have him0 : (W.charge E).im = 0 := by
      rcases W.upper E hheart hE with him' | ⟨him', -⟩
      · exact absurd him' him
      · exact him'
    have hrele : (W.charge E).re ≤ 0 := by
      rcases W.upper E hheart hE with him' | ⟨-, hre⟩
      · exact absurd him' him
      · exact hre
    have hrelt : (W.charge E).re < 0 := lt_of_le_of_ne hrele fun hre0 => by
      apply hcharge
      exact Complex.ext hre0 him0
    have harg : Complex.arg (W.charge E) = Real.pi := by
      rw [show W.charge E = ((W.charge E).re : ℂ) from Complex.ext rfl him0,
        Complex.arg_ofReal_of_neg hrelt]
    rw [harg]
    have hle : sigma.slicing.phiMinus C E hE ≤ 1 :=
      (sigma.slicing.phiMinus_le_phiPlus C E hE).trans
        (sigma.slicing.phiPlus_le_of_leProp C hE
          ((sigma.slicing.toTStructure_heart_iff C E).mp hheart).2)
    nlinarith [Real.pi_pos]

/-- A nonzero charged torsion-class object lies in the open upper half-plane
after a nontrivial phase rotation. -/
theorem phaseTiltCharge_im_pos_of_phaseTors
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    (hbeta0 : 0 < beta) {E : C}
    (hE : phaseTors sigma.slicing beta E)
    (hcharge :
      phaseTiltRotation beta
        (sigma.weakStabilityFunctionOnHeart.charge E) ≠ 0) :
    0 < (phaseTiltRotation beta
      (sigma.weakStabilityFunctionOnHeart.charge E)).im := by
  let W0 := sigma.weakStabilityFunctionOnHeart
  have hheart : sigma.slicing.toTStructure.heart E :=
    mem_heart_of_bounds sigma.slicing
      (sigma.slicing.gtProp_anti C hbeta0.le E hE.1) hE.2
  have hZ0 : W0.charge E ≠ 0 := by
    intro hz
    apply hcharge
    rw [show W0.charge E = 0 from hz]
    exact map_zero (phaseTiltRotation beta)
  have hE0 : ¬IsZero E := fun hzero => hZ0 (W0.charge_isZero hzero)
  have hlower :=
    pi_mul_phiMinus_le_charge_arg_of_charge_ne_zero sigma E hheart hZ0
  have hphase : beta < sigma.slicing.phiMinus C E hE0 :=
    sigma.slicing.phiMinus_gt_of_gtProp C hE0 hE.1
  have harg_lower : Real.pi * beta < Complex.arg (W0.charge E) := by
    nlinarith [Real.pi_pos]
  have hangle_pos : 0 < Complex.arg (W0.charge E) - Real.pi * beta := by
    linarith
  have hangle_lt : Complex.arg (W0.charge E) - Real.pi * beta < Real.pi := by
    nlinarith [Complex.arg_le_pi (W0.charge E), Real.pi_pos]
  have him : (phaseTiltRotation beta (W0.charge E)).im =
      ‖W0.charge E‖ * Real.sin (Complex.arg (W0.charge E) - Real.pi * beta) := by
    change (W0.charge E *
      Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)).im = _
    have polar := Complex.norm_mul_exp_arg_mul_I (W0.charge E)
    conv_lhs => rw [← polar]
    rw [mul_assoc, ← Complex.exp_add]
    have hexp :
        (Complex.arg (W0.charge E) : ℂ) * Complex.I +
            -(Real.pi * beta : ℂ) * Complex.I =
          ((Complex.arg (W0.charge E) - Real.pi * beta : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.exp_ofReal_mul_I_im]
  rw [him]
  exact mul_pos (norm_pos_iff.mpr hZ0)
    (Real.sin_pos_of_pos_of_lt_pi hangle_pos hangle_lt)

/-- Strict phase separation below phase `1` gives strict slope separation
after rotation. -/
theorem phaseTilt_slope_lt_of_phase_separated
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    {tTilt : TStructure C} (W : WeakStabilityFunction tTilt) {A B : C}
    (hAheart : sigma.slicing.toTStructure.heart A)
    (hBheart : sigma.slicing.toTStructure.heart B)
    (hAtilt : tTilt.heart A) (hBtilt : tTilt.heart B)
    (hWA : W.charge A = phaseTiltRotation beta
      (sigma.weakStabilityFunctionOnHeart.charge A))
    (hWB : W.charge B = phaseTiltRotation beta
      (sigma.weakStabilityFunctionOnHeart.charge B))
    (hA0 : ¬IsZero A) (hB0 : ¬IsZero B)
    (hsep : sigma.slicing.phiPlus C A hA0 < sigma.slicing.phiMinus C B hB0)
    (hAplus : sigma.slicing.phiPlus C A hA0 < 1)
    (hBcharge : sigma.weakStabilityFunctionOnHeart.charge B ≠ 0) :
    W.slope A < W.slope B := by
  let W0 := sigma.weakStabilityFunctionOnHeart
  obtain ⟨hAupper, hAarg⟩ :=
    sigma.charge_mem_upperHalfPlane_and_arg_le_phiPlus A hAheart hA0 hAplus
  have hBarg :=
    pi_mul_phiMinus_le_charge_arg_of_charge_ne_zero sigma B hBheart hBcharge
  have harglt : Complex.arg (W0.charge A) < Complex.arg (W0.charge B) := by
    calc
      Complex.arg (W0.charge A) ≤
          Real.pi * sigma.slicing.phiPlus C A hA0 := hAarg
      _ < Real.pi * sigma.slicing.phiMinus C B hB0 :=
        mul_lt_mul_of_pos_left hsep Real.pi_pos
      _ ≤ Complex.arg (W0.charge B) := hBarg
  have hAcrossB : 0 < cross (W0.charge A) (W0.charge B) :=
    cross_pos_of_arg_lt (arg_pos_of_mem_semiClosedUpperHalfPlane hAupper)
      (semiClosedUpperHalfPlane_ne_zero hAupper) hBcharge harglt
  have hcross : 0 < cross (W.charge A) (W.charge B) := by
    rw [hWA, hWB]
    rw [cross_phaseTiltRotation]
    exact hAcrossB
  exact slope_lt_of_cross_pos W hAtilt hBtilt hA0 hB0 hcross

/-- The shifted version of strict phase/slope separation.  This public form
is used by the `H⁻¹` quotient induction for the weak upper tilt. -/
theorem phaseTilt_slope_shift_lt_shift_of_phase_separated
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    {tTilt : TStructure C} (W : WeakStabilityFunction tTilt) {A B : C}
    (hAheart : sigma.slicing.toTStructure.heart A)
    (hBheart : sigma.slicing.toTStructure.heart B)
    (hAtilt : tTilt.heart (A⟦(1 : ℤ)⟧))
    (hBtilt : tTilt.heart (B⟦(1 : ℤ)⟧))
    (hWA : W.charge (A⟦(1 : ℤ)⟧) = phaseTiltRotation beta
      (-(sigma.weakStabilityFunctionOnHeart.charge A)))
    (hWB : W.charge (B⟦(1 : ℤ)⟧) = phaseTiltRotation beta
      (-(sigma.weakStabilityFunctionOnHeart.charge B)))
    (hA0 : ¬IsZero A) (hB0 : ¬IsZero B)
    (hsep : sigma.slicing.phiPlus C A hA0 < sigma.slicing.phiMinus C B hB0)
    (hAplus : sigma.slicing.phiPlus C A hA0 < 1)
    (hBcharge : sigma.weakStabilityFunctionOnHeart.charge B ≠ 0) :
    W.slope (A⟦(1 : ℤ)⟧) < W.slope (B⟦(1 : ℤ)⟧) := by
  let W0 := sigma.weakStabilityFunctionOnHeart
  obtain ⟨hAupper, hAarg⟩ :=
    sigma.charge_mem_upperHalfPlane_and_arg_le_phiPlus A hAheart hA0 hAplus
  have hBarg :=
    pi_mul_phiMinus_le_charge_arg_of_charge_ne_zero sigma B hBheart hBcharge
  have harglt : Complex.arg (W0.charge A) < Complex.arg (W0.charge B) := by
    calc
      Complex.arg (W0.charge A) ≤
          Real.pi * sigma.slicing.phiPlus C A hA0 := hAarg
      _ < Real.pi * sigma.slicing.phiMinus C B hB0 :=
        mul_lt_mul_of_pos_left hsep Real.pi_pos
      _ ≤ Complex.arg (W0.charge B) := hBarg
  have hAcrossB : 0 < cross (W0.charge A) (W0.charge B) :=
    cross_pos_of_arg_lt (arg_pos_of_mem_semiClosedUpperHalfPlane hAupper)
      (semiClosedUpperHalfPlane_ne_zero hAupper) hBcharge harglt
  have hcross : 0 < cross (W.charge (A⟦(1 : ℤ)⟧)) (W.charge (B⟦(1 : ℤ)⟧)) := by
    rw [hWA, hWB]
    rw [cross_phaseTiltRotation]
    simpa [cross, W0, WeakStabilityFunction.charge] using hAcrossB
  have hAshift0 : ¬IsZero (A⟦(1 : ℤ)⟧) := fun hzero =>
    hA0 (by
      rw [IsZero.iff_id_eq_zero] at hzero ⊢
      exact (Functor.map_eq_zero_iff (shiftFunctor C (1 : ℤ))).mp (by simpa using hzero))
  have hBshift0 : ¬IsZero (B⟦(1 : ℤ)⟧) := fun hzero =>
    hB0 (by
      rw [IsZero.iff_id_eq_zero] at hzero ⊢
      exact (Functor.map_eq_zero_iff (shiftFunctor C (1 : ℤ))).mp (by simpa using hzero))
  exact slope_lt_of_cross_pos W hAtilt hBtilt hAshift0 hBshift0 hcross

/-- A higher-phase unshifted factor has smaller tilted slope than the shift
of a lower-phase factor. -/
theorem phaseTilt_slope_unshifted_lt_shifted_of_phase_separated
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    {tTilt : TStructure C} (W : WeakStabilityFunction tTilt) {U V : C}
    (hUheart : sigma.slicing.toTStructure.heart U)
    (hVheart : sigma.slicing.toTStructure.heart V)
    (hUshiftTilt : tTilt.heart (U⟦(1 : ℤ)⟧))
    (hVtilt : tTilt.heart V)
    (hWU : W.charge (U⟦(1 : ℤ)⟧) = phaseTiltRotation beta
      (-(sigma.weakStabilityFunctionOnHeart.charge U)))
    (hWV : W.charge V = phaseTiltRotation beta
      (sigma.weakStabilityFunctionOnHeart.charge V))
    (hU0 : ¬IsZero U) (hV0 : ¬IsZero V)
    (hsep : sigma.slicing.phiPlus C U hU0 < sigma.slicing.phiMinus C V hV0)
    (hUplus : sigma.slicing.phiPlus C U hU0 < 1)
    (hVcharge : sigma.weakStabilityFunctionOnHeart.charge V ≠ 0) :
    W.slope V < W.slope (U⟦(1 : ℤ)⟧) := by
  let W0 := sigma.weakStabilityFunctionOnHeart
  obtain ⟨hUupper, hUarg⟩ :=
    sigma.charge_mem_upperHalfPlane_and_arg_le_phiPlus U hUheart hU0 hUplus
  have hVarg :=
    pi_mul_phiMinus_le_charge_arg_of_charge_ne_zero sigma V hVheart hVcharge
  have harglt : Complex.arg (W0.charge U) < Complex.arg (W0.charge V) := by
    calc
      Complex.arg (W0.charge U) ≤
          Real.pi * sigma.slicing.phiPlus C U hU0 := hUarg
      _ < Real.pi * sigma.slicing.phiMinus C V hV0 :=
        mul_lt_mul_of_pos_left hsep Real.pi_pos
      _ ≤ Complex.arg (W0.charge V) := hVarg
  have hUcrossV : 0 < cross (W0.charge U) (W0.charge V) :=
    cross_pos_of_arg_lt (arg_pos_of_mem_semiClosedUpperHalfPlane hUupper)
      (semiClosedUpperHalfPlane_ne_zero hUupper) hVcharge harglt
  have hcross : 0 < cross (W.charge V) (W.charge (U⟦(1 : ℤ)⟧)) := by
    rw [hWV, hWU]
    rw [cross_phaseTiltRotation_neg_right]
    unfold cross at hUcrossV ⊢
    linarith
  have hUshift0 : ¬IsZero (U⟦(1 : ℤ)⟧) := fun hzero =>
    hU0 (by
      rw [IsZero.iff_id_eq_zero] at hzero ⊢
      exact (Functor.map_eq_zero_iff (shiftFunctor C (1 : ℤ))).mp (by simpa using hzero))
  exact slope_lt_of_cross_pos W hVtilt hUshiftTilt hV0 hUshift0 hcross

end WeakPreStabilityCondition

end CategoryTheory.Triangulated.WeakStabilityCondition

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Semistable.TiltGeometry
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Cohomology.Basic

/-!
# The tilted heart and its weak stability function

This file owns the sign facts for the rotated charge of an object whose old
slicing phases lie in the tilted window, the identification of the HRS-tilted
heart by that phase interval, its agreement with the phase-shifted heart, and
the construction of the weak stability function the tilted heart carries.  Its
charge is the original charge rotated clockwise through `pi * beta`.
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

private theorem ray_cross_nonneg {psi theta m n : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hpsi : 0 < psi)
    (horder : psi ≤ theta) (htheta : theta ≤ 1) :
    0 ≤ cross
      ((m : ℂ) * Complex.exp (((Real.pi * psi : ℝ) : ℂ) * Complex.I))
      ((n : ℂ) * Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I)) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  unfold cross
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, mul_one, add_zero, zero_add]
  rw [show
      m * Real.cos (Real.pi * psi) * (n * Real.sin (Real.pi * theta)) -
          m * Real.sin (Real.pi * psi) * (n * Real.cos (Real.pi * theta)) =
        (m * n) * Real.sin (Real.pi * (theta - psi)) by
      rw [show Real.pi * (theta - psi) = Real.pi * theta - Real.pi * psi by ring,
        Real.sin_sub]
      ring]
  exact mul_nonneg (mul_nonneg hm hn)
    (Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))

omit [IsTriangulated C] in
private theorem rotatedCharge_weakUpperClosed_of_interval
    (sigma : WeakPreStabilityCondition v) {beta : ℝ} {E : C}
    (hgt : sigma.slicing.gtProp C beta E)
    (hle : sigma.slicing.leProp C (beta + 1) E) :
    WeakUpperClosed
      (sigma.Z (v (CategoryTheory.Triangulated.K₀.of C E)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)) := by
  classical
  by_cases hE : IsZero E
  · simpa [CategoryTheory.Triangulated.K₀.of_isZero C hE] using weakUpperClosed_zero
  obtain ⟨F, hn, hfirst, hlast⟩ :=
    sigma.slicing.exists_hn_nonzero_boundaries C hE
  let P := F.toPostnikovTower
  have hphase : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc beta (beta + 1) := by
    intro i
    constructor
    · calc
        beta < sigma.slicing.phiMinus C E hE :=
          sigma.slicing.phiMinus_gt_of_gtProp C hE hgt
        _ = F.φ ⟨F.n - 1, by lia⟩ := by
          simpa [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
            sigma.slicing.phiMinus_eq C E hE F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ :=
          F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = sigma.slicing.phiPlus C E hE := by
          simpa [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
            (sigma.slicing.phiPlus_eq C E hE F hn hfirst).symm
        _ ≤ beta + 1 := sigma.slicing.phiPlus_le_of_leProp C hE hle
  have hsum :
      sigma.Z (v (CategoryTheory.Triangulated.K₀.of C E)) *
          Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) =
        ∑ i : Fin F.n,
          sigma.Z (v (CategoryTheory.Triangulated.K₀.of C (P.factor i))) *
            Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := by
    rw [CategoryTheory.Triangulated.K₀.of_postnikovTower_eq_sum C P,
      map_sum, map_sum, Finset.sum_mul]
  rw [hsum]
  apply weakUpperClosed_sum
  intro i
  by_cases hi : IsZero (P.factor i)
  · simpa [CategoryTheory.Triangulated.K₀.of_isZero C hi] using weakUpperClosed_zero
  obtain ⟨m, hm, -, hmZ⟩ :=
    sigma.compat' (F.φ i) (P.factor i) (F.semistable i) hi
  rw [hmZ]
  exact rotatedRay_weakUpperClosed hm (hphase i)

omit [IsTriangulated C] in
/-- For an object whose old slicing phases lie in the tilted window, the cross
product of its rotated charge against a fixed ray is nonnegative. -/
theorem rotatedCharge_cross_ray_nonneg_of_bounds
    (sigma : WeakPreStabilityCondition v) {beta theta n : ℝ} {A : C}
    (hn : 0 ≤ n) (htheta : theta ≤ 1)
    (hgt : sigma.slicing.gtProp C beta A)
    (hle : sigma.slicing.leProp C (beta + theta) A) :
    0 ≤ cross
      (sigma.Z (v (CategoryTheory.Triangulated.K₀.of C A)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I))
      ((n : ℂ) *
        Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I)) := by
  classical
  by_cases hA : IsZero A
  · simp [CategoryTheory.Triangulated.K₀.of_isZero C hA, cross]
  obtain ⟨F, hFn, hfirst, hlast⟩ :=
    sigma.slicing.exists_hn_nonzero_boundaries C hA
  let P := F.toPostnikovTower
  let z : ℂ := (n : ℂ) *
    Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I)
  let f : Fin F.n → ℂ := fun i =>
    sigma.Z (v (CategoryTheory.Triangulated.K₀.of C (P.factor i))) *
      Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)
  have hphase : ∀ i : Fin F.n,
      0 < F.φ i - beta ∧ F.φ i - beta ≤ theta := by
    intro i
    constructor
    · calc
        0 < sigma.slicing.phiMinus C A hA - beta := by
          linarith [sigma.slicing.phiMinus_gt_of_gtProp C hA hgt]
        _ = F.φ ⟨F.n - 1, by lia⟩ - beta := by
          simpa [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
            congrArg (fun x : ℝ => x - beta)
              (sigma.slicing.phiMinus_eq C A hA F hFn hlast)
        _ ≤ F.φ i - beta := by
          have hi : i ≤ (⟨F.n - 1, by lia⟩ : Fin F.n) :=
            Fin.mk_le_mk.mpr (by lia)
          linarith [F.hφ.antitone hi]
    · calc
        F.φ i - beta ≤ F.φ ⟨0, hFn⟩ - beta := by
          have hi : (⟨0, hFn⟩ : Fin F.n) ≤ i :=
            Fin.mk_le_mk.mpr (Nat.zero_le _)
          linarith [F.hφ.antitone hi]
        _ = sigma.slicing.phiPlus C A hA - beta := by
          simpa [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
            congrArg (fun x : ℝ => x - beta)
              (sigma.slicing.phiPlus_eq C A hA F hFn hfirst).symm
        _ ≤ theta := by
          linarith [sigma.slicing.phiPlus_le_of_leProp C hA hle]
  have hsum :
      sigma.Z (v (CategoryTheory.Triangulated.K₀.of C A)) *
          Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) =
        ∑ i, f i := by
    rw [CategoryTheory.Triangulated.K₀.of_postnikovTower_eq_sum C P,
      map_sum, map_sum, Finset.sum_mul]
  rw [hsum]
  change 0 ≤ cross (∑ i, f i) z
  rw [show cross (∑ i, f i) z = ∑ i, cross (f i) z by
    simp [cross, Finset.sum_mul, ← Finset.sum_sub_distrib]]
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : IsZero (P.factor i)
  · simp [f, CategoryTheory.Triangulated.K₀.of_isZero C hi, cross]
  obtain ⟨m, hm, -, hmZ⟩ :=
    sigma.compat' (F.φ i) (P.factor i) (F.semistable i) hi
  have hrot : f i =
      (m : ℂ) *
        Complex.exp (((Real.pi * (F.φ i - beta) : ℝ) : ℂ) * Complex.I) := by
    dsimp [f]
    rw [hmZ, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hrot]
  exact ray_cross_nonneg hm hn (hphase i).1 (hphase i).2 htheta

/-- A tilted-heart object has all old slicing phases in `(beta, beta + 1]`.
This is the sector form of the HRS heart description. -/
theorem phaseTiltHeart_interval
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E : C}
    (hE : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E) :
    sigma.slicing.gtProp C beta E ∧
      sigma.slicing.leProp C (beta + 1) E := by
  obtain ⟨F, T, hF, hT, f, g, d, hdist⟩ :=
    (slicingTilt_heart_iff sigma.slicing hbeta0 hbeta1.le E).mp hE
  have hFgt : sigma.slicing.gtProp C beta (F⟦(1 : ℤ)⟧) := by
    have hshift := sigma.slicing.gtProp_shift C 0 F 1 hF.1
    have hshift' : sigma.slicing.gtProp C 1 (F⟦(1 : ℤ)⟧) := by
      simpa using hshift
    exact sigma.slicing.gtProp_anti C hbeta1.le _ hshift'
  have hFle : sigma.slicing.leProp C (beta + 1) (F⟦(1 : ℤ)⟧) := by
    simpa only [Int.cast_one] using
      sigma.slicing.leProp_shift C beta F 1 hF.2
  have hTgt : sigma.slicing.gtProp C beta T := hT.1
  have hTle : sigma.slicing.leProp C (beta + 1) T :=
    sigma.slicing.leProp_mono C (by linarith) T hT.2
  exact ⟨sigma.slicing.gtProp_of_triangle C beta hFgt hTgt hdist,
    sigma.slicing.leProp_of_triangle C (beta + 1) hFle hTle hdist⟩

/-- The HRS tilt at the phase cut is exactly the heart of the phase-shifted
slicing.  This identifies both descriptions with the interval
`P((beta, beta + 1])`. -/
theorem phaseTiltHeart_iff_phaseShiftHeart
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (E : C) :
    ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E ↔
      ((sigma.slicing.phaseShift C beta).toTStructure).heart E := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  constructor
  · intro hE
    obtain ⟨hgt, hle⟩ := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hE
    rw [(sigma.slicing.phaseShift C beta).toTStructure_heart_iff]
    exact ⟨(sigma.slicing.phaseShift_gtProp_zero C beta E).mpr hgt,
      (sigma.slicing.phaseShift_leProp C beta 1 E).mpr (by simpa [add_comm] using hle)⟩
  · intro hE
    have hbounds :=
      (sigma.slicing.phaseShift C beta).toTStructure_heart_iff C E |>.mp hE
    have hgt : sigma.slicing.gtProp C beta E :=
      (sigma.slicing.phaseShift_gtProp_zero C beta E).mp hbounds.1
    have hle : sigma.slicing.leProp C (beta + 1) E :=
      (sigma.slicing.phaseShift_leProp C beta 1 E).mp hbounds.2 |>
        (by simpa [add_comm] using ·)
    by_cases hzero : IsZero E
    · exact ObjectProperty.prop_of_iso (P.tilt).heart hzero.isoZero.symm
        (P.tors_mem_tilt_heart P.tors_zero)
    obtain ⟨F, hn, hfirst, hlast⟩ :=
      sigma.slicing.exists_hn_nonzero_boundaries C hzero
    have hphase : ∀ i : Fin F.n,
        beta < F.φ i ∧ F.φ i < beta + 2 := by
      intro i
      constructor
      · calc
          beta < sigma.slicing.phiMinus C E hzero :=
            sigma.slicing.phiMinus_gt_of_gtProp C hzero hgt
          _ = F.φ ⟨F.n - 1, by lia⟩ := by
            simpa [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
              sigma.slicing.phiMinus_eq C E hzero F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc
          F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = sigma.slicing.phiPlus C E hzero := by
            simpa [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
              (sigma.slicing.phiPlus_eq C E hzero F hn hfirst).symm
          _ ≤ beta + 1 := sigma.slicing.phiPlus_le_of_leProp C hzero hle
          _ < beta + 2 := by linarith
    obtain ⟨X, Y, f, g, d, hdist, hXgt, hYle, -⟩ :=
      sigma.slicing.exists_split_at_cutoff_with_upper_bound C F hphase hn (t := 1)
    have hXle : sigma.slicing.leProp C (beta + 1) X := by
      have hYshift : sigma.slicing.leProp C (beta + 1) (Y⟦(-1 : ℤ)⟧) := by
        have hshift := sigma.slicing.leProp_shift C 1 Y (-1) hYle
        exact sigma.slicing.leProp_mono C (by push_cast; linarith) _ hshift
      exact sigma.slicing.leProp_of_triangle C (beta + 1) hYshift hle
        (inv_rot_of_distTriang _ hdist)
    have hYgt : sigma.slicing.gtProp C beta Y := by
      have hXshift : sigma.slicing.gtProp C beta (X⟦(1 : ℤ)⟧) := by
        have hshift := sigma.slicing.gtProp_shift C 1 X 1 hXgt
        exact sigma.slicing.gtProp_anti C (by push_cast; linarith) _ hshift
      exact sigma.slicing.gtProp_of_triangle C beta hgt hXshift
        (rot_of_distTriang _ hdist)
    have hfree : phaseFree sigma.slicing beta (X⟦(-1 : ℤ)⟧) := by
      constructor
      · have hshift := sigma.slicing.gtProp_shift C 1 X (-1) hXgt
        convert hshift using 1
        all_goals push_cast
        all_goals ring
      · have hshift := sigma.slicing.leProp_shift C (beta + 1) X (-1) hXle
        convert hshift using 1
        all_goals push_cast
        all_goals ring
    have htors : phaseTors sigma.slicing beta Y := ⟨hYgt, hYle⟩
    let e : (X⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ X :=
      (shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by lia)).app X
    have hdist' :
        Triangle.mk (e.hom ≫ f) g (d ≫ e.inv⟦(1 : ℤ)⟧') ∈ distTriang C := by
      refine isomorphic_distinguished _ hdist _ ?_
      exact Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp [← Functor.map_comp])
    exact P.tilt_heart_of_triangle hfree htors hdist'

/-- The phase-language tilted weak stability function.  Its heart is the HRS
tilt at the cutoff `beta`, and its charge is the original charge rotated
clockwise through `pi * beta`. -/
noncomputable def phaseTiltWeakStabilityFunction
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    WeakStabilityFunction
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt where
  Z := sigma.phaseTiltCharge beta
  nonzero_mem E hrel := by
    obtain ⟨hE, _⟩ := hrel
    show 0 < ((sigma.phaseTiltCharge beta) (K₀.of C E)).im ∨
      (((sigma.phaseTiltCharge beta) (K₀.of C E)).im = 0 ∧
        ((sigma.phaseTiltCharge beta) (K₀.of C E)).re ≤ 0)
    obtain ⟨hgt, hle⟩ := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hE
    have hclosed :=
      rotatedCharge_weakUpperClosed_of_interval sigma hgt hle
    rcases lt_or_eq_of_le hclosed.1 with him | him
    · exact Or.inl him
    · exact Or.inr ⟨him.symm, hclosed.2 him.symm⟩

@[simp]
theorem phaseTiltWeakStabilityFunction_Z
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).Z =
      sigma.phaseTiltCharge beta := rfl

@[simp]
theorem phaseTiltWeakStabilityFunction_charge
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (E : C) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E =
      sigma.Z (v (K₀.of C E)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := rfl

end WeakPreStabilityCondition

end CategoryTheory.Triangulated.WeakStabilityCondition

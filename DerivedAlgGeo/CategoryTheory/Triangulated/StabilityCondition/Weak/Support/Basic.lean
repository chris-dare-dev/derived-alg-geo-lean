/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Support.Predicate.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Semistable

/-!
# Support property for weak stability and transport across a phase tilt

This file binds the generic linear-algebraic support predicate from
`WeakStabilityCondition/Support/Predicate/Basic.lean` to the numerical classes of nonzero weak
semistable heart objects.  It then proves the support-property transport used
in Proposition 14.16.

The proof follows Remark 14.9 and Lemma 14.17.  An original zero-charge object
is weak semistable, so the original support property forces its numerical
class to vanish.  The tilted classification then says that a nonzero-charge
tilted semistable class is either an original semistable class or the negative
of one, up to such a zero class.  Finally, multiplication of the charge by
`exp (-pi * beta * I)` preserves its norm.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.Support

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {v : K₀ C →+ V}

namespace WeakStabilityFunction

/-- Numerical classes of nonzero weak-semistable objects in the heart. -/
def semistableClasses {t : TStructure C} (W : WeakStabilityFunction t)
    (v : K₀ C →+ V) : Set V :=
  {x | ∃ E : C, W.IsSemistable E ∧ ¬IsZero E ∧ x = v (K₀.of C E)}

/-- The support property for a weak stability function, relative to a real
linear realization of its charge. -/
def HasSupportProperty {t : TStructure C} (W : WeakStabilityFunction t)
    (v : K₀ C →+ V) (Zlin : V →ₗ[ℝ] ℂ) : Prop :=
  CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasSupportProperty Zlin
    (W.semistableClasses v)

omit [IsTriangulated C] in
/-- A zero-charge object is weak semistable. -/
theorem isSemistable_of_zeroCharge {t : TStructure C}
    (W : WeakStabilityFunction t) {E : C} (hE : W.zeroCharge E) :
    W.IsSemistable E := by
  refine ⟨hE.1, ?_⟩
  intro A B hA hB hA0 hB0 f g d hdist
  have hAzero := W.zeroCharge_left hA hB hE hdist
  have hBzero := W.zeroCharge_right hA hB hE hdist
  rw [W.slope_of_im_nonpos (by simp [hAzero.2]),
    W.slope_of_im_nonpos (by simp [hBzero.2])]

omit [IsTriangulated C] [FiniteDimensional ℝ V] in
/-- Under the support property, every zero-charge heart object has zero
numerical class.  This is the weak-stability form of Remark 14.9. -/
theorem class_eq_zero_of_zeroCharge {t : TStructure C}
    (W : WeakStabilityFunction t) (Zlin : V →ₗ[ℝ] ℂ)
    (hcompat : ∀ k : K₀ C, Zlin (v k) = W.Z k)
    (hsupport : W.HasSupportProperty v Zlin) {E : C}
    (hE : W.zeroCharge E) : v (K₀.of C E) = 0 := by
  by_cases hzero : IsZero E
  · simp [K₀.of_isZero C hzero]
  apply hsupport.eq_zero_of_charge_eq_zero
  · exact ⟨E, W.isSemistable_of_zeroCharge hE, hzero, rfl⟩
  · rw [hcompat]
    exact hE.2

end WeakStabilityFunction

/-- The real-linear rotation of a charge used by the phase tilt. -/
def phaseTiltLinearCharge (beta : ℝ) (Zlin : V →ₗ[ℝ] ℂ) : V →ₗ[ℝ] ℂ :=
  (LinearMap.mulLeft ℝ
    (Complex.exp (((-(Real.pi * beta) : ℝ) : ℂ) * Complex.I))).comp Zlin

omit [FiniteDimensional ℝ V] in
@[simp]
theorem phaseTiltLinearCharge_apply (beta : ℝ) (Zlin : V →ₗ[ℝ] ℂ)
    (x : V) :
    phaseTiltLinearCharge beta Zlin x =
      Zlin x * Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := by
  simp [phaseTiltLinearCharge, mul_comm]

omit [FiniteDimensional ℝ V] in
/-- Rotating a complex charge does not change its norm. -/
theorem norm_phaseTiltLinearCharge (beta : ℝ) (Zlin : V →ₗ[ℝ] ℂ)
    (x : V) :
    ‖phaseTiltLinearCharge beta Zlin x‖ = ‖Zlin x‖ := by
  have hexp :
      ‖Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)‖ = 1 := by
    convert Complex.norm_exp_ofReal_mul_I (-(Real.pi * beta)) using 1
    push_cast
    ring
  rw [phaseTiltLinearCharge_apply, norm_mul, hexp, mul_one]

namespace WeakPreStabilityCondition

omit [FiniteDimensional ℝ V] in
/-- **Support-property transport across the phase tilt.**

For a cutoff strictly inside `(0, 1)`, the support property of the original
heart weak function implies the support property of the rotated weak function
on the tilted heart.  The same comparison constant works. -/
theorem phaseTilt_hasSupportProperty
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (Zlin : V →ₗ[ℝ] ℂ) (hcompat : ∀ x : V, Zlin x = sigma.Z x)
    (hsupport : sigma.weakStabilityFunctionOnHeart.HasSupportProperty v Zlin) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).HasSupportProperty
      v (phaseTiltLinearCharge beta Zlin) := by
  let W0 := sigma.weakStabilityFunctionOnHeart
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1
  have hcompat0 : ∀ k : K₀ C, Zlin (v k) = W0.Z k := by
    intro k
    exact hcompat (v k)
  obtain ⟨K, hK, hbound⟩ := hsupport
  have hsupport' : W0.HasSupportProperty v Zlin := ⟨K, hK, hbound⟩
  refine ⟨K, hK, ?_⟩
  intro x hx
  obtain ⟨E, hEss, hE0, rfl⟩ := hx
  by_cases hcharge : W.charge E = 0
  · have hEzeroNew : W.zeroCharge E := ⟨hEss.1, hcharge⟩
    have hEzeroOld : W0.zeroCharge E := by
      exact (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff
        beta hbeta0.le hbeta1 E).mp hEzeroNew
    have hclass : v (K₀.of C E) = 0 :=
      W0.class_eq_zero_of_zeroCharge Zlin hcompat0 hsupport' hEzeroOld
    simp [hclass]
  · have hclassification :=
      sigma.phaseTiltClassification_of_isSemistable beta hbeta0 hbeta1 hEss hcharge
    rcases hclassification with htypeOne | htypeTwo
    · have hold : v (K₀.of C E) ∈ W0.semistableClasses v :=
        ⟨E, htypeOne.1, hE0, rfl⟩
      have hb := hbound _ hold
      calc
        ‖v (K₀.of C E)‖ ≤ K * ‖Zlin (v (K₀.of C E))‖ := hb
        _ = K * ‖phaseTiltLinearCharge beta Zlin (v (K₀.of C E))‖ := by
          rw [norm_phaseTiltLinearCharge]
    · obtain ⟨U, V0, hUfree, hUss, hVzero, f, g, d, hdist, -⟩ := htypeTwo
      have hVclass : v (K₀.of C V0) = 0 :=
        W0.class_eq_zero_of_zeroCharge Zlin hcompat0 hsupport' hVzero
      have hclass : v (CategoryTheory.Triangulated.K₀.of C E) =
          -(v (CategoryTheory.Triangulated.K₀.of C U)) := by
        have hk : CategoryTheory.Triangulated.K₀.of C E =
            CategoryTheory.Triangulated.K₀.of C (U⟦(1 : ℤ)⟧) +
              CategoryTheory.Triangulated.K₀.of C V0 := by
          simpa using CategoryTheory.Triangulated.K₀.of_triangle C
            (Triangle.mk f g d) hdist
        rw [hk, map_add,
          CategoryTheory.Triangulated.K₀.of_shift_one C U,
          map_neg, hVclass, add_zero]
      have hU0 : ¬IsZero U := by
        intro hzero
        apply hcharge
        have hUclass : v (K₀.of C U) = 0 := by
          simp [K₀.of_isZero C hzero]
        rw [phaseTiltWeakStabilityFunction_charge, hclass, hUclass, neg_zero,
          map_zero, zero_mul]
      have hold : v (K₀.of C U) ∈ W0.semistableClasses v :=
        ⟨U, hUss, hU0, rfl⟩
      have hb := hbound _ hold
      calc
        ‖v (K₀.of C E)‖ = ‖v (K₀.of C U)‖ := by rw [hclass, norm_neg]
        _ ≤ K * ‖Zlin (v (K₀.of C U))‖ := hb
        _ = K * ‖phaseTiltLinearCharge beta Zlin (v (K₀.of C E))‖ := by
          rw [hclass, map_neg, norm_neg, norm_phaseTiltLinearCharge]

end WeakPreStabilityCondition

end

end CategoryTheory.Triangulated.WeakStabilityCondition

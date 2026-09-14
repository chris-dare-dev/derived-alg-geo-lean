/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Family
import Mathlib.Tactic

/-!
# Numerical walls of parameterized charge families

`CentralCharge/Family.lean` owns `ChargeFamily`, reindexing, pullback and
postcomposition.  This downstream file adds only determinant-alignment values
and their zero loci.

For two classes `v,w`, their universal wall equation is the determinant

`Re Z(v) Im Z(w) - Im Z(v) Re Z(w) = 0`.

The equation says that the two complex charges are real-linearly dependent;
positivity and nonvanishing hypotheses needed to identify actual equal phases
belong to later stability-condition layers.

The parameter type remains unconstrained.  Actual destabilization needs
nonvanishing charges and semistable objects in addition to this numerical
alignment equation.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

open scoped ComplexConjugate

universe u v w x

variable {P : Type u} {Q : Type v}
variable {N : Type w} {M : Type x}
variable [AddCommGroup N] [AddCommGroup M]

namespace ChargeFamily

variable (Z : ChargeFamily P N)

/-- The universal numerical wall expression for two classes. -/
def wallValue (p : P) (v w : N) : ℝ :=
  Z.re p v * Z.im p w - Z.im p v * Z.re p w

/-- The numerical wall locus of two classes in the parameter space.

This is the *numerical* wall (the pseudo-wall of Maciocia, the numerical wall
of Arcara--Miles): the locus where the two charges are real-proportional.  It
is the whole parameter space when `w` is an integral multiple of `v`
(`wall_self`, `wall_add_zsmul_right`) and wherever `Z(v) = 0`.  An actual wall
additionally needs nonvanishing charges and semistable objects with these
classes; those hypotheses belong to stability-condition layers, not here. -/
def wall (v w : N) : Set P := {p | Z.wallValue p v w = 0}

@[simp]
theorem mem_wall (p : P) (v w : N) :
    p ∈ Z.wall v w ↔ Z.wallValue p v w = 0 := Iff.rfl

/-- The determinant wall expression is the negative imaginary part of
`Z(v) * conj (Z(w))`. -/
theorem wallValue_eq_neg_im_mul_conj (p : P) (v w : N) :
    Z.wallValue p v w =
      -((Z.charge p v) * conj (Z.charge p w)).im := by
  simp only [wallValue, re, im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

@[simp]
theorem wallValue_self (p : P) (v : N) : Z.wallValue p v v = 0 := by
  simp only [wallValue]
  ring

@[simp]
theorem wall_self (v : N) : Z.wall v v = Set.univ := by
  ext p
  simp

theorem wallValue_swap (p : P) (v w : N) :
    Z.wallValue p w v = -Z.wallValue p v w := by
  simp only [wallValue]
  ring

theorem wall_swap (v w : N) : Z.wall w v = Z.wall v w := by
  ext p
  change Z.wallValue p w v = 0 ↔ Z.wallValue p v w = 0
  rw [wallValue_swap, neg_eq_zero]

@[simp]
theorem wallValue_zero_left (p : P) (w : N) : Z.wallValue p 0 w = 0 := by
  simp [wallValue]

@[simp]
theorem wallValue_zero_right (p : P) (v : N) : Z.wallValue p v 0 = 0 := by
  simp [wallValue]

theorem wallValue_add_left (p : P) (v₁ v₂ w : N) :
    Z.wallValue p (v₁ + v₂) w =
      Z.wallValue p v₁ w + Z.wallValue p v₂ w := by
  simp only [wallValue, re_add, im_add]
  ring

theorem wallValue_add_right (p : P) (v w₁ w₂ : N) :
    Z.wallValue p v (w₁ + w₂) =
      Z.wallValue p v w₁ + Z.wallValue p v w₂ := by
  simp only [wallValue, re_add, im_add]
  ring

theorem wallValue_neg_left (p : P) (v w : N) :
    Z.wallValue p (-v) w = -Z.wallValue p v w := by
  simp only [wallValue, re_neg, im_neg]
  ring

theorem wallValue_neg_right (p : P) (v w : N) :
    Z.wallValue p v (-w) = -Z.wallValue p v w := by
  simp only [wallValue, re_neg, im_neg]
  ring

@[simp]
theorem wallValue_zsmul_right (p : P) (n : ℤ) (v : N) :
    Z.wallValue p v (n • v) = 0 := by
  simp only [wallValue, re_zsmul, im_zsmul]
  ring

/-- A wall depends on the competitor only modulo integral multiples of the
reference class. -/
theorem wallValue_add_zsmul_right (p : P) (n : ℤ) (v w : N) :
    Z.wallValue p v (w + n • v) = Z.wallValue p v w := by
  rw [wallValue_add_right, wallValue_zsmul_right, add_zero]

theorem wall_add_zsmul_right (n : ℤ) (v w : N) :
    Z.wall v (w + n • v) = Z.wall v w := by
  ext p
  simp only [mem_wall, wallValue_add_zsmul_right]

/-- Compatibility version for a nonnegative integral multiple. -/
theorem wallValue_add_nsmul_right (p : P) (n : ℕ) (v w : N) :
    Z.wallValue p v (w + n • v) = Z.wallValue p v w := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, ← add_assoc, wallValue_add_right, ih, wallValue_self, add_zero]

/-- **The determinant law.**  `wallValue` is the determinant of the `2 × 2`
matrix of real and imaginary parts of the two charges, so post-composing with a
real-linear map multiplies it by that map's determinant. -/
theorem wallValue_linearAct (g : ℂ →ₗ[ℝ] ℂ) (p : P) (v w : N) :
    (Z.linearAct g).wallValue p v w = realDet g * Z.wallValue p v w := by
  simp only [wallValue, re, im, linearAct_charge, realDet]
  rw [map_eq_smul_add_smul g (Z.charge p v), map_eq_smul_add_smul g (Z.charge p w)]
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero]
  ring

/-- An invertible real-linear change of charge leaves every numerical wall
where it was. -/
theorem wall_linearAct {g : ℂ →ₗ[ℝ] ℂ} (hg : realDet g ≠ 0) (v w : N) :
    (Z.linearAct g).wall v w = Z.wall v w := by
  ext p
  simp only [mem_wall, wallValue_linearAct, mul_eq_zero]
  exact or_iff_right hg

/-- Rescaling the charges by `c` scales every wall expression by `‖c‖²`. -/
theorem wallValue_smul (c : ℂ) (p : P) (v w : N) :
    (Z.smul c).wallValue p v w = Complex.normSq c * Z.wallValue p v w := by
  rw [smul, wallValue_linearAct, realDet_mulLeft]

/-- **Numerical walls are invariant under rescaling the central charge.** -/
theorem wall_smul {c : ℂ} (hc : c ≠ 0) (v w : N) :
    (Z.smul c).wall v w = Z.wall v w :=
  Z.wall_linearAct (by
    rw [realDet_mulLeft]
    exact fun h => hc (Complex.normSq_eq_zero.mp h)) v w

/-- Reindexing a charge family pulls its wall locus back as a set. -/
theorem reindex_wall (f : Q → P) (v w : N) :
    (Z.reindex f).wall v w = f ⁻¹' Z.wall v w := rfl

/-- Pullback of numerical classes preserves the wall expression. -/
@[simp]
theorem pullback_wallValue (f : M →+ N) (p : P) (v w : M) :
    (Z.pullback f).wallValue p v w = Z.wallValue p (f v) (f w) := rfl

/-- Pullback of numerical classes identifies the corresponding wall loci. -/
theorem pullback_wall (f : M →+ N) (v w : M) :
    (Z.pullback f).wall v w = Z.wall (f v) (f w) := rfl

end ChargeFamily

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

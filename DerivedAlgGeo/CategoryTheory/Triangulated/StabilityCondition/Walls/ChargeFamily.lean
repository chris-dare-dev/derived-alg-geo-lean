/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Numerical walls of parameterized central charges

This file owns the dimension- and geometry-independent root of the numerical
wall hierarchy.  A `ChargeFamily P N` is only a family of additive central
charges on a numerical class group `N`, indexed by an arbitrary parameter type
`P`.  It does not assume that the parameters form a half-plane, that the
classes are Chern characters, or that a stability condition has been
constructed.

For two classes `v,w`, their universal wall equation is the determinant

`Re Z(v) Im Z(w) - Im Z(v) Re Z(w) = 0`.

The equation says that the two complex charges are real-linearly dependent;
positivity and nonvanishing hypotheses needed to identify actual equal phases
belong to later stability-condition layers.

The parameter type is intentionally unconstrained.  It may be a real affine
space of stability parameters, a base indexing fibers of a family, or a
product of both.  `reindex` changes parameters and `pullback` changes the
numerical class presentation, so concrete varieties and geometric families
become descendants without changing the wall definition.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

open scoped ComplexConjugate

universe u v w x

variable {P : Type u} {Q : Type v}
variable {N : Type w} {M : Type x}
variable [AddCommGroup N] [AddCommGroup M]

/-- A parameterized family of additive complex central charges.

This is numerical data only: it deliberately does not contain a heart, a
slicing, support-property data, or a topology on the parameter space. -/
structure ChargeFamily (P : Type u) (N : Type v) [AddCommGroup N] where
  /-- The central charge at a parameter value. -/
  charge : P → N →+ ℂ

namespace ChargeFamily

variable (Z : ChargeFamily P N)

@[ext]
theorem ext {Z W : ChargeFamily P N}
    (h : ∀ p, Z.charge p = W.charge p) : Z = W := by
  cases Z
  cases W
  congr
  funext p
  exact h p

/-- Change the parameter space of a charge family. -/
def reindex (f : Q → P) : ChargeFamily Q N where
  charge q := Z.charge (f q)

/-- Pull a charge family back along an additive map of numerical class
carriers. -/
def pullback (f : M →+ N) : ChargeFamily P M where
  charge p := (Z.charge p).comp f

@[simp]
theorem reindex_charge (f : Q → P) (q : Q) :
    (Z.reindex f).charge q = Z.charge (f q) := rfl

@[simp]
theorem pullback_charge (f : M →+ N) (p : P) (v : M) :
    (Z.pullback f).charge p v = Z.charge p (f v) := rfl

/-- Simultaneously changing parameters and pulling back classes evaluates by
composition in the two independent inputs. -/
theorem reindex_pullback_charge (f : Q → P) (g : M →+ N) (q : Q) (v : M) :
    ((Z.reindex f).pullback g).charge q v = Z.charge (f q) (g v) := rfl

/-! ### Functoriality of reindexing and pullback

Reindexing is contravariant in the parameter map and pullback is contravariant
in the class map; the two commute.  All of these are definitional, and they are
recorded so that a chain of slices and class presentations can be normalised
to one reindexing of one pullback. -/

@[simp]
theorem reindex_id : Z.reindex id = Z := rfl

theorem reindex_reindex {R : Type*} (f : Q → P) (g : R → Q) :
    (Z.reindex f).reindex g = Z.reindex (f ∘ g) := rfl

@[simp]
theorem pullback_id : Z.pullback (AddMonoidHom.id N) = Z := rfl

theorem pullback_pullback {L : Type*} [AddCommGroup L] (f : M →+ N) (g : L →+ M) :
    (Z.pullback f).pullback g = Z.pullback (f.comp g) := rfl

/-- Reindexing and pullback act on independent inputs, so they commute. -/
theorem pullback_reindex (f : Q → P) (g : M →+ N) :
    (Z.pullback g).reindex f = (Z.reindex f).pullback g := rfl

/-- The real part of the central charge of a class. -/
def re (p : P) (v : N) : ℝ := (Z.charge p v).re

/-- The imaginary part of the central charge of a class. -/
def im (p : P) (v : N) : ℝ := (Z.charge p v).im

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
theorem re_zero (p : P) : Z.re p 0 = 0 := by simp [re]

@[simp]
theorem im_zero (p : P) : Z.im p 0 = 0 := by simp [im]

@[simp]
theorem re_add (p : P) (v w : N) :
    Z.re p (v + w) = Z.re p v + Z.re p w := by simp [re]

@[simp]
theorem im_add (p : P) (v w : N) :
    Z.im p (v + w) = Z.im p v + Z.im p w := by simp [im]

@[simp]
theorem re_neg (p : P) (v : N) : Z.re p (-v) = -Z.re p v := by simp [re]

@[simp]
theorem im_neg (p : P) (v : N) : Z.im p (-v) = -Z.im p v := by simp [im]

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
theorem re_zsmul (p : P) (n : ℤ) (v : N) :
    Z.re p (n • v) = n • Z.re p v := by
  simp [re]

@[simp]
theorem im_zsmul (p : P) (n : ℤ) (v : N) :
    Z.im p (n • v) = n • Z.im p v := by
  simp [im]

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

/-! ### The real-linear action on charges

A stability condition may be post-composed with a real-linear automorphism of
`ℂ`; the universal cover of `GL⁺(2, ℝ)` acts on the space of stability
conditions this way, and the numerical wall of a pair of classes is one of the
things that action preserves.  Only the numerical half of that is available
here: the action on charges, and the determinant law for `wallValue`.  Nothing
below mentions a heart or a slicing, and no orientation is required — the wall
is preserved by every invertible real-linear map, while the *phase* is not,
which is why `GL⁺` rather than `GL` appears downstream. -/

/-- The determinant of a real-linear endomorphism of `ℂ`, computed in the basis
`1, I`.  This is the factor by which the map scales `wallValue`. -/
def realDet (g : ℂ →ₗ[ℝ] ℂ) : ℝ :=
  (g 1).re * (g Complex.I).im - (g 1).im * (g Complex.I).re

/-- A real-linear map of `ℂ` is determined by its values on `1` and `I`. -/
theorem map_eq_smul_add_smul (g : ℂ →ₗ[ℝ] ℂ) (z : ℂ) :
    g z = z.re • g 1 + z.im • g Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul]

/-- Post-compose every charge of a family with a real-linear map of `ℂ`. -/
def linearAct (g : ℂ →ₗ[ℝ] ℂ) : ChargeFamily P N where
  charge p := g.toAddMonoidHom.comp (Z.charge p)

@[simp]
theorem linearAct_charge (g : ℂ →ₗ[ℝ] ℂ) (p : P) (v : N) :
    (Z.linearAct g).charge p v = g (Z.charge p v) := rfl

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

/-- Rescale every charge by a complex scalar.  This is the scalar part of the
real-linear action. -/
def smul (c : ℂ) : ChargeFamily P N := Z.linearAct (LinearMap.mulLeft ℝ c)

@[simp]
theorem smul_charge (c : ℂ) (p : P) (v : N) :
    (Z.smul c).charge p v = c * Z.charge p v := rfl

/-- Multiplication by `c` has determinant `‖c‖²` as a real-linear map. -/
@[simp]
theorem realDet_mulLeft (c : ℂ) :
    realDet (LinearMap.mulLeft ℝ c) = Complex.normSq c := by
  simp only [realDet, LinearMap.mulLeft_apply, mul_one, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

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

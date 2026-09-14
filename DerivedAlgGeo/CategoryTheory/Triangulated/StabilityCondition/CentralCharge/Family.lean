/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Families of additive complex charges

This file owns the dimension- and geometry-independent charge-family root.  A
`ChargeFamily P N` is only a family of additive maps `N →+ ℂ`, indexed by an
arbitrary parameter type `P`.  It contains no heart, slicing, support property,
wall locus, Chern character, or scheme.

`reindex` changes parameters and `pullback` changes the additive class
presentation. `zeroLocus` names charge vanishing without calling it a wall.
Real-linear postcomposition and complex rescaling also belong here because they
act on charges before any wall or phase is considered.

The declarations keep their established `...Wall` namespace so the source
cutover preserves public names.  The path records the mathematical owner; wall
equations are downstream in `StabilityCondition/Walls/Alignment.lean`.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

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

/-- The parameters where the charge of one class vanishes. This is generally
two real equations, not a codimension-one numerical alignment wall. -/
def zeroLocus (v : N) : Set P := {p | Z.charge p v = 0}

@[simp]
theorem mem_zeroLocus (p : P) (v : N) :
    p ∈ Z.zeroLocus v ↔ Z.charge p v = 0 := Iff.rfl

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

/-- Reindexing pulls a charge-zero locus back along the parameter map. -/
theorem reindex_zeroLocus (f : Q → P) (v : N) :
    (Z.reindex f).zeroLocus v = f ⁻¹' Z.zeroLocus v := rfl

/-- Pullback of classes compares the corresponding charge-zero loci. -/
theorem pullback_zeroLocus (f : M →+ N) (v : M) :
    (Z.pullback f).zeroLocus v = Z.zeroLocus (f v) := rfl

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
theorem re_zsmul (p : P) (n : ℤ) (v : N) :
    Z.re p (n • v) = n • Z.re p v := by simp [re]

@[simp]
theorem im_zsmul (p : P) (n : ℤ) (v : N) :
    Z.im p (n • v) = n • Z.im p v := by simp [im]

/-- The determinant of a real-linear endomorphism of `ℂ`, computed in the basis
`1, I`. -/
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

/-- Rescale every charge by a complex scalar. -/
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

end ChargeFamily

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

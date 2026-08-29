/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Combined.Components

/-!
# Equivariance of period coordinates

The symmetry action on a stability condition has a corresponding action on
its central charge.  This file packages that charge action as additive
equivalences of `Λ →+ ℂ` and proves the equivariance square both on the full
stability space and on each connected component.

The `GLTilde` factor postcomposes by its real-linear action on `ℂ`; the
autoequivalence factor precomposes by its compatible lattice automorphism.
These operations are additive equivalences even though the first one need not
be complex-linear.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.StabilityCondition.GroupAction

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-! ## Additive equivalences of the charge space -/

/-- Postcomposition of a charge by the real-linear action of a lifted matrix. -/
def GLTilde.chargeAddEquiv (x : GLTilde) : (Λ →+ ℂ) ≃+ (Λ →+ ℂ) where
  toFun Z := (actC x.mat).toAddMonoidHom.comp Z
  invFun Z := (actC x⁻¹.mat).toAddMonoidHom.comp Z
  left_inv Z := by
    ext a
    change actC x⁻¹.mat (actC x.mat (Z a)) = Z a
    rw [← actC_mul, ← GLTilde.mul_mat]
    simp
  right_inv Z := by
    ext a
    change actC x.mat (actC x⁻¹.mat (Z a)) = Z a
    rw [← actC_mul, ← GLTilde.mul_mat]
    simp
  map_add' Z W := by
    ext a
    exact map_add (actC x.mat) (Z a) (W a)

@[simp]
theorem GLTilde.chargeAddEquiv_apply (x : GLTilde) (Z : Λ →+ ℂ) (a : Λ) :
    x.chargeAddEquiv Z a = actC x.mat (Z a) :=
  rfl

/-- Precomposition of a charge by the lattice automorphism carried by an
autoequivalence pair. -/
def AutPair.chargeAddEquiv (a : AutPair v) : (Λ →+ ℂ) ≃+ (Λ →+ ℂ) where
  toFun Z := Z.comp a.lam.toAddMonoidHom
  invFun Z := Z.comp a.lam.symm.toAddMonoidHom
  left_inv Z := by
    ext y
    exact congrArg Z (a.lam.apply_symm_apply y)
  right_inv Z := by
    ext y
    exact congrArg Z (a.lam.symm_apply_apply y)
  map_add' Z W := by
    ext y
    rfl

@[simp]
theorem AutPair.chargeAddEquiv_apply (a : AutPair v) (Z : Λ →+ ℂ) (y : Λ) :
    a.chargeAddEquiv Z y = Z (a.lam y) :=
  rfl

/-- The charge-space equivalence descends to `AutPairQuot`, since its setoid
fixes the lattice automorphism on the nose. -/
def AutPairQuot.chargeAddEquiv (q : AutPairQuot v) : (Λ →+ ℂ) ≃+ (Λ →+ ℂ) :=
  _root_.Quotient.liftOn q AutPair.chargeAddEquiv fun a b h ↦ by
    apply AddEquiv.ext
    intro Z
    ext y
    rw [AutPair.chargeAddEquiv_apply, AutPair.chargeAddEquiv_apply, h.2]

@[simp]
theorem AutPairQuot.chargeAddEquiv_mk (a : AutPair v) :
    (AutPairQuot.mk a).chargeAddEquiv = a.chargeAddEquiv :=
  rfl

/-- The combined charge action: precompose by the lattice automorphism, then
postcompose by the lifted real matrix. -/
def combinedChargeAddEquiv (p : GLTilde × AutPairQuot v) :
    (Λ →+ ℂ) ≃+ (Λ →+ ℂ) :=
  p.2.chargeAddEquiv.trans p.1.chargeAddEquiv

@[simp]
theorem combinedChargeAddEquiv_mk_apply (x : GLTilde) (a : AutPair v)
    (Z : Λ →+ ℂ) (y : Λ) :
    combinedChargeAddEquiv (x, AutPairQuot.mk a) Z y =
      actC x.mat (Z (a.lam y)) :=
  rfl

/-! ## Equivariance of the full period map -/

variable [IsTriangulated C]

theorem GLTilde.centralCharge_equivariant (x : GLTilde)
    (σ : StabilityCondition.WithClassMap C v) :
    (x • σ).Z = x.chargeAddEquiv σ.Z := by
  ext y
  exact smul_stab_Z C v x σ y

theorem AutPairQuot.centralCharge_equivariant (q : AutPairQuot v)
    (σ : StabilityCondition.WithClassMap C v) :
    (q • σ).Z = q.chargeAddEquiv σ.Z := by
  induction q using _root_.Quotient.inductionOn with
  | _ a =>
      ext y
      rfl

/-- The central-charge map is equivariant for the combined symmetry action. -/
theorem combinedCentralCharge_equivariant (p : GLTilde × AutPairQuot v)
    (σ : StabilityCondition.WithClassMap C v) :
    (p • σ).Z = combinedChargeAddEquiv p σ.Z := by
  change (p.1 • (p.2 • σ)).Z = _
  rw [p.1.centralCharge_equivariant, p.2.centralCharge_equivariant]
  rfl

theorem combinedCentralCharge_equivariant_apply
    (x : GLTilde) (a : AutPair v)
    (σ : StabilityCondition.WithClassMap C v) (y : Λ) :
    (((x, AutPairQuot.mk a) • σ).Z y) = actC x.mat (σ.Z (a.lam y)) :=
  prod_mk_smul_Z x a σ y

/-! ## The connected-component square -/

/-- On component subtypes, symmetry transport and the central-charge map form
the expected equivariant square. -/
theorem componentCentralCharge_equivariant
    (p : GLTilde × AutPairQuot v)
    (cc : ConnectedComponents (StabilityCondition.WithClassMap C v))
    (σ : {τ : StabilityCondition.WithClassMap C v //
      ConnectedComponents.mk τ = cc}) :
    (componentHomeomorph p cc σ).1.Z =
      combinedChargeAddEquiv p σ.1.Z := by
  exact combinedCentralCharge_equivariant p σ.1

end

end CategoryTheory.Triangulated.StabilityCondition.GroupAction

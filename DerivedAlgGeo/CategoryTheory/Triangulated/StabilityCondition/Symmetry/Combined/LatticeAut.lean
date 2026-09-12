/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.Action

/-!
# Lattice automorphisms in the combined symmetry group

The compatible lattice automorphism carried by `AutPair` descends through
`AutPairQuot`: the quotient relation fixes that component on the nose.  This
file exposes the descended automorphism and its interaction with the group
operations.

The multiplication formula is deliberately recorded as a plain lemma rather
than a bundled homomorphism.  Multiplication satisfies
`(p * q).lam = p.lam.trans q.lam`; choosing whether to regard this as a map to
`AddAut Λ` or its opposite is a variance decision that should be made only by
a consumer that needs the bundle.

The same file records that the real-linear action of a positive invertible
matrix on `ℂ` is injective and therefore detects zero.  These are the two
algebraic facts needed to transport charge-vanishing walls.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

namespace AutPairQuot

/-- The class-lattice automorphism carried by a compatible autoequivalence
pair, descended to the quotient by natural isomorphism. -/
def lam (q : AutPairQuot v) : Λ ≃+ Λ :=
  _root_.Quotient.liftOn q AutPair.lam fun _ _ h ↦ h.2

/-- The descended lattice automorphism agrees definitionally with a representative. -/
@[simp]
theorem lam_mk (a : AutPair v) : (mk a).lam = a.lam :=
  rfl

/-- Multiplication composes the carried lattice automorphisms in action order. -/
theorem lam_mul (p q : AutPairQuot v) :
    (p * q).lam = p.lam.trans q.lam := by
  induction p using _root_.Quotient.inductionOn with
  | _ a =>
      induction q using _root_.Quotient.inductionOn with
      | _ b => rfl

/-- The identity symmetry carries the identity lattice automorphism. -/
theorem lam_one : (1 : AutPairQuot v).lam = AddEquiv.refl Λ :=
  rfl

/-- Inversion replaces the carried lattice automorphism by its inverse. -/
theorem lam_inv (p : AutPairQuot v) : (p⁻¹).lam = p.lam.symm := by
  induction p using _root_.Quotient.inductionOn with
  | _ a => rfl

end AutPairQuot

/-- The real-linear action of an invertible positive matrix on `ℂ` is injective. -/
theorem actC_injective (T : Matrix.GLPos (Fin 2) ℝ) : Function.Injective (actC T) := by
  intro z w h
  calc
    z = actC (T⁻¹ * T) z := by simp
    _ = actC T⁻¹ (actC T z) := actC_mul T⁻¹ T z
    _ = actC T⁻¹ (actC T w) := congrArg (actC T⁻¹) h
    _ = actC (T⁻¹ * T) w := (actC_mul T⁻¹ T w).symm
    _ = w := by simp

/-- The real-linear action of an invertible positive matrix detects zero. -/
theorem actC_eq_zero_iff (T : Matrix.GLPos (Fin 2) ℝ) (z : ℂ) :
    actC T z = 0 ↔ z = 0 := by
  constructor
  · intro h
    exact actC_injective T (by simpa using h)
  · rintro rfl
    exact map_zero (actC T)

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

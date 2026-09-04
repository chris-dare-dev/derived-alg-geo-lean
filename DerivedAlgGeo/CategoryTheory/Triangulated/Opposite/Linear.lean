/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Linear.Opposite
import Mathlib.CategoryTheory.Shift.ShiftedHomOpposite

/-!
# `R`-linearity of the opposite shift

The `R`-linear counterparts of the `(shiftFunctor Cᵒᵖ n).Additive` instance
(`Mathlib/CategoryTheory/Triangulated/Opposite/Basic.lean`) and of the scalar behaviour of
`ShiftedHom.opEquiv` (`Mathlib/CategoryTheory/Shift/ShiftedHomOpposite.lean`). The opposite
shift is defined with the opposite of a pretriangulated category, so this file lives at that
definition site; the bare `Linear R Cᵒᵖ` instance it builds on is in
`CategoryTheory/Linear/Opposite.lean`.
-/


namespace CategoryTheory

section OppositeShift

open Pretriangulated.Opposite

variable (R : Type*) [Semiring R] (C : Type*) [Category C] [Preadditive C]
  [Linear R C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R]

/-- **The shift functors on `Cᵒᵖ` are `R`-linear when those on `C` are.**

The `R`-linear counterpart of Mathlib's `(shiftFunctor Cᵒᵖ n).Additive`
instance, and the piece that makes `Linear R Cᵒᵖ` more than a bare module
structure: without it the opposite category is linear but its shift is not
known to respect scalars, which is exactly what the `k`-linear Yoneda shift
sequence needs.

Shifting by `n` on `Cᵒᵖ` *is* shifting by `-n` on `C`, opposed --
`shiftFunctorOpIso` witnesses this as an `eqToIso` of a definitional equality --
so `Functor.op_linear` applied to `shiftFunctor C (-n)` is already the instance,
and `inferInstanceAs` is the whole proof. -/
instance shiftFunctorOppositeLinear (n : ℤ) : (shiftFunctor Cᵒᵖ n).Linear R :=
  inferInstanceAs <| ((shiftFunctor C (-n)).op).Linear R

end OppositeShift

namespace ShiftedHom

open Pretriangulated.Opposite

variable {C : Type*} [Category C] [HasShift C ℤ] {X Y : C}
  {R : Type*} [Ring R] [Preadditive C] [Linear R C]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, Functor.Linear R (shiftFunctor C n)]

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
set_option backward.defeqAttrib.useBackward true in
/-- The `smul` counterpart of `ShiftedHom.opEquiv_symm_add`.

The `set_option` mirrors Mathlib's on the additive twin, and is load-bearing for
the same reason: `dsimp` on an opposite-category shift leaves the goal not
type-correct at `instances` transparency, and the rewrite then cannot match. -/
@[simp]
lemma opEquiv_symm_smul {n : ℤ} (r : R)
    (x : ShiftedHom (Opposite.op Y) (Opposite.op X) n) :
    (opEquiv n).symm (r • x) = r • (opEquiv n).symm x := by
  dsimp [opEquiv_symm_apply]
  rw [← Linear.comp_smul, Functor.map_smul]

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
set_option backward.defeqAttrib.useBackward true in
/-- The `smul` counterpart of `ShiftedHom.opEquiv'_symm_add`. -/
@[simp]
lemma opEquiv'_symm_smul {n a : ℤ} (r : R)
    (x : (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)) (a' : ℤ) (h : n + a = a') :
    (opEquiv' n a a' h).symm (r • x) = r • (opEquiv' n a a' h).symm x := by
  dsimp [opEquiv']
  rw [opEquiv_symm_smul, Linear.smul_comp]

end ShiftedHom

end CategoryTheory

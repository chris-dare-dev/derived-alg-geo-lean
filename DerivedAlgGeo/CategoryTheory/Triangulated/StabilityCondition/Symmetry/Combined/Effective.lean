/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.PeriodMap
import DerivedAlgGeo.CategoryTheory.Triangulated.ShiftFunctor
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Deck overlap and the effective symmetry group

The two factors of the combined symmetry group overlap.  With the left-action
conventions of this project, the categorical shift `[2]` acts on stability
conditions as the deck transformation `deck (-1)`.  Consequently

```
(deck 1, [2])
```

acts trivially.

This file proves that convention-sensitive statement from the slicing shift
axiom, records the overlap in the kernel of the combined action, and defines
the effective symmetry group to be the quotient by the full action kernel.
The induced action of that quotient is faithful by construction.

The shift-functor coherence used here comes from the reusable sign-correct
interface in `Triangulated.ShiftFunctor`.  The local names below remain thin
compatibility wrappers for the stability-action API.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ## Shift functors as triangulated equivalences -/

set_option backward.isDefEq.respectTransparency false in
/-- A shift functor coherently commutes with every other shift.

**`scoped`, deliberately.** The underlying reusable structure is explicit so
that it cannot silently compete with another `CommShift` choice.  This wrapper
keeps the historical stability-action instance local to this namespace. -/
noncomputable scoped instance shiftFunctorCommShift (n : ℤ) :
    (shiftFunctor C n).CommShift ℤ :=
  Pretriangulated.shiftFunctorUnsignedCommShift C n

set_option backward.isDefEq.respectTransparency false in
/-- For the even shift `[2]`, mapping a triangle agrees with shifting that
triangle: the usual `(-1)^n` sign is `+1`. -/
noncomputable def shiftTwoMapTriangleIso :
    (shiftFunctor C (2 : ℤ)).mapTriangle ≅ Triangle.shiftFunctor C (2 : ℤ) :=
  Pretriangulated.shiftFunctorUnsignedMapTriangleIso C 2 (by norm_num)

noncomputable instance shiftTwoIsTriangulated :
    (shiftFunctor C (2 : ℤ)).IsTriangulated :=
  Pretriangulated.shiftFunctorUnsignedIsTriangulated C 2 (by norm_num)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse even shift has the same sign-free triangle comparison. -/
noncomputable def shiftNegTwoMapTriangleIso :
    (shiftFunctor C (-2 : ℤ)).mapTriangle ≅ Triangle.shiftFunctor C (-2 : ℤ) :=
  Pretriangulated.shiftFunctorUnsignedMapTriangleIso C (-2) (by norm_num)

noncomputable instance shiftNegTwoIsTriangulated :
    (shiftFunctor C (-2 : ℤ)).IsTriangulated :=
  Pretriangulated.shiftFunctorUnsignedIsTriangulated C (-2) (by norm_num)

/-- The categorical double shift as a bundled triangulated autoequivalence. -/
noncomputable def shiftTwoTriEquiv : TriEquiv C where
  e := shiftEquiv C (2 : ℤ)
  fAdd := inferInstanceAs ((shiftFunctor C (2 : ℤ)).Additive)
  iAdd := inferInstanceAs ((shiftFunctor C (-2 : ℤ)).Additive)
  fCS := shiftFunctorCommShift 2
  iCS := shiftFunctorCommShift (-2)
  fTri := shiftTwoIsTriangulated
  iTri := shiftNegTwoIsTriangulated

/-- The inverse functor of `[2]` acts trivially on `K₀`. -/
theorem K₀.map_shift_neg_two :
    K₀.map (shiftFunctor C (-2 : ℤ)) = AddMonoidHom.id (K₀ C) := by
  ext X
  rw [K₀.map_of]
  change CategoryTheory.Triangulated.K₀.of C (X⟦(-2 : ℤ)⟧) =
    CategoryTheory.Triangulated.K₀.of C X
  rw [CategoryTheory.Triangulated.K₀.of_shift_int]
  norm_num

variable {Λ : Type u'} [AddCommGroup Λ]

/-- The double shift paired with the identity automorphism of the class
lattice.  Compatibility follows because an even shift is the identity on
`K₀`. -/
noncomputable def shiftTwoPair (v : K₀ C →+ Λ) : AutPair v where
  Φ := shiftTwoTriEquiv
  lam := AddEquiv.refl Λ
  compat x := by
    change v (K₀.map (shiftFunctor C (-2 : ℤ)) x) = v x
    rw [K₀.map_shift_neg_two]
    rfl

theorem deckShift_neg_one_inv_apply (φ : ℝ) :
    (deckShift (-1))⁻¹.toOrderIso φ = φ + 2 := by
  rw [NormalizedShift.inv_apply]
  apply (deckShift (-1)).toOrderIso.injective
  rw [OrderIso.apply_symm_apply, deckShift_apply]
  norm_num

variable [IsTriangulated C]

/-- **Convention check.** With the contravariant autoequivalence action used
on slicings, the categorical double shift acts as `deck (-1)`, not `deck 1`.
-/
theorem shiftTwoPair_act_eq_deck_neg_one (v : K₀ C →+ Λ)
    (σ : StabilityCondition.WithClassMap C v) :
    (shiftTwoPair v).act σ = deck (-1) • σ := by
  refine StabilityCondition.WithClassMap.ext (C := C) ?_ ?_
  · refine Slicing.ext C ?_
    funext φ X
    apply propext
    change σ.slicing.P φ (X⟦(-2 : ℤ)⟧) ↔
      σ.slicing.P ((deckShift (-1))⁻¹.toOrderIso φ) X
    rw [deckShift_neg_one_inv_apply]
    have h := σ.slicing.shift_int C (φ + 2) X (-2)
    convert h.symm using 1
    all_goals norm_num
  · ext y
    change σ.Z y = actC (deck (-1)).mat (σ.Z y)
    simp

theorem deck_mul_deck (m n : ℤ) : deck m * deck n = deck (m + n) := by
  have h := deckHom.map_mul (Multiplicative.ofAdd m) (Multiplicative.ofAdd n)
  change deck (m + n) = deck m * deck n at h
  exact h.symm

@[simp]
theorem deck_zero : deck 0 = 1 := by
  have h := deckHom.map_one
  change deck 0 = 1 at h
  exact h

/-- The diagonal overlap generator `(deck 1, [2])` acts trivially. -/
theorem deck_one_shiftTwo_combined_smul (v : K₀ C →+ Λ)
    (σ : StabilityCondition.WithClassMap C v) :
    (deck 1, AutPairQuot.mk (shiftTwoPair v)) • σ = σ := by
  change deck 1 • ((shiftTwoPair v).act σ) = σ
  rw [shiftTwoPair_act_eq_deck_neg_one, ← mul_smul, deck_mul_deck]
  norm_num

/-! ## Quotient by the full action kernel -/

/-- The permutation representation of the combined symmetry group. -/
noncomputable def combinedActionHom (v : K₀ C →+ Λ) :
    (GLTilde × AutPairQuot v) →*
      Equiv.Perm (StabilityCondition.WithClassMap C v) :=
  MulAction.toPermHom _ _

/-- The subgroup of all combined symmetries acting trivially. -/
abbrev combinedActionKernel (v : K₀ C →+ Λ) :
    Subgroup (GLTilde × AutPairQuot v) :=
  (combinedActionHom v).ker

/-- The effective symmetry group is the combined group modulo its full action
kernel.  This may identify more than the explicit deck/shift overlap in a
particular category, exactly when additional symmetries act trivially. -/
abbrev EffectiveCombinedSymmetry (v : K₀ C →+ Λ) :=
  (GLTilde × AutPairQuot v) ⧸ combinedActionKernel v

/-- The faithful permutation representation of the effective quotient. -/
noncomputable def effectiveCombinedPermHom (v : K₀ C →+ Λ) :
    EffectiveCombinedSymmetry v →*
      Equiv.Perm (StabilityCondition.WithClassMap C v) :=
  QuotientGroup.kerLift (combinedActionHom v)

noncomputable instance effectiveCombinedMulAction (v : K₀ C →+ Λ) :
    MulAction (EffectiveCombinedSymmetry v)
      (StabilityCondition.WithClassMap C v) :=
  MulAction.compHom _ (effectiveCombinedPermHom v)

/-- The quotient action is faithful by construction. -/
instance effectiveCombinedFaithfulSMul (v : K₀ C →+ Λ) :
    FaithfulSMul (EffectiveCombinedSymmetry v)
      (StabilityCondition.WithClassMap C v) where
  eq_of_smul_eq_smul {a b} h := by
    apply QuotientGroup.kerLift_injective (combinedActionHom v)
    apply Equiv.ext
    intro σ
    exact h σ

/-- The explicit deck/double-shift overlap lies in the action kernel. -/
theorem deck_one_shiftTwo_mem_combinedActionKernel (v : K₀ C →+ Λ) :
    (deck 1, AutPairQuot.mk (shiftTwoPair v)) ∈ combinedActionKernel v := by
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro σ
  exact deck_one_shiftTwo_combined_smul v σ

/-- Hence the overlap generator becomes the identity in the effective
quotient. -/
theorem deck_one_shiftTwo_eq_one_in_effective (v : K₀ C →+ Λ) :
    ((deck 1, AutPairQuot.mk (shiftTwoPair v)) :
      EffectiveCombinedSymmetry v) = 1 :=
  (QuotientGroup.eq_one_iff _).2
    (deck_one_shiftTwo_mem_combinedActionKernel v)

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PrincipalIdealDomain

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The saturated zero-charge subgroup

Definition 21.9 of arXiv:1902.08184v4 uses the saturated subgroup generated
by all zero-charge classes before passing to the quotient lattice.  This file
constructs that subgroup for an arbitrary set of classes and proves its
universal property.  It also descends any charge that vanishes on the
generators.

Freeness of the quotient is not inferred merely from the words "lattice": it
requires the usual finite-free hypotheses on the original integral group.
The declarations here isolate the saturation and descent statements that do
not require those additional hypotheses.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.Support

namespace ZeroChargeLattice

variable {Λ Γ : Type*} [AddCommGroup Λ]

/-- A subgroup is saturated when membership of a nonzero natural multiple
forces membership of the original element. -/
def IsSaturated (H : AddSubgroup Λ) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃x : Λ⦄, n • x ∈ H → n = 0 ∨ x ∈ H

/-- The smallest saturated subgroup containing a set of classes. -/
def saturatedClosure (S : Set Λ) : AddSubgroup Λ :=
  sInf {H : AddSubgroup Λ | S ⊆ H ∧ IsSaturated H}

/-- The saturated closure contains every generator. -/
theorem subset_saturatedClosure (S : Set Λ) : S ⊆ saturatedClosure S := by
  intro x hx
  change x ∈ sInf {H : AddSubgroup Λ | S ⊆ H ∧ IsSaturated H}
  rw [AddSubgroup.mem_sInf]
  intro H hH
  exact hH.1 hx

/-- The saturated closure is saturated. -/
theorem isSaturated_saturatedClosure (S : Set Λ) :
    IsSaturated (saturatedClosure S) := by
  intro n x hnx
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  change x ∈ sInf {H : AddSubgroup Λ | S ⊆ H ∧ IsSaturated H}
  rw [AddSubgroup.mem_sInf]
  intro H hH
  apply (hH.2 ?_).resolve_left hn
  change n • x ∈ sInf {H : AddSubgroup Λ | S ⊆ H ∧ IsSaturated H} at hnx
  rw [AddSubgroup.mem_sInf] at hnx
  exact hnx H hH

/-- Universal property of the saturated closure. -/
theorem saturatedClosure_le {S : Set Λ} {H : AddSubgroup Λ}
    (hS : S ⊆ H) (hH : IsSaturated H) : saturatedClosure S ≤ H := by
  intro x hx
  change x ∈ sInf {K : AddSubgroup Λ | S ⊆ K ∧ IsSaturated K} at hx
  rw [AddSubgroup.mem_sInf] at hx
  exact hx H ⟨hS, hH⟩

/-- Membership in the saturated closure is invariant under negation. -/
theorem neg_mem_saturatedClosure_iff (S : Set Λ) (x : Λ) :
    -x ∈ saturatedClosure S ↔ x ∈ saturatedClosure S :=
  (saturatedClosure S).neg_mem_iff

/-- The integral quotient by the saturated zero-charge subgroup. -/
abbrev Quotient (S : Set Λ) := Λ ⧸ saturatedClosure S

/-- The canonical class in the zero-charge quotient. -/
def quotientClass (S : Set Λ) : Λ →+ Quotient S :=
  QuotientAddGroup.mk' (saturatedClosure S)

@[simp]
theorem quotientClass_eq_zero_iff (S : Set Λ) (x : Λ) :
    quotientClass S x = 0 ↔ x ∈ saturatedClosure S := by
  exact QuotientAddGroup.eq_zero_iff x

/-- Saturation is exactly what makes the additive quotient torsion-free. -/
theorem quotient_isAddTorsionFree (S : Set Λ) :
    IsAddTorsionFree (Quotient S) := by
  constructor
  intro n hn a b hab
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective
    (saturatedClosure S) a
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective
    (saturatedClosure S) b
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply (isSaturated_saturatedClosure S ?_).resolve_left hn
  have hab' : quotientClass S (n • x) = quotientClass S (n • y) := by
    simpa [quotientClass] using hab
  have hmem : (n • x) - (n • y) ∈ saturatedClosure S :=
    QuotientAddGroup.eq_iff_sub_mem.mp hab'
  simpa [nsmul_sub] using hmem

/-- A quotient of a finite integral module is finite as an integral module. -/
theorem quotient_moduleFinite [Module.Finite ℤ Λ] (S : Set Λ) :
    Module.Finite ℤ (Quotient S) :=
  Module.Finite.of_surjective (quotientClass S).toIntLinearMap
    (QuotientAddGroup.mk'_surjective (saturatedClosure S))

/-- Under the finite-generation hypothesis expected of a lattice, the
saturated quotient is a free abelian group, as asserted in Definition 21.9. -/
theorem quotient_moduleFree [Module.Finite ℤ Λ] (S : Set Λ) :
    Module.Free ℤ (Quotient S) := by
  letI : IsAddTorsionFree (Quotient S) := quotient_isAddTorsionFree S
  letI : Module.IsTorsionFree ℤ (Quotient S) :=
    Module.isTorsionFree_int_iff_isAddTorsionFree.mpr inferInstance
  letI : Module.Finite ℤ (Quotient S) := quotient_moduleFinite S
  exact Module.free_of_finite_type_torsion_free'

variable [AddCommGroup Γ]

/-- A charge into a torsion-free group that vanishes on the generators also
vanishes on their saturated closure. -/
theorem saturatedClosure_le_ker [IsAddTorsionFree Γ]
    (S : Set Λ) (Z : Λ →+ Γ) (hS : ∀ x ∈ S, Z x = 0) :
    saturatedClosure S ≤ Z.ker := by
  apply saturatedClosure_le
  · intro x hx
    exact hS x hx
  · intro n x hnx
    by_cases hn : n = 0
    · exact Or.inl hn
    right
    rw [AddMonoidHom.mem_ker] at hnx ⊢
    apply IsAddTorsionFree.nsmul_right_injective hn
    simpa using hnx

/-- The charge induced on the quotient by the saturated zero-charge
subgroup. -/
def quotientCharge [IsAddTorsionFree Γ]
    (S : Set Λ) (Z : Λ →+ Γ) (hS : ∀ x ∈ S, Z x = 0) :
    Quotient S →+ Γ :=
  QuotientAddGroup.lift (saturatedClosure S) Z
    (saturatedClosure_le_ker S Z hS)

@[simp]
theorem quotientCharge_quotientClass [IsAddTorsionFree Γ]
    (S : Set Λ) (Z : Λ →+ Γ) (hS : ∀ x ∈ S, Z x = 0) (x : Λ) :
    quotientCharge S Z hS (quotientClass S x) = Z x :=
  rfl

end ZeroChargeLattice

end CategoryTheory.Triangulated.WeakStabilityCondition.Support

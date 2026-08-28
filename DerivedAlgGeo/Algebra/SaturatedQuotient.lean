/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Saturated

/-!
# Saturated quotients of additive commutative groups

This file packages the algebraic construction shared by relative numerical
Grothendieck groups and any other quotient in which the relation subgroup must
first be saturated.  It belongs in the algebra layer: neither the saturation
nor its universal property depends on geometry or K-theory.
-/

namespace AddSubgroup

variable {A B : Type*} [AddCommGroup A]

/-- The saturation of an additive subgroup: an element belongs when a nonzero
natural multiple of it belongs to the original subgroup. -/
def saturation (H : AddSubgroup A) : AddSubgroup A where
  carrier := {x | ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ H}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro x y ⟨m, hm, hmx⟩ ⟨n, hn, hny⟩
    refine ⟨m * n, Nat.mul_ne_zero hm hn, ?_⟩
    rw [nsmul_add, mul_nsmul, Nat.mul_comm, mul_nsmul]
    exact H.add_mem (H.nsmul_mem hmx n) (H.nsmul_mem hny m)
  neg_mem' := by
    rintro x ⟨n, hn, hnx⟩
    exact ⟨n, hn, by simpa using H.neg_mem hnx⟩

@[simp]
theorem mem_saturation (H : AddSubgroup A) (x : A) :
    x ∈ H.saturation ↔ ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ H :=
  Iff.rfl

/-- The original subgroup is contained in its saturation. -/
theorem le_saturation (H : AddSubgroup A) : H ≤ H.saturation := by
  intro x hx
  exact ⟨1, one_ne_zero, H.nsmul_mem hx 1⟩

/-- The saturation is the least saturated subgroup containing the original
subgroup. -/
theorem saturation_le {H K : AddSubgroup A} (hHK : H ≤ K)
    (hK : K.NSMulSaturated) : H.saturation ≤ K := by
  rintro x ⟨n, hn, hnx⟩
  exact (hK (hHK hnx)).resolve_left hn

/-- Saturating a subgroup produces a saturated subgroup. -/
theorem saturation_nsmulSaturated (H : AddSubgroup A) :
    H.saturation.NSMulSaturated := by
  intro n x hnx
  rcases hnx with ⟨m, hm, hmnx⟩
  by_cases hn : n = 0
  · exact Or.inl hn
  · refine Or.inr ⟨n * m, Nat.mul_ne_zero hn hm, ?_⟩
    rw [mul_nsmul]
    exact hmnx

@[simp]
theorem saturation_eq_self {H : AddSubgroup A} (hH : H.NSMulSaturated) :
    H.saturation = H :=
  le_antisymm (saturation_le le_rfl hH) H.le_saturation

/-- The quotient by the saturation of a subgroup. -/
abbrev SaturatedQuotient (H : AddSubgroup A) := A ⧸ H.saturation

/-- Quotienting by a saturated subgroup removes all additive torsion. -/
instance saturatedQuotient_isAddTorsionFree (H : AddSubgroup A) :
    IsAddTorsionFree H.SaturatedQuotient where
  nsmul_right_injective n hn x y hxy := by
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
        change n • (x : A ⧸ H.saturation) = n • (y : A ⧸ H.saturation) at hxy
        change (x : A ⧸ H.saturation) = (y : A ⧸ H.saturation)
        rw [← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_nsmul,
          QuotientAddGroup.eq_iff_sub_mem, ← nsmul_sub] at hxy
        rw [QuotientAddGroup.eq_iff_sub_mem]
        exact (H.saturation_nsmulSaturated hxy).resolve_left hn

/-- The canonical map to the saturated quotient. -/
def saturatedQuotientMk (H : AddSubgroup A) : A →+ H.SaturatedQuotient :=
  QuotientAddGroup.mk' H.saturation

@[simp]
theorem saturatedQuotientMk_eq_zero_iff (H : AddSubgroup A) (x : A) :
    H.saturatedQuotientMk x = 0 ↔ x ∈ H.saturation :=
  QuotientAddGroup.eq_zero_iff x

/-- A map to a torsion-free group which kills the original subgroup factors
through the saturated quotient. -/
def saturatedQuotientLift [AddCommGroup B] [IsAddTorsionFree B]
    (H : AddSubgroup A) (f : A →+ B) (hf : H ≤ f.ker) :
    H.SaturatedQuotient →+ B :=
  QuotientAddGroup.lift H.saturation f
    (H.saturation_le hf (AddSubmonoid.ker_saturated f))

@[simp]
theorem saturatedQuotientLift_mk [AddCommGroup B] [IsAddTorsionFree B]
    (H : AddSubgroup A) (f : A →+ B) (hf : H ≤ f.ker) (x : A) :
    H.saturatedQuotientLift f hf (H.saturatedQuotientMk x) = f x :=
  rfl

/-- An additive homomorphism carrying one relation subgroup into another
induces a homomorphism of saturated quotients. -/
def saturatedQuotientMap [AddCommGroup B]
    (H : AddSubgroup A) (K : AddSubgroup B) (f : A →+ B)
    (hf : H ≤ K.comap f) : H.SaturatedQuotient →+ K.SaturatedQuotient :=
  QuotientAddGroup.map H.saturation K.saturation f <| by
    rintro x ⟨n, hn, hnx⟩
    exact ⟨n, hn, by simpa using hf hnx⟩

@[simp]
theorem saturatedQuotientMap_mk [AddCommGroup B]
    (H : AddSubgroup A) (K : AddSubgroup B) (f : A →+ B)
    (hf : H ≤ K.comap f) (x : A) :
    H.saturatedQuotientMap K f hf (H.saturatedQuotientMk x) =
      K.saturatedQuotientMk (f x) :=
  rfl

/-- Maps out of a saturated quotient are determined on representatives. -/
@[ext]
theorem saturatedQuotientHom_ext [AddCommGroup B]
    {H : AddSubgroup A} {f g : H.SaturatedQuotient →+ B}
    (h : f.comp H.saturatedQuotientMk = g.comp H.saturatedQuotientMk) :
    f = g :=
  QuotientAddGroup.addMonoidHom_ext H.saturation h

@[simp]
theorem saturatedQuotientMap_id (H : AddSubgroup A) :
    H.saturatedQuotientMap H (AddMonoidHom.id A) (by simp) =
      AddMonoidHom.id H.SaturatedQuotient := by
  apply saturatedQuotientHom_ext
  ext x
  rfl

/-- Saturated-quotient maps preserve composition. -/
theorem saturatedQuotientMap_comp {C : Type*} [AddCommGroup B] [AddCommGroup C]
    (H : AddSubgroup A) (K : AddSubgroup B) (L : AddSubgroup C)
    (f : A →+ B) (g : B →+ C) (hf : H ≤ K.comap f) (hg : K ≤ L.comap g) :
    (K.saturatedQuotientMap L g hg).comp (H.saturatedQuotientMap K f hf) =
      H.saturatedQuotientMap L (g.comp f) (by
        intro x hx
        exact hg (hf hx)) := by
  apply saturatedQuotientHom_ext
  ext x
  rfl

end AddSubgroup

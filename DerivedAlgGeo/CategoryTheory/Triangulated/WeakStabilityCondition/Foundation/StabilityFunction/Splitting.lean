/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.Cutoff
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.Truncation

/-!
# The splitting at a phase cutoff

`Cutoff.lean` cuts two classes out of the category by a number `β` and proves
that no map runs from the first to the second.  This file supplies the other
half of a torsion pair: **every object is an extension of an object of `F β` by
an object of `T β`.**

The object is cut where its own phases cross `β`.  The phases strictly
decrease, so the indices whose phase exceeds `β` form an initial segment
`0, …, k-1`; `exists_crossIndex` names its length `k`.  Cutting the chain there
gives

* `F.chain k`, filtered by `restrict`, whose phases are `φ₀, …, φ_{k-1}` — all
  above `β`;
* `E / F.chain k`, filtered by `tailAt`, whose phases are `φ_k, …, φ_{n-1}` —
  all at or below `β`.

The two boundary cases are not special pleading: at `k = 0` the sub is `⊥` and
at `k = n` the quotient is the cokernel of an isomorphism, so in each the
missing half is zero and lands in both classes by `isZero_mem_*`.  `restrict`
covers `k = n` and `tailAt` covers `k = 0`, so no other case is needed.

`hnTors_of_iso` and `hnFree_of_iso` are here because a torsion pair asks for
classes closed under isomorphism, which is `AbelianHNFiltration.ofIso`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AbelianHNFiltration

/-- **The crossing index.**  The HN phases strictly decrease, so the indices
whose phase exceeds `β` are an initial segment; this names its length. -/
theorem exists_crossIndex {Z : StabilityFunction A} {E : A}
    (F : AbelianHNFiltration Z E) (β : ℝ) :
    ∃ k ≤ F.n, (∀ j : Fin F.n, j.val < k → β < F.phase j) ∧
      (∀ j : Fin F.n, k ≤ j.val → F.phase j ≤ β) := by
  classical
  by_cases hex : ∃ m : ℕ, ∃ hm : m < F.n, F.phase ⟨m, hm⟩ ≤ β
  · obtain ⟨hlt, hle⟩ := Nat.find_spec hex
    refine ⟨Nat.find hex, le_of_lt hlt, ?_, ?_⟩
    · intro j hj
      by_contra hcon
      exact Nat.find_min hex hj ⟨j.isLt, by simpa using not_lt.mp hcon⟩
    · intro j hj
      exact le_trans (F.phase_strictAnti.antitone (Fin.le_def.mpr hj)) hle
  · refine ⟨F.n, le_rfl, ?_, ?_⟩
    · intro j _
      by_contra hcon
      exact hex ⟨j.val, j.isLt, by simpa using not_lt.mp hcon⟩
    · intro j hj
      exact absurd j.isLt (not_lt.mpr hj)

end AbelianHNFiltration

namespace StabilityFunction

variable {Z : StabilityFunction A} {β : ℝ}

/-- The torsion class is closed under isomorphism. -/
theorem hnTors_of_iso {E E' : A} (e : E ≅ E') (h : E ∈ hnTors Z β) :
    E' ∈ hnTors Z β := by
  rcases h with h0 | ⟨F, hF⟩
  · exact Or.inl (h0.of_iso e.symm)
  · exact Or.inr ⟨F.ofIso e, by simpa using hF⟩

/-- The torsion-free class is closed under isomorphism. -/
theorem hnFree_of_iso {E E' : A} (e : E ≅ E') (h : E ∈ hnFree Z β) :
    E' ∈ hnFree Z β := by
  rcases h with h0 | ⟨F, hF⟩
  · exact Or.inl (h0.of_iso e.symm)
  · exact Or.inr ⟨F.ofIso e, by simpa using hF⟩

/-- **The splitting.**  Every object has a subobject in `T β` whose cokernel is
in `F β`, obtained by cutting an HN filtration at its crossing index. -/
theorem exists_subobject_hnTors_cokernel_hnFree (hHN : Z.HasHNProperty)
    (E : A) :
    ∃ T : Subobject E,
      ((T : A) ∈ hnTors Z β) ∧ (cokernel T.arrow ∈ hnFree Z β) := by
  by_cases hE : IsZero E
  · exact ⟨⊥, Or.inl ((subobject_isZero_iff_eq_bot (⊥ : Subobject E)).2 rfl),
      Or.inl (IsZero.of_epi_eq_zero (cokernel.π (⊥ : Subobject E).arrow)
        (hE.eq_zero_of_src _))⟩
  obtain ⟨F⟩ := hHN E hE
  obtain ⟨k, hkn, hlow, hhigh⟩ := F.exists_crossIndex β
  refine ⟨F.chain ⟨k, by lia⟩, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Or.inl ((subobject_isZero_iff_eq_bot _).2 F.chain_bot)
    · refine Or.inr ⟨F.restrict k hk hkn, ?_⟩
      rw [F.restrict_phiMinus k hk hkn]
      exact hlow ⟨k - 1, by lia⟩ (by lia)
  · rcases eq_or_lt_of_le hkn with rfl | hklt
    · refine Or.inl ?_
      haveI : Epi (F.chain ⟨F.n, by lia⟩).arrow := by
        rw [show F.chain ⟨F.n, by lia⟩ = ⊤ from F.chain_top]
        infer_instance
      exact isZero_cokernel_of_epi _
    · refine Or.inr ⟨F.tailAt k hklt, ?_⟩
      rw [F.tailAt_phiPlus k hklt]
      exact hhigh ⟨k, hklt⟩ le_rfl

/-- The splitting as a short exact sequence with the given object in the
middle. -/
theorem exists_shortExact_hnTors_hnFree (hHN : Z.HasHNProperty) (E : A) :
    ∃ (T Q : A) (i : T ⟶ E) (p : E ⟶ Q) (w : i ≫ p = 0),
      T ∈ hnTors Z β ∧ Q ∈ hnFree Z β ∧ (ShortComplex.mk i p w).ShortExact := by
  obtain ⟨T, hT, hQ⟩ := exists_subobject_hnTors_cokernel_hnFree hHN (β := β) E
  exact ⟨(T : A), cokernel T.arrow, T.arrow, cokernel.π T.arrow,
    cokernel.condition _, hT, hQ, shortExact_of_mono T.arrow⟩

end StabilityFunction

end CategoryTheory.Triangulated

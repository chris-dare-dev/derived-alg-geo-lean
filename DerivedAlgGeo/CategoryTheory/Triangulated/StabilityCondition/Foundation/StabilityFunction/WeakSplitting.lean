/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.WeakTail

/-!
# The splitting at a weak slope cutoff

`WeakCutoff.lean` cuts two classes out of an abelian category by a slope `μ₀ : WithTop ℝ` and
proves that no map runs from the first to the second.  This file supplies the other half of a
torsion pair: **every object is an extension of an object of `F μ₀` by an object of `T μ₀`.**

The object is cut where its own slopes cross `μ₀`.  The slopes strictly decrease, so the indices
whose slope exceeds `μ₀` form an initial segment; `exists_crossIndex` (#789) names its length
`k`.  Cutting the chain there gives

* `F.chain k`, filtered by `restrict` (#789), whose slopes are all above `μ₀`;
* `E / F.chain k`, filtered by `tailAt` (`WeakTail.lean`), whose slopes are all at or below it.

The two boundary cases are not special pleading: at `k = 0` the sub is `⊥`, at `k = n` the
quotient is the cokernel of an isomorphism, and in each the missing half is zero and lands in
both classes by `isZero_mem_*`.

## What this completes

`WeakTruncation.lean` shipped `exists_subobject_hnTors` — the torsion **subobject** alone —
and said explicitly that the torsion-free quotient was unavailable because `tailAt` did not
port.  It does now, so the honest half-statement is superseded by the full one here, and the
weak `TorsionPair` follows in `Weak/Tilting/TorsionPair/WeakStabilityFunction.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace WeakStabilityFunctionOn

variable {W : WeakStabilityFunctionOn (abelianDatum A)} {μ₀ : WithTop ℝ}

/-- **The splitting.**  Every object has a subobject in `T μ₀` whose cokernel is in `F μ₀`,
obtained by cutting a weak HN filtration at its crossing index. -/
theorem exists_subobject_hnTors_cokernel_hnFree (hHN : W.HasHNProperty) (E : A) :
    ∃ T : Subobject E,
      ((T : A) ∈ hnTors W μ₀) ∧ (cokernel T.arrow ∈ hnFree W μ₀) := by
  by_cases hE : IsZero E
  · exact ⟨⊥,
      Or.inl ((StabilityFunction.subobject_isZero_iff_eq_bot (⊥ : Subobject E)).2 rfl),
      Or.inl (IsZero.of_epi_eq_zero (cokernel.π (⊥ : Subobject E).arrow)
        (hE.eq_zero_of_src _))⟩
  obtain ⟨F⟩ := hHN E hE
  obtain ⟨k, hkn, hlow, hhigh⟩ := F.exists_crossIndex μ₀
  refine ⟨F.chain ⟨k, by lia⟩, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Or.inl ((StabilityFunction.subobject_isZero_iff_eq_bot _).2 F.chain_bot)
    · refine Or.inr ⟨F.restrict k hk hkn, ?_⟩
      rw [F.restrict_μMinus k hk hkn]
      exact hlow ⟨k - 1, by lia⟩ (by lia)
  · rcases eq_or_lt_of_le hkn with rfl | hklt
    · refine Or.inl ?_
      haveI : Epi (F.chain ⟨F.n, by lia⟩).arrow := by
        rw [show F.chain ⟨F.n, by lia⟩ = ⊤ from F.chain_top]
        infer_instance
      exact isZero_cokernel_of_epi _
    · refine Or.inr ⟨F.tailAt k hklt, ?_⟩
      rw [F.tailAt_μPlus k hklt]
      exact hhigh ⟨k, hklt⟩ le_rfl

/-- The splitting as a short exact sequence with the given object in the middle. -/
theorem exists_shortExact_hnTors_hnFree (hHN : W.HasHNProperty) (E : A) :
    ∃ (T Q : A) (i : T ⟶ E) (p : E ⟶ Q) (w : i ≫ p = 0),
      T ∈ hnTors W μ₀ ∧ Q ∈ hnFree W μ₀ ∧ (ShortComplex.mk i p w).ShortExact := by
  obtain ⟨T, hT, hQ⟩ :=
    exists_subobject_hnTors_cokernel_hnFree (μ₀ := μ₀) hHN E
  exact ⟨(T : A), cokernel T.arrow, T.arrow, cokernel.π T.arrow,
    cokernel.condition _, hT, hQ, StabilityFunction.shortExact_of_mono T.arrow⟩

end WeakStabilityFunctionOn

end CategoryTheory.Triangulated

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.RingTheory.KrullAkizuki
import DerivedAlgGeo.RingTheory.LocalRing.LocalSubring
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Domination of local subrings by discrete valuation rings

Mathlib's `LocalSubring.exists_le_valuationSubring` (Stacks 00IA) dominates a local subring of a
field by a valuation subring. This file refines it (Stacks 00PH): a Noetherian local subring that
is not a field is dominated by a *discrete* valuation subring, with the field as fraction field, as
soon as the subring and finitely many elements generate the field.

## Main results

* `LocalSubring.exists_le_valuationSubring_dvr`: Stacks 00PH for local subrings.
* `exists_dvr_dominating`: Stacks 00PH for a Noetherian local domain and a finitely generated
  extension of its fraction field.

## Implementation notes

The valuation subring of Stacks 00IA need not be Noetherian. One first dominates the subring by a
one-dimensional Noetherian local subring `B` with the whole field as fraction field
(`LocalSubring.exists_le_ringKrullDim_eq_one_of_closure_eq_top`), then dominates `B` by a valuation
subring `V`. Krull--Akizuki (Stacks 00PG with `L = K`) makes `V` Noetherian, so `V` is a discrete
valuation ring. In particular, no transcendence basis and no finite extension of the fraction field
is needed.

## References

* [Stacks: Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
* [Stacks: Tag 00P8](https://stacks.math.columbia.edu/tag/00P8)
* [Stacks: Tag 00PG](https://stacks.math.columbia.edu/tag/00PG)

## Tags

local subring, domination, discrete valuation ring, valuation subring
-/

universe u

open IsLocalRing

namespace LocalSubring

variable {K : Type u} [Field K]

/-- **Stacks 00PH** for local subrings. A Noetherian local subring `A` of a field `K` that is not
itself a field, and that together with finitely many elements generates `K` as a field, is
dominated by a valuation subring of `K` that is a discrete valuation ring. -/
@[stacks 00PH]
theorem exists_le_valuationSubring_dvr (A : LocalSubring K) [IsNoetherianRing A.toSubring]
    (hA : ¬ IsField A.toSubring) (s : Finset K)
    (hs : Subfield.closure ((A.toSubring : Set K) ∪ s) = ⊤) :
    ∃ V : ValuationSubring K, A ≤ V.toLocalSubring ∧ IsDiscreteValuationRing V := by
  obtain ⟨B, hAB, hBN, hBdim, hBfr, -⟩ :=
    A.exists_le_ringKrullDim_eq_one_of_closure_eq_top hA s hs
  obtain ⟨V, hBV⟩ := B.exists_le_valuationSubring
  have : Ring.KrullDimLE 1 B.toSubring := Ring.krullDimLE_iff.mpr (by rw [hBdim]; rfl)
  have hVN : IsNoetherianRing V :=
    IsNoetherianRing.of_le_of_krullDimLE_one B.toSubring V.toSubring (toSubring_mono hBV)
  -- `V` is not a field, since it dominates the one-dimensional `B`.
  have hVf : ¬ IsField V := by
    intro hF
    let := hF.toField
    have hm : maximalIdeal B.toSubring ≠ ⊥ := fun h ↦ by
      have := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr h)
      rw [hBdim] at this
      exact one_ne_zero this
    obtain ⟨b, hb, hb0⟩ := (Submodule.ne_bot_iff _).mp hm
    have : IsUnit (Subring.inclusion (toSubring_mono hBV) b) :=
      isUnit_iff_ne_zero.mpr fun h ↦ hb0 (Subtype.ext (congr_arg (fun x : V ↦ (x : K)) h))
    exact (mem_maximalIdeal b).mp hb (hBV.2.map_nonunit _ this)
  have hVR : ValuationRing V := inferInstance
  exact ⟨V, hAB.trans hBV, ((IsDiscreteValuationRing.TFAE V hVf).out 2 1).mp hVR⟩

end LocalSubring

/-- **Stacks 00PH.** Let `A` be a Noetherian local domain that is not a field, with fraction
field `K`, and let `L` be a finitely generated field extension of `K`. Then a discrete valuation
ring with fraction field `L` dominates `A`.

No Japanese or Nagata hypothesis on `A` is assumed, so the discrete valuation ring need not be
essentially of finite type over `A`; see `exists_dvr_dominating_essFiniteType` for the universally
Japanese case, where it is, and Stacks Example 10.162.17 (Tag 09E1) for a Noetherian local domain
where it cannot be.

The hypotheses are all needed:
* `¬ IsField A`. For `A = K = L` a field, a discrete valuation ring with fraction field `L` that
  contains `L` is `L`, which is not one.
* Noetherianity. Take for `A` a valuation ring of rank one with value group `ℚ`, and `L = K`. A
  discrete valuation ring dominating `A` is a valuation subring dominating `A`, so equals `A` by
  maximality (`ValuationSubring.isMax_toLocalSubring`), but `A` is not Noetherian.
* `Algebra.EssFiniteType K L`. Take `A = ℤ_(p)`, `K = ℚ` and `L = ℚ̄`: every valuation of `ℚ̄`
  has a divisible value group, so no discrete valuation ring has fraction field `ℚ̄`. -/
@[stacks 00PH]
theorem exists_dvr_dominating {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : ¬ IsField A) (K : Type*) (L : Type u) [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra.EssFiniteType K L] :
    ∃ V : ValuationSubring L, LocalSubring.range (algebraMap A L) ≤ V.toLocalSubring ∧
      IsDiscreteValuationRing V := by
  have hf : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  let A' := LocalSubring.range (algebraMap A L)
  let e : A ≃+* A'.toSubring := RingEquiv.ofBijective
    ((algebraMap A L).codRestrict A'.toSubring fun a ↦ ⟨a, rfl⟩)
    ⟨fun a b h ↦ hf (congr_arg Subtype.val h), fun ⟨_, a, rfl⟩ ↦ ⟨a, rfl⟩⟩
  have : IsNoetherianRing A'.toSubring := isNoetherianRing_of_ringEquiv A e
  have hA' : ¬ IsField A'.toSubring := fun h ↦ hA (MulEquiv.isField h e.toMulEquiv)
  have hs :
      Subfield.closure ((A'.toSubring : Set L) ∪ Algebra.EssFiniteType.finset K L) = ⊤ := by
    refine Subfield.eq_top_of_essFiniteType K _ (fun k ↦ ?_)
      (Set.subset_union_right.trans Subfield.subset_closure)
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) k
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact div_mem (Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      (Subfield.subset_closure (Or.inl ⟨b, rfl⟩))
  exact A'.exists_le_valuationSubring_dvr hA' _ hs

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Domination by one-dimensional Noetherian local rings

This file extends Mathlib's domination order on `LocalSubring` (Stacks 00I9) with Stacks
Lemma 10.119.1: a Noetherian local subring of a field that is not a field is dominated by a
one-dimensional Noetherian local subring that is essentially of finite type over it. When
finitely many elements generate the field together with the subring, the dominating subring can be
taken to have the whole field as fraction field.

## Main definitions

None: the file adds a theorem about Mathlib's `LocalSubring` and its domination order.

## Main results

* `LocalSubring.exists_le_ringKrullDim_eq_one`: Stacks 00P8.
* `LocalSubring.exists_le_ringKrullDim_eq_one_of_closure_eq_top`: Stacks 00P8 with prescribed
  fraction field.

## Implementation notes

The proof follows Stacks. A valuation subring `V` dominating `A` orders the generators of the
maximal ideal of `A`; dividing by a generator `x` of largest valuation gives a finitely generated
`A`-subalgebra `S ⊆ V` in which `𝔪_A ⊆ x S`. Since `x` is not a unit of `V`, it is not a unit of
`S`, and the localization of `S` at a minimal prime over `x S` has dimension one by Krull's
principal ideal theorem.

## References

* [Stacks: Tag 00P8](https://stacks.math.columbia.edu/tag/00P8)

## Tags

local subring, domination, Krull dimension, Noetherian local ring
-/

universe u

open IsLocalRing
open scoped nonZeroDivisors

section FractionRing

variable {L : Type u} [Field L]

/-- A subring of a field that contains a subring with fraction field `L` has fraction field `L`. -/
theorem Subring.isFractionRing_of_le {D B : Subring L} (h : D ≤ B)
    [IsFractionRing D L] : IsFractionRing B L where
  map_units b := IsUnit.mk0 _ fun h0 ↦ nonZeroDivisors.coe_ne_zero b (Subtype.ext h0)
  surj z := by
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj D⁰ z
    refine ⟨⟨Subring.inclusion h x,
      ⟨Subring.inclusion h y, mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ?_⟩⟩, hxy⟩
    exact nonZeroDivisors.coe_ne_zero y (Subtype.ext (congr_arg (fun b : B ↦ (b : L)) h0))
  exists_of_eq h := ⟨1, by simpa using Subtype.ext h⟩

/-- A subring of a field that generates it as a field has the field as fraction field. -/
theorem Subring.isFractionRing_of_closure_eq_top (D : Subring L)
    (hD : Subfield.closure (D : Set L) = ⊤) : IsFractionRing D L where
  map_units b := IsUnit.mk0 _ fun h0 ↦ nonZeroDivisors.coe_ne_zero b (Subtype.ext h0)
  surj z := by
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      Subfield.mem_closure_iff.mp (by rw [hD]; exact Subfield.mem_top z)
    rw [Subring.closure_eq] at hx hy
    by_cases hy0 : y = 0
    · exact ⟨⟨0, 1⟩, by simp [hy0]⟩
    · refine ⟨⟨⟨x, hx⟩, ⟨⟨y, hy⟩, mem_nonZeroDivisors_of_ne_zero fun h ↦
        hy0 (congr_arg Subtype.val h)⟩⟩, ?_⟩
      show x / y * y = x
      exact div_mul_cancel₀ x hy0
  exists_of_eq h := ⟨1, by simpa using Subtype.ext h⟩

/-- A subfield of a finitely generated field extension of `K` that contains `K` and the chosen
generators is everything. -/
theorem Subfield.eq_top_of_essFiniteType (K : Type*) [Field K] [Algebra K L]
    [Algebra.EssFiniteType K L] (F : Subfield L) (hK : ∀ k, algebraMap K L k ∈ F)
    (hs : (Algebra.EssFiniteType.finset K L : Set L) ⊆ F) : F = ⊤ := by
  have hsub : Algebra.EssFiniteType.subalgebra K L ≤ (F.toIntermediateField hK).toSubalgebra :=
    Algebra.adjoin_le hs
  rw [eq_top_iff]
  intro l _
  obtain ⟨⟨x, y⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.EssFiniteType.submonoid K L) l
  have h1 := IsLocalization.mk'_spec L x y
  rw [← eq_div_iff (IsLocalization.map_units L y).ne_zero] at h1
  change IsLocalization.mk' L x y ∈ F
  rw [h1]
  exact div_mem (hsub x.2) (hsub (y : Algebra.EssFiniteType.subalgebra K L).2)

end FractionRing

namespace LocalSubring

variable {K : Type u} [Field K]

/-- **Stacks 00P8.** A Noetherian local subring `A` of a field that is not itself a field is
dominated by a Noetherian local subring `B` of dimension one, and the inclusion `A → B` is
essentially of finite type. -/
@[stacks 00P8]
theorem exists_le_ringKrullDim_eq_one (A : LocalSubring K) [IsNoetherianRing A.toSubring]
    (hA : ¬ IsField A.toSubring) :
    ∃ (B : LocalSubring K) (h : A ≤ B), IsNoetherianRing B.toSubring ∧
      ringKrullDim B.toSubring = 1 ∧ (Subring.inclusion (toSubring_mono h)).EssFiniteType := by
  classical
  set R := A.toSubring
  obtain ⟨V, hV⟩ := A.exists_le_valuationSubring
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  have hm : maximalIdeal R ≠ ⊥ := fun h ↦ hA (isField_iff_maximalIdeal_eq.mpr h)
  obtain ⟨y₀, hy₀s, hy₀⟩ : ∃ y ∈ s, y ≠ 0 := by
    by_contra! H
    exact hm (hs ▸ Ideal.span_eq_bot.mpr fun y hy ↦ H y hy)
  obtain ⟨x, hxs, hxmax⟩ :=
    s.exists_max_image (fun y : R ↦ V.valuation (y : K)) ⟨y₀, hy₀s⟩
  have hx0 : (x : K) ≠ 0 := by
    intro h
    have h₀ := hxmax y₀ hy₀s
    rw [h, map_zero] at h₀
    exact hy₀ (Subtype.ext ((Valuation.zero_iff _).mp (le_antisymm h₀ zero_le)))
  have hxm : x ∈ maximalIdeal R := hs ▸ Ideal.subset_span hxs
  have hgenV : ∀ y ∈ s, (y : K) / x ∈ V := by
    intro y hy
    rw [← V.valuation_le_one_iff, map_div₀,
      div_le_one₀ (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hx0))]
    exact hxmax y hy
  let S : Subalgebra R K := Algebra.adjoin R ↑(s.image fun y : R ↦ (y : K) / x)
  have hRS : R ≤ S.toSubring := fun r hr ↦ S.algebraMap_mem ⟨r, hr⟩
  have hgenS : ∀ y ∈ s, (y : K) / x ∈ S :=
    fun y hy ↦ Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hy))
  have hSV : S.toSubring ≤ V.toSubring := by
    rw [Algebra.adjoin_eq_ring_closure, Subring.closure_le]
    rintro _ (⟨r, rfl⟩ | hz)
    · exact hV.1 r.2
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact hgenV y hy
  have : Algebra.FiniteType R S :=
    (Subalgebra.fg_iff_finiteType S).mp (Subalgebra.fg_adjoin_finset _)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have : IsNoetherianRing S.toSubring := ‹IsNoetherianRing S›
  let x' : S.toSubring := Subring.inclusion hRS x
  have hx'0 : x' ≠ 0 := fun h ↦ hx0 congr(($h : K))
  have hx' : ¬ IsUnit x' := by
    intro hu
    have hu' : IsUnit (Subring.inclusion hV.1 x) := hu.map (Subring.inclusion hSV)
    exact (mem_maximalIdeal x).mp hxm (hV.2.map_nonunit _ hu')
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal (Ideal.span {x'})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le (J := M) hxM
  have : q.IsPrime := hq.1.1
  have hmq : (maximalIdeal R).map (Subring.inclusion hRS) ≤ q := by
    refine le_trans ?_ hq.1.2
    rw [← hs, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_span_singleton']
    exact ⟨⟨(y : K) / x, hgenS y hy⟩, Subtype.ext (div_mul_cancel₀ _ hx0)⟩
  let B := ofPrime S.toSubring q
  have hRB : R ≤ B.toSubring := hRS.trans (le_ofPrime _ q)
  have hcomp : Subring.inclusion hRB =
      (algebraMap S.toSubring B.toSubring).comp (Subring.inclusion hRS) := rfl
  have hAB : A ≤ B := by
    refine ⟨hRB, ⟨fun a ha ↦ ?_⟩⟩
    by_contra hna
    rw [hcomp, RingHom.comp_apply, IsLocalization.AtPrime.isUnit_to_map_iff _ q] at ha
    exact ha (hmq (Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).mpr hna)))
  refine ⟨B, hAB, IsLocalization.isNoetherianRing q.primeCompl _ inferInstance, ?_, ?_⟩
  · have hht : q.height = 1 := by
      refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq) ?_
      rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro hbot
      have hxq : x' ∈ q := hq.1.2 (Ideal.mem_span_singleton_self x')
      rw [hbot, Ideal.mem_bot] at hxq
      exact hx'0 hxq
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q B.toSubring, hht]
    rfl
  · change (Subring.inclusion hRB).EssFiniteType
    rw [hcomp]
    refine RingHom.EssFiniteType.comp ?_ ?_
    · exact RingHom.FiniteType.essFiniteType
        ((RingHom.finiteType_algebraMap (A := R) (B := S)).mpr inferInstance)
    · exact RingHom.essFiniteType_algebraMap.mpr
        (Algebra.EssFiniteType.of_isLocalization _ q.primeCompl)

/-- **Stacks 00P8 with prescribed fraction field.** Let `A` be a Noetherian local subring of a
field `L` that is not itself a field, and suppose `A` together with finitely many elements
generates `L` as a field. Then `A` is dominated by a one-dimensional Noetherian local subring `B`
with fraction field `L`, and `A → B` is essentially of finite type.

The proof adjoins to `A` the generators, or their inverses, that a valuation subring dominating `A`
contains. This gives a finitely generated `A`-algebra `D` with fraction field `L`; one localizes it
at the centre of that valuation subring and applies `exists_le_ringKrullDim_eq_one`. -/
theorem exists_le_ringKrullDim_eq_one_of_closure_eq_top (A : LocalSubring K)
    [IsNoetherianRing A.toSubring] (hA : ¬ IsField A.toSubring) (s : Finset K)
    (hs : Subfield.closure ((A.toSubring : Set K) ∪ s) = ⊤) :
    ∃ (B : LocalSubring K) (h : A ≤ B), IsNoetherianRing B.toSubring ∧
      ringKrullDim B.toSubring = 1 ∧ IsFractionRing B.toSubring K ∧
        (Subring.inclusion (toSubring_mono h)).EssFiniteType := by
  classical
  obtain ⟨V, hAW⟩ := A.exists_le_valuationSubring
  set W := V.toLocalSubring
  -- A finitely generated `A`-subalgebra `D ⊆ V` with fraction field `K`.
  let zs : Finset K := s.image fun z ↦ if z ∈ V then z else z⁻¹
  let D : Subalgebra A.toSubring K := Algebra.adjoin A.toSubring (zs : Set K)
  have hAD : A.toSubring ≤ D.toSubring := fun a ha ↦
    D.algebraMap_mem (⟨a, ha⟩ : A.toSubring)
  have hDW : D.toSubring ≤ W.toSubring := by
    rw [Algebra.adjoin_eq_ring_closure, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | hz)
    · exact toSubring_mono hAW a.2
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hz
      split_ifs with h
      · exact h
      · exact (V.mem_or_inv_mem z).resolve_left h
  have hD : Subfield.closure (D.toSubring : Set K) = ⊤ := by
    rw [eq_top_iff, ← hs, Subfield.closure_le]
    rintro z (hz | hz)
    · exact Subfield.subset_closure (hAD hz)
    · by_cases hzV : z ∈ V
      · exact Subfield.subset_closure
          (Algebra.subset_adjoin (Finset.mem_image.mpr ⟨z, hz, ite_eq_left hzV⟩))
      · have : z⁻¹ ∈ Subfield.closure (D.toSubring : Set K) := Subfield.subset_closure
          (Algebra.subset_adjoin (Finset.mem_image.mpr ⟨z, hz, ite_eq_right hzV⟩))
        simpa using inv_mem this
  have : IsFractionRing D.toSubring K := Subring.isFractionRing_of_closure_eq_top _ hD
  have : Algebra.FiniteType A.toSubring D :=
    (Subalgebra.fg_iff_finiteType D).mp (Subalgebra.fg_adjoin_finset zs)
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A.toSubring D
  have : IsNoetherianRing D.toSubring := ‹IsNoetherianRing D›
  -- Its localization `Dp` at the centre of `V`.
  let p : Ideal D.toSubring := (maximalIdeal W.toSubring).comap (Subring.inclusion hDW)
  let Dp := ofPrime D.toSubring p
  have hDDp : D.toSubring ≤ Dp.toSubring := le_ofPrime _ _
  have : IsNoetherianRing Dp.toSubring := IsLocalization.isNoetherianRing p.primeCompl _ ‹_›
  obtain ⟨hAW', hAWloc⟩ := hAW
  have hADp : A ≤ Dp := by
    refine ⟨hAD.trans hDDp, ⟨fun a ha ↦ ?_⟩⟩
    by_contra hna
    have hp : Subring.inclusion hAD a ∈ p :=
      (mem_maximalIdeal _).mpr fun h ↦ hna (isUnit_of_map_unit (Subring.inclusion hAW') a h)
    exact (IsLocalization.AtPrime.isUnit_to_map_iff Dp.toSubring p _).mp ha hp
  have hDpf : ¬ IsField Dp.toSubring := by
    intro hF
    let := hF.toField
    obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp ((isField_iff_maximalIdeal_eq).not.mp hA)
    obtain ⟨hADp', hADploc⟩ := hADp
    have : IsUnit (Subring.inclusion hADp' a) :=
      isUnit_iff_ne_zero.mpr fun h ↦
        ha0 (Subtype.ext (congr_arg (fun x : Dp.toSubring ↦ (x : K)) h))
    exact (mem_maximalIdeal a).mp ha (isUnit_of_map_unit _ a this)
  -- Stacks 00P8 gives a one-dimensional Noetherian local `B` dominating `Dp`.
  obtain ⟨B, hDpB, hBN, hBdim, hBeft⟩ := Dp.exists_le_ringKrullDim_eq_one hDpf
  have hAB : A.toSubring ≤ B.toSubring :=
    (hAD.trans hDDp).trans (toSubring_mono hDpB)
  have hADeft : (Subring.inclusion hAD).EssFiniteType :=
    (RingHom.finiteType_algebraMap.mpr ‹Algebra.FiniteType A.toSubring D›).essFiniteType
  have hDDpeft : (Subring.inclusion hDDp).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.mpr (.of_isLocalization _ p.primeCompl)
  exact ⟨B, hADp.trans hDpB, hBN, hBdim,
    Subring.isFractionRing_of_le (hDDp.trans (toSubring_mono hDpB)),
    (hADeft.comp hDDpeft).comp hBeft⟩

end LocalSubring

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Domination by one-dimensional Noetherian local rings

This file extends Mathlib's domination order on `LocalSubring` (Stacks 00I9) with Stacks
Lemma 10.119.1: a Noetherian local subring of a field that is not a field is dominated by a
one-dimensional Noetherian local subring that is essentially of finite type over it.

## Main definitions

None: the file adds a theorem about Mathlib's `LocalSubring` and its domination order.

## Main results

* `LocalSubring.exists_le_ringKrullDim_eq_one`: Stacks 00P8.

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

end LocalSubring

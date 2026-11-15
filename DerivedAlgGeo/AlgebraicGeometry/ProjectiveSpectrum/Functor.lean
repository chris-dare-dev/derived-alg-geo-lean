/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# `Proj` of a surjective graded ring map is a closed immersion

Let `ψ : 𝒜 →+*ᵍ ℬ` be a surjective graded ring map. It carries the irrelevant ideal of `𝒜` onto
that of `ℬ`, so Mathlib's `Proj.map ψ : Proj ℬ ⟶ Proj 𝒜` is defined, and it is a closed
immersion (Stacks 01N0 (2)).

## Main definitions

This file introduces no new definitions.

## Main results

* `AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective`: `ℬ₊ ≤ 𝒜₊.map ψ` for surjective `ψ`.
* `AlgebraicGeometry.Proj.away_map_surjective`: on a chart `D₊(s)`, the ring map
  `HomogeneousLocalization.Away.map ψ s` is surjective.
* `AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective`: `Proj.map ψ h` is a closed
  immersion for every proof `h` of the irrelevant-ideal hypothesis.
* `AlgebraicGeometry.Proj.isClosedImmersion_map`: the same for the proof supplied by
  `irrelevant_le_map_of_surjective`.
* `AlgebraicGeometry.Proj.exists_comap_eq_of_ker_le`: every point of `V₊(ker ψ)` is in the image.

## Implementation notes

Being a closed immersion is local on the target, and the charts `D₊(s)` for homogeneous `s` of
positive degree cover `Proj 𝒜`. The preimage of `D₊(s)` is `D₊(ψ s)`, and through the chart
isomorphisms `basicOpenIsoSpec` the restricted map is `Spec` of `Away.map ψ s`
(`awayι_comp_map`), which is surjective because `ψ` is.

`Proj.map` asks only for `ℬ₊ ≤ 𝒜₊.map ψ`; surjectivity is used in the chart computation, not in
the morphism. So the closed-immersion statement is proved for an arbitrary proof of that
hypothesis and then specialized.

## References

* [Stacks, Lemma 27.11.3 (Tag 01N0)](https://stacks.math.columbia.edu/tag/01N0).
* EGA II 2.9.2.

## Tags

Proj, closed immersion, graded ring map, functoriality
-/

universe u

open CategoryTheory HomogeneousIdeal HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] [CommRing B]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (hψ : Function.Surjective ψ)

include hψ in
/-- A surjective graded ring map carries the irrelevant ideal onto the irrelevant ideal: a
homogeneous `b` of positive degree `i` is the image of the degree-`i` component of any preimage.
This is the hypothesis of Mathlib's `Proj.map`. -/
theorem irrelevant_le_map_of_surjective : ℬ₊ ≤ 𝒜₊.map ψ := by
  rw [← toIdeal_le_toIdeal_iff, toIdeal_map, toIdeal_irrelevant_le]
  intro i hi b hb
  obtain ⟨a, rfl⟩ := hψ b
  have h : ψ (DirectSum.decompose 𝒜 a i) = ψ a := by
    rw [map_directSumDecompose 𝒜 ℬ, DirectSum.decompose_of_mem_same ℬ hb]
  rw [← h]
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem 𝒜 hi (SetLike.coe_mem _))

include hψ in
/-- On the chart of a homogeneous `s`, the induced map of degree-zero localizations
`(A_s)₀ → (B_{ψ s})₀` is surjective: `b / (ψ s)ⁿ` is the image of `aₙ / sⁿ`, where `aₙ` is the
matching homogeneous component of a preimage of `b`. -/
theorem away_map_surjective (s : A) {i : ℕ} (hs : s ∈ 𝒜 i) :
    Function.Surjective (Away.map ψ s) := by
  intro y
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (ψ.map_mem hs) y
  obtain ⟨a, rfl⟩ := hψ b
  refine ⟨Away.mk 𝒜 hs n _ (SetLike.coe_mem (DirectSum.decompose 𝒜 a (n • i))), ?_⟩
  rw [Away.map_mk]
  congr 1
  rw [map_directSumDecompose 𝒜 ℬ, DirectSum.decompose_of_mem_same ℬ hb]

include hψ in
/-- **`Proj` of a surjective graded ring map is a closed immersion** (Stacks 01N0 (2)), for any
proof `h` of the hypothesis of `Proj.map`. On the chart `D₊(s)` the map is `Spec` of the
surjection `Away.map ψ s`. -/
theorem isClosedImmersion_map_of_surjective (h : ℬ₊ ≤ 𝒜₊.map ψ) :
    IsClosedImmersion (map ψ h) := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x ↦ ?_
  obtain ⟨i, hi, s, hs, hsx⟩ : ∃ i > 0, ∃ s ∈ 𝒜 i, s ∉ x.asHomogeneousIdeal := by
    by_contra! H
    exact x.not_irrelevant_le ((irrelevant_le _).mpr fun i hi s hs ↦ H i hi s hs)
  refine ⟨basicOpen 𝒜 s, hsx, ?_⟩
  have key : map ψ h ∣_ basicOpen 𝒜 s =
      (Scheme.isoOfEq _ (map_preimage_basicOpen ψ h s)).hom ≫
        (basicOpenIsoSpec ℬ (ψ s) (ψ.map_mem hs) hi).hom ≫
          Spec.map (CommRingCat.ofHom (Away.map ψ s)) ≫ (basicOpenIsoSpec 𝒜 s hs hi).inv := by
    refine (cancel_mono (basicOpen 𝒜 s).ι).mp ?_
    rw [morphismRestrict_ι, Category.assoc, Category.assoc, Category.assoc, basicOpenIsoSpec_inv_ι,
      ← awayι_comp_map ψ h hi s hs, ← basicOpenIsoSpec_inv_ι_assoc, Iso.hom_inv_id_assoc,
      Scheme.isoOfEq_hom_ι_assoc]
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Away.map ψ s))
    (away_map_surjective ψ hψ s hs)
  rw [key]
  infer_instance

/-- **`Proj` of a surjective graded ring map is a closed immersion** (Stacks 01N0 (2)). -/
instance isClosedImmersion_map :
    IsClosedImmersion (map ψ (irrelevant_le_map_of_surjective ψ hψ)) :=
  isClosedImmersion_map_of_surjective ψ hψ _

include hψ in
/-- **The image of `Proj.map ψ` contains `V₊(ker ψ)`** for surjective `ψ`: a homogeneous prime `p`
containing the kernel is the preimage of its image `ψ(p)`, which is a point of `Proj ℬ`. -/
theorem exists_comap_eq_of_ker_le (h : ℬ₊ ≤ 𝒜₊.map ψ) (p : ProjectiveSpectrum 𝒜)
    (hp : RingHom.ker (ψ : A →+* B) ≤ p.asHomogeneousIdeal.toIdeal) :
    ∃ q : ProjectiveSpectrum ℬ, ProjectiveSpectrum.comap ψ h q = p := by
  have := p.isPrime
  have hcomap : (p.asHomogeneousIdeal.toIdeal.map (ψ : A →+* B)).comap (ψ : A →+* B) =
      p.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.comap_map_of_surjective' (ψ : A →+* B) hψ, sup_eq_left.mpr hp]
  have hprime : (p.asHomogeneousIdeal.map ψ).toIdeal.IsPrime := by
    rw [toIdeal_map]
    exact Ideal.map_isPrime_of_surjective (f := (ψ : A →+* B)) hψ hp
  refine ⟨⟨p.asHomogeneousIdeal.map ψ, hprime, fun hle ↦ p.not_irrelevant_le ?_⟩, ?_⟩
  · intro a ha
    have hψa : ψ a ∈ ℬ₊ := by
      rw [mem_irrelevant_iff, GradedRing.proj_apply, ← map_directSumDecompose 𝒜 ℬ]
      rw [mem_irrelevant_iff, GradedRing.proj_apply] at ha
      rw [ha, map_zero]
    have h' : (ψ : A →+* B) a ∈ p.asHomogeneousIdeal.toIdeal.map (ψ : A →+* B) := hle hψa
    rw [← Ideal.mem_comap, hcomap] at h'
    exact h'
  · apply ProjectiveSpectrum.ext
    apply toIdeal_injective
    exact hcomap

end AlgebraicGeometry.Proj

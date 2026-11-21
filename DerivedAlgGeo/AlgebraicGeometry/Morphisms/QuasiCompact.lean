/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Closure of the image of a quasi-compact morphism

## Main results

* `AlgebraicGeometry.exists_specializes_of_mem_closure_range`: for a quasi-compact morphism
  `f : X ⟶ Y`, every point of `closure (Set.range f)` is a specialization of a point of the image
  (Stacks 02JQ, "in particular").

## References

* [Stacks: Tag 02JQ](https://stacks.math.columbia.edu/tag/02JQ)
-/

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The affine case of `exists_specializes_of_mem_closure_range`: `V` is an affine open of `X`
mapping into an affine open `U` of `Y`, and `y ∈ U` lies in the closure of `f '' V`. -/
private theorem exists_specializes_of_mem_closure_image_affine (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    {y : Y} (hyU : y ∈ U) (hy : y ∈ closure (f '' (V : Set X))) : ∃ x ∈ V, f x ⤳ y := by
  set φ := f.appLE U V e
  set p := hU.primeIdealOf ⟨y, hyU⟩
  have hfs := IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e
  have hcomm : ∀ z : Spec Γ(X, V), f (hV.fromSpec z) = hU.fromSpec (Spec.map φ z) := fun z ↦
    (congr_arg (fun g : Spec Γ(X, V) ⟶ Y ↦ g z) hfs).symm
  have hemb : IsEmbedding hU.fromSpec := hU.fromSpec.isOpenEmbedding.isEmbedding
  have hp : p ∈ closure (Set.range (PrimeSpectrum.comap φ.hom)) := by
    have hc := hemb.closure_eq_preimage_closure_image
      (s := (Set.range (Spec.map φ) : Set (Spec Γ(Y, U))))
    have hp' : p ∈ (closure (Set.range (Spec.map φ) : Set (Spec Γ(Y, U)))) := by
      rw [hc]
      have hy' : hU.fromSpec p = y := hU.fromSpec_primeIdealOf ⟨y, hyU⟩
      show hU.fromSpec p ∈ closure (hU.fromSpec '' Set.range (Spec.map φ))
      rw [hy']
      have himg : f '' (V : Set X) = hU.fromSpec '' Set.range (Spec.map φ) := by
        rw [← Set.range_comp]
        have h1 : (hU.fromSpec ∘ Spec.map φ : Spec Γ(X, V) → Y) = f ∘ hV.fromSpec := by
          funext z; exact (hcomm z).symm
        rw [h1, Set.range_comp, hV.range_fromSpec]
      rw [← himg]; exact hy
    exact hp'
  rw [PrimeSpectrum.closure_range_comap] at hp
  obtain ⟨Q, -, hQ, hle⟩ := Ideal.exists_ideal_comap_le_prime (f := φ.hom) p.asIdeal ⊥
    (by rw [← RingHom.ker_eq_comap_bot]; exact hp)
  let Q' : Spec Γ(X, V) := ⟨Q, hQ⟩
  refine ⟨hV.fromSpec Q', ?_, ?_⟩
  · have : hV.fromSpec Q' ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
    rwa [hV.range_fromSpec] at this
  · have hy' : hU.fromSpec p = y := hU.fromSpec_primeIdealOf ⟨y, hyU⟩
    rw [hcomm, ← hy']
    exact ((PrimeSpectrum.le_iff_specializes
      (PrimeSpectrum.comap φ.hom ⟨Q, hQ⟩) p).mp hle).map hU.fromSpec.continuous


/-- **Stacks 02JQ**, "in particular". Let `f : X ⟶ Y` be a quasi-compact morphism of schemes. Every
point of the closure of the image of `f` is a specialization of a point of the image.

Quasi-compactness is needed: for `X = ∐ₚ Spec 𝔽ₚ ⟶ Spec ℤ` the generic point of `Spec ℤ` is in the
closure of the image but specializes from no point of the image. -/
@[stacks 02JQ "in particular"]
theorem exists_specializes_of_mem_closure_range (f : X ⟶ Y) [QuasiCompact f]
    {y : Y} (hy : y ∈ closure (Set.range f)) : ∃ x, f x ⤳ y := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hc : IsCompact (f ⁻¹ᵁ U : Set X) := QuasiCompact.isCompact_preimage _ U.isOpen hU.isCompact
  obtain ⟨s, hs, hsU⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
    (show IsCompact (X := X) (f ⁻¹ᵁ U) from hc)
  have h1 : y ∈ closure (⋃ i ∈ s, f '' (i : Set X)) := by
    have h2 : y ∈ (U : Set Y) ∩ closure (Set.range f) := ⟨hyU, hy⟩
    have h3 := U.isOpen.inter_closure h2
    refine closure_mono ?_ h3
    rintro _ ⟨hz, x, rfl⟩
    have : x ∈ (f ⁻¹ᵁ U : Set X) := hz
    rw [hsU] at this
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at this
    obtain ⟨i, hi, hxi⟩ := this
    exact Set.mem_biUnion hi ⟨x, hxi, rfl⟩
  rw [hs.closure_biUnion] at h1
  obtain ⟨⟨V, hV⟩, hVs, hyV⟩ := Set.mem_iUnion₂.mp h1
  have hVU : V ≤ f ⁻¹ᵁ U := by
    rw [hsU]
    exact le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ s) ↦ (i : X.Opens)) ⟨V, hV⟩ hVs
  obtain ⟨x, -, hx⟩ := exists_specializes_of_mem_closure_image_affine f hU hV hVU hyU hyV
  exact ⟨x, hx⟩

end AlgebraicGeometry

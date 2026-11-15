/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.FinitePresentation

/-!
# Universal closedness is tested on base changes locally of finite presentation

Let `f : X ⟶ S` be a quasi-compact morphism of schemes. This file proves that `f` is universally
closed as soon as `X ×[S] T ⟶ T` is closed for every affine `T` locally of finite presentation
over `S` (Stacks, Limits, Section 32.14).

## Main definitions

This file introduces no new definitions.

## Main results

* `AlgebraicGeometry.exists_locallyOfFinitePresentation_of_disjoint_fiber`: a closed subset of
  `X ×[S] T` missing the fibre over `t ∈ T` comes, over an affine neighbourhood `V` of `t`, from a
  closed subset of `X ×[S] T'` missing the fibre over the image of `t`, for an affine `T'` locally
  of finite presentation over `S` (Stacks 05BD).
* `AlgebraicGeometry.universallyClosed_iff_isClosedMap_of_locallyOfFinitePresentation`: `f` is
  universally closed if and only if its base change to every affine scheme locally of finite
  presentation over `S` is closed (Stacks 05JX, (1) ⇔ (2)).

## Implementation notes

Over affine opens `Spec A ⊆ S`, `Spec C ⊆ X` and `V = Spec B ⊆ T`, a closed `Z ⊆ Spec (C ⊗_A B)`
missing the fibre over `𝔮 ∈ Spec B` gives `s ∉ 𝔮` and `y ∈ 𝔮 (C ⊗_A B)` with `s - y` vanishing on
`Z`. Writing `y` through finitely many elements of `B`, every ring `R` over `A` with a map
`R ⟶ B` whose image contains them carries the same relation, and `Z' ⊆ X ×[S] Spec R` is the
closure of the image of `Z`. The ring `R` is the polynomial ring over `A` on those elements, so no
filtered colimit of finitely presented algebras is formed.

Two choices depart from Stacks. The relation keeps `s ∉ 𝔮` where Stacks inverts it to reach `1`;
`s ∉ 𝔮` already excludes the fibre over the image of `𝔮`, so `V` is any affine neighbourhood of `t`
over an affine open of `S`. And the basic open of the lifted relation is a neighbourhood of each
point over the image of `𝔮` that misses the image of `Z`, so the closure of the image serves where
Stacks takes the scheme-theoretic image. The tensor product `C ⊗_A B` enters only through
`CommRingCat.closure_range_union_range_eq_top_of_isPushout`.

## References

* [Stacks, Section 32.14 (Tag 05JW)](https://stacks.math.columbia.edu/tag/05JW).

## Tags

universally closed, limit, locally of finite presentation
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

section Affine

/-- In an affine scheme, a point lies in the basic open of `r` exactly when `r` is not in its
prime ideal of global sections. -/
private lemma mem_basicOpen_iff_notMem_isoSpec {Y : Scheme.{u}} [IsAffine Y] (z : Y)
    (r : Γ(Y, ⊤)) : z ∈ Y.basicOpen r ↔ r ∉ (Y.isoSpec.hom z).asIdeal := by
  rw [← Scheme.toSpecΓ_preimage_basicOpen, ← Scheme.isoSpec_hom]
  rfl

/-- The point of `Spec B` under `z` is the prime of `B` pulled back from the prime of `z`. -/
private lemma asIdeal_apply_eq_comap {Y : Scheme.{u}} [IsAffine Y] {B : CommRingCat.{u}}
    (h : Y ⟶ Spec B) (z : Y) :
    (h z).asIdeal =
      (Y.isoSpec.hom z).asIdeal.comap (h.appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom) := by
  ext β
  rw [← not_iff_not, Ideal.mem_comap, ← mem_basicOpen_iff_notMem_isoSpec]
  have := congr(z ∈ $(Scheme.preimage_basicOpen h ((Scheme.ΓSpecIso B).inv β)))
  rw [basicOpen_eq_of_affine] at this
  exact (Iff.of_eq this)

/-- Let `h : Y ⟶ Spec B` with `Y` affine and `Z ⊆ Y` closed, missing the fibre over `q`. Then some
`s ∉ q` agrees on `Z` with an element of `q Γ(Y)`. -/
private lemma exists_sub_notMem_basicOpen {Y : Scheme.{u}} [IsAffine Y] {B : CommRingCat.{u}}
    (h : Y ⟶ Spec B) (q : PrimeSpectrum B) (Z : Set Y) (hZ : IsClosed Z)
    (hZq : ∀ z ∈ Z, h z ≠ q) :
    ∃ s ∉ q.asIdeal, ∃ y ∈ q.asIdeal.map (h.appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom),
      ∀ z ∈ Z, z ∉ Y.basicOpen (h.appTop ((Scheme.ΓSpecIso B).inv s) - y) := by
  set x : B →+* Γ(Y, ⊤) := h.appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom
  set Z' : Set (PrimeSpectrum Γ(Y, ⊤)) := Y.isoSpec.inv ⁻¹' Z
  have hZ' : IsClosed Z' := hZ.preimage Y.isoSpec.inv.continuous
  have hI : ∀ r ∈ PrimeSpectrum.vanishingIdeal Z', ∀ z ∈ Z, z ∉ Y.basicOpen r := by
    intro r hr z hz hzr
    have hz' : Y.isoSpec.hom z ∈ Z' := by
      change Y.isoSpec.inv (Y.isoSpec.hom z) ∈ Z
      simpa using hz
    exact (mem_basicOpen_iff_notMem_isoSpec z r).1 hzr
      ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hr _ hz')
  by_contra! H
  have hdisj : Disjoint ((PrimeSpectrum.vanishingIdeal Z' ⊔ q.asIdeal.map x : Ideal Γ(Y, ⊤)) :
      Set Γ(Y, ⊤)) (q.asIdeal.primeCompl.map x) := by
    rw [Set.disjoint_left]
    rintro _ hJ ⟨s, hs, rfl⟩
    obtain ⟨r, hr, y, hy, hry⟩ := Submodule.mem_sup.1 hJ
    obtain ⟨z, hz, hzb⟩ := H s hs y hy
    have hxs : h.appTop ((Scheme.ΓSpecIso B).inv s) - y = r := by
      rw [show h.appTop ((Scheme.ΓSpecIso B).inv s) = x s from rfl, ← hry]
      ring
    exact hI r hr z hz (hxs ▸ hzb)
  obtain ⟨P, hP, hJP, hPdisj⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
  let p : Spec Γ(Y, ⊤) := (⟨P, hP⟩ : PrimeSpectrum Γ(Y, ⊤))
  have hpZ : Y.isoSpec.inv p ∈ Z := by
    have : p ∈ closure Z' := by
      rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact le_sup_left.trans hJP
    rw [hZ'.closure_eq] at this
    exact this
  apply hZq _ hpZ
  apply PrimeSpectrum.ext
  have hp : Y.isoSpec.hom (Y.isoSpec.inv p) = p := by simp
  rw [asIdeal_apply_eq_comap, hp]
  apply le_antisymm
  · intro β hβ
    by_contra hβq
    exact Set.disjoint_left.1 hPdisj hβ ⟨β, hβq, rfl⟩
  · exact Ideal.map_le_iff_le_comap.1 (le_sup_right.trans hJP)

end Affine

/-- An element of the subring generated by `s` and the range of `x` lies in the subring generated
by `s` and finitely many values of `x`. -/
private lemma exists_finset_mem_closure_union_image {R ι : Type*} [Ring R] {s : Set R}
    {x : ι → R} {c : R} (hc : c ∈ Subring.closure (s ∪ Set.range x)) :
    ∃ F : Finset ι, c ∈ Subring.closure (s ∪ x '' F) := by
  classical
  have mono {F G : Finset ι} (hFG : F ⊆ G) :
      Subring.closure (s ∪ x '' F) ≤ Subring.closure (s ∪ x '' G) :=
    Subring.closure_mono (Set.union_subset_union_right _ (Set.image_mono (by exact_mod_cast hFG)))
  induction hc using Subring.closure_induction with
  | mem c hc =>
    rcases hc with hc | ⟨i, rfl⟩
    · exact ⟨∅, Subring.subset_closure (Or.inl hc)⟩
    · exact ⟨{i}, Subring.subset_closure (Or.inr ⟨i, by simp, rfl⟩)⟩
  | zero => exact ⟨∅, zero_mem _⟩
  | one => exact ⟨∅, one_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨F, hF⟩ := ha
    obtain ⟨G, hG⟩ := hb
    exact ⟨F ∪ G, add_mem (mono Finset.subset_union_left hF) (mono Finset.subset_union_right hG)⟩
  | neg a _ ha =>
    obtain ⟨F, hF⟩ := ha
    exact ⟨F, neg_mem hF⟩
  | mul a b _ _ ha hb =>
    obtain ⟨F, hF⟩ := ha
    obtain ⟨G, hG⟩ := hb
    exact ⟨F ∪ G, mul_mem (mono Finset.subset_union_left hF) (mono Finset.subset_union_right hG)⟩

variable {X S : Scheme.{u}} (f : X ⟶ S)

section Descent

variable {W : S.Opens} (hW : IsAffineOpen W) {B : CommRingCat.{u}} (ρ : Γ(S, W) ⟶ B)
  (g : Spec B ⟶ S) (hg : Spec.map ρ ≫ hW.fromSpec = g)

include hg in
/-- The descent over one affine open `U ⊆ f⁻¹ W`: for a closed `Z ⊆ X ×[S] Spec B` missing the
fibre over `q`, finitely many elements of `B` suffice to keep the points of `X ×[S] Spec R` over
`U` and over the image of `q` out of the closure of the image of `Z`, for every `R` over
`Γ(S, W)` mapping to `B` with those elements in its image. -/
private lemma exists_finset_forall_notMem_closure_of_isAffineOpen (q : Spec B)
    (Z : Set (pullback f g :)) (hZ : IsClosed Z) (hZq : ∀ z ∈ Z, pullback.snd f g z ≠ q)
    {U : X.Opens} (hU : IsAffineOpen U) (hUW : U ≤ f ⁻¹ᵁ W) :
    ∃ E : Finset B, ∀ (R : CommRingCat.{u}) (κ : Γ(S, W) ⟶ R) (φ : R ⟶ B) (hφ : κ ≫ φ = ρ)
      (b : Spec R ⟶ S) (hb : Spec.map κ ≫ hW.fromSpec = b), (E : Set B) ⊆ Set.range φ →
      ∀ z ∈ closure (pullback.map f g f b (𝟙 X) (Spec.map φ) (𝟙 S) (by simp)
          (by simp [← hb, ← hg, ← hφ]) '' Z),
        pullback.fst f b z ∈ U → pullback.snd f b z ≠ Spec.map φ q := by
  classical
  have : IsAffine U := hU
  have hUrange : Set.range (U.ι ≫ f) ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact Set.image_subset_iff.2 hUW
  set fU : U.toScheme ⟶ Spec Γ(S, W) := IsOpenImmersion.lift hW.fromSpec (U.ι ≫ f) hUrange
  have hfU : fU ≫ hW.fromSpec = U.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
  set ι : pullback fU (Spec.map ρ) ⟶ pullback f g :=
    pullback.map fU (Spec.map ρ) f g U.ι (𝟙 _) hW.fromSpec hfU (by simp [hg])
  have hZU : IsClosed (ι ⁻¹' Z) := hZ.preimage ι.continuous
  have hZUq : ∀ z ∈ ι ⁻¹' Z, pullback.snd fU (Spec.map ρ) z ≠ q := by
    intro z hz h
    apply hZq _ hz
    rw [← h, ← Scheme.Hom.comp_apply, pullback.lift_snd, Category.comp_id]
  obtain ⟨s, hs, y, hy, hsy⟩ :=
    exists_sub_notMem_basicOpen (pullback.snd fU (Spec.map ρ)) q _ hZU hZUq
  set x : B →+* Γ(pullback fU (Spec.map ρ), ⊤) :=
    (pullback.snd fU (Spec.map ρ)).appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom
  have hgen : Subring.closure
      (Set.range (pullback.fst fU (Spec.map ρ)).appTop.hom ∪ Set.range x) = ⊤ := by
    rw [← CommRingCat.closure_range_union_range_eq_top_of_isPushout
      (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback fU (Spec.map ρ)))]
    congr 2
    ext a
    constructor
    · rintro ⟨β, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨(Scheme.ΓSpecIso B).hom γ, by simp [x]⟩
  obtain ⟨t, ht, c, hc⟩ := (Submodule.mem_span_image_iff_exists_fun _).1 hy
  choose F hF using fun i : t ↦
    exists_finset_mem_closure_union_image (hgen ▸ Subring.mem_top (c i))
  refine ⟨insert s (t ∪ Finset.univ.biUnion F), ?_⟩
  intro R κ φ hφ b hb hE z hz hzU hzq
  obtain ⟨rs, hrs⟩ := hE (Finset.mem_insert_self _ _)
  choose ri hri using fun i : t ↦ hE (Finset.mem_insert_of_mem (Finset.mem_union_left _ i.2))
  set μ : pullback fU (Spec.map ρ) ⟶ pullback fU (Spec.map κ) :=
    pullback.map fU (Spec.map ρ) fU (Spec.map κ) (𝟙 _) (Spec.map φ) (𝟙 _) (by simp)
      (by simp [← hφ])
  set ι' : pullback fU (Spec.map κ) ⟶ pullback f b :=
    pullback.map fU (Spec.map κ) f b U.ι (𝟙 _) hW.fromSpec hfU (by simp [hb])
  have : IsOpenImmersion ι' := by simp only [ι']; infer_instance
  set m : pullback f g ⟶ pullback f b := pullback.map f g f b (𝟙 X) (Spec.map φ) (𝟙 S) (by simp)
    (by simp [← hb, ← hg, ← hφ])
  have hcomm : μ ≫ ι' = ι ≫ m := by
    apply pullback.hom_ext <;> simp [μ, ι', ι, m]
  set x' : R →+* Γ(pullback fU (Spec.map κ), ⊤) :=
    (pullback.snd fU (Spec.map κ)).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
  have hμx' (r : R) : μ.appTop (x' r) = x (φ r) := by
    have h₁ : μ ≫ pullback.snd fU (Spec.map κ) = pullback.snd fU (Spec.map ρ) ≫ Spec.map φ := by
      simp [μ]
    have h₂ := congr((Scheme.Hom.appTop $h₁).hom ((Scheme.ΓSpecIso R).inv r))
    have h₃ := congr(($(Scheme.ΓSpecIso_inv_naturality φ)).hom r)
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h₂ h₃
    simp only [x', x, RingHom.comp_apply, h₂, h₃]
  have hμfst (a : Γ(U.toScheme, ⊤)) : μ.appTop ((pullback.fst fU (Spec.map κ)).appTop a) =
      (pullback.fst fU (Spec.map ρ)).appTop a := by
    have h₁ : μ ≫ pullback.fst fU (Spec.map κ) = pullback.fst fU (Spec.map ρ) := by
      simp [μ]
    have h₂ := congr((Scheme.Hom.appTop $h₁).hom a)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using h₂
  have hlift (i : t) : ∃ c', μ.appTop c' = c i := by
    refine (show Subring.closure _ ≤ μ.appTop.hom.range from ?_) (hF i)
    rw [Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨β, hβ, rfl⟩)
    · exact ⟨_, hμfst a⟩
    · obtain ⟨r, rfl⟩ := hE (Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hβ⟩)))
      exact ⟨_, hμx' r⟩
  choose c' hc' using hlift
  set w : Γ(pullback fU (Spec.map κ), ⊤) := x' rs - ∑ i, c' i * x' (ri i)
  have hμw : μ.appTop w = x s - y := by
    simp only [w, map_sub, map_sum, map_mul, hc', hμx', hri, hrs, ← hc, smul_eq_mul]
  obtain ⟨p', rfl⟩ : z ∈ Set.range ι' := by
    rw [Scheme.Pullback.range_map]
    exact ⟨by simpa using hzU, by simp⟩
  have hsnd' : pullback.snd fU (Spec.map κ) p' = Spec.map φ q := by
    have : ι' ≫ pullback.snd f b = pullback.snd fU (Spec.map κ) := by simp [ι']
    rw [← hzq, ← this, Scheme.Hom.comp_apply]
  have hmem (r : R) : p' ∈ (pullback fU (Spec.map κ)).basicOpen (x' r) ↔ φ r ∉ q.asIdeal := by
    have := congr(p' ∈ $(Scheme.preimage_basicOpen (pullback.snd fU (Spec.map κ))
      ((Scheme.ΓSpecIso R).inv r)))
    rw [basicOpen_eq_of_affine] at this
    refine (Iff.of_eq this).symm.trans ?_
    change r ∉ (pullback.snd fU (Spec.map κ) p').asIdeal ↔ _
    rw [hsnd']
    rfl
  have hp'w : p' ∈ (pullback fU (Spec.map κ)).basicOpen w := by
    by_contra hp'
    have h0 (r : R) (hr : φ r ∈ q.asIdeal) :
        (pullback fU (Spec.map κ)).evaluation ⊤ p' trivial (x' r) = 0 :=
      (Scheme.evaluation_eq_zero_iff_notMem_basicOpen _ _ _ _).2 fun h ↦ (hmem r).1 h hr
    have hw0 := (Scheme.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) _ p' trivial w).2 hp'
    have hrs0 : (pullback fU (Spec.map κ)).evaluation ⊤ p' trivial (x' rs) = 0 := by
      have : x' rs = w + ∑ i, c' i * x' (ri i) := by simp [w]
      rw [this, map_add, hw0, map_sum, zero_add]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [map_mul, h0 _ (by rw [hri]; exact ht i.2), mul_zero]
    exact (Scheme.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) _ p' trivial (x' rs)).2
      ((hmem rs).2 (hrs ▸ hs)) hrs0
  obtain ⟨_, ⟨p'', hp'', rfl⟩, v, hv, hvm⟩ := mem_closure_iff.1 hz _
    (ι'.isOpenEmbedding.isOpenMap _ (Opens.isOpen _)) ⟨p', hp'w, rfl⟩
  obtain ⟨p, rfl⟩ : v ∈ Set.range ι := by
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, by simp⟩
    have h₁ : m ≫ pullback.fst f b = pullback.fst f g := by simp [m]
    have h₂ : ι' ≫ pullback.fst f b = pullback.fst fU (Spec.map κ) ≫ U.ι := by simp [ι']
    change pullback.fst f g v ∈ Set.range U.ι
    rw [← h₁, Scheme.Hom.comp_apply, hvm, ← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hμp : μ p = p'' := ι'.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply, hvm])
  refine hsy p hv ?_
  change p ∈ (pullback fU (Spec.map ρ)).basicOpen (x s - y)
  rw [← hμw, ← Scheme.preimage_basicOpen_top]
  change μ p ∈ (pullback fU (Spec.map κ)).basicOpen w
  rwa [hμp]

include hg in
/-- The descent over the whole of `f⁻¹ W`, covered by finitely many affine opens since `f` is
quasi-compact. -/
private lemma exists_finset_forall_notMem_closure [QuasiCompact f] (q : Spec B)
    (Z : Set (pullback f g :)) (hZ : IsClosed Z) (hZq : ∀ z ∈ Z, pullback.snd f g z ≠ q) :
    ∃ E : Finset B, ∀ (R : CommRingCat.{u}) (κ : Γ(S, W) ⟶ R) (φ : R ⟶ B) (hφ : κ ≫ φ = ρ)
      (b : Spec R ⟶ S) (hb : Spec.map κ ≫ hW.fromSpec = b), (E : Set B) ⊆ Set.range φ →
      ∀ z ∈ closure (pullback.map f g f b (𝟙 X) (Spec.map φ) (𝟙 S) (by simp)
          (by simp [← hb, ← hg, ← hφ]) '' Z), pullback.snd f b z ≠ Spec.map φ q := by
  classical
  obtain ⟨𝒮, h𝒮, hcover⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := f ⁻¹ᵁ W)).1 (QuasiCompact.isCompact_preimage _ W.isOpen hW.isCompact)
  have hle (U : X.affineOpens) (hU : U ∈ 𝒮) : (U : X.Opens) ≤ f ⁻¹ᵁ W :=
    hcover ▸ le_biSup (fun i : X.affineOpens ↦ (i : X.Opens)) hU
  choose! E hE using fun (U : X.affineOpens) (hU : U ∈ 𝒮) ↦
    exists_finset_forall_notMem_closure_of_isAffineOpen f hW ρ g hg q Z hZ hZq U.2 (hle U hU)
  refine ⟨h𝒮.toFinset.biUnion E, ?_⟩
  intro R κ φ hφ b hb hEφ z hz hzq
  subst hb
  have hzW : pullback.fst f _ z ∈ f ⁻¹ᵁ W := by
    change f (pullback.fst f _ z) ∈ W
    rw [← Scheme.Hom.comp_apply, pullback.condition, ← SetLike.mem_coe, ← hW.range_fromSpec]
    exact ⟨Spec.map κ (pullback.snd f _ z), by simp⟩
  rw [hcover] at hzW
  obtain ⟨U, hU, hzU⟩ : ∃ U ∈ 𝒮, pullback.fst f _ z ∈ (U : X.Opens) := by
    simpa [Opens.mem_iSup] using hzW
  exact hE U hU R κ φ hφ _ rfl ((Finset.coe_subset.2
    (Finset.subset_biUnion_of_mem E (h𝒮.mem_toFinset.2 hU))).trans hEφ) z hz hzU hzq

end Descent

variable [QuasiCompact f]

/-- **Stacks 05BD** (Limits, Lemma 32.14.1). Let `f : X ⟶ S` be quasi-compact, `g : T ⟶ S`,
`t ∈ T`, and `Z ⊆ X ×[S] T` closed and disjoint from the fibre over `t`. Then there are an affine
open neighbourhood `V` of `t`, an affine `T'` locally of finite presentation over `S` and
`a : V ⟶ T'` over `S`, and a closed `Z' ⊆ X ×[S] T'` disjoint from the fibre over `a t` that
contains the image of `Z ∩ (X ×[S] V)`. -/
@[stacks 05BD]
theorem exists_locallyOfFinitePresentation_of_disjoint_fiber {T : Scheme.{u}} (g : T ⟶ S)
    (t : T) (Z : Set (pullback f g :)) (hZ : IsClosed Z)
    (hZt : ∀ z ∈ Z, pullback.snd f g z ≠ t) :
    ∃ (V : T.Opens) (ht : t ∈ V), IsAffineOpen V ∧ ∃ (T' : Scheme.{u}) (_ : IsAffine T')
      (b : T' ⟶ S) (_ : LocallyOfFinitePresentation b) (a : V.toScheme ⟶ T')
      (hab : a ≫ b = V.ι ≫ g) (Z' : Set (pullback f b :)), IsClosed Z' ∧
      (∀ z ∈ Z', pullback.snd f b z ≠ a ⟨t, ht⟩) ∧
      pullback.map f (V.ι ≫ g) f b (𝟙 X) a (𝟙 S) (by simp) (by simp [hab]) ''
        (pullback.map f (V.ι ≫ g) f g (𝟙 X) V.ι (𝟙 S) (by simp) (by simp) ⁻¹' Z) ⊆ Z' := by
  obtain ⟨W, hW, hgtW, -⟩ := exists_isAffineOpen_mem_and_subset (x := g t) (U := ⊤) trivial
  obtain ⟨V, hV, htV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := t) (U := g ⁻¹ᵁ W) hgtW
  have hVW' : V ≤ g ⁻¹ᵁ W := hVW
  set ρ : Γ(S, W) ⟶ Γ(T, V) := g.appLE W V hVW'
  have hg₀ : Spec.map ρ ≫ hW.fromSpec = hV.fromSpec ≫ g :=
    IsAffineOpen.SpecMap_appLE_fromSpec g hW hV hVW'
  set ι₀ := pullback.map f (hV.fromSpec ≫ g) f g (𝟙 X) hV.fromSpec (𝟙 S) (by simp) (by simp)
  have hZ₀q : ∀ z ∈ ι₀ ⁻¹' Z, pullback.snd f (hV.fromSpec ≫ g) z ≠ hV.primeIdealOf ⟨t, htV⟩ := by
    intro z hz h
    apply hZt _ hz
    have : ι₀ ≫ pullback.snd f g = pullback.snd f (hV.fromSpec ≫ g) ≫ hV.fromSpec := by
      simp [ι₀]
    rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply, h, hV.fromSpec_primeIdealOf]
  obtain ⟨E, hE⟩ := exists_finset_forall_notMem_closure f hW ρ _ hg₀ _ _
    (hZ.preimage ι₀.continuous) hZ₀q
  let R : CommRingCat.{u} := .of (MvPolynomial E Γ(S, W))
  let κ : Γ(S, W) ⟶ R := CommRingCat.ofHom (algebraMap _ _)
  let φ : R ⟶ Γ(T, V) := CommRingCat.ofHom (MvPolynomial.eval₂Hom ρ.hom Subtype.val)
  have hφ : κ ≫ φ = ρ := by
    ext a
    exact MvPolynomial.eval₂_C _ _ a
  have hEφ : (E : Set Γ(T, V)) ⊆ Set.range φ := fun β hβ ↦
    ⟨MvPolynomial.X ⟨β, hβ⟩, MvPolynomial.eval₂_X _ _ _⟩
  have : LocallyOfFinitePresentation (Spec.map κ) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.finitePresentation_algebraMap.2 inferInstance
  have hab : (hV.isoSpec.hom ≫ Spec.map φ) ≫ Spec.map κ ≫ hW.fromSpec = V.ι ≫ g := by
    rw [Category.assoc, ← Category.assoc (Spec.map φ), ← Spec.map_comp, hφ, hg₀,
      ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
  set m := pullback.map f (hV.fromSpec ≫ g) f (Spec.map κ ≫ hW.fromSpec) (𝟙 X) (Spec.map φ)
    (𝟙 S) (by simp) (by simp [← hg₀, ← hφ])
  refine ⟨V, htV, hV, Spec R, inferInstance, Spec.map κ ≫ hW.fromSpec, inferInstance,
    hV.isoSpec.hom ≫ Spec.map φ, hab, closure (m '' (ι₀ ⁻¹' Z)), isClosed_closure, ?_, ?_⟩
  · intro z hz
    convert hE R κ φ hφ _ rfl hEφ z hz using 1
    exact Scheme.Hom.comp_apply _ _ _
  · rintro _ ⟨w, hw, rfl⟩
    apply subset_closure
    refine ⟨pullback.map f (V.ι ≫ g) f (hV.fromSpec ≫ g) (𝟙 X) hV.isoSpec.hom (𝟙 S) (by simp)
      (by simp) w, ?_, ?_⟩
    · have : pullback.map f (V.ι ≫ g) f (hV.fromSpec ≫ g) (𝟙 X) hV.isoSpec.hom (𝟙 S) (by simp)
          (by simp) ≫ ι₀ =
          pullback.map f (V.ι ≫ g) f g (𝟙 X) V.ι (𝟙 S) (by simp) (by simp) := by
        apply pullback.hom_ext <;> simp [ι₀]
      rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, this]
    · have : pullback.map f (V.ι ≫ g) f (hV.fromSpec ≫ g) (𝟙 X) hV.isoSpec.hom (𝟙 S) (by simp)
          (by simp) ≫ m =
          pullback.map f (V.ι ≫ g) f (Spec.map κ ≫ hW.fromSpec) (𝟙 X)
            (hV.isoSpec.hom ≫ Spec.map φ) (𝟙 S) (by simp) (by simp [hab]) := by
        apply pullback.hom_ext <;> simp [m]
      rw [← Scheme.Hom.comp_apply, this]

/-- **Stacks 05JX** (Limits, Lemma 32.14.2, (1) ⇔ (2)). A quasi-compact morphism `f : X ⟶ S` is
universally closed if and only if `X ×[S] T ⟶ T` is closed for every affine `T` locally of finite
presentation over `S`. -/
@[stacks 05JX "(1) ⇔ (2), with affine test schemes"]
theorem universallyClosed_iff_isClosedMap_of_locallyOfFinitePresentation :
    UniversallyClosed f ↔ ∀ (T : Scheme.{u}) [IsAffine T] (b : T ⟶ S)
      [LocallyOfFinitePresentation b], IsClosedMap (pullback.snd f b) := by
  refine ⟨fun _ T _ b _ ↦ (pullback.snd f b).isClosedMap, fun H ↦ ?_⟩
  suffices h : ∀ {T : Scheme.{u}} (g : T ⟶ S), IsClosedMap (pullback.snd f g) by
    rw [universallyClosed_iff]
    intro X' Y' i₁ i₂ f' hsq
    change IsClosedMap f'
    rw [← hsq.flip.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (h i₂).comp hsq.flip.isoPullback.hom.isClosedMap
  intro T g
  rw [isClosedMap_iff_specializingMap]
  intro ξ t hξt
  by_contra! hne
  obtain ⟨V, htV, hV, T', _, b, _, a, hab, Z', hZ', hdisj, hincl⟩ :=
    exists_locallyOfFinitePresentation_of_disjoint_fiber f g t (closure {ξ}) isClosed_closure
      fun z hz ↦ hne z (specializes_iff_mem_closure.2 hz)
  set ιV := pullback.map f (V.ι ≫ g) f g (𝟙 X) V.ι (𝟙 S) (by simp) (by simp)
  obtain ⟨w, hw⟩ : ξ ∈ Set.range ιV := by
    rw [Scheme.Pullback.range_map]
    exact ⟨by simp, by simpa using hξt.mem_open V.isOpen htV⟩
  set m := pullback.map f (V.ι ≫ g) f b (𝟙 X) a (𝟙 S) (by simp) (by simp [hab])
  have hmw : m w ∈ Z' := hincl ⟨w, by rw [Set.mem_preimage, hw]; exact subset_closure rfl, rfl⟩
  have hsnd : V.ι (pullback.snd f (V.ι ≫ g) w) = pullback.snd f g ξ := by
    have : ιV ≫ pullback.snd f g = pullback.snd f (V.ι ≫ g) ≫ V.ι := by simp [ιV]
    rw [← hw, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this]
  have hsp : pullback.snd f (V.ι ≫ g) w ⤳ ⟨t, htV⟩ := by
    apply V.ι.isOpenEmbedding.isInducing.specializes_iff.1
    rw [hsnd]
    exact hξt
  have hmsnd : pullback.snd f b (m w) = a (pullback.snd f (V.ι ≫ g) w) := by
    have : m ≫ pullback.snd f b = pullback.snd f (V.ι ≫ g) ≫ a := by simp [m]
    rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]
  obtain ⟨z, hz, hzt⟩ := (hsp.map a.continuous).mem_closed (H T' b _ hZ') ⟨m w, hmw, hmsnd⟩
  exact hdisj z hz hzt

end AlgebraicGeometry

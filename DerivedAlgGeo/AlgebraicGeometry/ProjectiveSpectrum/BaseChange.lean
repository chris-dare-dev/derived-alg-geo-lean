/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.RingTheory.GradedAlgebra.TensorProduct
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of `Proj`

For a graded `R`-algebra `𝒜` and an `R`-algebra `S`, the base change `S ⊗[R] 𝒜` is graded by
`fun i ↦ (𝒜 i).baseChange S`, and `Proj` commutes with this base change:

    Proj (S ⊗[R] A) ≅ Spec S ×_{Spec R} Proj A.

## Main definitions

* `Proj.map (GradedRingHom.includeRight S 𝒜) _ : Proj (S ⊗[R] A) ⟶ Proj A` is the top arrow of
  the base-change square; this file adds no new data, only properties of `Proj.map`.

## Main results

* `AlgebraicGeometry.Proj.map_toSpecZero`: `Proj.map` lies over `Spec` of the induced map of
  degree-zero parts.
* `AlgebraicGeometry.Proj.isIso_map_of_bijective`: `Proj` of a bijective graded ring map is an
  isomorphism.
* `AlgebraicGeometry.Proj.isPullback_map_baseChange`: the base-change square is cartesian
  (Stacks 01N2, EGA II 2.8.10).
* `AlgebraicGeometry.Proj.isPullback_map_of_isPushout`: the same square for any graded model
  `A'` of the base change, given as a pushout square of algebras `Algebra.IsPushout R R' A A'`;
  `AlgebraicGeometry.Proj.irrelevant_le_map_of_isPushout` supplies the hypothesis of `Proj.map`.

## Implementation notes

The square is cartesian on the standard affine cover `D₊(f)` of `Proj A`. Its preimage in
`Proj (S ⊗[R] A)` is `D₊(1 ⊗ f)`, and on that chart the square is `Spec` of the ring square
`R → S`, `R → A_(f)`, `S → (S ⊗[R] A)_(1 ⊗ f)`, which is a pushout by
`HomogeneousLocalization.Away.isPushout_baseChange`. No flatness or finiteness hypothesis is
needed. For a model `A'` of the base change, `Proj A' ≅ Proj (R' ⊗[R] A)` by
`isIso_map_of_bijective`, and the square is the base-change square pasted with that isomorphism.

## References

* [Stacks, Lemma 27.11.6 (Tag 01N2)](https://stacks.math.columbia.edu/tag/01N2).
* EGA II, Proposition 2.8.10.

## Tags

Proj, projective spectrum, base change, fibre product, functoriality
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Proj

section Functor

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

set_option backward.isDefEq.respectTransparency false in
/-- `Proj.map` lies over `Spec` of the induced map of degree-zero parts. -/
@[reassoc]
theorem map_toSpecZero :
    map f hf ≫ toSpecZero 𝒜 =
      toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  refine (mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, mapAffineOpenCover_f,
    awayι_comp_map_assoc _ _ _ _ s.2.2, awayι_toSpecZero, awayι_toSpecZero_assoc,
    ← Spec.map_comp]
  congr 1
  ext x
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  change HomogeneousLocalization.val (HomogeneousLocalization.map _ _
      (HomogeneousLocalization.mk _)) = HomogeneousLocalization.val (HomogeneousLocalization.mk _)
  rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk]
  simp

/-- `Proj` of a bijective graded ring map is an isomorphism, with inverse `Proj` of the graded
inverse. -/
theorem isIso_map_of_bijective (hbij : Function.Bijective f) : IsIso (map f hf) := by
  let g := GradedRingHom.symmOfBijective f hbij
  have hg := GradedRingHom.irrelevant_le_map_of_bijective g
    (GradedRingHom.bijective_symmOfBijective f hbij)
  have hgf : g.comp f = GradedRingHom.id 𝒜 :=
    GradedRingHom.ext (GradedRingHom.symmOfBijective_apply_apply f hbij)
  have hfg : f.comp g = GradedRingHom.id ℬ :=
    GradedRingHom.ext (GradedRingHom.apply_symmOfBijective_apply f hbij)
  refine ⟨map g hg, ?_, ?_⟩
  · rw [← map_comp, ← map_id]
    congr
  · rw [← map_comp, ← map_id]
    congr

end Functor

section BaseChange

variable {R S A : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

variable (S) in
set_option backward.isDefEq.respectTransparency false in
/-- **`Proj` commutes with base change** (Stacks 01N2, EGA II 2.8.10): for a graded `R`-algebra
`𝒜` and an `R`-algebra `S`,

    Proj (S ⊗[R] A) ⟶ Proj A
         ↓                ↓
       Spec S    ⟶    Spec R

is cartesian. There is no flatness or finiteness hypothesis. -/
theorem isPullback_map_baseChange :
    IsPullback
      (map (GradedRingHom.includeRight S 𝒜) (GradedRingHom.irrelevant_baseChange_le_map S 𝒜))
      (toSpecZero (fun i ↦ (𝒜 i).baseChange S) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S ((𝒜 0).baseChange S))))
      (toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0))))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (affineOpenCover 𝒜).openCover fun i ↦ ?_
  obtain ⟨m, s, hs⟩ := i
  let φ := GradedRingHom.includeRight S 𝒜
  have hφ := GradedRingHom.irrelevant_baseChange_le_map S 𝒜
  -- The chart `D₊(1 ⊗ s)` is the preimage of the chart `D₊(s)`.
  have hchart : IsPullback (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map φ s)))
      (awayι _ (φ s) (φ.map_mem hs) m.pos) (awayι 𝒜 s hs m.pos) (map φ hφ) :=
    IsOpenImmersion.isPullback _ _ _ _ (awayι_comp_map φ hφ m.pos s hs) (by
      rw [opensRange_awayι, opensRange_awayι, map_preimage_basicOpen])
  -- On that chart the square is `Spec` of a pushout of rings.
  have hring := (isPullback_SpecMap_of_isPushout _ _ _ _
    (HomogeneousLocalization.Away.isPushout_baseChange S hs)).flip
  refine hring.of_iso hchart.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id]
    exact hchart.flip.isoPullback_hom_snd.symm
  · rw [Iso.refl_hom, Category.comp_id]
    change _ = hchart.flip.isoPullback.hom ≫ pullback.fst _ _ ≫ _
    rw [hchart.flip.isoPullback_hom_fst_assoc, awayι_toSpecZero_assoc, ← Spec.map_comp]
    rfl
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    change _ = awayι 𝒜 s hs m.pos ≫ _
    rw [awayι_toSpecZero_assoc, ← Spec.map_comp]
    rfl
  · simp

end BaseChange

section IsPushout

variable {R R' A A' : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
  [Algebra R R'] [Algebra R A] [Algebra R' A'] [Algebra A A'] [Algebra R A']
  [IsScalarTower R R' A'] [IsScalarTower R A A'] [Algebra.IsPushout R R' A A']
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {𝒜' : ℕ → Submodule R' A'} [GradedAlgebra 𝒜']
  (φ : 𝒜 →+*ᵍ 𝒜') (hφ : ∀ a, φ a = algebraMap A A' a)

include hφ

omit [GradedAlgebra 𝒜] [GradedAlgebra 𝒜'] in
/-- The comparison `R' ⊗[R] A ≃ A'` of a pushout square, as a graded ring map from the
base-change grading. -/
private noncomputable def pushoutGradedEquiv : (fun i ↦ (𝒜 i).baseChange R') →+*ᵍ 𝒜' where
  toRingHom := (Algebra.IsPushout.equiv R R' A A').toRingHom
  map_mem {i x} hx := by
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      change Algebra.IsPushout.equiv R R' A A' (1 ⊗ₜ a) ∈ 𝒜' i
      rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul, ← hφ]
      exact φ.map_mem ha
    | zero => simp
    | add y z _ _ hy hz => simpa using add_mem hy hz
    | smul r y _ hy =>
      change Algebra.IsPushout.equiv R R' A A' (r • y) ∈ 𝒜' i
      rw [map_smul]
      exact Submodule.smul_mem _ r hy

omit [GradedAlgebra 𝒜] [GradedAlgebra 𝒜'] in
private lemma pushoutGradedEquiv_comp :
    (pushoutGradedEquiv φ hφ).comp (GradedRingHom.includeRight R' 𝒜) = φ :=
  GradedRingHom.ext fun a ↦ by
    change Algebra.IsPushout.equiv R R' A A' (1 ⊗ₜ a) = φ a
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul, hφ]

omit [GradedAlgebra 𝒜] [GradedAlgebra 𝒜'] in
private lemma bijective_pushoutGradedEquiv : Function.Bijective (pushoutGradedEquiv φ hφ) :=
  (Algebra.IsPushout.equiv R R' A A').bijective

/-- In a pushout square of graded algebras, the irrelevant ideal of `A'` is generated by the
image of the irrelevant ideal of `A`. This is the hypothesis `Proj.map` asks of `φ`. -/
theorem irrelevant_le_map_of_isPushout :
    HomogeneousIdeal.irrelevant 𝒜' ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ := by
  rw [← pushoutGradedEquiv_comp φ hφ]
  exact HomogeneousIdeal.irrelevant_le_map_comp
    (GradedRingHom.irrelevant_baseChange_le_map R' 𝒜)
    (GradedRingHom.irrelevant_le_map_of_bijective _ (bijective_pushoutGradedEquiv φ hφ))

set_option backward.isDefEq.respectTransparency false in
/-- **`Proj` turns pushouts into pullbacks** (Stacks 01N2). If `A' = R' ⊗[R] A` as algebras,
through a graded ring map `φ : A → A'` over `R → R'`, then

    Proj A' ⟶ Proj A
       ↓          ↓
    Spec R' ⟶ Spec R

is cartesian. This is `AlgebraicGeometry.Proj.isPullback_map_baseChange` for a model `A'` of the
base change. -/
theorem isPullback_map_of_isPushout :
    IsPullback (map φ (irrelevant_le_map_of_isPushout φ hφ))
      (toSpecZero 𝒜' ≫ Spec.map (CommRingCat.ofHom (algebraMap R' (𝒜' 0))))
      (toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0))))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  let ψ := pushoutGradedEquiv φ hφ
  have hψ := GradedRingHom.irrelevant_le_map_of_bijective _ (bijective_pushoutGradedEquiv φ hφ)
  have : IsIso (map ψ hψ) := isIso_map_of_bijective ψ hψ (bijective_pushoutGradedEquiv φ hφ)
  have h₁ : IsPullback (map ψ hψ)
      (toSpecZero 𝒜' ≫ Spec.map (CommRingCat.ofHom (algebraMap R' (𝒜' 0))))
      (toSpecZero (fun i ↦ (𝒜 i).baseChange R') ≫
        Spec.map (CommRingCat.ofHom (algebraMap R' ((𝒜 0).baseChange R'))))
      (𝟙 _) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [map_toSpecZero_assoc, Category.comp_id, ← Spec.map_comp]
    congr 2
    ext r
    exact (Algebra.IsPushout.equiv R R' A A').commutes r
  have h := h₁.paste_horiz (isPullback_map_baseChange R' 𝒜)
  rw [Category.id_comp, ← map_comp] at h
  convert h using 2
  exact (pushoutGradedEquiv_comp φ hφ).symm

end IsPushout

end AlgebraicGeometry.Proj

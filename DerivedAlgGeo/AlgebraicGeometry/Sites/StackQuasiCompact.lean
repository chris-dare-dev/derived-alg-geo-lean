/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
import DerivedAlgGeo.AlgebraicGeometry.Sites.BigZariski
import DerivedAlgGeo.AlgebraicGeometry.Sites.Comparison
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids
import DerivedAlgGeo.CategoryTheory.Sites.Over

/-!
# Stacks for the quasi-compact topology

Let `P` be a morphism property of schemes that is stable under base change, multiplicative and
Zariski-local on the source, such that the topology `Scheme.propQCTopology P` is
subcanonical. A pseudofunctor `F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat` is a stack for
`Scheme.propQCTopology P` if and only if it is a stack for the big Zariski topology and has
effective descent along every surjective `P`-morphism of affine schemes `Spec S ⟶ Spec R`.
This is the stack analogue of Mathlib's `isSheaf_type_propQCTopology_iff`, which is Stacks
022H; for the fpqc topology, the implication from right to left is Vistoli's Lemma 4.25. The
fpqc, fppf and étale topologies are instances.

## Main results

* `AlgebraicGeometry.isPrestack_propQCTopology_iff`: the prestack version.
* `AlgebraicGeometry.isStack_propQCTopology_iff`: the criterion.
* `AlgebraicGeometry.isStack_fpqcTopology_iff`, `AlgebraicGeometry.isStack_fppfTopology_iff`,
  `AlgebraicGeometry.isStack_etaleTopology_iff`: the criterion for flat, flat and locally finitely
  presented, and étale morphisms.

## Implementation notes

The proof follows Vistoli's.

* The prestack condition is a sheaf condition on the presheaves of morphisms over each
  scheme `T`. By `GrothendieckTopology.isSheaf_over_iff_isSheaf_totalPresheaf` it is the sheaf
  condition for their total presheaves on schemes, to which Mathlib's
  `isSheaf_type_propQCTopology_iff` applies. This uses that `yoneda.obj T` is a sheaf, hence the
  subcanonicity hypothesis.
* Effective descent along a cover of `T` is local on `T`
  (`Pseudofunctor.isStackFor_of_isStackFor_pullback`), so `T` may be taken affine. A
  quasi-compact cover of an affine scheme is refined by a finite cover by affine schemes
  (`QuasiCompactCover.exists_hom`), and descent along the refinement implies descent along
  the cover since `F` is a prestack (`Pseudofunctor.IsStackFor.of_le`). Finally, descent along
  a finite family of affine schemes is descent along the single morphism out of their
  coproduct (`isStackFor_singleton_sigmaDesc_iff`), which is affine.

The subcanonicity hypothesis is an artifact of this proof of the prestack condition; it holds
for the fpqc topology and hence for the coarser fppf and étale topologies.

## References

* A. Vistoli, *Notes on Grothendieck topologies, fibered categories and descent theory*,
  arXiv:math/0412512v4, Lemma 4.25.
* [Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H)

## Tags

stack, descent, fpqc, fppf, étale, quasi-compact topology
-/

universe v' u' u

open CategoryTheory Bicategory Limits

namespace AlgebraicGeometry

open Scheme

variable {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
  {F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- A pseudofunctor is a prestack for the `P`-qc topology if and only if it is a prestack for
the Zariski topology and for every single object covering `{ Spec S ⟶ Spec R }` by a surjective
`P`-morphism. This is Step 1 of the proof of Vistoli's Lemma 4.25. The subcanonicity
hypothesis is an artifact of the proof. -/
theorem isPrestack_propQCTopology_iff [P.IsMultiplicative] [IsZariskiLocalAtSource P]
    [(propQCTopology P).Subcanonical] (F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{v', u'}) :
    F.IsPrestack (propQCTopology P) ↔
      F.IsPrestack zariskiTopology ∧
        ∀ ⦃R S : CommRingCat.{u}⦄ (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
          F.IsPrestackFor (.singleton (Spec.map f)) := by
  refine ⟨fun _ ↦ ⟨.of_isPrestackFor fun S R hR ↦
    F.isPrestackFor' R (zariskiTopology_le_propQCTopology (P := P) _ hR), fun R S f hf _ ↦
      F.isPrestackFor _ (Hom.generate_singleton_mem_propQCTopology _ hf)⟩,
    fun ⟨_, hF⟩ ↦ ⟨fun {T} M N ↦ ?_⟩⟩
  rw [isSheaf_iff_isSheaf_of_type, (propQCTopology P).isSheaf_over_iff_isSheaf_totalPresheaf
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _),
    isSheaf_type_propQCTopology_iff]
  refine ⟨?_, fun f hf hs ↦ ?_⟩
  · rw [← zariskiTopology.isSheaf_over_iff_isSheaf_totalPresheaf
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _),
      ← isSheaf_iff_isSheaf_of_type]
    exact Pseudofunctor.IsPrestack.isSheaf zariskiTopology M N
  · rw [Presieve.isSheafFor_iff_generate]
    refine Over.isSheafFor_totalPresheaf
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := propQCTopology P) _ _
        (Hom.generate_singleton_mem_propQCTopology _ hf)) fun p ↦ ?_
    exact (F.isPrestackFor_iff_isSheafFor' _).1
      ((F.IsPrestackFor_generate_iff _).2 (hF f hf hs)) M N p

/-- Two morphisms that differ by an isomorphism of their sources generate the same sieve. -/
private lemma generate_singleton_iso_comp {X Y S : Scheme.{u}} (e : X ≅ Y) (g : Y ⟶ S) :
    Sieve.generate (.singleton (e.hom ≫ g)) = Sieve.generate (.singleton g) := by
  refine le_antisymm ?_ ?_ <;> rw [Sieve.generate_le_iff] <;> rintro _ _ ⟨⟩
  · exact ⟨_, e.hom, g, ⟨⟩, rfl⟩
  · exact ⟨_, e.inv, e.hom ≫ g, ⟨⟩, by simp⟩

variable [IsZariskiLocalAtSource P]

omit [P.IsStableUnderBaseChange] in
/-- Effective descent along a quasi-compact `P`-cover of an affine scheme, from effective
descent along single surjective `P`-morphisms of affine schemes. These are Steps 2 to 4 of the
proof of Vistoli's Lemma 4.25. -/
private lemma isStackFor_ofArrows_of_isAffine [F.IsStack zariskiTopology]
    [F.IsPrestack (propQCTopology P)]
    (hF : ∀ ⦃R S : CommRingCat.{u}⦄ (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
      F.IsStackFor (.singleton (Spec.map f)))
    {R : CommRingCat.{u}} (𝒰 : Scheme.Cover.{u} (propQCPrecoverage P) (Spec R)) :
    F.IsStackFor (.ofArrows 𝒰.X 𝒰.f) := by
  obtain ⟨𝒱, φ, hfin, -⟩ := QuasiCompactCover.exists_hom.{u} 𝒰.forgetQc
  have : Finite 𝒱.I₀ := hfin
  have : Finite 𝒱.cover.I₀ := hfin
  have : IsAffine (∐ 𝒱.cover.X) := by dsimp [AffineCover.cover]; infer_instance
  let e := (∐ 𝒱.cover.X).isoSpec
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (e.inv ≫ Sigma.desc 𝒱.cover.f)
  have : Surjective (Sigma.desc 𝒱.cover.f) := inferInstance
  have hV : F.IsStackFor (.ofArrows 𝒱.cover.X 𝒱.cover.f) := by
    rw [← isStackFor_singleton_sigmaDesc_iff, ← F.IsStackFor_generate_iff,
      ← generate_singleton_iso_comp e.symm, F.IsStackFor_generate_iff]
    refine hψ ▸ hF ψ (hψ ▸ ?_) (hψ ▸ ?_)
    · exact IsZariskiLocalAtSource.comp (IsZariskiLocalAtSource.sigmaDesc 𝒱.cover.map_prop) _
    · infer_instance
  refine (F.IsStackFor_generate_iff _).1 (Pseudofunctor.IsStackFor.of_le F hV (J := propQCTopology P)
    (Cover.mem_propQCTopology 𝒱.cover) ?_)
  rintro _ _ ⟨j⟩
  exact ⟨_, φ.h₀ j, 𝒰.f (φ.s₀ j), ⟨_⟩, φ.w₀ j⟩

/-- Effective descent along a quasi-compact `P`-cover, from effective descent along single
surjective `P`-morphisms of affine schemes. -/
private lemma isStackFor_ofArrows [F.IsStack zariskiTopology]
    [F.IsPrestack (propQCTopology P)]
    (hF : ∀ ⦃R S : CommRingCat.{u}⦄ (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
      F.IsStackFor (.singleton (Spec.map f)))
    {T : Scheme.{u}} (𝒰 : Scheme.Cover.{u} (propQCPrecoverage P) T) :
    F.IsStackFor (.ofArrows 𝒰.X 𝒰.f) := by
  rw [← F.IsStackFor_generate_iff]
  refine F.isStackFor_of_isStackFor_pullback (J₀ := zariskiTopology)
    (Cover.mem_propQCTopology 𝒰.forgetQc) T.affineCover.f
    T.affineCover.mem_grothendieckTopology fun i ↦ ?_
  rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback, F.IsStackFor_generate_iff]
  exact isStackFor_ofArrows_of_isAffine hF (𝒰.pullback₂ (T.affineCover.f i))

variable (P) [P.IsMultiplicative] in
/-- A pseudofunctor is a stack for the `P`-qc topology if and only if it is a stack for the
Zariski topology and has effective descent along every single object covering
`{ Spec S ⟶ Spec R }` by a surjective `P`-morphism.

This is the stack analogue of Mathlib's `isSheaf_type_propQCTopology_iff`, which is Stacks
022H. For the fpqc topology, the implication from right to left is Vistoli's Lemma 4.25, stated
there for fibered categories over the category of schemes over a base scheme. The subcanonicity
hypothesis is an artifact of the proof of the prestack condition, through
`isPrestack_propQCTopology_iff`. -/
theorem isStack_propQCTopology_iff [(propQCTopology P).Subcanonical]
    (F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{v', u'}) :
    F.IsStack (propQCTopology P) ↔
      F.IsStack zariskiTopology ∧
        ∀ ⦃R S : CommRingCat.{u}⦄ (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
          F.IsStackFor (.singleton (Spec.map f)) := by
  refine ⟨fun _ ↦ ⟨.of_le (zariskiTopology_le_propQCTopology (P := P)), fun R S f hf _ ↦
    F.isStackFor _ (Hom.generate_singleton_mem_propQCTopology _ hf)⟩, fun ⟨_, hF⟩ ↦ ?_⟩
  have := (isPrestack_propQCTopology_iff F).2
    ⟨inferInstance, fun R S f hf hs ↦ (hF f hf hs).isPrestackFor⟩
  refine Pseudofunctor.IsStack.of_precoverage fun T R hR ↦ ?_
  obtain ⟨E₀, rfl⟩ := R.exists_eq_preZeroHypercover
  let E : Precoverage.ZeroHypercover (propQCPrecoverage P) T := ⟨E₀, hR⟩
  let E' := Precoverage.ZeroHypercover.restrictIndexOfSmall.{u} E
  refine Pseudofunctor.IsStackFor.of_le F (isStackFor_ofArrows hF E') (J := propQCTopology P)
    (Precoverage.generate_mem_toGrothendieck E'.mem₀) ?_
  rintro _ _ ⟨i⟩
  exact ⟨_⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A pseudofunctor is a stack for the fpqc topology if and only if it is a stack for the
Zariski topology and has effective descent along every faithfully flat morphism of affine
schemes. The implication from right to left is Vistoli's Lemma 4.25, stated there for fibered
categories over the category of schemes over a base scheme. -/
theorem isStack_fpqcTopology_iff (F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{v', u'}) :
    F.IsStack fpqcTopology ↔ F.IsStack zariskiTopology ∧
      ∀ ⦃R S : CommRingCat.{u}⦄ (f : R ⟶ S), Flat (Spec.map f) → Surjective (Spec.map f) →
        F.IsStackFor (.singleton (Spec.map f)) := by
  have : (propQCTopology @Flat).Subcanonical := fpqcTopology_eq_propQCTopology ▸ inferInstance
  rw [fpqcTopology_eq_propQCTopology]
  exact isStack_propQCTopology_iff _ F

set_option backward.isDefEq.respectTransparency.types false in
/-- A pseudofunctor is a stack for the fppf topology if and only if it is a stack for the
Zariski topology and has effective descent along every faithfully flat morphism of affine
schemes that is locally of finite presentation. -/
theorem isStack_fppfTopology_iff (F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{v', u'}) :
    F.IsStack fppfTopology ↔ F.IsStack zariskiTopology ∧
      ∀ ⦃R S : CommRingCat.{u}⦄ (f : R ⟶ S), Flat (Spec.map f) →
        LocallyOfFinitePresentation (Spec.map f) → Surjective (Spec.map f) →
          F.IsStackFor (.singleton (Spec.map f)) := by
  have : MorphismProperty.IsMultiplicative @LocallyOfFinitePresentation :=
    { id_mem := fun _ ↦ inferInstance }
  have : (propQCTopology (@Flat ⊓ @LocallyOfFinitePresentation)).Subcanonical :=
    fppfTopology_eq_propQCTopology ▸ inferInstance
  rw [fppfTopology_eq_propQCTopology, isStack_propQCTopology_iff]
  exact and_congr_right fun _ ↦ forall₃_congr fun _ _ _ ↦
    ⟨fun h hf hl ↦ h ⟨hf, hl⟩, fun h hf ↦ h hf.1 hf.2⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A pseudofunctor is a stack for the étale topology if and only if it is a stack for the
Zariski topology and has effective descent along every surjective étale morphism of affine
schemes. -/
theorem isStack_etaleTopology_iff (F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{v', u'}) :
    F.IsStack etaleTopology ↔ F.IsStack zariskiTopology ∧
      ∀ ⦃R S : CommRingCat.{u}⦄ (f : R ⟶ S), Etale (Spec.map f) → Surjective (Spec.map f) →
        F.IsStackFor (.singleton (Spec.map f)) := by
  have : (propQCTopology @Etale).Subcanonical := etaleTopology_eq_propQCTopology ▸ inferInstance
  rw [etaleTopology_eq_propQCTopology]
  exact isStack_propQCTopology_iff _ F

end AlgebraicGeometry

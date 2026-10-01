/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Morphisms.AlmostDisconnected
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The filtration property

Definition 3.19 of [arXiv:2607.28411v1](https://arxiv.org/abs/2607.28411v1) describes a
filtration of the diagonal kernel on `X ×_Y X` by graph sheaves.  Lemma B.4 gives the neutral
geometric characterization used here: for separated `f : X ⟶ Y`, the first projection is
almost disconnected and every closed support occurring in its witness also maps isomorphically
to `X` under the second projection.

## Main definitions

* `AlgebraicGeometry.FiltrationProperty.Witness`: the data of Lemma B.4 for a morphism `f`.
* `AlgebraicGeometry.FiltrationProperty.Witness.automorphism`: the automorphism of `X` over `Y`
  recovered from the two support isomorphisms of a graded piece.
* `AlgebraicGeometry.HasFiltrationProperty`: the morphism property of admitting such a witness.

## Main results

* `AlgebraicGeometry.FiltrationProperty.monoWitness`,
  `AlgebraicGeometry.HasFiltrationProperty.of_mono` and
  `AlgebraicGeometry.HasFiltrationProperty.of_isIso`: monomorphisms, in particular isomorphisms,
  have the filtration property.  For an isomorphism this is the trivial-Galois-group case of
  Example 3.20(1); the mono case is not in the paper.
* `AlgebraicGeometry.FiltrationProperty.monoWitness_automorphism_eq_refl`: the recovered
  automorphism of this witness is the identity.
* `AlgebraicGeometry.HasFiltrationProperty.monomorphisms_le`: the same as an inequality of
  morphism properties.

## Implementation notes

This formulation is intentionally an independent consumer of
`AlgebraicGeometry.IsAlmostDisconnected`; graph sheaves and stability conditions do not enter the
morphism root.  The two support isomorphisms canonically recover the relative automorphisms
appearing in Definition 3.19.

Lemma B.5 (flat-base-change stability) is informally Lemma B.2 plus the standard comparison
between base change of the relative self-product and the self-product after base change.  It is
not asserted until Lemma B.2 and the cartesian comparison described in
`AlmostDisconnected.lean` exist.

## References

* [arXiv:2607.28411v1](https://arxiv.org/abs/2607.28411v1), Definition 3.19, Example 3.20(1) and
  Appendix B, Lemma B.4.

## Tags

filtration property, almost disconnected morphism, kernel pair, Galois cover
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

namespace FiltrationProperty

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Data for the filtration property, in the equivalent form of Lemma B.4 of
arXiv:2607.28411v1. -/
structure Witness (f : X ⟶ Y) where
  /-- Definition 3.19 assumes that `f` is separated. -/
  isSeparated : IsSeparated f
  /-- The first projection `X ×_Y X ⟶ X` is almost disconnected. -/
  kernel : AlmostDisconnected.Witness (pullback.fst f f)
  /-- Every support in the kernel filtration maps isomorphically to `X` by `p₂`. -/
  secondProjectionIso : ∀ i, kernel.support i ≅ X
  /-- The second support isomorphism is induced by the second projection. -/
  secondProjectionIso_hom : ∀ i,
    (secondProjectionIso i).hom = kernel.inclusion i ≫ pullback.snd f f

namespace Witness

variable (W : Witness f)

/-- The relative automorphism of `X` recovered from the two support isomorphisms in Lemma B.4. -/
noncomputable def automorphism (i : Fin W.kernel.filtration.length) : X ≅ X :=
  (W.kernel.baseIso i).symm ≪≫ W.secondProjectionIso i

/-- The recovered automorphism is a morphism over `Y`. -/
theorem automorphism_hom_over (i : Fin W.kernel.filtration.length) :
    (W.automorphism i).hom ≫ f = f := by
  change (W.kernel.baseIso i).inv ≫ (W.secondProjectionIso i).hom ≫ f = f
  rw [W.secondProjectionIso_hom i]
  simp only [Category.assoc]
  rw [← pullback.condition]
  rw [← Category.assoc (W.kernel.inclusion i) (pullback.fst f f) f]
  rw [← W.kernel.baseIso_hom i]
  simp

/-- The inverse of the recovered automorphism is also a morphism over `Y`. -/
theorem automorphism_inv_over (i : Fin W.kernel.filtration.length) :
    (W.automorphism i).inv ≫ f = f := by
  calc
    (W.automorphism i).inv ≫ f =
        (W.automorphism i).inv ≫ ((W.automorphism i).hom ≫ f) := by
      rw [W.automorphism_hom_over i]
    _ = ((W.automorphism i).inv ≫ (W.automorphism i).hom) ≫ f :=
      (Category.assoc _ _ _).symm
    _ = f := by simp

/-- The automorphism of `X` regarded intrinsically as an automorphism of the object `X ⟶ Y` in
the over-category. -/
noncomputable def overAutomorphism (i : Fin W.kernel.filtration.length) :
    Over.mk f ≅ Over.mk f where
  hom := Over.homMk (W.automorphism i).hom (W.automorphism_hom_over i)
  inv := Over.homMk (W.automorphism i).inv (W.automorphism_inv_over i)
  hom_inv_id := by
    ext
    simp
  inv_hom_id := by
    ext
    simp

end Witness

/-- The filtration property of a monomorphism, with the single support `X ×_Y X ≅ X`.

For a monomorphism `f` both projections of `X ×_Y X` are isomorphisms and agree
(`CategoryTheory.Limits.fst_eq_snd_of_mono_eq`).  So
`AlgebraicGeometry.AlmostDisconnected.isoWitness` for the first
projection is a one-step kernel witness, and Lemma B.4 requires `p₂ ∘ ι₁` to be an isomorphism as
well, which holds because `p₂ = p₁`.  Separatedness is Mathlib's
`AlgebraicGeometry.IsSeparated.isSeparated_of_mono`. -/
noncomputable def monoWitness (f : X ⟶ Y) [Mono f] : Witness f where
  isSeparated := inferInstance
  kernel := AlmostDisconnected.isoWitness (pullback.fst f f)
  secondProjectionIso := fun _ => (asIso (pullback.snd f f) : pullback f f ≅ X)
  secondProjectionIso_hom := fun _ => by
    change (asIso (pullback.snd f f)).hom = 𝟙 _ ≫ pullback.snd f f
    simp

/-- For a monomorphism `f`, the automorphism `p₂ ∘ ι₁ ∘ (p₁ ∘ ι₁)⁻¹` that the witness
`monoWitness f` recovers in Lemma B.4 is the identity, because `p₁ = p₂`
(`CategoryTheory.Limits.fst_eq_snd_of_mono_eq`). -/
theorem monoWitness_automorphism_eq_refl (f : X ⟶ Y) [Mono f]
    (i : Fin (monoWitness f).kernel.filtration.length) :
    (monoWitness f).automorphism i = Iso.refl X := by
  ext
  change (asIso (pullback.fst f f)).inv ≫ (asIso (pullback.snd f f)).hom = 𝟙 _
  simp [fst_eq_snd_of_mono_eq f]

end FiltrationProperty

/-- The filtration property of Definition 3.19, represented by the equivalent scheme-theoretic
criterion of Lemma B.4 of arXiv:2607.28411v1. -/
def HasFiltrationProperty : MorphismProperty Scheme :=
  fun _ _ f => Nonempty (FiltrationProperty.Witness f)

namespace HasFiltrationProperty

/-- A monomorphism has the filtration property: `X ×_Y X ≅ X`, the single graph is the diagonal
and the automorphism is the identity
(`AlgebraicGeometry.FiltrationProperty.monoWitness_automorphism_eq_refl`). -/
theorem of_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] : HasFiltrationProperty f :=
  ⟨FiltrationProperty.monoWitness f⟩

/-- The lattice form of `AlgebraicGeometry.HasFiltrationProperty.of_mono`, for combining with other
morphism properties by `le_trans`.  There is no `CategoryTheory.MorphismProperty.RespectsIso`
instance for this property, so it is proved directly. -/
theorem monomorphisms_le : MorphismProperty.monomorphisms Scheme ≤ HasFiltrationProperty :=
  fun _ _ f (_ : Mono f) => of_mono f

/-- An isomorphism has the filtration property.  This is the trivial-Galois-group case of
Example 3.20(1) of arXiv:2607.28411v1, in the Lemma B.4 formulation. -/
theorem of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : HasFiltrationProperty f :=
  of_mono f

end HasFiltrationProperty

end AlgebraicGeometry

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

This formulation is intentionally an independent consumer of `IsAlmostDisconnected`; graph
sheaves and stability conditions do not enter the morphism root.  The two support isomorphisms
canonically recover the relative automorphisms appearing in Definition 3.19.

Lemma B.5 (flat-base-change stability) will follow from Lemma B.2 plus the standard comparison
between base change of the relative self-product and the self-product after base change.  It is
not asserted until the missing neutral flat-pullback/pushforward comparison documented in
`AlmostDisconnected.lean` exists.
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

end FiltrationProperty

/-- The filtration property of Definition 3.19, represented by the equivalent scheme-theoretic
criterion of Lemma B.4 of arXiv:2607.28411v1. -/
def HasFiltrationProperty : MorphismProperty Scheme :=
  fun _ _ f => Nonempty (FiltrationProperty.Witness f)

end AlgebraicGeometry

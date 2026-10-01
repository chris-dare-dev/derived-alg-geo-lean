/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The projection morphism of a monoidal adjunction

Let F ⊣ G be an adjunction between monoidal categories C and D, with F : C ⥤ D oplax monoidal, G : D
⥤ C lax monoidal, and `CategoryTheory.Adjunction.IsMonoidal` expressing the compatibility of the two
structures. For M in D and K in C the projection morphism is the composite G(M) ⊗ K ⟶ G(M) ⊗ G(F(K))
⟶ G(M ⊗ F(K)) of the unit of the adjunction and the tensorator of G. For F the pullback and G the
pushforward of module sheaves, it is the morphism of the projection formula.

If F is monoidal and K has a two-sided tensor inverse, the projection morphism is an isomorphism for
every M. No rigidity, symmetry or braiding is assumed.

## Main definitions

* `CategoryTheory.Adjunction.projectionMorphism`: the projection morphism.
* `CategoryTheory.MonoidalCategory.TensorInverse`: a two-sided tensor inverse of an object.
* `CategoryTheory.Adjunction.projectionIso`: the projection isomorphism at an object with a tensor
  inverse.

## Main results

* `CategoryTheory.Adjunction.projectionMorphism_naturality_left` and
  `CategoryTheory.Adjunction.projectionMorphism_naturality_right`: naturality in M and in K.
* `CategoryTheory.Adjunction.projectionMorphism_tensor`: compatibility with the tensor product in K.
* `CategoryTheory.Adjunction.projectionMorphism_tensorUnit`: the projection morphism at the tensor
  unit is a structural isomorphism.
* `CategoryTheory.Adjunction.isIso_projectionMorphism`: the projection morphism at an object with a
  two-sided tensor inverse is an isomorphism.

## Implementation notes

The declarations about the adjunction are in the namespace `CategoryTheory.Adjunction`, next to
Mathlib's `CategoryTheory.Adjunction.IsMonoidal`, so they are available by dot notation on the
adjunction. The proof of `CategoryTheory.Adjunction.isIso_projectionMorphism` is formal. For K ⊗ K'
≅ 𝟙, the tensor compatibility expresses the projection morphism at K ⊗ K' as the projection morphism
at K whiskered by K', followed by the projection morphism at K' on M ⊗ F(K), up to isomorphisms, so
the second factor is a split epimorphism. Exchanging the roles of K and K' shows it is also a
monomorphism, hence an isomorphism, hence so is the whiskered first factor, and whiskering by K'
reflects isomorphisms. Several proofs set `backward.isDefEq.respectTransparency false`, because the
components of the unit have source `(𝟭 C).obj K`, which is not reducibly K.

## References

* The Stacks Project, Tag 01E8 (Lemma 20.54.2, the projection formula for a finite locally free
  module on a ringed space), as the geometric statement of which this is the formal categorical form
  for invertible objects. The statement was not obtained verbatim: only a summary of that page was
  fetched, so the tag gives literature context and is not quoted.

## Tags

monoidal adjunction, projection formula, projection morphism, tensor inverse, invertible object
-/

namespace CategoryTheory

open Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

universe v₁ v₂ u₁ u₂

namespace MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- A two-sided tensor inverse of an object `K` of a monoidal category: an object `obj`
together with isomorphisms `K ⊗ obj ≅ 𝟙_ C` and `obj ⊗ K ≅ 𝟙_ C`. No compatibility
between the two isomorphisms is required. -/
structure TensorInverse (K : C) where
  /-- The inverse object. -/
  obj : C
  /-- The isomorphism `K ⊗ obj ≅ 𝟙_ C`. -/
  rightIso : K ⊗ obj ≅ 𝟙_ C
  /-- The isomorphism `obj ⊗ K ≅ 𝟙_ C`. -/
  leftIso : obj ⊗ K ≅ 𝟙_ C

end MonoidalCategory

namespace Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- The projection morphism `G.obj M ⊗ K ⟶ G.obj (M ⊗ F.obj K)` of an adjunction `F ⊣ G`
with `G` lax monoidal: the unit `K ⟶ G.obj (F.obj K)` followed by the tensorator of `G`. -/
def projectionMorphism [G.LaxMonoidal] (M : D) (K : C) :
    G.obj M ⊗ K ⟶ G.obj (M ⊗ F.obj K) :=
  G.obj M ◁ adj.unit.app K ≫ μ G M (F.obj K)

section Lax

variable [G.LaxMonoidal]

set_option backward.isDefEq.respectTransparency false in
/-- The projection morphism is natural in the object `M` of `D`. -/
@[reassoc]
lemma projectionMorphism_naturality_left {M M' : D} (g : M ⟶ M') (K : C) :
    adj.projectionMorphism M K ≫ G.map (g ▷ F.obj K) =
      G.map g ▷ K ≫ adj.projectionMorphism M' K := by
  dsimp only [projectionMorphism, Functor.id_obj, Functor.comp_obj]
  rw [assoc, ← μ_natural_left, ← whisker_exchange_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The projection morphism is natural in the object `K` of `C`. -/
@[reassoc]
lemma projectionMorphism_naturality_right (M : D) {K K' : C} (f : K ⟶ K') :
    adj.projectionMorphism M K ≫ G.map (M ◁ F.map f) =
      G.obj M ◁ f ≫ adj.projectionMorphism M K' := by
  have h := adj.unit.naturality f
  dsimp at h
  dsimp only [projectionMorphism, Functor.id_obj, Functor.comp_obj]
  rw [assoc, ← μ_natural_right, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, h]

/-- Being an isomorphism is invariant under replacing `K` by an isomorphic object. -/
lemma isIso_projectionMorphism_of_iso (M : D) {K K' : C} (e : K ≅ K')
    [IsIso (adj.projectionMorphism M K')] : IsIso (adj.projectionMorphism M K) := by
  have : IsIso (adj.projectionMorphism M K ≫ G.map (M ◁ F.map e.hom)) := by
    rw [projectionMorphism_naturality_right]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.map (M ◁ F.map e.hom))

end Lax

/-- A coherence identity used to compare projection morphisms. -/
private lemma whiskerLeft_tensorHom_comp_aux (X : C) {K₁ A₁ K₂ A₂ Y Z : C} (u₁ : K₁ ⟶ A₁)
    (u₂ : K₂ ⟶ A₂) (m : X ⊗ A₁ ⟶ Y) (n : Y ⊗ A₂ ⟶ Z) :
    X ◁ (u₁ ⊗ₘ u₂) ≫ (α_ X A₁ A₂).inv ≫ m ▷ A₂ ≫ n =
      (α_ X K₁ K₂).inv ≫ (X ◁ u₁ ≫ m) ▷ K₂ ≫ Y ◁ u₂ ≫ n := by
  simp only [tensorHom_def, whiskerLeft_comp, comp_whiskerRight, assoc,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_inv_naturality_middle_assoc]

/-- Conjugating `(f ▷ A) ▷ B` by `A ⊗ B ≅ 𝟙_ C` recovers `f`. -/
private lemma eq_conj_whiskerRight_whiskerRight {A B : C} (e : A ⊗ B ≅ 𝟙_ C) {X Y : C}
    (f : X ⟶ Y) :
    f = (ρ_ X).inv ≫ X ◁ e.inv ≫ (α_ X A B).inv ≫ (f ▷ A) ▷ B ≫ (α_ Y A B).hom ≫
      Y ◁ e.hom ≫ (ρ_ Y).hom := by
  rw [whiskerRight_tensor_symm, assoc, assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc,
    whisker_exchange_assoc, ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp,
    whiskerRight_id]
  simp

/-- Right whiskering by `A` reflects isomorphisms when `A ⊗ B ≅ 𝟙_ C` for some `B`. -/
private lemma isIso_of_isIso_whiskerRight {A B : C} (e : A ⊗ B ≅ 𝟙_ C) {X Y : C} (f : X ⟶ Y)
    [IsIso (f ▷ A)] : IsIso f := by
  rw [eq_conj_whiskerRight_whiskerRight e f]
  infer_instance

/-- If `f ▷ A ≫ g` is an isomorphism and `A ⊗ B ≅ 𝟙_ C`, then `f` is a monomorphism. -/
private lemma mono_of_isIso_whiskerRight_comp {A B : C} (e : A ⊗ B ≅ 𝟙_ C) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⊗ A ⟶ Z) (h : IsIso (f ▷ A ≫ g)) : Mono f := by
  have : IsIso ((f ▷ A ≫ g) ▷ B) := inferInstance
  rw [comp_whiskerRight] at this
  have : Mono ((f ▷ A) ▷ B) := mono_of_mono _ (g ▷ B)
  rw [eq_conj_whiskerRight_whiskerRight e f]
  infer_instance

omit [MonoidalCategory C] in
/-- If `f ≫ g` is an isomorphism, then `g` is a split epimorphism. -/
private lemma isSplitEpi_of_isIso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso (f ≫ g)] :
    IsSplitEpi g :=
  IsSplitEpi.mk' ⟨inv (f ≫ g) ≫ f, by simp⟩

section Oplax

variable [F.OplaxMonoidal] [G.LaxMonoidal] [adj.IsMonoidal]

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the projection morphism with the tensor product in `K`: up to the
associators and the comonoidal structure `δ F` of the left adjoint, `p_{M, K₁ ⊗ K₂}` is
`p_{M, K₁} ▷ K₂` followed by `p_{M ⊗ F.obj K₁, K₂}`. -/
@[reassoc]
lemma projectionMorphism_tensor (M : D) (K₁ K₂ : C) :
    adj.projectionMorphism M (K₁ ⊗ K₂) ≫
        G.map (M ◁ δ F K₁ K₂ ≫ (α_ M (F.obj K₁) (F.obj K₂)).inv) =
      (α_ (G.obj M) K₁ K₂).inv ≫ adj.projectionMorphism M K₁ ▷ K₂ ≫
        adj.projectionMorphism (M ⊗ F.obj K₁) K₂ := by
  have h := adj.unit_app_tensor_comp_map_δ K₁ K₂
  dsimp at h
  dsimp only [projectionMorphism, Functor.id_obj, Functor.comp_obj]
  rw [Functor.map_comp, assoc, ← μ_natural_right_assoc, ← whiskerLeft_comp_assoc, h,
    whiskerLeft_comp_assoc, whiskerLeft_μ_comp_μ_assoc, ← Functor.map_comp, Iso.hom_inv_id,
    Functor.map_id, comp_id]
  exact whiskerLeft_tensorHom_comp_aux _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The projection morphism at the tensor unit, followed by `G` applied to the counit
`η F` of the left adjoint and the right unitor, is the right unitor of `G.obj M`. -/
@[reassoc]
lemma projectionMorphism_tensorUnit (M : D) :
    adj.projectionMorphism M (𝟙_ C) ≫ G.map (M ◁ η F ≫ (ρ_ M).hom) = (ρ_ (G.obj M)).hom := by
  have h := adj.unit_app_unit_comp_map_η
  dsimp at h
  dsimp only [projectionMorphism, Functor.id_obj, Functor.comp_obj]
  rw [Functor.map_comp, assoc, ← μ_natural_right_assoc, ← whiskerLeft_comp_assoc, h]
  exact (right_unitality G M).symm

end Oplax

section Monoidal

variable [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

/-- For a monoidal left adjoint, `p_{M, K₁ ⊗ K₂}` factors through `p_{M, K₁} ▷ K₂` and
`p_{M ⊗ F.obj K₁, K₂}`, followed by `G` applied to the associator and the tensorator
`μ F K₁ K₂`. -/
lemma projectionMorphism_tensor_eq (M : D) (K₁ K₂ : C) :
    adj.projectionMorphism M (K₁ ⊗ K₂) =
      (α_ (G.obj M) K₁ K₂).inv ≫ adj.projectionMorphism M K₁ ▷ K₂ ≫
        adj.projectionMorphism (M ⊗ F.obj K₁) K₂ ≫
          G.map ((α_ M (F.obj K₁) (F.obj K₂)).hom ≫ M ◁ μ F K₁ K₂) := by
  rw [← projectionMorphism_tensor_assoc, ← Functor.map_comp]
  simp

/-- For a monoidal left adjoint, the projection morphism at the tensor unit is the right
unitor followed by `G` applied to the inverse right unitor and the unit `ε F`. -/
lemma projectionMorphism_tensorUnit_eq (M : D) :
    adj.projectionMorphism M (𝟙_ C) = (ρ_ (G.obj M)).hom ≫ G.map ((ρ_ M).inv ≫ M ◁ ε F) := by
  rw [← adj.projectionMorphism_tensorUnit, assoc, ← Functor.map_comp]
  simp

/-- The projection morphism at the tensor unit is an isomorphism. -/
instance isIso_projectionMorphism_tensorUnit (M : D) :
    IsIso (adj.projectionMorphism M (𝟙_ C)) := by
  rw [projectionMorphism_tensorUnit_eq]
  infer_instance

/-- If `K ⊗ K' ≅ 𝟙_ C`, then `p_{M,K} ▷ K' ≫ p_{M ⊗ F.obj K, K'}` is an isomorphism. -/
lemma isIso_projectionMorphism_whiskerRight_comp {K K' : C} (e : K ⊗ K' ≅ 𝟙_ C) (M : D) :
    IsIso (adj.projectionMorphism M K ▷ K' ≫ adj.projectionMorphism (M ⊗ F.obj K) K') := by
  have := adj.isIso_projectionMorphism_of_iso M e
  have : IsIso ((α_ (G.obj M) K K').inv ≫ adj.projectionMorphism M K ▷ K' ≫
      adj.projectionMorphism (M ⊗ F.obj K) K') := by
    rw [← projectionMorphism_tensor]
    infer_instance
  exact IsIso.of_isIso_comp_left (α_ (G.obj M) K K').inv _

/-- **Projection formula for invertible objects.** If `K` has a two-sided tensor inverse
`K'`, then the projection morphism `G.obj M ⊗ K ⟶ G.obj (M ⊗ F.obj K)` is an isomorphism
for every `M`. -/
theorem isIso_projectionMorphism (M : D) {K K' : C} (e₁ : K ⊗ K' ≅ 𝟙_ C)
    (e₂ : K' ⊗ K ≅ 𝟙_ C) : IsIso (adj.projectionMorphism M K) := by
  have := adj.isIso_projectionMorphism_whiskerRight_comp e₁ M
  have : Mono (adj.projectionMorphism (M ⊗ F.obj K) K') :=
    mono_of_isIso_whiskerRight_comp e₁ _ _
      (adj.isIso_projectionMorphism_whiskerRight_comp e₂ (M ⊗ F.obj K))
  have : IsSplitEpi (adj.projectionMorphism (M ⊗ F.obj K) K') :=
    isSplitEpi_of_isIso_comp (adj.projectionMorphism M K ▷ K') _
  have := isIso_of_mono_of_isSplitEpi (adj.projectionMorphism (M ⊗ F.obj K) K')
  have : IsIso (adj.projectionMorphism M K ▷ K') :=
    IsIso.of_isIso_comp_right _ (adj.projectionMorphism (M ⊗ F.obj K) K')
  exact isIso_of_isIso_whiskerRight e₂ _

/-- The projection morphism at an object with a tensor inverse is an isomorphism. -/
theorem isIso_projectionMorphism_of_tensorInverse (M : D) {K : C} (h : TensorInverse K) :
    IsIso (adj.projectionMorphism M K) :=
  adj.isIso_projectionMorphism M h.rightIso h.leftIso

/-- The projection isomorphism `G.obj M ⊗ K ≅ G.obj (M ⊗ F.obj K)` for an object `K` with a
tensor inverse. -/
noncomputable def projectionIso (M : D) {K : C} (h : TensorInverse K) :
    G.obj M ⊗ K ≅ G.obj (M ⊗ F.obj K) :=
  have := adj.isIso_projectionMorphism_of_tensorInverse M h
  asIso (adj.projectionMorphism M K)

/-- The forward morphism of `CategoryTheory.Adjunction.projectionIso` is the projection morphism. -/
@[simp]
lemma projectionIso_hom (M : D) {K : C} (h : TensorInverse K) :
    (adj.projectionIso M h).hom = adj.projectionMorphism M K :=
  rfl

end Monoidal

end Adjunction

end CategoryTheory

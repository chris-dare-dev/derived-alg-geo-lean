/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Monoidal
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Dual

/-!
# The projection formula for invertible sheaves

For a morphism of schemes `f : X ⟶ Y`, a module sheaf `M` on `X` and an invertible sheaf `L` on
`Y`, the projection map `f_*M ⊗ L ⟶ f_*(M ⊗ f^*L)` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.projectionMap`: the unit `L ⟶ f_*f^*L`, then the lax
  structure of `f_*` (`AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_projectionMap_of_isInvertible`: the projection map is
  an isomorphism when `L` is invertible.

## Implementation notes

The argument uses only the monoidal structures and a tensor inverse of `L`; it never computes on
sections. Projection maps compose: tensoring the map for `L` with `K` and then applying the map
for `K` gives the map for `L ⊗ K`, up to the associators and the tensorator of the strong
monoidal `f^*`. The map for `𝒪_Y` is an isomorphism by unitality. If `L ⊗ K ≅ 𝒪_Y` and
`K ⊗ L ≅ 𝒪_Y`, the first composite makes the map for `L` a split monomorphism, and the second,
applied to `M ⊗ f^*L ⊗ f^*K ≅ M`, makes it a split epimorphism. An invertible sheaf has such a
`K`, its sheafified dual (`AlgebraicGeometry.Scheme.Modules.tensorDualIso`).

## References

* Stacks Project, Tag 01E8 (the projection formula), the case `q = 0` for a rank-one sheaf.

## Tags

projection formula, invertible sheaf, pushforward, pullback, monoidal adjunction
-/

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

section Adjunction

variable {C D : Type*} [Category* C] [MonoidalCategory C] [Category* D] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.LaxMonoidal]

/-- The projection map `G M ⊗ L ⟶ G (M ⊗ F L)` of an adjunction with lax monoidal right adjoint. -/
private def projMap (M : D) (L : C) : G.obj M ⊗ L ⟶ G.obj (M ⊗ F.obj L) :=
  G.obj M ◁ adj.unit.app L ≫ μ G M (F.obj L)

private lemma projMap_natural_left {N M : D} (e : N ⟶ M) (L : C) :
    projMap adj N L ≫ G.map (e ▷ F.obj L) = G.map e ▷ L ≫ projMap adj M L := by
  simp only [projMap, Category.assoc, ← μ_natural_left]
  rw [← whisker_exchange_assoc]
  rfl

private lemma projMap_natural_right (M : D) {L K : C} (k : L ⟶ K) :
    projMap adj M L ≫ G.map (M ◁ F.map k) = G.obj M ◁ k ≫ projMap adj M K := by
  simp only [projMap, Category.assoc, ← μ_natural_right]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [adj.unit.naturality k]
  rfl

private lemma isIso_projMap_of_iso (M : D) {L L' : C} (e : L ≅ L')
    [IsIso (projMap adj M L')] : IsIso (projMap adj M L) := by
  have : IsIso (projMap adj M L ≫ G.map (M ◁ F.map e.hom)) := by
    rw [projMap_natural_right]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.map (M ◁ F.map e.hom))

variable [F.OplaxMonoidal] [adj.IsMonoidal]

private lemma projMap_unit (M : D) :
    projMap adj M (𝟙_ C) ≫ G.map (M ◁ η F) = (ρ_ (G.obj M)).hom ≫ G.map (ρ_ M).inv := by
  simp only [projMap, Category.assoc, ← μ_natural_right,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Adjunction.unit_app_unit_comp_map_η]
  simp

/-- Projection maps compose: the map for `L ⊗ K` is the map for `L`, tensored with `K`, followed
by the map for `K`. -/
private lemma projMap_trans (M : D) (L K : C) :
    projMap adj M L ▷ K ≫ projMap adj (M ⊗ F.obj L) K ≫ G.map (α_ M (F.obj L) (F.obj K)).hom =
      (α_ (G.obj M) L K).hom ≫ projMap adj M (L ⊗ K) ≫ G.map (M ◁ δ F L K) := by
  simp only [projMap, comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc]
  simp only [Functor.comp_obj]
  rw [Functor.LaxMonoidal.associativity, ← μ_natural_right,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Adjunction.unit_app_tensor_comp_map_δ,
    MonoidalCategory.whiskerLeft_comp_assoc]
  have h : (G.obj M ◁ adj.unit.app L) ▷ K ≫ (G.obj M ⊗ G.obj (F.obj L)) ◁ adj.unit.app K ≫
      (α_ (G.obj M) (G.obj (F.obj L)) (G.obj (F.obj K))).hom =
      (α_ (G.obj M) L K).hom ≫ G.obj M ◁ (adj.unit.app L ⊗ₘ adj.unit.app K) := by
    simp [tensorHom_def]
  rw [reassoc_of% h]

variable [IsIso (η F)]

private lemma isIso_projMap_unit (M : D) : IsIso (projMap adj M (𝟙_ C)) := by
  have : IsIso (projMap adj M (𝟙_ C) ≫ G.map (M ◁ η F)) := by
    rw [projMap_unit]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.map (M ◁ η F))

variable [∀ X Y, IsIso (δ F X Y)]

/-- Tensoring with an object that has a tensor inverse reflects split monomorphisms. -/
private lemma isSplitMono_of_whiskerRight {A B : C} (g : A ⟶ B) {K L : C} (e : K ⊗ L ≅ 𝟙_ C)
    [IsSplitMono (g ▷ K)] : IsSplitMono g := by
  let θ : tensorRight K ⋙ tensorRight L ≅ 𝟭 C :=
    (tensorRightTensor K L).symm ≪≫ (tensoringRight C).mapIso e ≪≫ rightUnitorNatIso C
  have hg : g = θ.inv.app A ≫ (tensorRight L).map (g ▷ K) ≫ θ.hom.app B :=
    (NatIso.naturality_1 θ g).symm
  rw [hg]
  infer_instance

/-- The projection map for an object with a two-sided tensor inverse is an isomorphism. -/
private theorem isIso_projMap (M : D) {L K : C} (e₁ : L ⊗ K ≅ 𝟙_ C) (e₂ : K ⊗ L ≅ 𝟙_ C) :
    IsIso (projMap adj M L) := by
  have hLK (N : D) : IsIso (projMap adj N (L ⊗ K)) := by
    have := isIso_projMap_unit adj N
    exact isIso_projMap_of_iso adj N e₁
  have hKL (N : D) : IsIso (projMap adj N (K ⊗ L)) := by
    have := isIso_projMap_unit adj N
    exact isIso_projMap_of_iso adj N e₂
  have : IsSplitMono (projMap adj M L ▷ K) := by
    have := hLK M
    let r := (α_ (G.obj M) L K).hom ≫ projMap adj M (L ⊗ K) ≫ G.map (M ◁ δ F L K)
    exact IsSplitMono.mk' ⟨(projMap adj (M ⊗ F.obj L) K ≫
      G.map (α_ M (F.obj L) (F.obj K)).hom) ≫ inv r, by
        rw [← Category.assoc, projMap_trans, IsIso.hom_inv_id]⟩
  have := isSplitMono_of_whiskerRight (projMap adj M L) e₂
  let N := M ⊗ F.obj L
  have hepi : IsSplitEpi (projMap adj (N ⊗ F.obj K) L) := by
    have := hKL N
    let r := (α_ (G.obj N) K L).hom ≫ projMap adj N (K ⊗ L) ≫ G.map (N ◁ δ F K L)
    have : IsSplitEpi (projMap adj (N ⊗ F.obj K) L ≫ G.map (α_ N (F.obj K) (F.obj L)).hom) :=
      IsSplitEpi.mk' ⟨inv r ≫ projMap adj N K ▷ L, by
        rw [Category.assoc, projMap_trans, IsIso.inv_hom_id]⟩
    have : projMap adj (N ⊗ F.obj K) L = (projMap adj (N ⊗ F.obj K) L ≫
        G.map (α_ N (F.obj K) (F.obj L)).hom) ≫ inv (G.map (α_ N (F.obj K) (F.obj L)).hom) := by
      simp
    rw [this]
    infer_instance
  let φ : (N ⊗ F.obj K) ≅ M := (α_ M (F.obj L) (F.obj K) ≪≫
    whiskerLeftIso M ((asIso (δ F L K)).symm ≪≫ F.mapIso e₁ ≪≫ asIso (η F)) ≪≫ ρ_ M)
  have hφ : projMap adj M L = inv (G.map φ.hom ▷ L) ≫ projMap adj (N ⊗ F.obj K) L ≫
      G.map (φ.hom ▷ F.obj L) := by
    rw [projMap_natural_left, IsIso.inv_hom_id_assoc]
  have : IsSplitEpi (projMap adj M L) := by
    rw [hφ]
    infer_instance
  exact isIso_of_epi_of_isSplitMono _

end Adjunction

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The projection map `f_*M ⊗ L ⟶ f_*(M ⊗ f^*L)`: the unit `L ⟶ f_*f^*L`, then the lax
structure of `f_*`. -/
def projectionMap (M : X.Modules) (L : Y.Modules) :
    tensorObj ((pushforward f).obj M) L ⟶
      (pushforward f).obj (tensorObj M ((pullback f).obj L)) :=
  (pushforward f).obj M ◁ (pullbackPushforwardAdjunction f).unit.app L ≫
    μ (pushforward f) M ((pullback f).obj L)

/-- The projection formula for an invertible sheaf (Stacks, Tag 01E8, the case `q = 0`). -/
theorem isIso_projectionMap_of_isInvertible (M : X.Modules) (L : Y.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} (show SheafOfModules Y.ringCatSheaf from L)] :
    IsIso (projectionMap f M L) :=
  isIso_projMap (pullbackPushforwardAdjunction f) M (tensorDualIso L)
    (tensorCommIso (dualLine L) L ≪≫ tensorDualIso L)

end

end AlgebraicGeometry.Scheme.Modules

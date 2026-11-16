/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Descent along a pullback-preserving reindexing

Let `Φ : D ⥤ C` be a functor and `G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` a pseudofunctor. For a
family of morphisms `f i : X i ⟶ S` of `D` whose pairwise and triple pullbacks exist in `D` and
are preserved by `Φ`, the reindexed pseudofunctor `Φ.op.toPseudofunctor.comp G` has effective
descent along `f` exactly when `G` has effective descent along the image family `Φ.map (f i)`.

## Main definitions

None. The images of chosen pullbacks under `Φ`, and the equivalence between the two categories
`DescentData'` that they induce, are private to this file.

## Main results

* `Pseudofunctor.isStackFor_ofArrows_comp_toPseudofunctor_iff`: under these hypotheses,
  `Φ.op.toPseudofunctor.comp G` is a stack for `Presieve.ofArrows X f` if and only if `G` is a
  stack for `Presieve.ofArrows (fun i ↦ Φ.obj (X i)) (fun i ↦ Φ.map (f i))`.
* `Pseudofunctor.isStackFor_singleton_comp_toPseudofunctor_iff`: the case of one morphism.

## Implementation notes

`DescentData` quantifies over every test object of the site, and `D` and `C` have different
test objects, so the categories of descent data are not compared directly. Both sides are
replaced by `DescentData'` through `DescentData'.descentDataEquivalence`. `DescentData'` only
involves the chosen pairwise and triple pullbacks of the family and the pullback functors
between their fibres. The images under `Φ` of chosen pullbacks in `D` are chosen pullbacks in
`C`, the fibres of `Φ.op.toPseudofunctor.comp G` are those of `G`, and its compositors are those
of `G` at the images, so the two categories `DescentData'` have the same objects and
morphisms.

The triple pullback of `f i`, `f j` and `f k` is the pullback of `pullback.snd (f i) (f j)` and
`pullback.fst (f j) (f k)`, the shape `ChosenPullback₃` uses. Its existence in `D` is a
hypothesis: preservation of pullbacks by `Φ` does not provide it.

## References

No literature source is followed. Both sides are compared through Mathlib's
`Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime`, which relates `DescentData'` to
`DescentData`.

## Tags

descent, stack, reindexing, pullback
-/

universe t v₂ v' v u₂ u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory Limits LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D] (Φ : D ⥤ C)
  (G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- The compositors of `Φ.op.toPseudofunctor.comp G` are those of `G` at the images. -/
private lemma comp_mapComp'_eq {a b c : LocallyDiscrete Dᵒᵖ} (u : a ⟶ b) (w : b ⟶ c)
    (uw : a ⟶ c) (h : u ≫ w = uw) :
    (Φ.op.toPseudofunctor.comp G).mapComp' u w uw h =
      G.mapComp' (Φ.op.toPseudofunctor.map u) (Φ.op.toPseudofunctor.map w)
        (Φ.op.toPseudofunctor.map uw)
        (by
          subst h
          exact (obj_ext_of_isDiscrete (Φ.op.toPseudofunctor.mapComp u w).hom).symm) := by
  subst h
  rw [mapComp'_eq_mapComp, Pseudofunctor.comp_mapComp, Pseudofunctor.mapComp']
  congr 1

/-- Pulling back a morphism for `Φ.op.toPseudofunctor.comp G` is pulling it back for `G` along
the image under `Φ`. -/
private lemma pullHom_comp_toPseudofunctor ⦃X₁ X₂ : D⦄
    ⦃M₁ : (Φ.op.toPseudofunctor.comp G).obj (.mk (op X₁))⦄
    ⦃M₂ : (Φ.op.toPseudofunctor.comp G).obj (.mk (op X₂))⦄ ⦃Y : D⦄ ⦃f₁ : Y ⟶ X₁⦄
    ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((Φ.op.toPseudofunctor.comp G).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((Φ.op.toPseudofunctor.comp G).map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : D⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ =
      pullHom (F := G) (f₁ := Φ.map f₁) (f₂ := Φ.map f₂) φ (Φ.map g) (Φ.map gf₁) (Φ.map gf₂)
        (by rw [← Φ.map_comp, hgf₁]) (by rw [← Φ.map_comp, hgf₂]) := by
  dsimp only [pullHom]
  rw [comp_mapComp'_eq, comp_mapComp'_eq]
  rfl

/-- `pullHom` along equal morphisms. -/
private lemma pullHom_congr_left {G' : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} ⦃X₁ X₂ : C⦄
    ⦃M₁ : G'.obj (.mk (op X₁))⦄ ⦃M₂ : G'.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄
    ⦃f₂ : Y ⟶ X₂⦄
    (φ : (G'.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (G'.map f₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ (g g' : Y' ⟶ Y) (hg : g = g') (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (hgf₁' : g' ≫ f₁ = gf₁)
    (hgf₂' : g' ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = pullHom φ g' gf₁ gf₂ hgf₁' hgf₂' := by
  subst hg
  rfl

/-- The image of a chosen pullback under a functor that preserves it. -/
private noncomputable def chosenPullbackMap {X₁ X₂ S : D} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
    (h : ChosenPullback f₁ f₂) [PreservesLimit (cospan f₁ f₂) Φ] :
    ChosenPullback (Φ.map f₁) (Φ.map f₂) where
  pullback := Φ.obj h.pullback
  p₁ := Φ.map h.p₁
  p₂ := Φ.map h.p₂
  condition := by rw [← Φ.map_comp, ← Φ.map_comp, h.condition]
  isLimit := (Φ.map_isPullback h.isPullback).isLimit
  p := Φ.map h.p
  hp₁ := by rw [← Φ.map_comp, h.hp₁]

/-- The image of a chosen triple pullback under a functor that preserves the pullbacks
involved. -/
private noncomputable def chosenPullback₃Map {X₁ X₂ X₃ S : D} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
    {f₃ : X₃ ⟶ S} {h₁₂ : ChosenPullback f₁ f₂} {h₂₃ : ChosenPullback f₂ f₃}
    {h₁₃ : ChosenPullback f₁ f₃} (h : ChosenPullback₃ h₁₂ h₂₃ h₁₃)
    [PreservesLimit (cospan f₁ f₂) Φ] [PreservesLimit (cospan f₂ f₃) Φ]
    [PreservesLimit (cospan f₁ f₃) Φ] [PreservesLimit (cospan h₁₂.p₂ h₂₃.p₁) Φ] :
    ChosenPullback₃ (chosenPullbackMap Φ h₁₂) (chosenPullbackMap Φ h₂₃)
      (chosenPullbackMap Φ h₁₃) where
  chosenPullback := chosenPullbackMap Φ h.chosenPullback
  p := Φ.map h.p
  p₁ := Φ.map h.p₁
  p₃ := Φ.map h.p₃
  l :=
    { f := Φ.map h.l.f
      f_p₁ := by simp [chosenPullbackMap, ← Φ.map_comp]
      f_p₂ := by simp [chosenPullbackMap, ← Φ.map_comp]
      f_p := by simp [chosenPullbackMap, ← Φ.map_comp] }
  hp₁ := by simp [chosenPullbackMap, ← Φ.map_comp, h.hp₁]
  hp₃ := by simp [chosenPullbackMap, ← Φ.map_comp, h.hp₃]

section

variable {ι : Type t} {S : D} {X : ι → D} (f : ∀ i, X i ⟶ S) [∀ i j, HasPullback (f i) (f j)]

/-- The pullbacks of the members of a family, as chosen pullbacks. -/
private noncomputable def chosenPullbackFamily (i j : ι) : ChosenPullback (f i) (f j) where
  pullback := pullback (f i) (f j)
  p₁ := pullback.fst (f i) (f j)
  p₂ := pullback.snd (f i) (f j)
  condition := pullback.condition
  isLimit := pullbackIsPullback (f i) (f j)

/-- The triple pullbacks of the members of a family, as chosen triple pullbacks. -/
private noncomputable def chosenPullback₃Family
    [∀ i j k, HasPullback (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k))] (i j k : ι) :
    ChosenPullback₃ (chosenPullbackFamily f i j) (chosenPullbackFamily f j k)
      (chosenPullbackFamily f i k) where
  chosenPullback :=
    { pullback := pullback (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k))
      p₁ := pullback.fst (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k))
      p₂ := pullback.snd (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k))
      condition :=
        pullback.condition (f := pullback.snd (f i) (f j)) (g := pullback.fst (f j) (f k))
      isLimit := pullbackIsPullback (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k)) }
  l :=
    { f := pullback.lift
        (pullback.fst (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k)) ≫
          pullback.fst (f i) (f j))
        (pullback.snd (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k)) ≫
          pullback.snd (f j) (f k)) (by
          simp only [Category.assoc, pullback.condition, pullback.condition_assoc])
      f_p₁ := by simp [chosenPullbackFamily]
      f_p₂ := by simp [chosenPullbackFamily]
      f_p := by simp [chosenPullbackFamily] }

end

section

variable {ι : Type t} {S : D} {X : ι → D} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j)) [∀ i j, PreservesLimit (cospan (f i) (f j)) Φ]

/-- `pullHom'` for `Φ.op.toPseudofunctor.comp G` over `sq` is `pullHom'` for `G` over the images
of `sq`, at the images of the morphisms. -/
private lemma pullHom'_comp_toPseudofunctor
    {obj obj' : ∀ i, (Φ.op.toPseudofunctor.comp G).obj (.mk (op (X i)))}
    (hom : ∀ (i j : ι),
      ((Φ.op.toPseudofunctor.comp G).map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
        ((Φ.op.toPseudofunctor.comp G).map (sq i j).p₂.op.toLoc).toFunctor.obj (obj' j))
    ⦃Y : D⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂) (hg₁ : g₁ ≫ f i₁ = q)
    (hg₂ : g₂ ≫ f i₂ = q) :
    DescentData'.pullHom' (sq := sq) hom q g₁ g₂ hg₁ hg₂ =
      DescentData'.pullHom' (F := G) (sq := fun i j ↦ chosenPullbackMap Φ (sq i j))
        hom (Φ.map q) (i₁ := i₁) (i₂ := i₂) (Φ.map g₁) (Φ.map g₂)
        (by rw [← Φ.map_comp, hg₁]) (by rw [← Φ.map_comp, hg₂]) := by
  dsimp only [DescentData'.pullHom']
  rw [pullHom_comp_toPseudofunctor]
  exact pullHom_congr_left _ _ _ ((chosenPullbackMap Φ (sq i₁ i₂)).hom_ext
    (by simp [chosenPullbackMap, ← Φ.map_comp]) (by simp [chosenPullbackMap, ← Φ.map_comp]))
    _ _ _ _ _ _

private lemma pullHom'_congr_id {obj : ∀ i, G.obj (.mk (op (Φ.obj (X i))))}
    (hom : ∀ (i j : ι),
      (G.map (chosenPullbackMap Φ (sq i j)).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
        (G.map (chosenPullbackMap Φ (sq i j)).p₂.op.toLoc).toFunctor.obj (obj j))
    (i : ι) (u : Φ.obj (X i) ⟶ Φ.obj (X i)) (hu : u = 𝟙 _)
    (h : u ≫ Φ.map (f i) = Φ.map (f i)) :
    DescentData'.pullHom' (sq := fun i j ↦ chosenPullbackMap Φ (sq i j)) hom
        (Φ.map (f i)) (i₁ := i) (i₂ := i) u u h h = 𝟙 _ ↔
      DescentData'.pullHom' (sq := fun i j ↦ chosenPullbackMap Φ (sq i j)) hom
        (Φ.map (f i)) (i₁ := i) (i₂ := i) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
  subst hu
  rfl

private lemma pullHom'_self_iff {obj : ∀ i, (Φ.op.toPseudofunctor.comp G).obj (.mk (op (X i)))}
    (hom : ∀ (i j : ι),
      ((Φ.op.toPseudofunctor.comp G).map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
        ((Φ.op.toPseudofunctor.comp G).map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (i : ι) :
    DescentData'.pullHom' (sq := sq) hom (f i) (i₁ := i) (i₂ := i)
        (𝟙 (X i)) (𝟙 (X i)) (by simp) (by simp) = 𝟙 _ ↔
      DescentData'.pullHom' (F := G) (sq := fun i j ↦ chosenPullbackMap Φ (sq i j)) hom
        (Φ.map (f i)) (i₁ := i) (i₂ := i) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
  rw [pullHom'_comp_toPseudofunctor]
  exact pullHom'_congr_id Φ G sq hom i _ (Φ.map_id (X i)) _

variable (sq₃ : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
  [∀ i₁ i₂ i₃, PreservesLimit (cospan (sq i₁ i₂).p₂ (sq i₂ i₃).p₁) Φ]

private lemma pullHom'_comp_iff
    {obj : ∀ i, (Φ.op.toPseudofunctor.comp G).obj (.mk (op (X i)))}
    (hom : ∀ (i j : ι),
      ((Φ.op.toPseudofunctor.comp G).map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
        ((Φ.op.toPseudofunctor.comp G).map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (i₁ i₂ i₃ : ι) :
    DescentData'.pullHom' (sq := sq) hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁
        (sq₃ i₁ i₂ i₃).p₂ (by simp) (by simp) ≫
      DescentData'.pullHom' (sq := sq) hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂
        (sq₃ i₁ i₂ i₃).p₃ (by simp) (by simp) =
      DescentData'.pullHom' (sq := sq) hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁
        (sq₃ i₁ i₂ i₃).p₃ (by simp) (by simp) ↔
    DescentData'.pullHom' (F := G) (sq := fun i j ↦ chosenPullbackMap Φ (sq i j)) hom
        (chosenPullback₃Map Φ (sq₃ i₁ i₂ i₃)).p (chosenPullback₃Map Φ (sq₃ i₁ i₂ i₃)).p₁
        (chosenPullback₃Map Φ (sq₃ i₁ i₂ i₃)).p₂ (by simp) (by simp) ≫
      DescentData'.pullHom' (F := G) (sq := fun i j ↦ chosenPullbackMap Φ (sq i j)) hom
        (chosenPullback₃Map Φ (sq₃ i₁ i₂ i₃)).p (chosenPullback₃Map Φ (sq₃ i₁ i₂ i₃)).p₂
        (chosenPullback₃Map Φ (sq₃ i₁ i₂ i₃)).p₃ (by simp) (by simp) =
      DescentData'.pullHom' (F := G) (sq := fun i j ↦ chosenPullbackMap Φ (sq i j)) hom
        (chosenPullback₃Map Φ (sq₃ i₁ i₂ i₃)).p (chosenPullback₃Map Φ (sq₃ i₁ i₂ i₃)).p₁
        (chosenPullback₃Map Φ (sq₃ i₁ i₂ i₃)).p₃ (by simp) (by simp) := by
  rw [pullHom'_comp_toPseudofunctor, pullHom'_comp_toPseudofunctor,
    pullHom'_comp_toPseudofunctor]
  rfl

/-- `DescentData'` along `f` for `Φ.op.toPseudofunctor.comp G` is `DescentData'` along the
images `Φ.map (f i)` for `G`, over the images of the chosen pullbacks. -/
private noncomputable def descentDataPrimeEquivalence :
    (Φ.op.toPseudofunctor.comp G).DescentData' sq sq₃ ≌
      G.DescentData' (fun i j ↦ chosenPullbackMap Φ (sq i j))
        (fun i₁ i₂ i₃ ↦ chosenPullback₃Map Φ (sq₃ i₁ i₂ i₃)) :=
  Equivalence.mk
    { obj D :=
        { obj := D.obj
          hom := D.hom
          pullHom'_hom_self i := (pullHom'_self_iff Φ G sq D.hom i).1 (D.pullHom'_hom_self i)
          pullHom'_hom_comp i₁ i₂ i₃ :=
            (pullHom'_comp_iff Φ G sq sq₃ D.hom i₁ i₂ i₃).1 (D.pullHom'_hom_comp i₁ i₂ i₃) }
      map φ :=
        { hom := φ.hom
          comm := φ.comm }
      map_id _ := DescentData'.hom_ext (fun _ ↦ rfl)
      map_comp _ _ := DescentData'.hom_ext (fun _ ↦ rfl) }
    { obj D :=
        { obj := D.obj
          hom := D.hom
          pullHom'_hom_self i := (pullHom'_self_iff Φ G sq D.hom i).2 (D.pullHom'_hom_self i)
          pullHom'_hom_comp i₁ i₂ i₃ :=
            (pullHom'_comp_iff Φ G sq sq₃ D.hom i₁ i₂ i₃).2 (D.pullHom'_hom_comp i₁ i₂ i₃) }
      map φ :=
        { hom := φ.hom
          comm := φ.comm }
      map_id _ := DescentData'.hom_ext (fun _ ↦ rfl)
      map_comp _ _ := DescentData'.hom_ext (fun _ ↦ rfl) }
    (NatIso.ofComponents (fun D ↦ DescentData'.isoMk (fun _ ↦ Iso.refl _) (fun _ _ ↦ by
        simp only [Iso.refl_hom, Functor.map_id, Category.id_comp, Category.comp_id]; rfl))
      (fun _ ↦ DescentData'.hom_ext (fun _ ↦ (Category.comp_id _).trans
        (Category.id_comp _).symm)))
    (NatIso.ofComponents (fun D ↦ DescentData'.isoMk (fun _ ↦ Iso.refl _) (fun _ _ ↦ by
        simp only [Iso.refl_hom, Functor.map_id, Category.id_comp, Category.comp_id]; rfl))
      (fun _ ↦ DescentData'.hom_ext (fun _ ↦ (Category.comp_id _).trans
        (Category.id_comp _).symm)))

omit [∀ i j, PreservesLimit (cospan (f i) (f j)) Φ] in
private lemma ofObj_hom_comp_toPseudofunctor (M : (Φ.op.toPseudofunctor.comp G).obj (.mk (op S)))
    ⦃Y : D⦄ (q : Y ⟶ S) (i₁ i₂ : ι) (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂) (hg₁ : g₁ ≫ f i₁ = q)
    (hg₂ : g₂ ≫ f i₂ = q) :
    (DescentData.ofObj (F := Φ.op.toPseudofunctor.comp G) (f := f) M).hom
        q (i₁ := i₁) (i₂ := i₂) g₁ g₂ hg₁ hg₂ =
      (DescentData.ofObj (F := G) (f := fun i ↦ Φ.map (f i)) M).hom (Φ.map q)
        (i₁ := i₁) (i₂ := i₂) (Φ.map g₁) (Φ.map g₂) (by rw [← Φ.map_comp, hg₁])
        (by rw [← Φ.map_comp, hg₂]) := by
  simp only [DescentData.ofObj_hom]
  rw [comp_mapComp'_eq, comp_mapComp'_eq]
  rfl

/-- Restriction to descent data commutes with `descentDataPrimeEquivalence`. -/
private noncomputable def toDescentDataCompDescentDataPrimeEquivalenceIso :
    (Φ.op.toPseudofunctor.comp G).toDescentData f ⋙
        (DescentData'.descentDataEquivalence _ sq sq₃).inverse ⋙
        (descentDataPrimeEquivalence Φ G sq sq₃).functor ≅
      G.toDescentData (fun i ↦ Φ.map (f i)) ⋙
        (DescentData'.descentDataEquivalence _ (fun i j ↦ chosenPullbackMap Φ (sq i j))
          (fun i₁ i₂ i₃ ↦ chosenPullback₃Map Φ (sq₃ i₁ i₂ i₃))).inverse :=
  NatIso.ofComponents (fun M ↦ DescentData'.isoMk (fun _ ↦ Iso.refl _) (fun i₁ i₂ ↦ by
      rw [Iso.refl_hom]
      erw [Functor.map_id, Functor.map_id]
      exact (Category.id_comp _).trans ((ofObj_hom_comp_toPseudofunctor Φ G M (sq i₁ i₂).p i₁ i₂
        (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ (sq i₁ i₂).hp₁ (sq i₁ i₂).hp₂).symm.trans
        (Category.comp_id _).symm)))
    (fun _ ↦ DescentData'.hom_ext (fun _ ↦ (Category.comp_id _).trans
      (Category.id_comp _).symm))

end

/-- Let `f i : X i ⟶ S` be a family of morphisms of `D` whose pairwise pullbacks and triple
pullbacks (the pullbacks of `pullback.snd (f i) (f j)` and `pullback.fst (f j) (f k)`) exist in
`D`, and let `Φ : D ⥤ C` preserve them. Then `Φ.op.toPseudofunctor.comp G` has effective
descent along the family `f` if and only if `G` has effective descent along the image family
`Φ.map (f i)`. -/
theorem isStackFor_ofArrows_comp_toPseudofunctor_iff {ι : Type t} {S : D} {X : ι → D}
    (f : ∀ i, X i ⟶ S) [∀ i j, HasPullback (f i) (f j)]
    [∀ i j k, HasPullback (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k))]
    [∀ i j, PreservesLimit (cospan (f i) (f j)) Φ]
    [∀ i j k, PreservesLimit (cospan (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k))) Φ] :
    (Φ.op.toPseudofunctor.comp G).IsStackFor (Presieve.ofArrows X f) ↔
      G.IsStackFor (Presieve.ofArrows (fun i ↦ Φ.obj (X i)) (fun i ↦ Φ.map (f i))) := by
  have : ∀ i j k, PreservesLimit
      (cospan (chosenPullbackFamily f i j).p₂ (chosenPullbackFamily f j k).p₁) Φ :=
    fun i j k ↦ (inferInstance :
      PreservesLimit (cospan (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k))) Φ)
  rw [isStackFor_ofArrows_iff, isStackFor_ofArrows_iff]
  have e := toDescentDataCompDescentDataPrimeEquivalenceIso Φ G (chosenPullbackFamily f)
    (chosenPullback₃Family f)
  constructor
  · intro h
    have := (Functor.isEquivalence_iff_of_iso e).1
      (@Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h inferInstance)
    exact @Functor.isEquivalence_of_comp_right _ _ _ _ _ _ _ _ inferInstance this
  · intro h
    have := (Functor.isEquivalence_iff_of_iso e).2
      (@Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h inferInstance)
    exact @Functor.isEquivalence_of_comp_right _ _ _ _ _ _ _ _ inferInstance this

/-- Let `Φ : D ⥤ C` preserve the pullback of `f : X ⟶ S` along itself and the triple pullback
(the pullback of `pullback.snd f f` and `pullback.fst f f`), both of which exist in `D`. Then
`Φ.op.toPseudofunctor.comp G` has effective descent along `f` if and only if `G` has effective
descent along `Φ.map f`. -/
theorem isStackFor_singleton_comp_toPseudofunctor_iff {X S : D} (f : X ⟶ S) [HasPullback f f]
    [HasPullback (pullback.snd f f) (pullback.fst f f)] [PreservesLimit (cospan f f) Φ]
    [PreservesLimit (cospan (pullback.snd f f) (pullback.fst f f)) Φ] :
    (Φ.op.toPseudofunctor.comp G).IsStackFor (Presieve.singleton f) ↔
      G.IsStackFor (Presieve.singleton (Φ.map f)) := by
  rw [← Presieve.ofArrows_pUnit.{0}, ← Presieve.ofArrows_pUnit.{0}]
  exact isStackFor_ofArrows_comp_toPseudofunctor_iff Φ G (fun _ : PUnit.{1} ↦ f)

end CategoryTheory.Pseudofunctor

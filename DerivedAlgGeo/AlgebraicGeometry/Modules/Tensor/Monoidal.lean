/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Basic

/-!
# The monoidal category of invertible module sheaves

The sheafified tensor product descends to invertible sheaves. Its associator is natural and
satisfies the triangle and pentagon identities because the comparison maps cancel, reducing the
coherence diagrams to those for the objectwise tensor product of presheaves.
-/

open CategoryTheory MonoidalCategory BraidedCategory

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

local instance : Category X.Modules :=
  inferInstanceAs (Category (SheafOfModules X.ringCatSheaf))

local instance : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

local instance : SymmetricCategory X.PresheafOfModules :=
  PresheafOfModules.symmetricCategory (R := X.presheaf)

private noncomputable abbrev invertibleTensor (L M : InvertibleSheaf X) :
    InvertibleSheaf X := by
  letI : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L.1) := L.2
  letI : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M.1) := M.2
  exact ⟨tensorObj L.1 M.1, isInvertible_tensorObj L.1 M.1⟩

private noncomputable abbrev invertibleAssoc (L M N : InvertibleSheaf X) :
    invertibleTensor (invertibleTensor L M) N ≅
      invertibleTensor L (invertibleTensor M N) := by
  letI : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L.1) := L.2
  letI : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from N.1) := N.2
  exact (isInvertible X).isoMk (tensorAssocIso L.1 M.1 N.1)

private noncomputable abbrev invertibleUnit : InvertibleSheaf X :=
  ⟨SheafOfModules.unit X.ringCatSheaf,
    SheafOfModules.instIsInvertibleUnit.{u, u, u}⟩

lemma tensorSheafificationComparisonRight_naturality {P Q : X.PresheafOfModules}
    (f : P ⟶ Q) {L M : X.Modules} (g : L ⟶ M) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (f ⊗ₘ (toPresheafOfModules X).map g) ≫
      tensorSheafificationComparisonRight Q M =
    tensorSheafificationComparisonRight P L ≫
      tensorHom
        ((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map f) g := by
  dsimp [tensorSheafificationComparisonRight, tensorHom]
  change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (f ⊗ₘ (toPresheafOfModules X).map g) ≫
      (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app Q ▷
              (toPresheafOfModules X).obj M) =
    (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app P ▷
              (toPresheafOfModules X).obj L) ≫
      (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          ((toPresheafOfModules X).map
              ((PresheafOfModules.sheafification
                (𝟙 X.ringCatSheaf.obj)).map f) ⊗ₘ
            (toPresheafOfModules X).map g)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp only [← MonoidalCategory.tensorHom_id]
  calc
    (f ⊗ₘ (toPresheafOfModules X).map g) ≫
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app Q ⊗ₘ 𝟙 _) =
      (f ≫ (PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app Q) ⊗ₘ
        ((toPresheafOfModules X).map g ≫ 𝟙 _) :=
          MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
    _ = ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P ≫
        (toPresheafOfModules X).map
          ((PresheafOfModules.sheafification
            (𝟙 X.ringCatSheaf.obj)).map f)) ⊗ₘ
          (toPresheafOfModules X).map g := by
      rw [Category.comp_id]
      congr 1
      have hn := (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit_naturality f
      have hmap :
          (SheafOfModules.forget X.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars
              (𝟙 X.ringCatSheaf.obj)).map
                ((PresheafOfModules.sheafification
                  (𝟙 X.ringCatSheaf.obj)).map f) =
            (toPresheafOfModules X).map
              ((PresheafOfModules.sheafification
                (𝟙 X.ringCatSheaf.obj)).map f) := by
        ext U x
        rfl
      rw [hmap] at hn
      exact hn.symm
    _ = ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P ⊗ₘ 𝟙 _) ≫
        ((toPresheafOfModules X).map
            ((PresheafOfModules.sheafification
              (𝟙 X.ringCatSheaf.obj)).map f) ⊗ₘ
          (toPresheafOfModules X).map g) := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
      rw [Category.id_comp]

lemma tensorSheafificationComparisonLeft_naturality {L M : X.Modules} (f : L ⟶ M)
    {P Q : X.PresheafOfModules} (g : P ⟶ Q) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        ((toPresheafOfModules X).map f ⊗ₘ g) ≫
      tensorSheafificationComparisonLeft M Q =
    tensorSheafificationComparisonLeft L P ≫
      tensorHom f
        ((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map g) := by
  dsimp [tensorSheafificationComparisonLeft, tensorHom]
  change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          ((toPresheafOfModules X).map f ⊗ₘ g) ≫
      (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          ((toPresheafOfModules X).obj M ◁
            (PresheafOfModules.sheafificationAdjunction
              (𝟙 X.ringCatSheaf.obj)).unit.app Q) =
    (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          ((toPresheafOfModules X).obj L ◁
            (PresheafOfModules.sheafificationAdjunction
              (𝟙 X.ringCatSheaf.obj)).unit.app P) ≫
      (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          ((toPresheafOfModules X).map f ⊗ₘ
            (toPresheafOfModules X).map
              ((PresheafOfModules.sheafification
                (𝟙 X.ringCatSheaf.obj)).map g))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp only [← MonoidalCategory.id_tensorHom]
  calc
    ((toPresheafOfModules X).map f ⊗ₘ g) ≫
        (𝟙 _ ⊗ₘ (PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app Q) =
      ((toPresheafOfModules X).map f ≫ 𝟙 _) ⊗ₘ
        (g ≫ (PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app Q) :=
            MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
    _ = (toPresheafOfModules X).map f ⊗ₘ
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app P ≫
          (toPresheafOfModules X).map
            ((PresheafOfModules.sheafification
              (𝟙 X.ringCatSheaf.obj)).map g)) := by
      rw [Category.comp_id]
      congr 1
      have hn := (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit_naturality g
      have hmap :
          (SheafOfModules.forget X.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars
              (𝟙 X.ringCatSheaf.obj)).map
                ((PresheafOfModules.sheafification
                  (𝟙 X.ringCatSheaf.obj)).map g) =
            (toPresheafOfModules X).map
              ((PresheafOfModules.sheafification
                (𝟙 X.ringCatSheaf.obj)).map g) := by
        ext U x
        rfl
      rw [hmap] at hn
      exact hn.symm
    _ = (𝟙 _ ⊗ₘ (PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P) ≫
        ((toPresheafOfModules X).map f ⊗ₘ
          (toPresheafOfModules X).map
            ((PresheafOfModules.sheafification
              (𝟙 X.ringCatSheaf.obj)).map g)) := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
      rw [Category.id_comp]

/-- Naturality of the associator. `L₁` and `L₂` carried invertibility hypotheses until #833
made `tensorAssocIso` independent of its left-hand factor; only the right-hand ones remain. -/
lemma tensorAssocIso_naturality
    {L₁ L₂ M₁ M₂ N₁ N₂ : X.Modules}
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from N₁)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from N₂)]
    (f : L₁ ⟶ L₂) (g : M₁ ⟶ M₂) (h : N₁ ⟶ N₂) :
    tensorHom (tensorHom f g) h ≫ (tensorAssocIso L₂ M₂ N₂).hom =
      (tensorAssocIso L₁ M₁ N₁).hom ≫
        tensorHom f (tensorHom g h) := by
  let cR₁ := tensorSheafificationComparisonRight
    ((toPresheafOfModules X).obj L₁ ⊗ (toPresheafOfModules X).obj M₁) N₁
  let cR₂ := tensorSheafificationComparisonRight
    ((toPresheafOfModules X).obj L₂ ⊗ (toPresheafOfModules X).obj M₂) N₂
  let cL₁ := tensorSheafificationComparisonLeft L₁
    ((toPresheafOfModules X).obj M₁ ⊗ (toPresheafOfModules X).obj N₁)
  let cL₂ := tensorSheafificationComparisonLeft L₂
    ((toPresheafOfModules X).obj M₂ ⊗ (toPresheafOfModules X).obj N₂)
  rw [← cancel_epi cR₁, ← cancel_mono (inv cL₂)]
  have hR := tensorSheafificationComparisonRight_naturality
    ((toPresheafOfModules X).map f ⊗ₘ (toPresheafOfModules X).map g) h
  change (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map
        (((toPresheafOfModules X).map f ⊗ₘ
          (toPresheafOfModules X).map g) ⊗ₘ
            (toPresheafOfModules X).map h) ≫ cR₂ =
    cR₁ ≫ tensorHom (tensorHom f g) h at hR
  have hL := tensorSheafificationComparisonLeft_naturality f
    ((toPresheafOfModules X).map g ⊗ₘ (toPresheafOfModules X).map h)
  change (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map
        ((toPresheafOfModules X).map f ⊗ₘ
          ((toPresheafOfModules X).map g ⊗ₘ
            (toPresheafOfModules X).map h)) ≫ cL₂ =
    cL₁ ≫ tensorHom f (tensorHom g h) at hL
  dsimp only [cR₁, cR₂, cL₁, cL₂] at hR hL ⊢
  simp only [tensorAssocIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, Category.assoc]
  rw [← reassoc_of% hR]
  simp only [IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% hL]
  simp only [IsIso.hom_inv_id, Category.comp_id]
  change (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map
        (((toPresheafOfModules X).map f ⊗ₘ
          (toPresheafOfModules X).map g) ⊗ₘ
            (toPresheafOfModules X).map h) ≫
      (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (α_ ((toPresheafOfModules X).obj L₂)
            ((toPresheafOfModules X).obj M₂)
            ((toPresheafOfModules X).obj N₂)).hom =
    (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (α_ ((toPresheafOfModules X).obj L₁)
            ((toPresheafOfModules X).obj M₁)
            ((toPresheafOfModules X).obj N₁)).hom ≫
      (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          ((toPresheafOfModules X).map f ⊗ₘ
            ((toPresheafOfModules X).map g ⊗ₘ
              (toPresheafOfModules X).map h))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact MonoidalCategory.associator_naturality
    ((toPresheafOfModules X).map f)
    ((toPresheafOfModules X).map g)
    ((toPresheafOfModules X).map h)

lemma tensorHom_id_id (L M : X.Modules) :
    tensorHom (𝟙 L) (𝟙 M) = 𝟙 (tensorObj L M) := by
  dsimp [tensorHom]
  rw [(toPresheafOfModules X).map_id,
    (toPresheafOfModules X).map_id,
    MonoidalCategory.id_tensorHom_id]
  exact (PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).map_id _

lemma tensorHom_comp_tensorHom
    {L₁ L₂ L₃ M₁ M₂ M₃ : X.Modules}
    (f₁ : L₁ ⟶ L₂) (f₂ : M₁ ⟶ M₂)
    (g₁ : L₂ ⟶ L₃) (g₂ : M₂ ⟶ M₃) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ =
      tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  dsimp [tensorHom]
  rw [← Functor.map_comp,
    MonoidalCategory.tensorHom_comp_tensorHom,
    (toPresheafOfModules X).map_comp,
    (toPresheafOfModules X).map_comp]

/-- Tensoring is functorial in each argument, so an isomorphism transports through it.

`tensorObj` is not a bifunctor in this file — the monoidal structure is only available on the
invertible sheaves — but the two lemmas above are exactly the functoriality an isomorphism needs,
and transporting one factor is what a twist comparison does constantly. -/
noncomputable def tensorObjIso {L L' M M' : X.Modules} (e : L ≅ L') (g : M ≅ M') :
    tensorObj L M ≅ tensorObj L' M' where
  hom := tensorHom e.hom g.hom
  inv := tensorHom e.inv g.inv
  hom_inv_id := by
    rw [tensorHom_comp_tensorHom, e.hom_inv_id, g.hom_inv_id, tensorHom_id_id]
  inv_hom_id := by
    rw [tensorHom_comp_tensorHom, e.inv_hom_id, g.inv_hom_id, tensorHom_id_id]

private lemma comparisonLeft_counit (L M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    tensorSheafificationComparisonLeft L ((toPresheafOfModules X).obj M) ≫
      tensorHom (𝟙 L)
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).counit.app M) =
      𝟙 (tensorObj L M) := by
  dsimp [tensorSheafificationComparisonLeft, tensorHom]
  rw [← Functor.map_comp]
  have hId : (toPresheafOfModules X).map (𝟙 L) = 𝟙 _ :=
    (toPresheafOfModules X).map_id L
  rw [hId]
  simp only [← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let P := (toPresheafOfModules X).obj M
  let ε := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit.app M
  have hmap :
      (SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars
          (𝟙 X.ringCatSheaf.obj)).map
            ε = (toPresheafOfModules X).map ε := by
    ext U x
    rfl
  have hc := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit_naturality ε
  rw [hmap] at hc
  have heq : F.map ((toPresheafOfModules X).map ε) =
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit.app (F.obj P) := by
    rw [← cancel_mono ε]
    exact hc
  let k := (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P ≫
    (toPresheafOfModules X).map ε
  have hk : F.map k = 𝟙 _ := by
    dsimp only [k]
    rw [Functor.map_comp, heq]
    exact (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).left_triangle_components P
  have hn := tensorSheafificationComparisonLeft_naturality (𝟙 L) k
  simp only [Functor.id_obj] at hk hn
  rw [hId, hk, tensorHom_id_id, Category.comp_id] at hn
  rw [← cancel_mono
    (tensorSheafificationComparisonLeft L P)]
  change F.map (𝟙 ((toPresheafOfModules X).obj L) ⊗ₘ k) ≫
      tensorSheafificationComparisonLeft L P =
    tensorSheafificationComparisonLeft L P
  exact hn

private lemma comparisonRight_counit (L M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)] :
    tensorSheafificationComparisonRight ((toPresheafOfModules X).obj L) M ≫
      tensorHom
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).counit.app L) (𝟙 M) =
      𝟙 (tensorObj L M) := by
  dsimp [tensorSheafificationComparisonRight, tensorHom]
  rw [← Functor.map_comp]
  have hId : (toPresheafOfModules X).map (𝟙 M) = 𝟙 _ :=
    (toPresheafOfModules X).map_id M
  rw [hId]
  simp only [← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let P := (toPresheafOfModules X).obj L
  let ε := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit.app L
  have hmap :
      (SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars
          (𝟙 X.ringCatSheaf.obj)).map
            ε = (toPresheafOfModules X).map ε := by
    ext U x
    rfl
  have hc := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit_naturality ε
  rw [hmap] at hc
  have heq : F.map ((toPresheafOfModules X).map ε) =
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit.app (F.obj P) := by
    rw [← cancel_mono ε]
    exact hc
  let k := (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P ≫
    (toPresheafOfModules X).map ε
  have hk : F.map k = 𝟙 _ := by
    dsimp only [k]
    rw [Functor.map_comp, heq]
    exact (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).left_triangle_components P
  have hn := tensorSheafificationComparisonRight_naturality k (𝟙 M)
  simp only [Functor.id_obj] at hk hn
  rw [hId, hk, tensorHom_id_id, Category.comp_id] at hn
  rw [← cancel_mono
    (tensorSheafificationComparisonRight P M)]
  change F.map (k ⊗ₘ 𝟙 ((toPresheafOfModules X).obj M)) ≫
      tensorSheafificationComparisonRight P M =
    tensorSheafificationComparisonRight P M
  exact hn

private lemma tensorAssocIso_triangle (L M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)] :
    (tensorAssocIso L (SheafOfModules.unit X.ringCatSheaf) M).hom ≫
        tensorHom (𝟙 L) (tensorUnitLeftIso M).hom =
      tensorHom (tensorUnitRightIso L).hom (𝟙 M) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let A := (toPresheafOfModules X).obj L
  let B := (toPresheafOfModules X).obj M
  let I := (toPresheafOfModules X).obj
    (SheafOfModules.unit X.ringCatSheaf)
  let cR₀ := tensorSheafificationComparisonRight (A ⊗ I) M
  let cL₀ := tensorSheafificationComparisonLeft L (I ⊗ B)
  let cR₁ := tensorSheafificationComparisonRight A M
  let cL₁ := tensorSheafificationComparisonLeft L B
  let εL := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit.app L
  let εM := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit.app M
  have hL := tensorSheafificationComparisonLeft_naturality (𝟙 L) (λ_ B).hom
  have hL' := hL =≫ tensorHom (𝟙 L) εM
  simp only [Category.assoc] at hL'
  rw [comparisonLeft_counit] at hL'
  rw [tensorHom_comp_tensorHom] at hL'
  simp only [Category.id_comp] at hL'
  change F.map (𝟙 A ⊗ₘ (λ_ B).hom) =
    cL₀ ≫ tensorHom (𝟙 L) (tensorUnitLeftIso M).hom at hL'
  have hR := tensorSheafificationComparisonRight_naturality (ρ_ A).hom (𝟙 M)
  have hR' := hR =≫ tensorHom εL (𝟙 M)
  simp only [Category.assoc] at hR'
  rw [comparisonRight_counit] at hR'
  rw [tensorHom_comp_tensorHom] at hR'
  simp only [Category.id_comp] at hR'
  change F.map ((ρ_ A).hom ⊗ₘ 𝟙 B) =
    cR₀ ≫ tensorHom (tensorUnitRightIso L).hom (𝟙 M) at hR'
  dsimp only [cR₀, cL₀, A, B, I, F] at hL' hR' ⊢
  rw [← cancel_epi cR₀]
  dsimp only [cR₀, A, I]
  simp only [tensorAssocIso, Iso.trans_hom,
    Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
    IsIso.hom_inv_id_assoc]
  rw [← hL', ← hR']
  change (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map (α_ A I B).hom ≫
        (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map (𝟙 A ⊗ₘ (λ_ B).hom) =
    (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map ((ρ_ A).hom ⊗ₘ 𝟙 B)
  rw [← Functor.map_comp]
  congr 1
  exact MonoidalCategory.triangle A B

/-- The right comparison composed with the associator. The hypothesis on `L` went with #833. -/
lemma tensorSheafificationComparisonRight_comp_tensorAssocIso
    (L M N : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from N)] :
    tensorSheafificationComparisonRight
        ((toPresheafOfModules X).obj L ⊗ (toPresheafOfModules X).obj M) N ≫
      (tensorAssocIso L M N).hom =
    (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (α_ ((toPresheafOfModules X).obj L)
            ((toPresheafOfModules X).obj M)
            ((toPresheafOfModules X).obj N)).hom ≫
      tensorSheafificationComparisonLeft L
        ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N) := by
  simp only [tensorAssocIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, IsIso.hom_inv_id_assoc]
  rfl

private lemma tensorAssocIso_pentagon (W L M N : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from W)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from N)] :
    tensorHom (tensorAssocIso W L M).hom (𝟙 N) ≫
        (tensorAssocIso W (tensorObj L M) N).hom ≫
          tensorHom (𝟙 W) (tensorAssocIso L M N).hom =
      (tensorAssocIso (tensorObj W L) M N).hom ≫
        (tensorAssocIso W L (tensorObj M N)).hom := by
  let A := (toPresheafOfModules X).obj W
  let B := (toPresheafOfModules X).obj L
  let C := (toPresheafOfModules X).obj M
  let D := (toPresheafOfModules X).obj N
  let r₀ := tensorSheafificationComparisonRight ((A ⊗ B) ⊗ C) N
  let r₁ := tensorSheafificationComparisonRight (A ⊗ B) M
  let l₀ := tensorSheafificationComparisonLeft W (B ⊗ (C ⊗ D))
  let l₁ := tensorSheafificationComparisonLeft L (C ⊗ D)
  let k₀ := r₀ ≫ tensorHom r₁ (𝟙 N)
  let k₄ := l₀ ≫ tensorHom (𝟙 W) l₁
  haveI : IsIso r₁ := by dsimp only [r₁]; infer_instance
  haveI : IsIso l₁ := by dsimp only [l₁]; infer_instance
  haveI : IsIso (tensorHom r₁ (𝟙 N)) := by
    dsimp only [tensorHom]
    haveI : IsIso ((toPresheafOfModules X).map r₁) := by infer_instance
    haveI : IsIso ((toPresheafOfModules X).map (𝟙 N)) := by infer_instance
    haveI : IsIso ((toPresheafOfModules X).map r₁ ⊗ₘ
        (toPresheafOfModules X).map (𝟙 N)) := by infer_instance
    infer_instance
  haveI : IsIso (tensorHom (𝟙 W) l₁) := by
    dsimp only [tensorHom]
    haveI : IsIso ((toPresheafOfModules X).map (𝟙 W)) := by infer_instance
    haveI : IsIso ((toPresheafOfModules X).map l₁) := by infer_instance
    haveI : IsIso ((toPresheafOfModules X).map (𝟙 W) ⊗ₘ
        (toPresheafOfModules X).map l₁) := by infer_instance
    infer_instance
  haveI : IsIso k₀ := by dsimp only [k₀]; infer_instance
  haveI : IsIso k₄ := by dsimp only [k₄]; infer_instance
  rw [← cancel_epi k₀, ← cancel_mono (inv k₄)]
  dsimp only [k₀, k₄]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [tensorHom_comp_tensorHom]
  slice_lhs 2 2 => rw [tensorSheafificationComparisonRight_comp_tensorAssocIso]
  slice_lhs 2 2 => rw [← tensorHom_comp_tensorHom]
  have hR₀ := tensorSheafificationComparisonRight_naturality (X := X) (f := (α_ A B C).hom)
    (g := 𝟙 N)
  rw [(toPresheafOfModules X).map_id] at hR₀
  slice_lhs 1 2 => rw [← hR₀]
  let ηBC := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (B ⊗ C)
  have hR₁ := tensorSheafificationComparisonRight_naturality (X := X)
    (f := 𝟙 A ⊗ₘ ηBC) (g := 𝟙 N)
  rw [(toPresheafOfModules X).map_id] at hR₁
  change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (((𝟙 A) ⊗ₘ ηBC) ⊗ₘ 𝟙 D) ≫
      tensorSheafificationComparisonRight
        (A ⊗ (toPresheafOfModules X).obj (tensorObj L M)) N =
    tensorSheafificationComparisonRight (A ⊗ (B ⊗ C)) N ≫
      tensorHom (tensorSheafificationComparisonLeft W (B ⊗ C)) (𝟙 N) at hR₁
  slice_lhs 2 3 => rw [← hR₁]
  slice_lhs 3 4 =>
    rw [tensorSheafificationComparisonRight_comp_tensorAssocIso W (tensorObj L M) N]
  let rBC := tensorSheafificationComparisonRight (B ⊗ C) N
  haveI : IsIso rBC := by dsimp only [rBC]; infer_instance
  have hAssocLMN : (tensorAssocIso L M N).hom =
      inv rBC ≫
        (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map (α_ B C D).hom ≫ l₁ := by
    rfl
  have hTensorAssocLMN : tensorHom (𝟙 W) (tensorAssocIso L M N).hom =
      tensorHom (𝟙 W) (inv rBC) ≫
        tensorHom (𝟙 W)
          ((PresheafOfModules.sheafification
            (𝟙 X.ringCatSheaf.obj)).map (α_ B C D).hom) ≫
          tensorHom (𝟙 W) l₁ := by
    rw [hAssocLMN, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, Category.id_comp]
    congr 1
  rw [hTensorAssocLMN]
  simp only [Category.assoc]
  have hAssocNat₀ := MonoidalCategory.associator_naturality
    (𝟙 A) ηBC (𝟙 D)
  change (((𝟙 A ⊗ₘ ηBC) ⊗ₘ 𝟙 D) ≫
      (α_ A ((toPresheafOfModules X).obj (tensorObj L M)) D).hom) =
    (α_ A (B ⊗ C) D).hom ≫ (𝟙 A ⊗ₘ (ηBC ⊗ₘ 𝟙 D)) at hAssocNat₀
  slice_lhs 2 3 =>
    rw [← Functor.map_comp, hAssocNat₀, Functor.map_comp]
  let gBCD := ηBC ⊗ₘ 𝟙 D
  let l₂ := tensorSheafificationComparisonLeft W ((B ⊗ C) ⊗ D)
  have hL₀ := tensorSheafificationComparisonLeft_naturality (X := X) (𝟙 W) gBCD
  rw [(toPresheafOfModules X).map_id] at hL₀
  change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map (𝟙 A ⊗ₘ gBCD) ≫
      tensorSheafificationComparisonLeft W
        ((toPresheafOfModules X).obj (tensorObj L M) ⊗ D) =
    l₂ ≫ tensorHom (𝟙 W) rBC at hL₀
  slice_lhs 3 4 => rw [hL₀]
  have hCancelRBC : tensorHom (𝟙 W) rBC ≫
      tensorHom (𝟙 W) (inv rBC) = 𝟙 _ := by
    rw [tensorHom_comp_tensorHom, IsIso.hom_inv_id]
    have hIdW : 𝟙 W ≫ 𝟙 W = 𝟙 W := Category.id_comp _
    rw [hIdW]
    exact tensorHom_id_id W _
  slice_lhs 4 5 => rw [hCancelRBC]
  slice_lhs 4 5 => rw [Category.id_comp]
  have hL₁ := tensorSheafificationComparisonLeft_naturality (X := X) (𝟙 W) (α_ B C D).hom
  rw [(toPresheafOfModules X).map_id] at hL₁
  change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map (𝟙 A ⊗ₘ (α_ B C D).hom) ≫ l₀ =
    l₂ ≫ tensorHom (𝟙 W)
      ((PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map (α_ B C D).hom) at hL₁
  slice_lhs 3 4 => rw [← hL₁]
  slice_lhs 4 6 =>
    change k₄ ≫ inv k₄
    rw [IsIso.hom_inv_id]
  let ηAB := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (A ⊗ B)
  let ηCD := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (C ⊗ D)
  let r₃ := tensorSheafificationComparisonRight
    ((toPresheafOfModules X).obj (tensorObj W L) ⊗ C) N
  let l₃ := tensorSheafificationComparisonLeft (tensorObj W L) (C ⊗ D)
  have hR₂ := tensorSheafificationComparisonRight_naturality (X := X)
    (f := ηAB ⊗ₘ 𝟙 C) (g := 𝟙 N)
  rw [(toPresheafOfModules X).map_id] at hR₂
  change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map ((ηAB ⊗ₘ 𝟙 C) ⊗ₘ 𝟙 D) ≫
      r₃ = r₀ ≫ tensorHom r₁ (𝟙 N) at hR₂
  slice_rhs 1 2 => rw [← hR₂]
  slice_rhs 2 3 =>
    rw [tensorSheafificationComparisonRight_comp_tensorAssocIso (tensorObj W L) M N]
  have hAssocNat₁ := MonoidalCategory.associator_naturality
    ηAB (𝟙 C) (𝟙 D)
  rw [MonoidalCategory.id_tensorHom_id] at hAssocNat₁
  change (((ηAB ⊗ₘ 𝟙 C) ⊗ₘ 𝟙 D) ≫
      (α_ ((toPresheafOfModules X).obj (tensorObj W L)) C D).hom) =
    (α_ (A ⊗ B) C D).hom ≫ (ηAB ⊗ₘ 𝟙 (C ⊗ D)) at hAssocNat₁
  slice_rhs 1 2 =>
    rw [← Functor.map_comp, hAssocNat₁, Functor.map_comp]
  have hSquare : (ηAB ⊗ₘ 𝟙 (C ⊗ D)) ≫
        (𝟙 ((toPresheafOfModules X).obj (tensorObj W L)) ⊗ₘ ηCD) =
      (𝟙 (A ⊗ B) ⊗ₘ ηCD) ≫
        (ηAB ⊗ₘ 𝟙 ((toPresheafOfModules X).obj (tensorObj M N))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom]
    congr 1
  have hl₃ : l₃ = (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map
        (𝟙 ((toPresheafOfModules X).obj (tensorObj W L)) ⊗ₘ ηCD) := by
    rfl
  slice_rhs 2 3 =>
    change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map (ηAB ⊗ₘ 𝟙 (C ⊗ D)) ≫
      (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (𝟙 ((toPresheafOfModules X).obj (tensorObj W L)) ⊗ₘ ηCD)
    rw [← Functor.map_comp, hSquare, Functor.map_comp]
  let r₄ := tensorSheafificationComparisonRight (A ⊗ B) (tensorObj M N)
  let l₄ := tensorSheafificationComparisonLeft W
    (B ⊗ (toPresheafOfModules X).obj (tensorObj M N))
  have hr₄ : r₄ = (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map
        (ηAB ⊗ₘ 𝟙 ((toPresheafOfModules X).obj (tensorObj M N))) := by
    rfl
  slice_rhs 3 4 =>
    rw [← hr₄, tensorSheafificationComparisonRight_comp_tensorAssocIso W L (tensorObj M N)]
  have hAssocNat₂ := MonoidalCategory.associator_naturality
    (𝟙 A) (𝟙 B) ηCD
  rw [MonoidalCategory.id_tensorHom_id] at hAssocNat₂
  change ((𝟙 (A ⊗ B) ⊗ₘ ηCD) ≫
      (α_ A B ((toPresheafOfModules X).obj (tensorObj M N))).hom) =
    (α_ A B (C ⊗ D)).hom ≫ (𝟙 A ⊗ₘ (𝟙 B ⊗ₘ ηCD)) at hAssocNat₂
  slice_rhs 2 3 =>
    rw [← Functor.map_comp, hAssocNat₂, Functor.map_comp]
  let gBCD' := 𝟙 B ⊗ₘ ηCD
  have hL₂ := tensorSheafificationComparisonLeft_naturality (X := X) (𝟙 W) gBCD'
  rw [(toPresheafOfModules X).map_id] at hL₂
  change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map (𝟙 A ⊗ₘ gBCD') ≫ l₄ =
    l₀ ≫ tensorHom (𝟙 W) l₁ at hL₂
  slice_rhs 3 4 => rw [hL₂]
  slice_rhs 3 5 =>
    change k₄ ≫ inv k₄
    rw [IsIso.hom_inv_id]
  rw [Category.comp_id, Category.comp_id]
  simp only [← Functor.map_comp]
  congr 1
  exact MonoidalCategory.pentagon A B C D

noncomputable instance invertibleSheafMonoidalCategoryStruct :
    MonoidalCategoryStruct (InvertibleSheaf X) where
  tensorObj := invertibleTensor
  whiskerLeft L _ _ f := ObjectProperty.homMk
    (tensorHom (𝟙 L.1) f.hom)
  whiskerRight f M := ObjectProperty.homMk
    (tensorHom f.hom (𝟙 M.1))
  tensorHom f g := ObjectProperty.homMk (tensorHom f.hom g.hom)
  tensorUnit := invertibleUnit
  associator := invertibleAssoc
  leftUnitor L := (isInvertible X).isoMk (tensorUnitLeftIso L.1)
  rightUnitor L := (isInvertible X).isoMk (tensorUnitRightIso L.1)

set_option maxHeartbeats 800000 in
noncomputable instance invertibleSheafMonoidalCategory :
    MonoidalCategory (InvertibleSheaf X) where
  tensorHom_def f g := by
    apply ObjectProperty.hom_ext
    change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        ((toPresheafOfModules X).map f.hom ⊗ₘ
          (toPresheafOfModules X).map g.hom) =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          ((toPresheafOfModules X).map f.hom ▷ _) ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          (_ ◁ (toPresheafOfModules X).map g.hom)
    rw [← Functor.map_comp, MonoidalCategory.tensorHom_def]
  id_tensorHom_id L M := by
    apply ObjectProperty.hom_ext
    change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (𝟙 _ ⊗ₘ 𝟙 _) = 𝟙 _
    rw [MonoidalCategory.id_tensorHom_id]
    exact (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map_id _
  tensorHom_comp_tensorHom f f' g g' := by
    apply ObjectProperty.hom_ext
    change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map _ ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map _ =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map _
    rw [← Functor.map_comp, MonoidalCategory.tensorHom_comp_tensorHom,
      ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.comp_hom,
      Functor.map_comp, Functor.map_comp]
  whiskerLeft_id L M := by
    apply ObjectProperty.hom_ext
    change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (𝟙 _ ⊗ₘ 𝟙 _) = 𝟙 _
    rw [MonoidalCategory.id_tensorHom_id]
    exact (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map_id _
  id_whiskerRight L M := by
    apply ObjectProperty.hom_ext
    change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (𝟙 _ ⊗ₘ 𝟙 _) = 𝟙 _
    rw [MonoidalCategory.id_tensorHom_id]
    exact (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map_id _
  associator_naturality := by
    intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from X₁.1) := X₁.2
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from X₃.1) := X₃.2
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from Y₁.1) := Y₁.2
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from Y₃.1) := Y₃.2
    apply ObjectProperty.hom_ext
    exact tensorAssocIso_naturality f₁.hom f₂.hom f₃.hom
  leftUnitor_naturality := by
    intro X₁ X₂ f
    apply ObjectProperty.hom_ext
    change tensorHom (𝟙 (SheafOfModules.unit X.ringCatSheaf)) f.hom ≫
        (tensorUnitLeftIso X₂.1).hom =
      (tensorUnitLeftIso X₁.1).hom ≫ f.hom
    change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          ((toPresheafOfModules X).map
              (𝟙 (SheafOfModules.unit X.ringCatSheaf)) ⊗ₘ
            (toPresheafOfModules X).map f.hom) ≫
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
            (λ_ ((toPresheafOfModules X).obj X₂.1)).hom ≫
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).counit.app X₂.1) =
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
            (λ_ ((toPresheafOfModules X).obj X₁.1)).hom ≫
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).counit.app X₁.1) ≫ f.hom
    have hId : (toPresheafOfModules X).map
        (𝟙 (SheafOfModules.unit X.ringCatSheaf)) = 𝟙 _ :=
      (toPresheafOfModules X).map_id _
    rw [hId]
    change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          (𝟙_ X.PresheafOfModules ◁ (toPresheafOfModules X).map f.hom) ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
            (λ_ ((toPresheafOfModules X).obj X₂.1)).hom ≫
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).counit.app X₂.1 = _
    rw [← Functor.map_comp_assoc, MonoidalCategory.leftUnitor_naturality,
      Functor.map_comp]
    have hc := (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit_naturality f.hom
    change (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map
            (λ_ ((toPresheafOfModules X).obj X₁.1)).hom ≫
        ((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map
            ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars
                (𝟙 X.ringCatSheaf.obj)).map f.hom) ≫
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).counit.app X₂.1) = _
    rw [hc, ← Category.assoc]
  rightUnitor_naturality := by
    intro X₁ X₂ f
    apply ObjectProperty.hom_ext
    change tensorHom f.hom (𝟙 (SheafOfModules.unit X.ringCatSheaf)) ≫
        (tensorUnitRightIso X₂.1).hom =
      (tensorUnitRightIso X₁.1).hom ≫ f.hom
    change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          ((toPresheafOfModules X).map f.hom ⊗ₘ
            (toPresheafOfModules X).map
              (𝟙 (SheafOfModules.unit X.ringCatSheaf))) ≫
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
            (ρ_ ((toPresheafOfModules X).obj X₂.1)).hom ≫
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).counit.app X₂.1) =
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
            (ρ_ ((toPresheafOfModules X).obj X₁.1)).hom ≫
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).counit.app X₁.1) ≫ f.hom
    have hId : (toPresheafOfModules X).map
        (𝟙 (SheafOfModules.unit X.ringCatSheaf)) = 𝟙 _ :=
      (toPresheafOfModules X).map_id _
    rw [hId]
    change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          ((toPresheafOfModules X).map f.hom ▷ 𝟙_ X.PresheafOfModules) ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
            (ρ_ ((toPresheafOfModules X).obj X₂.1)).hom ≫
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).counit.app X₂.1 = _
    rw [← Functor.map_comp_assoc, MonoidalCategory.rightUnitor_naturality,
      Functor.map_comp]
    have hc := (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit_naturality f.hom
    change (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map
            (ρ_ ((toPresheafOfModules X).obj X₁.1)).hom ≫
        ((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map
            ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars
                (𝟙 X.ringCatSheaf.obj)).map f.hom) ≫
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).counit.app X₂.1) = _
    rw [hc, ← Category.assoc]
  pentagon := by
    intro W₁ X₁ Y₁ Z₁
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from W₁.1) := W₁.2
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from X₁.1) := X₁.2
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from Y₁.1) := Y₁.2
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from Z₁.1) := Z₁.2
    apply ObjectProperty.hom_ext
    exact tensorAssocIso_pentagon W₁.1 X₁.1 Y₁.1 Z₁.1
  triangle := by
    intro X₁ Y₁
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from X₁.1) := X₁.2
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from Y₁.1) := Y₁.2
    apply ObjectProperty.hom_ext
    exact tensorAssocIso_triangle X₁.1 Y₁.1

end

end AlgebraicGeometry.Scheme.Modules

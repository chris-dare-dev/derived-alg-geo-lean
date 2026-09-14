/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Bifunctor

/-!
# Derived bifunctors from K-flat resolutions

This file isolates the categorical core of the unbounded derived tensor product. Given a tensor
bifunctor on cochain complexes, a `KFlatResolution C tensor` is a functorial quasi-isomorphic
replacement by objects for which tensoring in either variable sends quasi-isomorphisms to
isomorphisms after derived localization.

Resolving both inputs makes the complex-level tensor bifunctor invert quasi-isomorphisms in both
variables. `Localization.lift₂` therefore constructs an honest bifunctor on the unbounded derived
category, together with its comparison to the underived bifunctor.

Only a bifunctor is required here, rather than a monoidal structure on complexes: associativity,
unit, and symmetry play no role in localization. Existence of K-flat resolutions is deliberately
separate. Scheme-module sheaves will supply the complex tensor and its resolutions through total
tensor, K-flat replacement, and descent.
-/

namespace CategoryTheory

open Limits

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

private abbrev W : MorphismProperty (CochainComplex C ℤ) :=
  HomologicalComplex.quasiIso C (ComplexShape.up ℤ)

/-- A cochain complex is K-flat for `tensor` when tensoring with it in either variable sends
quasi-isomorphisms to isomorphisms after derived localization.

The two clauses are kept explicit because the supplied bifunctor need not carry a braiding. For
the total tensor of complexes of modules they agree by symmetry. -/
def IsKFlat (tensor : CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (K : CochainComplex C ℤ) : Prop :=
  W.IsInvertedBy (tensor.obj K ⋙ DerivedCategory.Q) ∧
    W.IsInvertedBy (tensor.flip.obj K ⋙ DerivedCategory.Q)

namespace IsKFlat

variable {tensor : CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ}
  {K : CochainComplex C ℤ} (hK : CochainComplex.IsKFlat tensor K)

include hK

/-- Left tensoring with a K-flat complex inverts quasi-isomorphisms. -/
lemma tensorLeft_inverts :
    W.IsInvertedBy (tensor.obj K ⋙ DerivedCategory.Q) :=
  hK.1

/-- Right tensoring with a K-flat complex inverts quasi-isomorphisms. -/
lemma tensorRight_inverts :
    W.IsInvertedBy (tensor.flip.obj K ⋙ DerivedCategory.Q) :=
  hK.2

end IsKFlat

end CochainComplex

/-- A functorial two-sided K-flat replacement for a complex-level tensor bifunctor. -/
structure KFlatResolution (C : Type u) [Category.{v} C] [Abelian C]
    (tensor : CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ) where
  /-- Functorial K-flat replacement. -/
  resolution : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  /-- Comparison from the replacement to the original complex. -/
  comparison : resolution ⟶ 𝟭 (CochainComplex C ℤ)
  /-- Every comparison component is a quasi-isomorphism. -/
  comparison_quasiIso (K : CochainComplex C ℤ) :
    HomologicalComplex.quasiIso C (ComplexShape.up ℤ) (comparison.app K)
  /-- Every replacement is K-flat for the supplied tensor bifunctor. -/
  isKFlat (K : CochainComplex C ℤ) :
    CochainComplex.IsKFlat tensor (resolution.obj K)

namespace KFlatResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  {tensor : CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ}

private abbrev W : MorphismProperty (CochainComplex C ℤ) :=
  HomologicalComplex.quasiIso C (ComplexShape.up ℤ)

/-- The comparison component, with its identity-functor codomain normalized. -/
def comparisonApp (R : KFlatResolution C tensor) (K : CochainComplex C ℤ) :
    R.resolution.obj K ⟶ K :=
  R.comparison.app K

@[reassoc]
lemma comparisonApp_naturality (R : KFlatResolution C tensor)
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    R.resolution.map f ≫ R.comparisonApp L = R.comparisonApp K ≫ f := by
  simpa only [comparisonApp, Functor.id_obj, Functor.id_map] using R.comparison.naturality f

/-- A K-flat replacement functor preserves quasi-isomorphisms. -/
lemma map_quasiIso (R : KFlatResolution C tensor) {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (hf : W f) : W (R.resolution.map f) := by
  have hf' : W ((𝟭 (CochainComplex C ℤ)).map f) := by
    simpa only [Functor.id_obj, Functor.id_map] using hf
  have hcomp : W
      (R.comparison.app K ≫ (𝟭 (CochainComplex C ℤ)).map f) :=
    W.comp_mem _ _ (R.comparison_quasiIso K) hf'
  have hcomp' : W (R.resolution.map f ≫ R.comparison.app L) := by
    rw [R.comparison.naturality]
    exact hcomp
  exact W.of_postcomp _ _ (R.comparison_quasiIso L) hcomp'

/-- Apply `tensor` after K-flat replacement in both inputs and then localize. -/
def resolvedTensor (R : KFlatResolution C tensor) :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ DerivedCategory C :=
  R.resolution ⋙ tensor ⋙
    (Functor.whiskeringLeft _ _ _).obj R.resolution ⋙
    (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q

@[simp]
lemma resolvedTensor_obj_obj (R : KFlatResolution C tensor)
    (K L : CochainComplex C ℤ) :
    ((R.resolvedTensor.obj K).obj L) =
      DerivedCategory.Q.obj ((tensor.obj (R.resolution.obj K)).obj (R.resolution.obj L)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Resolving both variables makes `tensor` invert quasi-isomorphisms in both variables. -/
lemma resolvedTensor_inverts (R : KFlatResolution C tensor) :
    MorphismProperty.IsInvertedBy₂ W W R.resolvedTensor := by
  rintro ⟨K₁, L₁⟩ ⟨K₂, L₂⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have hRf := R.map_quasiIso f hf
  have hRg := R.map_quasiIso g hg
  haveI h₁ : IsIso (DerivedCategory.Q.map
      ((tensor.map (R.resolution.map f)).app (R.resolution.obj L₁))) := by
    change IsIso (DerivedCategory.Q.map
      ((tensor.flip.obj (R.resolution.obj L₁)).map (R.resolution.map f)))
    exact (R.isKFlat L₁).tensorRight_inverts _ hRf
  haveI h₂ : IsIso (DerivedCategory.Q.map
      ((tensor.obj (R.resolution.obj K₂)).map (R.resolution.map g))) :=
    (R.isKFlat K₂).tensorLeft_inverts _ hRg
  change IsIso
    (DerivedCategory.Q.map
        ((tensor.map (R.resolution.map f)).app (R.resolution.obj L₁)) ≫
      DerivedCategory.Q.map
        ((tensor.obj (R.resolution.obj K₂)).map (R.resolution.map g)))
  infer_instance

/-- The unbounded derived bifunctor constructed by resolving both inputs and descending through
quasi-isomorphism localization. -/
def derivedTensor (R : KFlatResolution C tensor) :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift₂ R.resolvedTensor R.resolvedTensor_inverts
    DerivedCategory.Q DerivedCategory.Q

/-- Pulling the derived bifunctor back to complexes recovers resolved tensor. -/
def derivedTensorFactors (R : KFlatResolution C tensor) :
    (((Functor.whiskeringLeft₂ (DerivedCategory C)).obj DerivedCategory.Q).obj
        DerivedCategory.Q).obj R.derivedTensor ≅ R.resolvedTensor := by
  change
    (((Functor.whiskeringLeft₂ (DerivedCategory C)).obj DerivedCategory.Q).obj
        DerivedCategory.Q).obj
        (Localization.lift₂ R.resolvedTensor R.resolvedTensor_inverts
          DerivedCategory.Q DerivedCategory.Q) ≅ R.resolvedTensor
  exact Localization.Lifting₂.iso DerivedCategory.Q DerivedCategory.Q W W
    R.resolvedTensor
    (Localization.lift₂ R.resolvedTensor R.resolvedTensor_inverts
      DerivedCategory.Q DerivedCategory.Q)

/-- The natural comparison from resolved tensor to the original bifunctor followed by derived
localization. -/
def resolvedTensorComparison (R : KFlatResolution C tensor) :
    R.resolvedTensor ⟶
      tensor ⋙ (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q where
  app K :=
    { app := fun L ↦ DerivedCategory.Q.map
        ((tensor.map (R.comparisonApp K)).app (R.resolution.obj L) ≫
          (tensor.obj K).map (R.comparisonApp L))
      naturality := fun {L M} f ↦ by
        change DerivedCategory.Q.map
              ((tensor.obj (R.resolution.obj K)).map (R.resolution.map f)) ≫
            DerivedCategory.Q.map
              ((tensor.map (R.comparisonApp K)).app (R.resolution.obj M) ≫
                (tensor.obj K).map (R.comparisonApp M)) =
          DerivedCategory.Q.map
              ((tensor.map (R.comparisonApp K)).app (R.resolution.obj L) ≫
                (tensor.obj K).map (R.comparisonApp L)) ≫
            DerivedCategory.Q.map ((tensor.obj K).map f)
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        simp only [Category.assoc, NatTrans.naturality_assoc, ← Functor.map_comp]
        rw [R.comparisonApp_naturality] }
  naturality {K L} f := by
    ext M
    change DerivedCategory.Q.map
          ((tensor.map (R.resolution.map f)).app (R.resolution.obj M)) ≫
        DerivedCategory.Q.map
          ((tensor.map (R.comparisonApp L)).app (R.resolution.obj M) ≫
            (tensor.obj L).map (R.comparisonApp M)) =
      DerivedCategory.Q.map
          ((tensor.map (R.comparisonApp K)).app (R.resolution.obj M) ≫
            (tensor.obj K).map (R.comparisonApp M)) ≫
        DerivedCategory.Q.map ((tensor.map f).app M)
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp,
      R.comparisonApp_naturality]
    simp only [Functor.map_comp, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [(tensor.map f).naturality]

/-- Comparison from the derived bifunctor evaluated on localized complexes to the original
bifunctor followed by localization. -/
def derivedTensorCounit (R : KFlatResolution C tensor) :
    (((Functor.whiskeringLeft₂ (DerivedCategory C)).obj DerivedCategory.Q).obj
        DerivedCategory.Q).obj R.derivedTensor ⟶
      tensor ⋙ (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q :=
  R.derivedTensorFactors.hom ≫ R.resolvedTensorComparison

end KFlatResolution

end

end CategoryTheory

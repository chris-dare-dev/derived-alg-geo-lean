/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.KInjective.Resolution

/-!
# Unbounded right-derived functors from K-injective resolutions

Let `C` be an abelian category. The K-injective complexes form a triangulated subcategory of
the homotopy category `K(C)` on which `Qh : K(C) ⥤ D(C)` is fully faithful. When every complex
has a K-injective resolution, this subcategory is equivalent to `D(C)`, and every additive
functor `F : C ⥤ D` has a right derived functor `RF : D(C) ⥤ D(D)`, computed by applying `F`
to K-injective representatives (Stacks, Section 13.31). This is the unbounded companion of
Mathlib's `Functor.rightDerivedFunctorPlus`, and the K-injective twin of
`DerivedCategory/KProjective.lean`.

## Main definitions

* `CategoryTheory.kInjectiveHomotopy` and `CategoryTheory.KInjectiveHomotopyCategory`: the
  K-injective objects of `K(C)`, defined as Mathlib's right orthogonal of the acyclic
  complexes, and their full subcategory.
* `CategoryTheory.kInjectiveQh`: `Qh` restricted to K-injective complexes.
* `CategoryTheory.kInjectiveLocalizerMorphism`: the inclusion, as a localizer morphism from
  the isomorphisms of K-injective complexes to the quasi-isomorphisms of `K(C)`.
* `CategoryTheory.kInjectiveQhEquivalence`: `KInjectiveHomotopyCategory C ≌ D(C)`, given
  resolutions.
* `CategoryTheory.kInjectiveDerivedFunctor`: `RF`, with its units
  `kInjectiveDerivedFunctorUnit` on `K(C)` and `kInjectiveDerivedFunctorComplexUnit` on
  cochain complexes.
* `CategoryTheory.kInjectiveDerivedFunctorPlusIso`: on `D⁺(C)`, `RF` agrees with Mathlib's
  `F.rightDerivedFunctorPlus`.
* `CategoryTheory.kInjectiveDerivedFunctorComp`: `R(F ⋙ G) ≅ RF ⋙ RG` when `F` preserves
  K-injective complexes.

## Main results

* `CategoryTheory.kInjectiveQh_full` and `CategoryTheory.kInjectiveQh_faithful`: full
  faithfulness, with no resolution hypothesis (Stacks, Tag 070I).
* `CategoryTheory.kInjectiveLocalizerMorphism_isRightDerivabilityStructure`: given
  resolutions, the inclusion is a right derivability structure.
* Instances: `RF` is a right derived functor of `F` on `K(C)` and on cochain complexes, it
  stays one after post-composition with any functor (the absoluteness hypothesis of
  `Adjunction.derived`), it commutes with shifts and is triangulated, and its units are
  isomorphisms at K-injective complexes (Stacks, Tags 070Y and 070K).
* `CategoryTheory.isKInjective_mapHomologicalComplex_of_adjunction`: a right adjoint of an
  exact functor preserves K-injective complexes (Stacks, Tag 08BJ).

## Implementation notes

The only non-formal input is the class `Cdg.HasKInjectiveResolutions C`. Every Grothendieck
abelian category satisfies it, by `Cdg.hasKInjectiveResolutions_of_isGrothendieckAbelian`
(Stacks, Tag 079P). Full faithfulness of `kInjectiveQh` uses no resolutions.

Given resolutions, `kInjectiveQhEquivalence` yields a functorial resolution
`kInjectiveHomotopyResolutionι C : 𝟭 _ ⟶ kInjectiveHomotopyResolution C ⋙ ι` on `K(C)`, and
Mathlib's `LocalizerMorphism.isRightDerivabilityStructure_of_functorial_resolutions` makes
the inclusion a right derivability structure. Its source carries the isomorphisms, as for
Mathlib's `HomotopyCategory.Plus.localizerMorphism` on `K⁺`. Such a structure derives every
functor out of `K(C)`. That gives the universal property, absoluteness, the composition law,
and, through Mathlib's `Functor.IsRightDerivedFunctor.commShift` and
`LocalizerMorphism.Derives.isTriangulated_of_isRightDerivedFunctor`, the shift and
triangulated structures of `RF`.

The unit on cochain complexes is the unit on `K(C)` transported along
`DerivedCategory.quotientCompQhIso`; it is not the same natural transformation by `rfl`,
since `Q` is a localization functor in its own right. Its universal property holds because
precomposition with the localization functor `HomotopyCategory.quotient` induces an
equivalence of categories of left extensions.

The derived categories of `C` and `D` are arbitrary instances of `HasDerivedCategory`, so the
construction applies with `HasDerivedCategory.standard` and with
`HasDerivedCategory.ofIsGrothendieckAbelian` alike.

## References

* [The Stacks project, Section 13.31](https://stacks.math.columbia.edu/tag/070G)
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988)
* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008)

## Tags

K-injective complex, right derived functor, derived category, derivability structure
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w w' w'' v v' v'' u u' u''

namespace CategoryTheory

open Limits CategoryTheory.Functor

noncomputable section

section General

/-- Precomposing with a localization functor `q` keeps a right derived functor a right derived
functor, along any localization functor isomorphic to `q ⋙ L`. -/
private lemma isRightDerivedFunctor_of_precomp_localization
    {C₀ C₁ D₁ H : Type*} [Category C₀] [Category C₁] [Category D₁] [Category H]
    (q : C₀ ⥤ C₁) (Wq : MorphismProperty C₀) [q.IsLocalization Wq]
    {L : C₁ ⥤ D₁} (W : MorphismProperty C₁) [L.IsLocalization W]
    {L₀ : C₀ ⥤ D₁} (W₀ : MorphismProperty C₀) [L₀.IsLocalization W₀]
    {F : C₁ ⥤ H} {RF : D₁ ⥤ H} (α : F ⟶ L ⋙ RF) [RF.IsRightDerivedFunctor α W]
    {F₀ : C₀ ⥤ H} (α₀ : F₀ ⟶ L₀ ⋙ RF) (eF : F₀ ≅ q ⋙ F) (eL : q ⋙ L ≅ L₀)
    (h : α₀ = eF.hom ≫ whiskerLeft q α ≫ (associator _ _ _).inv ≫ whiskerRight eL.hom RF) :
    RF.IsRightDerivedFunctor α₀ W₀ := by
  have := (isRightDerivedFunctor_iff_isLeftKanExtension RF α W).1 inferInstance
  rw [isRightDerivedFunctor_iff_isLeftKanExtension]
  have := Localization.full_whiskeringLeft q Wq H
  have := Localization.faithful_whiskeringLeft q Wq H
  have : (LeftExtension.precomp L F q).IsEquivalence := StructuredArrow.isEquivalenceMap₂ _ _
  let E := LeftExtension.precomp L F q ⋙ (leftExtensionEquivalenceOfIso₁ eL (q ⋙ F)).functor ⋙
    (leftExtensionEquivalenceOfIso₂ L₀ eF.symm).functor
  have hE : Limits.IsInitial (E.obj (LeftExtension.mk RF α)) :=
    Limits.IsInitial.isInitialObj E _ (isUniversalOfIsLeftKanExtension RF α)
  exact ⟨⟨hE.ofIso (StructuredArrow.isoMk (Iso.refl _) (by
    ext X
    simp [E, h, leftExtensionEquivalenceOfIso₂, StructuredArrow.mapIso]))⟩⟩

end General

section KInjective

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The K-injective objects of the homotopy category `K(C)` (Stacks, Definition 13.31.1,
Tag 070H): Mathlib's right orthogonal of the acyclic complexes. -/
def kInjectiveHomotopy : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal

/-- The K-injective complexes form a triangulated subcategory, as the right orthogonal of a
triangulated subcategory. -/
instance kInjectiveHomotopy_isTriangulated : (kInjectiveHomotopy C).IsTriangulated :=
  inferInstanceAs (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal.IsTriangulated

/-- The full homotopy category of K-injective cochain complexes. -/
abbrev KInjectiveHomotopyCategory := (kInjectiveHomotopy C).FullSubcategory

variable {C}

/-- A cochain complex is K-injective exactly when its image in `K(C)` is. -/
lemma kInjectiveHomotopy_quotient_obj_iff (K : CochainComplex C ℤ) :
    kInjectiveHomotopy C ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ↔
      K.IsKInjective :=
  (CochainComplex.isKInjective_iff_rightOrthogonal K).symm

/-- The underlying complex of an object of the K-injective homotopy category is
K-injective. -/
instance kInjectiveHomotopyCategory_isKInjective (K : KInjectiveHomotopyCategory C) :
    CochainComplex.IsKInjective K.obj.as :=
  (kInjectiveHomotopy_quotient_obj_iff K.obj.as).1 K.property

/-- `Qh` is bijective on morphisms into a K-injective object of `K(C)` (Stacks,
Lemma 13.31.2 (3), Tag 070I). -/
@[stacks 070I]
lemma Qh_map_bijective_of_kInjectiveHomotopy [HasDerivedCategory.{w} C]
    {L : HomotopyCategory C (ComplexShape.up ℤ)} (hL : kInjectiveHomotopy C L)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    Function.Bijective (DerivedCategory.Qh.map : (K ⟶ L) → _) := by
  have : DerivedCategory.Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic C).trW := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  exact ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated hL _ K

/-- A quasi-isomorphism between K-injective objects of `K(C)` is an isomorphism. -/
lemma isIso_of_kInjectiveHomotopy {K L : HomotopyCategory C (ComplexShape.up ℤ)}
    (hK : kInjectiveHomotopy C K) (hL : kInjectiveHomotopy C L) (f : K ⟶ L)
    (hf : HomotopyCategory.quasiIso C (ComplexShape.up ℤ) f) : IsIso f := by
  let := HasDerivedCategory.standard C
  have := (DerivedCategory.isIso_Qh_map_iff f).2 hf
  obtain ⟨g, hg⟩ := (Qh_map_bijective_of_kInjectiveHomotopy hK L).2
    (inv (DerivedCategory.Qh.map f))
  refine ⟨g, (Qh_map_bijective_of_kInjectiveHomotopy hK K).1 ?_,
    (Qh_map_bijective_of_kInjectiveHomotopy hL L).1 ?_⟩
  · simp [hg]
  · simp [hg]

/-- A morphism of the K-injective homotopy category is an isomorphism exactly when it is a
quasi-isomorphism. -/
lemma kInjectiveHomotopyCategory_isIso_iff {K L : KInjectiveHomotopyCategory C} (f : K ⟶ L) :
    IsIso f ↔ HomotopyCategory.quasiIso C (ComplexShape.up ℤ) f.hom := by
  constructor
  · intro
    exact MorphismProperty.of_isIso (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((kInjectiveHomotopy C).ι.map f)
  · intro hf
    have : IsIso ((kInjectiveHomotopy C).ι.map f) :=
      isIso_of_kInjectiveHomotopy K.property L.property f.hom hf
    exact isIso_of_reflects_iso f (kInjectiveHomotopy C).ι

/-- On K-injective complexes, quasi-isomorphisms in `K(C)` are the isomorphisms. -/
lemma inverseImage_quasiIso_kInjectiveHomotopy_ι :
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).inverseImage (kInjectiveHomotopy C).ι =
      MorphismProperty.isomorphisms (KInjectiveHomotopyCategory C) := by
  ext K L f
  exact (kInjectiveHomotopyCategory_isIso_iff f).symm

variable (C) in
/-- The inclusion of the K-injective homotopy category, as a localizer morphism from its
isomorphisms to the quasi-isomorphisms of `K(C)`. -/
abbrev kInjectiveLocalizerMorphism : LocalizerMorphism
    (MorphismProperty.isomorphisms (KInjectiveHomotopyCategory C))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) where
  functor := (kInjectiveHomotopy C).ι
  map _ _ f hf := (kInjectiveHomotopyCategory_isIso_iff f).1 hf

/-- Every functor out of `K(C)` inverts the isomorphisms of K-injective complexes. -/
lemma kInjectiveLocalizerMorphism_derives {H : Type*} [Category H]
    (G : HomotopyCategory C (ComplexShape.up ℤ) ⥤ H) :
    (kInjectiveLocalizerMorphism C).Derives G :=
  MorphismProperty.isInvertedBy_isomorphisms _

section DerivedCategory

variable [HasDerivedCategory.{w} C]

variable (C) in
/-- `Qh` restricted to the K-injective homotopy category. -/
def kInjectiveQh : KInjectiveHomotopyCategory C ⥤ DerivedCategory C :=
  (kInjectiveHomotopy C).ι ⋙ DerivedCategory.Qh

/-- Localization is full on morphisms whose target is K-injective. -/
instance kInjectiveQh_full : (kInjectiveQh C).Full where
  map_surjective {K L} f := by
    obtain ⟨g, hg⟩ := (Qh_map_bijective_of_kInjectiveHomotopy L.property K.obj).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩

/-- Localization is faithful on morphisms whose target is K-injective. -/
instance kInjectiveQh_faithful : (kInjectiveQh C).Faithful where
  map_injective {K L} f g h := by
    apply ObjectProperty.hom_ext
    exact (Qh_map_bijective_of_kInjectiveHomotopy L.property K.obj).1 h

noncomputable instance kInjectiveQhCommShift : (kInjectiveQh C).CommShift ℤ :=
  inferInstanceAs (((kInjectiveHomotopy C).ι ⋙ DerivedCategory.Qh).CommShift ℤ)

instance kInjectiveQh_isTriangulated : (kInjectiveQh C).IsTriangulated :=
  inferInstanceAs (((kInjectiveHomotopy C).ι ⋙ DerivedCategory.Qh).IsTriangulated)

section Resolutions

variable [Cdg.HasKInjectiveResolutions C]

/-- Every object of `D(C)` is represented by a K-injective complex. -/
instance kInjectiveQh_essSurj : (kInjectiveQh C).EssSurj where
  mem_essImage Y := by
    obtain ⟨L, hL, f, hf⟩ := Cdg.HasKInjectiveResolutions.exists_kInjective_quasiIso
      (DerivedCategory.Q.objPreimage Y)
    exact ⟨⟨_, (kInjectiveHomotopy_quotient_obj_iff L).2 hL⟩,
      ⟨(DerivedCategory.quotientCompQhIso C).app L ≪≫ (asIso (DerivedCategory.Q.map f)).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso Y⟩⟩

instance kInjectiveQh_isEquivalence : (kInjectiveQh C).IsEquivalence where

variable (C) in
/-- With K-injective resolutions, `Qh` restricts to an equivalence from the K-injective
homotopy category onto `D(C)`: it is fully faithful by Stacks, Lemma 13.31.2 (Tag 070I), and
essentially surjective by the resolutions. -/
def kInjectiveQhEquivalence : KInjectiveHomotopyCategory C ≌ DerivedCategory C :=
  (kInjectiveQh C).asEquivalence

variable (C) in
/-- A K-injective resolution functor on `K(C)`: localize, then choose a K-injective
representative through `kInjectiveQhEquivalence`. -/
def kInjectiveHomotopyResolution :
    HomotopyCategory C (ComplexShape.up ℤ) ⥤ KInjectiveHomotopyCategory C :=
  DerivedCategory.Qh ⋙ (kInjectiveQhEquivalence C).inverse

variable (C) in
/-- The comparison `K ⟶ kInjectiveHomotopyResolution C K`: the unique morphism of `K(C)`
whose localization is the inverse of the counit of `kInjectiveQhEquivalence`. -/
def kInjectiveHomotopyResolutionι :
    𝟭 (HomotopyCategory C (ComplexShape.up ℤ)) ⟶
      kInjectiveHomotopyResolution C ⋙ (kInjectiveHomotopy C).ι where
  app K := (Equiv.ofBijective _ (Qh_map_bijective_of_kInjectiveHomotopy
    ((kInjectiveHomotopyResolution C).obj K).property K)).symm
      ((kInjectiveQhEquivalence C).counitIso.inv.app (DerivedCategory.Qh.obj K))
  naturality K L f := (Qh_map_bijective_of_kInjectiveHomotopy
    ((kInjectiveHomotopyResolution C).obj L).property K).1 (by
      have hK := (Equiv.ofBijective _ (Qh_map_bijective_of_kInjectiveHomotopy
        ((kInjectiveHomotopyResolution C).obj K).property K)).apply_symm_apply
          ((kInjectiveQhEquivalence C).counitIso.inv.app (DerivedCategory.Qh.obj K))
      have hL := (Equiv.ofBijective _ (Qh_map_bijective_of_kInjectiveHomotopy
        ((kInjectiveHomotopyResolution C).obj L).property L)).apply_symm_apply
          ((kInjectiveQhEquivalence C).counitIso.inv.app (DerivedCategory.Qh.obj L))
      simp only [Equiv.ofBijective_apply] at hK hL
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.map_comp, hK, hL,
        Functor.comp_map]
      exact (kInjectiveQhEquivalence C).counitIso.inv.naturality (DerivedCategory.Qh.map f))

/-- The localization of the comparison with the K-injective resolution is the inverse of the
counit of `kInjectiveQhEquivalence`. -/
@[simp]
lemma Qh_map_kInjectiveHomotopyResolutionι_app (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.map ((kInjectiveHomotopyResolutionι C).app K) =
      (kInjectiveQhEquivalence C).counitIso.inv.app (DerivedCategory.Qh.obj K) :=
  (Equiv.ofBijective _ (Qh_map_bijective_of_kInjectiveHomotopy
    ((kInjectiveHomotopyResolution C).obj K).property K)).apply_symm_apply _

/-- The comparison with the K-injective resolution is a quasi-isomorphism. -/
lemma quasiIso_kInjectiveHomotopyResolutionι_app
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
      ((kInjectiveHomotopyResolutionι C).app K) := by
  rw [← DerivedCategory.isIso_Qh_map_iff, Qh_map_kInjectiveHomotopyResolutionι_app]
  exact ((kInjectiveQhEquivalence C).counitIso.app _).isIso_inv

/-- The comparison with the K-injective resolution is an isomorphism at a K-injective
object. -/
lemma isIso_kInjectiveHomotopyResolutionι_app {K : HomotopyCategory C (ComplexShape.up ℤ)}
    (hK : kInjectiveHomotopy C K) : IsIso ((kInjectiveHomotopyResolutionι C).app K) :=
  isIso_of_kInjectiveHomotopy hK ((kInjectiveHomotopyResolution C).obj K).property _
    (quasiIso_kInjectiveHomotopyResolutionι_app K)

end Resolutions

end DerivedCategory

section Derivability

variable [Cdg.HasKInjectiveResolutions C]

/-- With K-injective resolutions, the inclusion of K-injective complexes is a right
derivability structure for the quasi-isomorphisms of `K(C)`. -/
instance kInjectiveLocalizerMorphism_isRightDerivabilityStructure :
    (kInjectiveLocalizerMorphism C).IsRightDerivabilityStructure := by
  let := HasDerivedCategory.standard C
  have : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty := by
    have : HomotopyCategory.quasiIso C (ComplexShape.up ℤ) =
        (MorphismProperty.isomorphisms _).inverseImage DerivedCategory.Qh := by
      ext K L f
      exact (DerivedCategory.isIso_Qh_map_iff f).symm
    rw [this]
    infer_instance
  exact (kInjectiveLocalizerMorphism C).isRightDerivabilityStructure_of_functorial_resolutions
    (kInjectiveHomotopyResolutionι C) quasiIso_kInjectiveHomotopyResolutionι_app
    inverseImage_quasiIso_kInjectiveHomotopy_ι.symm

/-- Every morphism of `K(C)` has a resolution by a morphism of K-injective complexes. -/
instance kInjectiveLocalizerMorphism_hasRightResolutions_arrow :
    (kInjectiveLocalizerMorphism C).arrow.HasRightResolutions := by
  let := HasDerivedCategory.standard C
  exact (kInjectiveLocalizerMorphism C).hasRightResolutions_arrow_of_functorial_resolutions
    (kInjectiveHomotopyResolutionι C) quasiIso_kInjectiveHomotopyResolutionι_app

/-- With K-injective resolutions, every functor out of `K(C)` has a pointwise right derived
functor with respect to quasi-isomorphisms. -/
instance hasPointwiseRightDerivedFunctor_of_hasKInjectiveResolutions {H : Type*} [Category H]
    (G : HomotopyCategory C (ComplexShape.up ℤ) ⥤ H) :
    G.HasPointwiseRightDerivedFunctor (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  (kInjectiveLocalizerMorphism_derives G).hasPointwiseRightDerivedFunctor

/-- K-injective complexes compute right derived functors (Stacks, Lemma 13.31.6, Tag 070Y):
the unit of any right derived functor out of `K(C)` is an isomorphism at a K-injective
complex. -/
@[stacks 070Y]
instance isIso_app_of_isRightDerivedFunctor [HasDerivedCategory.{w} C] {H : Type*} [Category H]
    {G : HomotopyCategory C (ComplexShape.up ℤ) ⥤ H} {RG : DerivedCategory C ⥤ H}
    (α : G ⟶ DerivedCategory.Qh ⋙ RG)
    [RG.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) [CochainComplex.IsKInjective K.as] :
    IsIso (α.app K) :=
  (kInjectiveLocalizerMorphism_derives G).isIso_of_isRightDerivedFunctor α
    ⟨K, (kInjectiveHomotopy_quotient_obj_iff K.as).2 inferInstance⟩

end Derivability

section DerivedFunctor

variable {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [Cdg.HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]

/-- **Stacks, Lemma 13.31.7 (Tag 070K)**: the right derived functor `RF : D(C) ⥤ D(D)` of an
additive functor, computed by applying `F` to a K-injective representative. -/
@[stacks 070K]
def kInjectiveDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D :=
  (kInjectiveQhEquivalence C).inverse ⋙ (kInjectiveHomotopy C).ι ⋙
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The unit `F K ⟶ RF K` of the right derived functor on `K(C)`: `F` applied to the
comparison of `K` with its K-injective resolution. -/
def kInjectiveDerivedFunctorUnit :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ kInjectiveDerivedFunctor F :=
  whiskerRight (kInjectiveHomotopyResolutionι C)
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)

/-- The unit on `K(C)` at `K` is `F` applied to the comparison of `K` with its
K-injective resolution. -/
@[simp]
lemma kInjectiveDerivedFunctorUnit_app (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (kInjectiveDerivedFunctorUnit F).app K =
      DerivedCategory.Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((kInjectiveHomotopyResolutionι C).app K)) :=
  rfl

/-- The unit is an isomorphism at a K-injective object of `K(C)`. -/
lemma isIso_kInjectiveDerivedFunctorUnit_app {K : HomotopyCategory C (ComplexShape.up ℤ)}
    (hK : kInjectiveHomotopy C K) : IsIso ((kInjectiveDerivedFunctorUnit F).app K) := by
  have := isIso_kInjectiveHomotopyResolutionι_app hK
  have := Functor.map_isIso (F.mapHomotopyCategory (ComplexShape.up ℤ))
    ((kInjectiveHomotopyResolutionι C).app K)
  rw [kInjectiveDerivedFunctorUnit_app]
  exact Functor.map_isIso DerivedCategory.Qh _

/-- `RF` is a right derived functor of `F` on `K(C)`. -/
instance kInjectiveDerivedFunctor_isRightDerivedFunctor :
    (kInjectiveDerivedFunctor F).IsRightDerivedFunctor (kInjectiveDerivedFunctorUnit F)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  (kInjectiveLocalizerMorphism_derives _).isRightDerivedFunctor_of_isIso _ fun K ↦
    isIso_kInjectiveDerivedFunctorUnit_app F K.property

/-- **Absoluteness.** The right derived functor stays a right derived functor after
post-composition with any functor; this is the hypothesis shape of `Adjunction.derived`. -/
instance kInjectiveDerivedFunctor_comp_isRightDerivedFunctor {H : Type*} [Category H]
    (G : DerivedCategory D ⥤ H) :
    (kInjectiveDerivedFunctor F ⋙ G).IsRightDerivedFunctor
      (whiskerRight (kInjectiveDerivedFunctorUnit F) G ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  refine (kInjectiveLocalizerMorphism_derives _).isRightDerivedFunctor_of_isIso _ fun K ↦ ?_
  have := isIso_kInjectiveDerivedFunctorUnit_app F K.property
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id]
  exact Functor.map_isIso G ((kInjectiveDerivedFunctorUnit F).app K.obj)

/-- `RF` commutes with shifts, through its universal property. -/
noncomputable instance kInjectiveDerivedFunctorCommShift :
    (kInjectiveDerivedFunctor F).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift _ (kInjectiveDerivedFunctorUnit F)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ℤ

instance kInjectiveDerivedFunctorUnit_commShift :
    NatTrans.CommShift (kInjectiveDerivedFunctorUnit F) ℤ :=
  Functor.IsRightDerivedFunctor.natTrans_commShift _ _
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ℤ

/-- `RF` is a triangulated functor. -/
instance kInjectiveDerivedFunctor_isTriangulated : (kInjectiveDerivedFunctor F).IsTriangulated := by
  have := Localization.essSurj_mapArrow DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  exact (kInjectiveLocalizerMorphism_derives _).isTriangulated_of_isRightDerivedFunctor
    (kInjectiveDerivedFunctorUnit F)

/-- The unit of the right derived functor on cochain complexes, the shape that
`RightDerivedPushforward` uses: the unit on `K(C)`, transported along
`DerivedCategory.quotientCompQhIso`. -/
def kInjectiveDerivedFunctorComplexUnit :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ kInjectiveDerivedFunctor F :=
  whiskerLeft _ (DerivedCategory.quotientCompQhIso D).inv ≫ (Functor.associator _ _ _).inv ≫
    whiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv _ ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
      (kInjectiveDerivedFunctorUnit F) ≫
    (Functor.associator _ _ _).inv ≫ whiskerRight (DerivedCategory.quotientCompQhIso C).hom _

/-- The unit on cochain complexes at `K`, through the unit on `K(C)`. -/
lemma kInjectiveDerivedFunctorComplexUnit_app (K : CochainComplex C ℤ) :
    (kInjectiveDerivedFunctorComplexUnit F).app K =
      (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
        (kInjectiveDerivedFunctorUnit F).app _ ≫
        (kInjectiveDerivedFunctor F).map ((DerivedCategory.quotientCompQhIso C).hom.app K) := by
  simp [kInjectiveDerivedFunctorComplexUnit]

/-- `RF` is a right derived functor of `F` on cochain complexes. -/
instance kInjectiveDerivedFunctor_isRightDerivedFunctor_complexUnit :
    (kInjectiveDerivedFunctor F).IsRightDerivedFunctor (kInjectiveDerivedFunctorComplexUnit F)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_of_precomp_localization (HomotopyCategory.quotient C (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (kInjectiveDerivedFunctorUnit F) _
    (isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _)
    (DerivedCategory.quotientCompQhIso C) (by ext; simp [kInjectiveDerivedFunctorComplexUnit])

/-- **Absoluteness** on cochain complexes, the shape `Adjunction.derived` consumes for an
adjunction of functors between categories of cochain complexes. -/
instance kInjectiveDerivedFunctor_comp_isRightDerivedFunctor_complexUnit {H : Type*}
    [Category H] (G : DerivedCategory D ⥤ H) :
    (kInjectiveDerivedFunctor F ⋙ G).IsRightDerivedFunctor
      (whiskerRight (kInjectiveDerivedFunctorComplexUnit F) G ≫ (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_of_precomp_localization (HomotopyCategory.quotient C (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (whiskerRight (kInjectiveDerivedFunctorUnit F) G ≫ (Functor.associator _ _ _).hom) _
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (isoWhiskerRight (DerivedCategory.quotientCompQhIso D).symm G) ≪≫
      isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _)
    (DerivedCategory.quotientCompQhIso C) (by ext; simp [kInjectiveDerivedFunctorComplexUnit])

/-- K-injective complexes compute `RF` (Stacks, Lemma 13.31.7, Tag 070K): the unit on
cochain complexes is an isomorphism at a K-injective complex. -/
@[stacks 070K]
instance isIso_kInjectiveDerivedFunctorComplexUnit_app (K : CochainComplex C ℤ)
    [K.IsKInjective] : IsIso ((kInjectiveDerivedFunctorComplexUnit F).app K) := by
  have := isIso_kInjectiveDerivedFunctorUnit_app F
    ((kInjectiveHomotopy_quotient_obj_iff K).2 inferInstance)
  rw [kInjectiveDerivedFunctorComplexUnit_app]
  infer_instance

/-- On a K-injective complex `K`, the right derived functor is `F` applied degreewise
(Stacks, Tag 070K). -/
def kInjectiveDerivedFunctorObjIso (K : CochainComplex C ℤ) [K.IsKInjective] :
    (kInjectiveDerivedFunctor F).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (asIso ((kInjectiveDerivedFunctorComplexUnit F).app K)).symm

section Plus

variable [EnoughInjectives C]

/-- On the bounded-below derived category, the right derived functor agrees with Mathlib's
`Functor.rightDerivedFunctorPlus`: there is no second bounded-below theory. -/
def kInjectiveDerivedFunctorPlusIso :
    DerivedCategory.Plus.ι ⋙ kInjectiveDerivedFunctor F ≅
      F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι := by
  let G := F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι
  let αR : G ⟶ DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι :=
    whiskerRight F.rightDerivedFunctorPlusUnith DerivedCategory.Plus.ι
  let αL : G ⟶ DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ⋙ kInjectiveDerivedFunctor F :=
    whiskerLeft F.mapHomotopyCategoryPlus (DerivedCategory.Plus.QhCompιIsoιCompQh D).hom ≫
      whiskerRight F.mapHomotopyCategoryPlusCompι.hom DerivedCategory.Qh ≫
      whiskerLeft (HomotopyCategory.Plus.ι C) (kInjectiveDerivedFunctorUnit F) ≫
      whiskerRight (DerivedCategory.Plus.QhCompιIsoιCompQh C).inv (kInjectiveDerivedFunctor F)
  have : (DerivedCategory.Plus.ι ⋙ kInjectiveDerivedFunctor F).IsRightDerivedFunctor αL
      (HomotopyCategory.Plus.quasiIso C) := by
    refine (HomotopyCategory.Plus.localizerMorphism_derives G).isRightDerivedFunctor_of_isIso _
      fun X ↦ ?_
    let Y := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X
    obtain ⟨n, _⟩ : CochainComplex.plus C Y.obj.as := by
      rw [← HomotopyCategory.plus_quotient_obj_iff]
      exact Y.property
    have := isIso_kInjectiveDerivedFunctorUnit_app F
      (K := (HomotopyCategory.Plus.ι C).obj
        ((HomotopyCategory.Plus.localizerMorphism C).functor.obj X))
      ((kInjectiveHomotopy_quotient_obj_iff Y.obj.as).2
        (CochainComplex.isKInjective_of_injective _ n))
    simp only [αL, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
    infer_instance
  have : (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).IsRightDerivedFunctor αR
      (HomotopyCategory.Plus.quasiIso C) :=
    (HomotopyCategory.Plus.localizerMorphism_derives G).isRightDerivedFunctor_of_isIso _
      fun X ↦ by
        simp only [αR, whiskerRight_app]
        infer_instance
  exact Functor.rightDerivedUnique _ _ αL αR (HomotopyCategory.Plus.quasiIso C)

end Plus

section Comp

variable {E : Type u''} [Category.{v''} E] [Abelian E] [HasDerivedCategory.{w''} E]
  [Cdg.HasKInjectiveResolutions D] (G : D ⥤ E) [G.Additive]

/-- Right derived functors compose when the first functor preserves K-injective complexes. -/
def kInjectiveDerivedFunctorComp
    (hF : ∀ I : CochainComplex C ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    kInjectiveDerivedFunctor (F ⋙ G) ≅
      kInjectiveDerivedFunctor F ⋙ kInjectiveDerivedFunctor G := by
  let β : (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ kInjectiveDerivedFunctor F ⋙ kInjectiveDerivedFunctor G :=
    whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
      whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) (kInjectiveDerivedFunctorUnit G) ≫
      whiskerRight (kInjectiveDerivedFunctorUnit F) (kInjectiveDerivedFunctor G)
  have : (kInjectiveDerivedFunctor F ⋙ kInjectiveDerivedFunctor G).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
    refine (kInjectiveLocalizerMorphism_derives _).isRightDerivedFunctor_of_isIso _ fun K ↦ ?_
    have := isIso_kInjectiveDerivedFunctorUnit_app F (K := (kInjectiveHomotopy C).ι.obj K)
      K.property
    have := isIso_kInjectiveDerivedFunctorUnit_app G
      (K := (F.mapHomotopyCategory (ComplexShape.up ℤ)).obj ((kInjectiveHomotopy C).ι.obj K))
      ((kInjectiveHomotopy_quotient_obj_iff _).2
        (hF _ (kInjectiveHomotopyCategory_isKInjective K)))
    simp only [β, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
    infer_instance
  exact Functor.rightDerivedUnique _ _ (kInjectiveDerivedFunctorUnit (F ⋙ G)) β
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

end Comp

end DerivedFunctor

section Adjunction

variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- **Stacks, Lemma 13.31.9 (Tag 08BJ)**: the right adjoint of an exact functor carries
K-injective complexes to K-injective complexes. -/
@[stacks 08BJ]
theorem isKInjective_mapHomologicalComplex_of_adjunction {u : C ⥤ D} {v : D ⥤ C}
    [u.PreservesZeroMorphisms] (adj : v ⊣ u)
    [PreservesFiniteLimits v] [PreservesFiniteColimits v] (I : CochainComplex C ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  have : v.Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts v
    exact Functor.additive_of_preservesBinaryBiproducts v
  have : u.Additive := adj.right_adjoint_additive
  let adj' := adj.mapHomologicalComplex (ComplexShape.up ℤ)
  refine ⟨fun {M} f hM ↦ ?_⟩
  have hvM : ((v.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).Acyclic :=
    fun i ↦ (hM i).map v
  obtain ⟨h⟩ := CochainComplex.IsKInjective.nonempty_homotopy_zero
    ((adj'.homEquiv _ _).symm f) hvM
  refine ⟨Homotopy.trans (.ofEq ?_) (((u.mapHomotopy h).compLeft (adj'.unit.app M)).trans
    (.ofEq ?_))⟩
  · exact ((adj'.homEquiv M I).apply_symm_apply f).symm.trans (adj'.homEquiv_unit _ _ _)
  · simp

/-- `Adjunction.derived` applies to an adjunction `v ⊣ u` with `v` exact: the derived functors
`v.mapDerivedCategory ⊣ kInjectiveDerivedFunctor u` are adjoint. -/
example [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [Cdg.HasKInjectiveResolutions C]
    {u : C ⥤ D} {v : D ⥤ C} [u.Additive] [v.Additive] (adj : v ⊣ u)
    [PreservesFiniteLimits v] [PreservesFiniteColimits v] :
    v.mapDerivedCategory ⊣ kInjectiveDerivedFunctor u := by
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) _ v.mapDerivedCategoryFactors
  have : (v.mapDerivedCategory ⋙ kInjectiveDerivedFunctor u).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight v.mapDerivedCategoryFactors.hom (kInjectiveDerivedFunctor u))
      (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight v.mapDerivedCategoryFactors (kInjectiveDerivedFunctor u))
  exact (adj.mapHomologicalComplex (ComplexShape.up ℤ)).derived
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    v.mapDerivedCategoryFactors.hom (kInjectiveDerivedFunctorComplexUnit u)

end Adjunction

end KInjective

end

end CategoryTheory

namespace CochainComplex.IsKInjective

open CategoryTheory HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- An additive functor carries a quasi-isomorphism between K-injective cochain complexes to a
homotopy equivalence: such a quasi-isomorphism is already a homotopy equivalence. -/
lemma homotopyEquivalences_map (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} [K.IsKInjective] [L.IsKInjective]
    {g : K ⟶ L} (hg : quasiIso C (ComplexShape.up ℤ) g) :
    homotopyEquivalences D (ComplexShape.up ℤ)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
  rw [mem_quasiIso_iff] at hg
  obtain ⟨e, rfl⟩ := (CochainComplex.IsKInjective.quasiIso_iff g).1 hg
  exact ⟨F.mapHomotopyEquiv e, rfl⟩

/-- An additive functor carries a quasi-isomorphism between K-injective cochain complexes to a
quasi-isomorphism. -/
lemma quasiIso_map (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} [K.IsKInjective] [L.IsKInjective]
    {g : K ⟶ L} (hg : quasiIso C (ComplexShape.up ℤ) g) :
    quasiIso D (ComplexShape.up ℤ)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) :=
  homotopyEquivalences_le_quasiIso D (ComplexShape.up ℤ) _
    (homotopyEquivalences_map F hg)

/-- The bounded-below degreewise-injective case of `quasiIso_map`. -/
lemma quasiIso_map_of_injective (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} (dK dL : ℤ)
    [K.IsStrictlyGE dK] [L.IsStrictlyGE dL]
    [∀ n : ℤ, Injective (K.X n)] [∀ n : ℤ, Injective (L.X n)]
    {g : K ⟶ L} (hg : quasiIso C (ComplexShape.up ℤ) g) :
    quasiIso D (ComplexShape.up ℤ)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) :=
  have := CochainComplex.isKInjective_of_injective K dK
  have := CochainComplex.isKInjective_of_injective L dL
  quasiIso_map F hg

end CochainComplex.IsKInjective

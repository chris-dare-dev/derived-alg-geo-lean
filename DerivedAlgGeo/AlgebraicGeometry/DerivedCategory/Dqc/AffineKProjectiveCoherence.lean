/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectivePullback

/-!
# Preservation of the affine K-projective pullback locus

This file cuts out the concrete locus represented by bounded-above
complexes of projective modules. An additive functor preserving projective
objects maps this locus to itself. Consequently arbitrary extension of
scalars gives a composable derived pullback between the corresponding full
derived subcategories, without a flatness hypothesis.

This is the supported affine pseudofunctor lane needed before gluing
relative-perfect pullback across big-Zariski covers. Identity, composition,
and descent coherence are developed on top of this preserved locus.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v v' u u'

attribute [local instance] HasDerivedCategory.standard

/-- Homotopy-category objects whose displayed complex is bounded above and
degreewise projective. -/
def boundedAboveProjectiveHomotopy
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  fun K ↦ ∃ d : ℤ, CochainComplex.IsStrictlyLE K.as d ∧
    ∀ n : ℤ, Projective (K.as.X n)

/-- The full homotopy category of displayed bounded-above complexes of
projective objects. -/
abbrev BoundedAboveProjectiveHomotopyCategory
    (C : Type u) [Category.{v} C] [Abelian C] :=
  (boundedAboveProjectiveHomotopy C).FullSubcategory

/-- A bounded-above degreewise-projective complex is K-projective. -/
theorem boundedAboveProjectiveHomotopy_le_kProjective
    (C : Type u) [Category.{v} C] [Abelian C] :
    boundedAboveProjectiveHomotopy C ≤ kProjectiveHomotopy C := by
  intro K hK
  obtain ⟨d, hd, hP⟩ := hK
  letI : CochainComplex.IsStrictlyLE K.as d := hd
  letI (n : ℤ) : Projective (K.as.X n) := hP n
  exact CochainComplex.isKProjective_of_projective K.as d

/-- Inclusion of bounded-above projective representatives into all
K-projective representatives. -/
def boundedAboveProjectiveToKProjective
    (C : Type u) [Category.{v} C] [Abelian C] :
    BoundedAboveProjectiveHomotopyCategory C ⥤
      KProjectiveHomotopyCategory C :=
  ObjectProperty.ιOfLE (boundedAboveProjectiveHomotopy_le_kProjective C)

/-- Localization of bounded-above projective representatives. -/
def boundedAboveProjectiveQh
    (C : Type u) [Category.{v} C] [Abelian C] :
    BoundedAboveProjectiveHomotopyCategory C ⥤ DerivedCategory C :=
  ObjectProperty.ι (boundedAboveProjectiveHomotopy C) ⋙
    DerivedCategory.Qh

instance boundedAboveProjectiveHomotopyCategory_isKProjective
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : BoundedAboveProjectiveHomotopyCategory C) :
    CochainComplex.IsKProjective K.obj.as :=
  boundedAboveProjectiveHomotopy_le_kProjective C K.obj K.property

instance boundedAboveProjectiveQh_full
    (C : Type u) [Category.{v} C] [Abelian C] :
    (boundedAboveProjectiveQh C).Full := by
  constructor
  intro K L f
  obtain ⟨g, hg⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective K.obj.as L.obj).2 f
  exact ⟨ObjectProperty.homMk g, hg⟩

instance boundedAboveProjectiveQh_faithful
    (C : Type u) [Category.{v} C] [Abelian C] :
    (boundedAboveProjectiveQh C).Faithful := by
  constructor
  intro K L f g h
  apply ObjectProperty.hom_ext
  apply (CochainComplex.IsKProjective.Qh_map_bijective
    K.obj.as L.obj).1
  exact h

/-- The full derived locus represented by bounded-above complexes of
projective objects. -/
abbrev BoundedAboveProjectiveDerivedCategory
    (C : Type u) [Category.{v} C] [Abelian C] :=
  (boundedAboveProjectiveQh C).EssImageSubcategory

/-- Bounded-above projective representatives modulo homotopy are equivalent
to their essential image in the derived category. -/
def boundedAboveProjectiveQhEquivalence
    (C : Type u) [Category.{v} C] [Abelian C] :
    BoundedAboveProjectiveHomotopyCategory C ≌
      BoundedAboveProjectiveDerivedCategory C := by
  letI : (boundedAboveProjectiveQh C).toEssImage.IsEquivalence := {
    faithful := inferInstance
    full := inferInstance
    essSurj := inferInstance }
  exact (boundedAboveProjectiveQh C).toEssImage.asEquivalence

/-- An additive functor preserving projective objects acts on
bounded-above projective representatives. -/
def mapBoundedAboveProjectiveHomotopy
    {C : Type u} {D : Type u'} [Category.{v} C] [Abelian C]
    [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [F.PreservesProjectiveObjects] :
    BoundedAboveProjectiveHomotopyCategory C ⥤
      BoundedAboveProjectiveHomotopyCategory D :=
  (boundedAboveProjectiveHomotopy D).lift
    (ObjectProperty.ι (boundedAboveProjectiveHomotopy C) ⋙
      F.mapHomotopyCategory (ComplexShape.up ℤ)) fun K ↦ by
        obtain ⟨d, hd, hP⟩ := K.property
        refine ⟨d, ?_, ?_⟩
        · letI : CochainComplex.IsStrictlyLE K.obj.as d := hd
          change CochainComplex.IsStrictlyLE
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj.as) d
          infer_instance
        · intro n
          change Projective (F.obj (K.obj.as.X n))
          exact F.projective_obj_of_projective (hP n)

/-- Composition of functors preserving projectives agrees on the
bounded-above projective homotopy loci. -/
def mapBoundedAboveProjectiveHomotopyCompIso
    {C : Type u} {D : Type u'} {E : Type*}
    [Category.{v} C] [Abelian C] [Category.{v'} D] [Abelian D]
    [Category E] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesProjectiveObjects] [G.PreservesProjectiveObjects]
    [H.PreservesProjectiveObjects] (e : F ⋙ G ≅ H) :
    mapBoundedAboveProjectiveHomotopy F ⋙
        mapBoundedAboveProjectiveHomotopy G ≅
      mapBoundedAboveProjectiveHomotopy H := by
  let e' := F.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)
  refine NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk (boundedAboveProjectiveHomotopy E)
      (X := (mapBoundedAboveProjectiveHomotopy F ⋙
        mapBoundedAboveProjectiveHomotopy G).obj K)
      (Y := (mapBoundedAboveProjectiveHomotopy H).obj K)
      (e'.app K.obj)) ?_
  intro K L g
  apply ObjectProperty.hom_ext
  exact e'.hom.naturality g.hom

/-- The supported derived functor lands back in the bounded-above
projective derived locus. -/
def boundedAboveProjectiveDerivedFunctor
    {C : Type u} {D : Type u'} [Category.{v} C] [Abelian C]
    [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [F.PreservesProjectiveObjects] :
    BoundedAboveProjectiveDerivedCategory C ⥤
      BoundedAboveProjectiveDerivedCategory D :=
  (boundedAboveProjectiveQhEquivalence C).inverse ⋙
    mapBoundedAboveProjectiveHomotopy F ⋙
    (boundedAboveProjectiveQhEquivalence D).functor

/-- Composition of supported derived functors agrees with the supported
derived functor of the composite. -/
def boundedAboveProjectiveDerivedFunctorCompIso
    {C : Type u} {D : Type u'} {E : Type*}
    [Category.{v} C] [Abelian C] [Category.{v'} D] [Abelian D]
    [Category E] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesProjectiveObjects] [G.PreservesProjectiveObjects]
    [H.PreservesProjectiveObjects] (e : F ⋙ G ≅ H) :
    boundedAboveProjectiveDerivedFunctor F ⋙
        boundedAboveProjectiveDerivedFunctor G ≅
      boundedAboveProjectiveDerivedFunctor H := by
  let EC := boundedAboveProjectiveQhEquivalence C
  let ED := boundedAboveProjectiveQhEquivalence D
  let EE := boundedAboveProjectiveQhEquivalence E
  let MF := mapBoundedAboveProjectiveHomotopy F
  let MG := mapBoundedAboveProjectiveHomotopy G
  let MH := mapBoundedAboveProjectiveHomotopy H
  let e' := mapBoundedAboveProjectiveHomotopyCompIso F G H e
  let cancelED : ED.functor ⋙ (ED.inverse ⋙ MG) ≅ MG :=
    (Functor.associator ED.functor ED.inverse MG).symm ≪≫
      Functor.isoWhiskerRight ED.unitIso.symm MG ≪≫ MG.leftUnitor
  change (EC.inverse ⋙ MF ⋙ ED.functor) ⋙
      (ED.inverse ⋙ MG ⋙ EE.functor) ≅
    EC.inverse ⋙ MH ⋙ EE.functor
  exact
    (Functor.associator (EC.inverse ⋙ MF ⋙ ED.functor)
      (ED.inverse ⋙ MG) EE.functor).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator (EC.inverse ⋙ MF) ED.functor
        (ED.inverse ⋙ MG)) EE.functor ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (EC.inverse ⋙ MF) cancelED) EE.functor ≪≫
    Functor.isoWhiskerRight
      (Functor.associator EC.inverse MF MG) EE.functor ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft EC.inverse e') EE.functor

/-- Extension of scalars preserves projective modules. -/
instance affineExtendScalars_preservesProjectiveObjects
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (ModuleCat.extendScalars.{u, u, u} f.hom).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom)

/-- Arbitrary affine extension of scalars acts on bounded-above projective
homotopy representatives. -/
def affineBoundedAboveProjectiveHomotopyPullback
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    BoundedAboveProjectiveHomotopyCategory (ModuleCat R) ⥤
      BoundedAboveProjectiveHomotopyCategory (ModuleCat A) :=
  mapBoundedAboveProjectiveHomotopy
    (ModuleCat.extendScalars.{u, u, u} f.hom)

/-- Affine extension of scalars composes on bounded-above projective
homotopy representatives. -/
def affineBoundedAboveProjectiveHomotopyPullbackCompIso
    {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) :
    affineBoundedAboveProjectiveHomotopyPullback f ⋙
        affineBoundedAboveProjectiveHomotopyPullback g ≅
      affineBoundedAboveProjectiveHomotopyPullback (f ≫ g) :=
  mapBoundedAboveProjectiveHomotopyCompIso
    (ModuleCat.extendScalars.{u, u, u} f.hom)
    (ModuleCat.extendScalars.{u, u, u} g.hom)
    (ModuleCat.extendScalars.{u, u, u} (f ≫ g).hom)
    (by simpa using (ModuleCat.extendScalarsComp f.hom g.hom).symm)

/-- Arbitrary affine derived pullback preserves the full derived locus
represented by bounded-above complexes of projective modules. -/
def affineBoundedAboveProjectiveDerivedPullback
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    BoundedAboveProjectiveDerivedCategory (ModuleCat R) ⥤
      BoundedAboveProjectiveDerivedCategory (ModuleCat A) :=
  boundedAboveProjectiveDerivedFunctor (ModuleCat.extendScalars f.hom)

/-- Arbitrary affine derived pullback composes on the bounded-above
projective derived loci. -/
def affineBoundedAboveProjectiveDerivedPullbackCompIso
    {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) :
    affineBoundedAboveProjectiveDerivedPullback f ⋙
        affineBoundedAboveProjectiveDerivedPullback g ≅
      affineBoundedAboveProjectiveDerivedPullback (f ≫ g) :=
  boundedAboveProjectiveDerivedFunctorCompIso
    (ModuleCat.extendScalars.{u, u, u} f.hom)
    (ModuleCat.extendScalars.{u, u, u} g.hom)
    (ModuleCat.extendScalars.{u, u, u} (f ≫ g).hom)
    (by simpa using (ModuleCat.extendScalarsComp f.hom g.hom).symm)

end

end CategoryTheory.Triangulated.StabilityCondition.Families

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.EssentialImage

/-!
# Derived functors on K-projective complexes

The K-projective homotopy category of any abelian category embeds fully
faithfully in its derived category.  An arbitrary additive functor can then be
derived on this locus without exactness assumptions.  Ring extension of
scalars is one downstream consumer, not part of the construction itself.
-/

namespace CategoryTheory

open Limits

noncomputable section

universe v v' u u'

attribute [local instance] HasDerivedCategory.standard

/-- K-projective objects in the homotopy category of cochain complexes. -/
def kProjectiveHomotopy (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  fun K ↦ CochainComplex.IsKProjective K.as

/-- The full homotopy category of K-projective cochain complexes. -/
abbrev KProjectiveHomotopyCategory (C : Type u)
    [Category.{v} C] [Abelian C] :=
  (kProjectiveHomotopy C).FullSubcategory

/-- The underlying complex of an object of the K-projective homotopy
category is K-projective. -/
instance kProjectiveHomotopyCategory_isKProjective
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : KProjectiveHomotopyCategory C) :
    CochainComplex.IsKProjective K.obj.as :=
  K.property

/-- Inclusion of the K-projective homotopy category into the derived
category. -/
def kProjectiveQh (C : Type u) [Category.{v} C] [Abelian C] :
    KProjectiveHomotopyCategory C ⥤ DerivedCategory C :=
  ObjectProperty.ι (kProjectiveHomotopy C) ⋙ DerivedCategory.Qh

/-- Localization is full on morphisms whose source is K-projective. -/
instance kProjectiveQh_full
    (C : Type u) [Category.{v} C] [Abelian C] :
    (kProjectiveQh C).Full where
  map_surjective {K L} f := by
    obtain ⟨g, hg⟩ :=
      (CochainComplex.IsKProjective.Qh_map_bijective K.obj.as L.obj).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩

/-- Localization is faithful on morphisms whose source is K-projective. -/
instance kProjectiveQh_faithful
    (C : Type u) [Category.{v} C] [Abelian C] :
    (kProjectiveQh C).Faithful where
  map_injective {K L} f g h := by
    apply ObjectProperty.hom_ext
    apply (CochainComplex.IsKProjective.Qh_map_bijective
      K.obj.as L.obj).1
    exact h

/-- The full derived subcategory consisting of objects represented by
K-projective complexes. -/
abbrev KProjectiveDerivedCategory (C : Type u)
    [Category.{v} C] [Abelian C] :=
  (kProjectiveQh C).EssImageSubcategory

/-- K-projective complexes modulo homotopy are equivalent to their essential
image in the derived category. -/
def kProjectiveQhEquivalence
    (C : Type u) [Category.{v} C] [Abelian C] :
    KProjectiveHomotopyCategory C ≌ KProjectiveDerivedCategory C := by
  letI : (kProjectiveQh C).toEssImage.IsEquivalence := {
    faithful := inferInstance
    full := inferInstance
    essSurj := inferInstance }
  exact (kProjectiveQh C).toEssImage.asEquivalence

/-- A bounded-above complex of projective objects, regarded as an object of
the K-projective homotopy category. -/
def KProjectiveHomotopyCategory.ofBoundedAboveProjectives
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d]
    [∀ n : ℤ, Projective (K.X n)] : KProjectiveHomotopyCategory C :=
  ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K,
    CochainComplex.isKProjective_of_projective K d⟩

/-- Apply an additive functor to K-projective representatives in the
homotopy category, then localize the resulting complexes. This construction
does not require the additive functor to be exact. -/
def kProjectiveDerivedFunctor
    {C : Type u} {D : Type u'} [Category.{v} C] [Abelian C]
    [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive] :
    KProjectiveHomotopyCategory C ⥤ DerivedCategory D :=
  ObjectProperty.ι (kProjectiveHomotopy C) ⋙
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The supported derived functor, now expressed on an honest full
subcategory of the source derived category rather than on chosen
representatives. -/
def kProjectiveLocusDerivedFunctor
    {C : Type u} {D : Type u'} [Category.{v} C] [Abelian C]
    [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive] :
    KProjectiveDerivedCategory C ⥤ DerivedCategory D :=
  (kProjectiveQhEquivalence C).inverse ⋙ kProjectiveDerivedFunctor F

/-- Pulling an actual K-projective representative into the derived locus and
then applying the locus functor recovers the representative-level
construction. -/
def kProjectiveLocusDerivedComparison
    {C : Type u} {D : Type u'} [Category.{v} C] [Abelian C]
    [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive] :
    (kProjectiveQhEquivalence C).functor ⋙
        kProjectiveLocusDerivedFunctor F ≅
      kProjectiveDerivedFunctor F :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (kProjectiveQhEquivalence C).unitIso.symm
      (kProjectiveDerivedFunctor F) ≪≫
    Functor.leftUnitor _

/-- On a concrete bounded-above projective complex, the supported derived
functor is represented by applying the original functor degreewise. -/
def kProjectiveDerivedFunctorObjIso
    {C : Type u} {D : Type u'} [Category.{v} C] [Abelian C]
    [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d]
    [∀ n : ℤ, Projective (K.X n)] :
    (kProjectiveDerivedFunctor F).obj
        (KProjectiveHomotopyCategory.ofBoundedAboveProjectives K d) ≅
      DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (DerivedCategory.quotientCompQhIso D).app _

end

end CategoryTheory

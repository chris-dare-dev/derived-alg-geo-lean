/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.EssentialImage
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.Affine

/-!
# Affine derived pullback from K-projective complexes

This file constructs a genuinely derived pullback along an arbitrary affine
ring map on the locus represented by K-projective complexes. No flatness of
the ring map is assumed. The construction applies extension of scalars in the
homotopy category and then localizes the target at quasi-isomorphisms.

The source K-projective homotopy category embeds fully faithfully in the
derived category. Bounded-above complexes of projective modules give
concrete objects of this source category, using Mathlib's K-projectivity
theorem. This is the affine supported lane toward arbitrary big-Zariski
pullback; extending it to every relative-perfect object still requires
functorial K-flat or K-projective representatives and geometric descent.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

noncomputable section

universe v v' u u'

attribute [local instance] HasDerivedCategory.standard

/-- Extension of scalars is additive. Mathlib supplies the adjunction and
the tensor-product formulas; this instance records the resulting elementary
compatibility with addition of module homomorphisms. -/
instance affineExtendScalars_additive
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (ModuleCat.extendScalars f.hom).Additive where
  map_add {M N} g h := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    let φ : R →+* A := f.hom
    letI : Module R A := Module.compHom A φ
    change (1 : A) ⊗ₜ[R,φ] (g m + h m) =
      (1 : A) ⊗ₜ[R,φ] g m + (1 : A) ⊗ₜ[R,φ] h m
    rw [TensorProduct.tmul_add]

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

/-- Arbitrary extension of scalars on affine K-projective representatives.
No flatness hypothesis is imposed on `f`. -/
def affineKProjectivePullback {R A : CommRingCat.{u}} (f : R ⟶ A) :
    KProjectiveHomotopyCategory (ModuleCat R) ⥤
      DerivedCategory (ModuleCat A) :=
  kProjectiveDerivedFunctor (ModuleCat.extendScalars f.hom)

/-- Arbitrary affine derived pullback on the full derived locus represented
by K-projective complexes. -/
def affineKProjectiveDerivedPullback
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    KProjectiveDerivedCategory (ModuleCat R) ⥤
      DerivedCategory (ModuleCat A) :=
  kProjectiveLocusDerivedFunctor (ModuleCat.extendScalars f.hom)

/-- The derived-locus construction agrees with extension of scalars on
actual K-projective representatives. -/
def affineKProjectiveDerivedPullbackComparison
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (kProjectiveQhEquivalence (ModuleCat R)).functor ⋙
        affineKProjectiveDerivedPullback f ≅
      affineKProjectivePullback f :=
  kProjectiveLocusDerivedComparison (ModuleCat.extendScalars f.hom)

/-- A bounded-above complex of projective `R`-modules computes arbitrary
affine derived pullback by degreewise extension of scalars. -/
def affineKProjectivePullbackObjIso {R A : CommRingCat.{u}} (f : R ⟶ A)
    (K : CochainComplex (ModuleCat R) ℤ) (d : ℤ) [K.IsStrictlyLE d]
    [∀ n : ℤ, Projective (K.X n)] :
    (affineKProjectivePullback f).obj
        (KProjectiveHomotopyCategory.ofBoundedAboveProjectives K d) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars f.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  kProjectiveDerivedFunctorObjIso (ModuleCat.extendScalars f.hom) K d

end

end CategoryTheory.Triangulated.StabilityCondition.Families

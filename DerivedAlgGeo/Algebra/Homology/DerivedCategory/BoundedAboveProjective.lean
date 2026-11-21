/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KProjective

/-!
# The bounded-above projective derived locus

For any abelian category, this file cuts out the derived locus represented by
bounded-above complexes of projective objects.  Additive functors preserving
projectives act functorially on this locus.  Extension of scalars for module
categories is a downstream affine instance.

With enough projectives, Mathlib's bounded-below injective replacement, applied
in the opposite category, gives every strictly bounded-above complex a strictly
bounded-above projective replacement
(`CochainComplex.exists_boundedAbove_projective_replacement`). So the bounded-above
derived category `DerivedCategory.Minus C` lies in the bounded-above projective
locus, and any additive functor can be derived on it by K-projective replacement
(`minusKProjectiveDerivedFunctor`), computed on a bounded-above complex of
projectives by applying the functor degreewise
(`minusKProjectiveDerivedFunctorObjIso`). No exactness is assumed of the functor,
no universal property of a left-derived functor is stated, and nothing is asserted
on unbounded objects.
-/

namespace CochainComplex

open CategoryTheory Limits

/-- Reindexing an opposite-category cochain complex by negation preserves a
quasi-isomorphism. The short complexes in degree `n` and `-n` are definitionally
the same after choosing their adjacent indices explicitly. -/
private lemma quasiIso_restrictionNeg {C : Type*} [Category* C] [Abelian C]
    {J L : CochainComplex Cᵒᵖ ℤ} (i : J ⟶ L) (hi : QuasiIso i) :
    QuasiIso (HomologicalComplex.restrictionMap i ComplexShape.embeddingDownIntUpInt) := by
  letI : QuasiIso i := hi
  rw [quasiIso_iff]
  intro n
  have hi' : QuasiIsoAt i (-n) := (quasiIso_iff i).mp inferInstance (-n)
  have hsc := (quasiIsoAt_iff' i (- (n + 1)) (-n) (- (n - 1))
    (by simp; omega) (by simp; omega)).mp hi'
  apply (quasiIsoAt_iff'
    (HomologicalComplex.restrictionMap i ComplexShape.embeddingDownIntUpInt)
    (n + 1) n (n - 1) (by simp) (by simp)).mpr
  exact hsc

/-- In an abelian category with enough projectives, a strictly bounded-above complex
has a strictly bounded-above quasi-isomorphic complex of projective objects, with the
same upper bound. Its lower tail may be infinite. -/
theorem exists_boundedAbove_projective_replacement {C : Type*} [Category* C] [Abelian C]
    [EnoughProjectives C] (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    ∃ (P : CochainComplex C ℤ) (p : P ⟶ K),
      P.IsStrictlyLE b ∧ (∀ i : ℤ, Projective (P.X i)) ∧ QuasiIso p := by
  let E := CochainComplex.opEquivalence C
  let J := E.functor.obj (Opposite.op K)
  have hJ : J.IsStrictlyGE (-b) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have hzero : IsZero (K.X (-i)) := K.isZero_of_isStrictlyLE b (-i) (by omega)
    change IsZero (Opposite.op (K.X (-i)))
    exact hzero.op
  letI : J.IsStrictlyGE (-b) := hJ
  obtain ⟨L, i, hqi, hInj, hL⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective J (-b)
  let P : CochainComplex C ℤ := Opposite.unop (E.inverse.obj L)
  let p : P ⟶ K := (E.inverse.map i).unop ≫ (E.unitIso.app (Opposite.op K)).unop.hom
  have hBound : P.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    change IsZero (Opposite.unop (L.X (-n)))
    have hzero : IsZero (L.X (-n)) := by
      letI : L.IsStrictlyGE (-b) := hL
      exact L.isZero_of_isStrictlyGE (-b) (-n) (by omega)
    exact hzero.unop
  have hProj (n : ℤ) : Projective (P.X n) := by
    change Projective (Opposite.unop (L.X (-n)))
    letI : Injective (L.X (-n)) := hInj (-n)
    infer_instance
  have hRestrict : QuasiIso
      (HomologicalComplex.restrictionMap i ComplexShape.embeddingDownIntUpInt) :=
    quasiIso_restrictionNeg i hqi
  have hUnop : QuasiIso (E.inverse.map i).unop := by
    change QuasiIso ((HomologicalComplex.unopFunctor C (ComplexShape.down ℤ)).map
        (HomologicalComplex.restrictionMap i ComplexShape.embeddingDownIntUpInt).op)
    exact (HomologicalComplex.quasiIso_unopFunctor_map_iff _).mpr hRestrict
  letI : QuasiIso (E.inverse.map i).unop := hUnop
  refine ⟨P, p, hBound, hProj, ?_⟩
  dsimp [p]
  infer_instance

end CochainComplex

namespace CategoryTheory

open Limits

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

section Minus

variable (C : Type u) [Category.{v} C] [Abelian C] [EnoughProjectives C]

/-- With enough projectives, every bounded-above object of the derived category is
represented by a bounded-above complex of projective objects. -/
theorem minus_le_essImage_boundedAboveProjectiveQh :
    DerivedCategory.TStructure.t.minus ≤ (boundedAboveProjectiveQh C).essImage := by
  rintro X ⟨n, hn⟩
  letI : X.IsLE n := hn
  obtain ⟨K, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE n
  obtain ⟨P, p, hP, hProj, hp⟩ :=
    CochainComplex.exists_boundedAbove_projective_replacement K n
  exact ⟨⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P, n, hP, hProj⟩,
    ⟨(DerivedCategory.quotientCompQhIso C).app P ≪≫
      asIso (DerivedCategory.Q.map p) ≪≫ e.symm⟩⟩

/-- With enough projectives, every bounded-above object of the derived category is
represented by a K-projective complex. -/
theorem minus_le_essImage_kProjectiveQh :
    DerivedCategory.TStructure.t.minus ≤ (kProjectiveQh C).essImage := by
  intro X hX
  obtain ⟨K, ⟨e⟩⟩ := minus_le_essImage_boundedAboveProjectiveQh C X hX
  exact ⟨(boundedAboveProjectiveToKProjective C).obj K, ⟨e⟩⟩

/-- The bounded-above derived category, as a full subcategory of the K-projective
derived locus. -/
def minusToKProjectiveDerived :
    DerivedCategory.Minus C ⥤ KProjectiveDerivedCategory C :=
  (kProjectiveQh C).essImage.lift DerivedCategory.Minus.ι
    fun X ↦ minus_le_essImage_kProjectiveQh C _ X.property

variable {C} {D : Type u'} [Category.{v'} D] [Abelian D]

/-- An additive functor derived on the bounded-above derived category: replace by a
K-projective complex and apply the functor degreewise. No exactness of the functor is
assumed, and no universal property of a left-derived functor is stated. -/
def minusKProjectiveDerivedFunctor (F : C ⥤ D) [F.Additive] :
    DerivedCategory.Minus C ⥤ DerivedCategory D :=
  minusToKProjectiveDerived C ⋙ kProjectiveLocusDerivedFunctor F

/-- On a bounded-above complex of projective objects, `minusKProjectiveDerivedFunctor` is
the functor applied degreewise. -/
def minusKProjectiveDerivedFunctorObjIso (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] [∀ n : ℤ, Projective (K.X n)] :
    (minusKProjectiveDerivedFunctor F).obj ⟨DerivedCategory.Q.obj K, d, inferInstance⟩ ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (kProjectiveLocusDerivedFunctor F).mapIso
      (ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso C).app K)).symm ≪≫
    (kProjectiveLocusDerivedComparison F).app
      (KProjectiveHomotopyCategory.ofBoundedAboveProjectives K d) ≪≫
    kProjectiveDerivedFunctorObjIso F K d

end Minus

end

end CategoryTheory

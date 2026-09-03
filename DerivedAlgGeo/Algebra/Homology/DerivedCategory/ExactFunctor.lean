/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Retracts

/-!
# Exact functors between derived categories

Exact functors between arbitrary abelian categories preserve strict complex
bounds and therefore preserve the canonical derived t-structure and its
bounded objects.  The file also records that `Functor.mapDerivedCategory` is
functorial up to natural isomorphism: it transports natural isomorphisms and
takes identities and composites to identities and composites.  No scheme,
sheaf, or other geometric input occurs here.

## Main definitions

* `NatIso.mapDerivedCategory`, `Functor.mapDerivedCategoryIdIso`, and
  `Functor.mapDerivedCategoryCompIso`: the pseudofunctoriality of
  `Functor.mapDerivedCategory`, each obtained from the corresponding
  isomorphism on complexes through the universal property of the
  localization (`Localization.liftNatIso`).

## Main results

* `mapDerivedCategory_bounded`: an exact functor preserves bounded objects;
* `Functor.singleFunctorIsoOfFactors`: the degree-`n` embedding commutes with any functor on
  derived categories that factors degreewise through `F`.
-/

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

open Limits Pretriangulated Triangulated

variable {A B C : Type*} [Category A] [Category B] [Category C] [Abelian A] [Abelian B]
  [Abelian C]

/-- An additive functor sends a strictly bounded-above cochain complex to a
strictly bounded-above cochain complex with the same bound. -/
lemma mapHomologicalComplex_isStrictlyLE (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) (n : ℤ) (hK : K.IsStrictlyLE n) :
    CochainComplex.IsStrictlyLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [CochainComplex.isStrictlyLE_iff] at hK ⊢
  intro i hi
  exact F.map_isZero (hK i hi)

/-- An additive functor sends a strictly bounded-below cochain complex to a
strictly bounded-below cochain complex with the same bound. -/
lemma mapHomologicalComplex_isStrictlyGE (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) (n : ℤ) (hK : K.IsStrictlyGE n) :
    CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [CochainComplex.isStrictlyGE_iff] at hK ⊢
  intro i hi
  exact F.map_isZero (hK i hi)

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]

/-- The functor on derived categories induced by an exact functor preserves
the canonical `≤ n` truncation bound. -/
lemma mapDerivedCategory_isLE (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : DerivedCategory A) (n : ℤ)
    (hE : (DerivedCategory.TStructure.t (C := A)).IsLE E n) :
    (DerivedCategory.TStructure.t (C := B)).IsLE
      (F.mapDerivedCategory.obj E) n := by
  obtain ⟨K, e, hK⟩ := hE
  exact ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K,
    mapHomologicalComplex_isStrictlyLE F K n hK⟩

/-- The functor on derived categories induced by an exact functor preserves
the canonical `≥ n` truncation bound. -/
lemma mapDerivedCategory_isGE (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : DerivedCategory A) (n : ℤ)
    (hE : (DerivedCategory.TStructure.t (C := A)).IsGE E n) :
    (DerivedCategory.TStructure.t (C := B)).IsGE
      (F.mapDerivedCategory.obj E) n := by
  obtain ⟨K, e, hK⟩ := hE
  exact ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K,
    mapHomologicalComplex_isStrictlyGE F K n hK⟩

/-- Exact functors preserve bounded objects in the canonical derived
t-structures. -/
lemma mapDerivedCategory_bounded (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : DerivedCategory A)
    (hE : (DerivedCategory.TStructure.t (C := A)).bounded E) :
    (DerivedCategory.TStructure.t (C := B)).bounded
      (F.mapDerivedCategory.obj E) :=
  ⟨⟨hE.1.choose, mapDerivedCategory_isGE F E hE.1.choose hE.1.choose_spec⟩,
    ⟨hE.2.choose, mapDerivedCategory_isLE F E hE.2.choose hE.2.choose_spec⟩⟩

/-- A natural isomorphism of exact functors induces a natural isomorphism of
the functors on derived categories, by the universal property of the
localization applied to `NatIso.mapHomologicalComplex`. -/
noncomputable def NatIso.mapDerivedCategory {F G : A ⥤ B} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
      DerivedCategory.Q)

variable (A) in
/-- The derived functor of the identity is the identity, up to the natural
isomorphism lifted from `Functor.mapHomologicalComplexIdIso`.  The category is
explicit because nothing else determines it. -/
noncomputable def Functor.mapDerivedCategoryIdIso :
    (𝟭 A).mapDerivedCategory ≅ 𝟭 (DerivedCategory A) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    ((𝟭 A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q
    (𝟭 A).mapDerivedCategory (𝟭 (DerivedCategory A))
    (Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫ Functor.leftUnitor _)

/-- A factorization `F ⋙ G ≅ H` of exact functors induces the factorization of
the derived functors, in the shape of `Functor.mapHomologicalComplexCompIso`:
the composite is given as a third functor `H` so that a caller need not
elaborate `(F ⋙ G).mapDerivedCategory`, whose exactness instances
`comp_preservesFiniteLimits` does not supply by search. -/
noncomputable def Functor.mapDerivedCategoryCompIso {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    (e : F ⋙ G ≅ H)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
      G.mapDerivedCategory)
    (H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) H.mapDerivedCategory
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The degree-`n` embedding commutes with any functor `G` on derived categories that is
degreewise `F` on complexes, `DerivedCategory.Q ⋙ G ≅ F.mapHomologicalComplex _ ⋙ Q`.  This
is the argument of Mathlib's `Functor.mapDerivedCategorySingleFunctor`, whose `G` is
`F.mapDerivedCategory`, run on an arbitrary factorization, so that a contract carrying its
derived functor as data can use it. -/
noncomputable def Functor.singleFunctorIsoOfFactors (F : A ⥤ B) [F.PreservesZeroMorphisms]
    (G : DerivedCategory A ⥤ DerivedCategory B)
    (e : DerivedCategory.Q ⋙ G ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) (n : ℤ) :
    DerivedCategory.singleFunctor A n ⋙ G ≅ F ⋙ DerivedCategory.singleFunctor B n :=
  Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ A n) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    (Functor.isoWhiskerLeft _ (DerivedCategory.singleFunctorIsoCompQ B n)).symm

end CategoryTheory

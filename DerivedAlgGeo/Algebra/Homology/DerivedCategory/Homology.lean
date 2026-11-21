/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Homology and exact derived functors

An exact functor between arbitrary abelian categories commutes with canonical
derived-category homology.  This is the generic comparison used by geometric
realizations such as coherent sheaves and `Dqc(X)`.

`mapDerivedCategoryHomologyIso` is the comparison at one object;
`mapDerivedCategoryHomologyFunctorIso` is the natural isomorphism of functors
`F.mapDerivedCategory ⋙ H^n ≅ H^n ⋙ F`, obtained from the comparison on cochain
complexes through the universal property of the localization functor `Q`.
-/

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

open Limits

universe u v w

/-- Exact functors commute with homology after passage to derived categories.
The isomorphism is constructed from a representative complex, the two
localization comparison isomorphisms, and preservation of homology. -/
noncomputable def mapDerivedCategoryHomologyIso
    {A : Type u} {B : Type v} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} B] (F : A ⥤ B)
    (hadd : F.Additive) (hlim : PreservesFiniteLimits F)
    (hcolim : PreservesFiniteColimits F)
    (E : DerivedCategory A) (n : ℤ) :
    (DerivedCategory.homologyFunctor B n).obj (F.mapDerivedCategory.obj E) ≅
      F.obj ((DerivedCategory.homologyFunctor A n).obj E) :=
  by
    letI : F.Additive := hadd
    letI : PreservesFiniteLimits F := hlim
    letI : PreservesFiniteColimits F := hcolim
    let K := DerivedCategory.Q.objPreimage E
    exact (DerivedCategory.homologyFunctor B n).mapIso
        (F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm) ≪≫
      (DerivedCategory.homologyFunctor B n).mapIso
        (F.mapDerivedCategoryFactors.app K) ≪≫
      (DerivedCategory.homologyFunctorFactors B n).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
      (K.sc n).mapHomologyIso F ≪≫
      F.mapIso ((DerivedCategory.homologyFunctorFactors A n).app K).symm ≪≫
      F.mapIso ((DerivedCategory.homologyFunctor A n).mapIso
        (DerivedCategory.Q.objObjPreimageIso E))

/-- Exact functors commute with homology after passage to derived categories, naturally in
the object: `F.mapDerivedCategory ⋙ H^n ≅ H^n ⋙ F`. On cochain complexes it is the homology
comparison `ShortComplex.mapHomologyIso`; it descends along the localization functor `Q`. -/
noncomputable def mapDerivedCategoryHomologyFunctorIso
    {A : Type u} {B : Type v} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B n ≅
      DerivedCategory.homologyFunctor A n ⋙ F := by
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  letI : Localization.Lifting DerivedCategory.Q W
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) n)
      (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B n) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors B n)⟩
  letI : Localization.Lifting DerivedCategory.Q W
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n ⋙ F)
      (DerivedCategory.homologyFunctor A n ⋙ F) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors A n) F⟩
  exact Localization.liftNatIso DerivedCategory.Q W
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) n)
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n ⋙ F) _ _
    (NatIso.ofComponents (fun K ↦ (K.sc n).mapHomologyIso F) (fun φ ↦
      ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n).map φ) F))

end CategoryTheory

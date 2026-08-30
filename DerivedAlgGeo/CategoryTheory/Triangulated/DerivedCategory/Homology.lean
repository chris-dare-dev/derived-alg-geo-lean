/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.ExactFunctor

/-!
# Homology and exact derived functors

An exact functor between arbitrary abelian categories commutes with canonical
derived-category homology.  This is the generic comparison used by geometric
realizations such as coherent sheaves and `Dqc(X)`.
-/

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

end CategoryTheory

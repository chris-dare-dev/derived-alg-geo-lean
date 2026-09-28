/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Colimits of direct-sum total complexes

The direct-sum total functor for integer-indexed cochain bicomplexes preserves
colimits of any shape when the target category has the corresponding colimits
and coproducts over each total-degree fiber. This requires no exactness
assumption: each total degree is a coproduct of bidegrees.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex₂

private abbrev TotalDegreeFiber (n : ℤ) :=
  (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)) ⁻¹' {n}

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {J : Type w} [Category J]
  [∀ n : ℤ, HasCoproductsOfShape
    ((ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) ⁻¹' {n}) C]
  [HasColimitsOfShape J C]

private def totalDegreeFiberFunctor (n : ℤ) :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      GradedObject (TotalDegreeFiber n) C where
  obj K i := (K.X i.1.1).X i.1.2
  map f i := (f.f i.1.1).f i.1.2

private noncomputable def totalDegreeIsColimit
    (F : J ⥤ HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (s : Cocone F) (n : ℤ)
    (hs : ∀ i : TotalDegreeFiber n, IsColimit
      ((GradedObject.eval (C := C) i).mapCocone
        ((totalDegreeFiberFunctor n).mapCocone s))) :
    IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapCocone
      ((totalFunctor C (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).mapCocone s)) := by
  change IsColimit (colim.mapCocone
    ((piEquivalenceFunctorDiscrete (TotalDegreeFiber n) C).functor.mapCocone
      ((totalDegreeFiberFunctor n).mapCocone s)))
  apply isColimitOfPreserves
  exact evaluationJointlyReflectsColimits _ (fun i => hs i.as)

private noncomputable def totalIsColimit
    (F : J ⥤ HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (s : Cocone F)
    (hs : ∀ (n : ℤ) (i : TotalDegreeFiber n), IsColimit
      ((GradedObject.eval (C := C) i).mapCocone
        ((totalDegreeFiberFunctor n).mapCocone s))) :
    IsColimit ((totalFunctor C (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).mapCocone s) :=
  HomologicalComplex.isColimitOfEval _ _ (fun n => totalDegreeIsColimit F s n (hs n))

/-- Direct-sum totalization preserves a colimit cocone of integer-indexed
cochain bicomplexes. The coproduct assumption concerns only the fibers of
each total degree, and exactness of colimits is not needed. -/
noncomputable def isColimitTotalFunctorMapCocone
    (F : J ⥤ HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (s : Cocone F) (h : IsColimit s) :
    IsColimit ((totalFunctor C (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).mapCocone s) := by
  apply totalIsColimit F s
  intro n i
  let p : ℤ := i.1.1
  let q : ℤ := i.1.2
  change IsColimit
    ((HomologicalComplex.eval (CochainComplex C ℤ) (ComplexShape.up ℤ) p ⋙
      HomologicalComplex.eval C (ComplexShape.up ℤ) q).mapCocone s)
  exact isColimitOfPreserves _ h

/-- Direct-sum totalization preserves colimits of shape `J` whenever each
total degree admits the requisite coproduct. -/
noncomputable instance totalFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J
      (totalFunctor C (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :=
  ⟨fun {F} => ⟨fun h => ⟨isColimitTotalFunctorMapCocone F _ h⟩⟩⟩

end HomologicalComplex₂

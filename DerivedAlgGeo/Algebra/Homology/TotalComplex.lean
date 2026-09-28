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

Mathlib's direct-sum total functor preserves colimits of any diagram shape when
the component category has those colimits and each total-degree fiber admits
coproducts. For a particular cocone, colimits of its bidegree diagrams suffice.
No exactness or homology argument is involved.

## Main definitions

* `HomologicalComplex₂.isColimitTotalFunctorMapCocone` constructs the
  universal property for the literal mapped cocone.

## Main results

* `HomologicalComplex₂.totalFunctor_preservesColimitsOfShape` exposes
  colimit preservation to typeclass search.

## Implementation notes

Evaluate in each total degree, view its diagonal coproduct as a colimit over
a discrete category, and commute the two colimits. Degreewise evaluation
then reflects the resulting universal property.

## References

The construction extends Mathlib's `HomologicalComplex₂.totalFunctor` and
uses `HomologicalComplex.isColimitOfEval` and
`CategoryTheory.Limits.evaluationJointlyReflectsColimits`.

## Tags

bicomplex, total complex, coproduct, colimit
-/

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {J : Type w} [Category J]
  {I₁ I₂ I₁₂ : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  [∀ n : I₁₂, HasCoproductsOfShape ((ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}) C]

private def totalDegreeFiberFunctor
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {I₁ I₂ I₁₂ : Type*}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] (n : I₁₂) :
    HomologicalComplex₂ C c₁ c₂ ⥤
      GradedObject ((ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}) C where
  obj K i := (K.X i.1.1).X i.1.2
  map f i := (f.f i.1.1).f i.1.2

private noncomputable def totalDegreeIsColimit
    (F : J ⥤ HomologicalComplex₂ C c₁ c₂) (s : Cocone F) (n : I₁₂)
    (hs : ∀ i : (ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}, IsColimit
      ((GradedObject.eval (C := C) i).mapCocone
        ((totalDegreeFiberFunctor c₁ c₂ c₁₂ n).mapCocone s))) :
    IsColimit ((HomologicalComplex.eval C c₁₂ n).mapCocone
      ((totalFunctor C c₁ c₂ c₁₂).mapCocone s)) := by
  change IsColimit (colim.mapCocone
    ((piEquivalenceFunctorDiscrete ((ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}) C).functor.mapCocone
      ((totalDegreeFiberFunctor c₁ c₂ c₁₂ n).mapCocone s)))
  apply isColimitOfPreserves
  exact evaluationJointlyReflectsColimits _ (fun i => hs i.as)

private noncomputable def totalIsColimit
    (F : J ⥤ HomologicalComplex₂ C c₁ c₂) (s : Cocone F)
    (hs : ∀ (n : I₁₂) (i : (ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}), IsColimit
      ((GradedObject.eval (C := C) i).mapCocone
        ((totalDegreeFiberFunctor c₁ c₂ c₁₂ n).mapCocone s))) :
    IsColimit ((totalFunctor C c₁ c₂ c₁₂).mapCocone s) :=
  HomologicalComplex.isColimitOfEval _ _
    (fun n => totalDegreeIsColimit c₁ c₂ c₁₂ F s n (hs n))

/-- Evaluate the cocone in each bidegree, commute its diagram colimit with
the coproduct over each total-degree fiber, and reflect colimits through
degreewise evaluation. Only the bidegree diagrams occurring in `F` need
colimits; ambient colimits of shape `J` are unnecessary. -/
noncomputable def isColimitTotalFunctorMapCocone
    (F : J ⥤ HomologicalComplex₂ C c₁ c₂)
    [∀ (p : I₁) (q : I₂), HasColimit
      ((F ⋙ HomologicalComplex.eval (HomologicalComplex C c₂) c₁ p) ⋙
        HomologicalComplex.eval C c₂ q)]
    (s : Cocone F) (h : IsColimit s) :
    IsColimit ((totalFunctor C c₁ c₂ c₁₂).mapCocone s) := by
  apply totalIsColimit c₁ c₂ c₁₂ F s
  intro n i
  let p : I₁ := i.1.1
  let q : I₂ := i.1.2
  change IsColimit
    ((HomologicalComplex.eval (HomologicalComplex C c₂) c₁ p ⋙
      HomologicalComplex.eval C c₂ q).mapCocone s)
  exact isColimitOfPreserves _ h

/-- Register `HomologicalComplex₂.isColimitTotalFunctorMapCocone` for
 typeclass search, so downstream consumers can transport their cocones with
 `CategoryTheory.Limits.isColimitOfPreserves`. -/
noncomputable instance totalFunctor_preservesColimitsOfShape
    [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (totalFunctor C c₁ c₂ c₁₂) :=
  ⟨fun {F} => ⟨fun h => ⟨isColimitTotalFunctorMapCocone c₁ c₂ c₁₂ F _ h⟩⟩⟩

end HomologicalComplex₂

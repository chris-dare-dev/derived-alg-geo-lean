/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Exactness
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Slicing.Quotient
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Serre functors as triangulated autoequivalences

When a Serre functor is an equivalence, its additive, signed shift, and exact
structures supply the bundled `GroupAction.TriEquiv` used by the stability
action. This adapter lives with that consumer so the generic Serre theory does
not import the stability-condition tree.
-/

namespace CategoryTheory.SerreFunctor.SerreFunctorData

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition

universe w v u

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]
  [Pretriangulated C]

/-- Bundle the Serre autoequivalence with its proved additive, signed shift,
and triangulated structures. Equivalence is a separate hypothesis, supplied
for example by Serre data with a co-Serre witness. -/
noncomputable def toTriEquiv (D : SerreFunctorData k C)
    [D.S.IsEquivalence] : GroupAction.TriEquiv C := by
  letI : D.S.Additive := D.additive
  letI : D.S.CommShift ℤ := D.signedCommShift
  letI : D.S.IsTriangulated := D.isTriangulated
  let E : C ≌ C := D.S.asEquivalence
  letI : E.functor.Additive := by
    change D.S.Additive
    infer_instance
  letI : E.functor.CommShift ℤ := by
    change D.S.CommShift ℤ
    infer_instance
  letI : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
  letI : E.CommShift ℤ := E.commShift_of_functor ℤ
  letI : E.functor.IsTriangulated := by
    change D.S.IsTriangulated
    infer_instance
  letI : E.IsTriangulated := Equivalence.IsTriangulated.mk' E inferInstance
  exact {
    e := E
    fAdd := inferInstance
    iAdd := inferInstance
    fCS := inferInstance
    iCS := inferInstance
    fTri := inferInstance
    iTri := inferInstance }

end CategoryTheory.SerreFunctor.SerreFunctorData

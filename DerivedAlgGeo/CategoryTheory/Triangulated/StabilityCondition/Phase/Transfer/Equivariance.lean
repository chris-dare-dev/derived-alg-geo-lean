/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Phase
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap

/-!
# Equivariance of preimage transfer

Preimage transfer commutes with compatible autoequivalences.  Compatibility is
the natural isomorphism one obtains by passing an equivariant geometric
functor through the inverse representatives used by `Slicing.mapEquiv`.

The final theorem spells this out for representatives of `AutPairQuot`.  The
class-lattice components do not enter the slicing equality, but retaining the
pairs in the statement gives downstream stability-family code the exact
representative-level interface it needs before descending to quotients.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

universe v₁ u₁ v₂ u₂ u₃ u₄

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

variable (s : Slicing D) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
  [F.IsTriangulated] (h : s.PreimageData F)

/-- Preimage transfer commutes with compatible triangulated
autoequivalences.  The compatibility is stated for inverse functors because
`Slicing.mapEquiv` defines membership by applying the inverse representative. -/
theorem Slicing.preimage_mapEquiv (PhiC : C ≌ C) (PhiD : D ≌ D)
    [PhiC.functor.Additive] [PhiC.inverse.Additive]
    [PhiC.functor.CommShift ℤ] [PhiC.inverse.CommShift ℤ]
    [PhiC.functor.IsTriangulated] [PhiC.inverse.IsTriangulated]
    [PhiD.functor.Additive] [PhiD.inverse.Additive]
    [PhiD.functor.CommShift ℤ] [PhiD.inverse.CommShift ℤ]
    [PhiD.functor.IsTriangulated] [PhiD.inverse.IsTriangulated]
    (alpha : F ⋙ PhiD.inverse ≅ PhiC.inverse ⋙ F)
    (hmap : (s.mapEquiv PhiD).PreimageData F) :
    (s.mapEquiv PhiD).preimage F hmap =
      (s.preimage F h).mapEquiv PhiC := by
  apply Slicing.ext
  funext phi E
  apply propext
  constructor
  · intro hE
    change s.P phi ((F ⋙ PhiD.inverse).obj E) at hE
    change s.P phi ((PhiC.inverse ⋙ F).obj E)
    exact ObjectProperty.prop_of_iso _ (alpha.app E) hE
  · intro hE
    change s.P phi ((PhiC.inverse ⋙ F).obj E) at hE
    change s.P phi ((F ⋙ PhiD.inverse).obj E)
    exact ObjectProperty.prop_of_iso _ (alpha.app E).symm hE

variable [IsTriangulated C] [IsTriangulated D]
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

end CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D]
variable {LambdaC : Type u₃} [AddCommGroup LambdaC]
variable {LambdaD : Type u₄} [AddCommGroup LambdaD]

omit [IsTriangulated C] [IsTriangulated D] in
/-- Representative-level `AutPairQuot` compatibility for preimage transfer.

This theorem is intentionally about representatives `aC` and `aD`: quotient
descent additionally requires the geometric transfer data to be independent
of representatives, which is a property of the eventual family functors. -/
@[nolint unusedArguments]
theorem AutPair.preimage_representatives
    (s : Slicing D) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] (h : s.PreimageData F)
    (vC : K₀ C →+ LambdaC) (vD : K₀ D →+ LambdaD)
    (aC : AutPair vC) (aD : AutPair vD)
    (alpha : F ⋙ aD.Φ.e.inverse ≅ aC.Φ.e.inverse ⋙ F)
    (hmap : (s.mapEquiv aD.Φ.e).PreimageData F) :
    (s.mapEquiv aD.Φ.e).preimage F hmap =
      (s.preimage F h).mapEquiv aC.Φ.e :=
  CategoryTheory.Triangulated.Slicing.preimage_mapEquiv
    s F h aC.Φ.e aD.Φ.e alpha hmap

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

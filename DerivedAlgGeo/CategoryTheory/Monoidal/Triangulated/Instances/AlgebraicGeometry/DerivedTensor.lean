/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Monoidal.Triangulated
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.DerivedTensorCoherence

/-!
# Geometric derived tensors as monoidal-triangulated structures

This bridge registers the scheme-specific coherent derived-tensor contract as
an instance of the generic compatibility interface. The generic monoidal
umbrella deliberately does not import this file.
-/

universe u

namespace CategoryTheory.Triangulated.StabilityCondition.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.FourierMukai
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open AlgebraicGeometry SchemeBaseChange

variable {S : Scheme.{u}}

/-- A coherent geometric derived tensor realizes the generic compatibility
interface between its monoidal and triangulated structures. -/
instance hasCoherentDerivedTensorIsCompatibleWithTriangulation
    (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left]
    [HasCoherentDerivedTensor Z] :
    MonoidalCategory.IsCompatibleWithTriangulation
      (SchemeBoundedCoherentDerivedCategory Z.left) where
  tensorAdditive := HasCoherentDerivedTensor.additive
  tensorCommShift := HasCoherentDerivedTensor.commShift
  tensorIsTriangulated := HasCoherentDerivedTensor.isTriangulated

end CategoryTheory.Triangulated.StabilityCondition.Families

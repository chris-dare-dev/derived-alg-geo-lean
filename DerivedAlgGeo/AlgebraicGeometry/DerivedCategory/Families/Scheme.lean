/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.Families.BaseChange

/-!
# Scheme-indexed triangulated families

This file specializes the generic categorical family interface to the category
of schemes over a fixed scheme. The fibers and pullback functors remain
client-supplied categorical data; no stability condition is imposed.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Triangulated.Families

noncomputable section

universe u w

/-- The category of scheme-valued base changes over a fixed scheme. -/
abbrev SchemeBaseChange (S : Scheme.{u}) := Over S

/-- An abstract triangulated category over every scheme base change of `S`.
The fibers and pullback functors are explicit client data. -/
abbrev SchemeTriangulatedFiberFamily (S : Scheme.{u}) :=
  TriangulatedFiberFamily (B := SchemeBaseChange S)

namespace SchemeTriangulatedFiberFamily

/-- The constant triangulated family on the category of schemes over `S`. -/
def constant (S : Scheme.{u})
    (C : Type w) [Category.{w} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] : SchemeTriangulatedFiberFamily S :=
  TriangulatedFiberFamily.constant (SchemeBaseChange S) C

end SchemeTriangulatedFiberFamily

end


end CategoryTheory.Triangulated.StabilityCondition.Families

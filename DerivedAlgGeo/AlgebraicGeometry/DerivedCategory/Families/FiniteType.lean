/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.Scheme

/-!
# Finite-type scheme base changes

This neutral geometric predicate is shared by derived-category families,
moduli problems, and stability applications. It does not impose stability data.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory AlgebraicGeometry

universe u

/-- A scheme base change is of finite type when its structure morphism is
locally of finite type and quasi-compact. -/
def IsFiniteTypeBaseChange {S : Scheme.{u}} (T : SchemeBaseChange S) : Prop :=
  LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom

end CategoryTheory.Triangulated.StabilityCondition.Families

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.LinearDual
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Opposite
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The derived lift of exact linear duality

The exact linear-dual functor of `Algebra/Category/ModuleCat/LinearDual.lean` induces a
functor on derived categories. To use this lift from the opposite of a derived category, a
client supplies the generic `CategoryTheory.DerivedCategory.OppositeComparison`. The
resulting derived linear-dual functors are categorical infrastructure; geometric Serre
duality imports them as consumers.
-/


universe u

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

namespace ModuleCat

variable (k : Type u) [Field k]

/-- The derived functor induced by exact algebraic linear duality. Its source
is the derived category of the opposite abelian category. -/
noncomputable def derivedLinearDualFunctor :
    DerivedCategory ((ModuleCat.{u + 1} k)ᵒᵖ) ⥤
      DerivedCategory (ModuleCat.{u + 1} k) :=
  (linearDualFunctor.{u, u + 1} k).mapDerivedCategory

/-- Algebraic derived linear duality as a functor from the opposite derived
category, once the explicit opposite/derived comparison is supplied. -/
noncomputable def derivedLinearDualFromOpposite
    (B : CategoryTheory.DerivedCategory.OppositeComparison
      (ModuleCat.{u + 1} k)) :
    (DerivedCategory (ModuleCat.{u + 1} k))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} k) :=
  B.equivalence.functor ⋙ derivedLinearDualFunctor k

/-- Derived linear duality followed by a cohomological shift. -/
noncomputable def derivedLinearDualShift
    (B : CategoryTheory.DerivedCategory.OppositeComparison
      (ModuleCat.{u + 1} k)) (n : ℤ) :
    (DerivedCategory (ModuleCat.{u + 1} k))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} k) :=
  derivedLinearDualFromOpposite k B ⋙
    shiftFunctor (DerivedCategory (ModuleCat.{u + 1} k)) n

end ModuleCat

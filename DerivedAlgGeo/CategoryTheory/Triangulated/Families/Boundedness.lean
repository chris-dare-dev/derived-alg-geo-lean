/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/

/-!
# Abstract boundedness problems

A minimal categorical interface for a collection of moduli problems and the
predicate that each is bounded. Stability-family packages may consume this
interface, but boundedness itself does not depend on stability data.
-/

namespace CategoryTheory.Triangulated.Families

universe u

/-- Abstract moduli problems and the predicate expressing their boundedness. -/
structure BoundednessProblem (M : Type u) where
  /-- The geometric boundedness predicate for each numerical moduli problem. -/
  IsBounded : M → Prop

/-- Every supplied moduli problem is bounded. -/
def UniversalBoundedness {M : Type u} (P : BoundednessProblem M) : Prop :=
  ∀ m, P.IsBounded m

end CategoryTheory.Triangulated.Families

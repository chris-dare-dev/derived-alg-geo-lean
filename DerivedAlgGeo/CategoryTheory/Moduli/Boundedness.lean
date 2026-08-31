/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/

/-!
# Abstract boundedness problems

A minimal categorical interface for a collection of moduli problems and the
predicate that each is bounded. Stability-family and geometric packages may
consume this interface, but boundedness itself does not depend on a
triangulated category, a stability condition, or a geometric realization.
-/

namespace CategoryTheory.Moduli

universe u

/-- Abstract moduli problems and the predicate expressing their boundedness. -/
structure BoundednessProblem (M : Type u) where
  /-- The boundedness predicate for each supplied moduli problem. -/
  IsBounded : M → Prop

/-- Every supplied moduli problem is bounded. -/
def UniversalBoundedness {M : Type u} (P : BoundednessProblem M) : Prop :=
  ∀ m, P.IsBounded m

end CategoryTheory.Moduli

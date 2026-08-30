/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.ExactPullbackCoherence

/-!
# Left-derived pullback along arbitrary scheme morphisms

Ordinary pullback of module sheaves is right exact, so applying it degreewise
does not define a functor on unbounded derived categories for an arbitrary
scheme morphism. This file records the correct construction boundary.

A `LeftDerivedPullback` contains an actual functor between the scheme-derived
categories, a comparison from localization followed by that functor to
degreewise module pullback followed by localization, and Mathlib's
left-derived universal property for this comparison. Thus an inhabitant
cannot be supplied by choosing an unrelated functor.

Exact pullback gives a genuine inhabitant. The later K-flat construction can
provide inhabitants for nonexact morphisms through the same interface.

## Main definitions

- `SchemeBaseChange.LeftDerivedPullback`: arbitrary left-derived pullback
  data with its universal property.
- `SchemeBaseChange.LeftDerivedPullback.ofExact`: the existing exact derived
  pullback as an instance of the general interface.
- `SchemeBaseChange.LeftDerivedPullback.exactComparison`: uniqueness of the
  general and exact constructions when ordinary pullback is exact.
-/

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}} {T U : SchemeBaseChange S}

/-- An actual left-derived pullback along an arbitrary scheme base-change
morphism.

The `isLeftDerived` field is the universal property of the displayed
comparison. It is deliberately stronger than storing only a functor with the
correct source and target. -/
structure LeftDerivedPullback (f : T ⟶ U) where
  /-- The functor on the unbounded derived categories of module sheaves. -/
  functor : U.DerivedFiber ⥤ T.DerivedFiber
  /-- Comparison from applying the functor after localization to applying
  ordinary pullback degreewise before localization. -/
  counit : SchemeDerivedCategory.Q U.left ⋙ functor ⟶
    complexPullback f ⋙ SchemeDerivedCategory.Q T.left
  /-- The comparison exhibits `functor` as the left-derived functor of
  degreewise module pullback. -/
  isLeftDerived : functor.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))

namespace LeftDerivedPullback

variable {S : Scheme.{u}} {T U : SchemeBaseChange S} {f : T ⟶ U}

attribute [instance] isLeftDerived

/-- Exact derived pullback satisfies the arbitrary left-derived pullback
interface. -/
def ofExact (f : T ⟶ U) [IsExactPullback f] : LeftDerivedPullback f where
  functor := derivedPullback f
  counit := (derivedPullbackFactors f).hom
  isLeftDerived := CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
    (derivedPullback f) (derivedPullbackFactors f)

/-- The left-derived pullback along the identity morphism. -/
def identity (T : SchemeBaseChange S) : LeftDerivedPullback (𝟙 T) :=
  ofExact (𝟙 T)

/-- Any arbitrary left-derived pullback agrees canonically with the existing
exact construction when ordinary pullback is exact. -/
def exactComparison (P : LeftDerivedPullback f) [IsExactPullback f] :
    P.functor ≅ derivedPullback f := by
  let E := ofExact f
  letI := P.isLeftDerived
  letI := E.isLeftDerived
  exact CategoryTheory.Functor.leftDerivedUnique E.functor P.functor P.counit E.counit
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))

/-- Transport arbitrary derived-pullback data along equality of the
underlying scheme base-change morphisms. -/
def congr {g : T ⟶ U} (P : LeftDerivedPullback f) (h : f = g) :
    LeftDerivedPullback g := by
  subst g
  exact P

end LeftDerivedPullback

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families

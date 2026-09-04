/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FlatPullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.PullbackAcyclicResolution

/-!
# The identity resolution for flat pullback

Flat morphisms have exact pullback on module sheaves, so their derived
pullback needs no nontrivial replacement: the identity functor on complexes
is a pullback-acyclic resolution. This file connects the geometric flatness
theorem with the resolution-based arbitrary derived-pullback construction.

The resulting functor is canonically isomorphic to the existing exact
derived pullback. This supplies a normalization test for later K-flat
resolutions along genuinely non-flat morphisms.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}} {T U : SchemeBaseChange S}

namespace PullbackAcyclicResolution

/-- A flat scheme morphism has the identity pullback-acyclic resolution. -/
def ofFlat (f : T ⟶ U) [Flat f.left] : PullbackAcyclicResolution f :=
  ofExact f

/-- Resolution-derived pullback along a flat morphism agrees canonically
with exact derived pullback. -/
def flatComparison (f : T ⟶ U) [Flat f.left] :
    (ofFlat f).derivedFunctor ≅ derivedPullback f :=
  exactComparison f

/-- The flat comparison respects the displayed transformations to ordinary
degreewise pullback. -/
@[reassoc]
lemma flatComparison_hom_counit (f : T ⟶ U) [Flat f.left] :
    CategoryTheory.Functor.whiskerLeft (SchemeDerivedCategory.Q U.left)
        (flatComparison f).hom ≫
      (derivedPullbackFactors f).hom =
        (ofFlat f).counit := by
  exact exactComparison_hom_counit f

end PullbackAcyclicResolution

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families

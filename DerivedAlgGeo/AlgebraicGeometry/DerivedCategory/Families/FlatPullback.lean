/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.ExactPullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk

/-!
# Exact pullback along flat morphisms

The canonical module pullback-to-stalk comparison lives in
`AlgebraicGeometry.Modules.Pullback.Stalk`.  A flat scheme morphism has flat
maps on local rings, so extension of scalars preserves finite limits at every
stalk.  Joint reflection by module stalks then proves that module-sheaf
pullback preserves finite limits, and hence is exact.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- At every point of a flat scheme morphism, extension of scalars along the
induced local-ring map preserves finite limits. -/
theorem flatStalkMap_preservesFiniteLimits
    {T U : SchemeBaseChange S} (f : T ⟶ U) [Flat f.left] (x : T.left) :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (f.left.stalkMap x).hom) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (Flat.stalkMap f.left x)

/-- The stalkwise model for pullback along a flat scheme morphism preserves
finite limits. -/
theorem flatPullbackStalkModel_preservesFiniteLimits
    {T U : SchemeBaseChange S} (f : T ⟶ U) [Flat f.left] (x : T.left) :
    PreservesFiniteLimits
      (Scheme.Modules.moduleStalkFunctor U.left (f.left x) ⋙
        ModuleCat.extendScalars.{u, u, u} (f.left.stalkMap x).hom) := by
  have hStalk : PreservesFiniteLimits
      (Scheme.Modules.moduleStalkFunctor U.left (f.left x)) :=
    Scheme.Modules.moduleStalkFunctor_preservesFiniteLimits U.left (f.left x)
  have hScalars : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (f.left.stalkMap x).hom) :=
    flatStalkMap_preservesFiniteLimits f x
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hStalk hScalars

/-- Module-sheaf pullback along a flat morphism preserves finite limits. -/
theorem modulePullback_preservesFiniteLimits_of_flat
    {T U : SchemeBaseChange S} (f : T ⟶ U) [Flat f.left] :
    PreservesFiniteLimits (modulePullback f) :=
  Scheme.Modules.preservesFiniteLimits_of_stalkwise (modulePullback f) fun x ↦ by
    have hTarget : PreservesFiniteLimits
        (Scheme.Modules.moduleStalkFunctor U.left (f.left x) ⋙
          ModuleCat.extendScalars.{u, u, u} (f.left.stalkMap x).hom) :=
      flatPullbackStalkModel_preservesFiniteLimits f x
    exact @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (Scheme.Modules.pullbackStalkIso f.left x).symm hTarget

/-- Pullback along a flat morphism of scheme base changes is exact. -/
theorem isExactPullback_of_flat
    {T U : SchemeBaseChange S} (f : T ⟶ U) [Flat f.left] :
    IsExactPullback f := by
  letI : PreservesFiniteLimits (modulePullback f) :=
    modulePullback_preservesFiniteLimits_of_flat f
  exact IsExactPullback.of_preservesFiniteLimits f

/-- Exact pullback along flat morphisms is available to the derived pullback
API without a caller-supplied exactness instance. -/
instance (priority := 800) isExactPullbackOfFlat
    {T U : SchemeBaseChange S} (f : T ⟶ U) [Flat f.left] :
    IsExactPullback f :=
  isExactPullback_of_flat f

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families

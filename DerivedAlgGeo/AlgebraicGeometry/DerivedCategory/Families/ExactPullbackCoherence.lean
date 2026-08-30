/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.ExactPullback

/-!
# Coherence for exact pullback on scheme-derived fibers

Exact pullback of module sheaves is closed under identity morphisms and
composition.  This file records those instances and lifts Mathlib's coherent
identity and composition isomorphisms for module pullback to cochain
complexes.  Consequently the derived pullback functors from
`Families.ExactPullback` are available for identities and composites without
additional exactness hypotheses.

This is still a deliberately strict boundary: no identity or composition
isomorphism is asserted after localization to derived categories, no
pseudofunctor coherence is proved there, and exactness is not deduced from
flatness.  Those constructions belong to later milestones.
-/

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- Pullback along an identity morphism is exact. -/
instance isExactPullbackId (T : SchemeBaseChange S) :
    IsExactPullback (𝟙 T) where
  preservesFiniteLimits :=
    preservesFiniteLimits_of_natIso (modulePullbackId T).symm
  preservesFiniteColimits :=
    preservesFiniteColimits_of_natIso (modulePullbackId T).symm

/-- A composite of exact pullbacks is exact. -/
instance isExactPullbackComp {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V) [IsExactPullback f] [IsExactPullback g] :
    IsExactPullback (f ≫ g) where
  preservesFiniteLimits := by
    letI := comp_preservesFiniteLimits (modulePullback g) (modulePullback f)
    exact preservesFiniteLimits_of_natIso (modulePullbackComp f g)
  preservesFiniteColimits := by
    letI := comp_preservesFiniteColimits (modulePullback g) (modulePullback f)
    exact preservesFiniteColimits_of_natIso (modulePullbackComp f g)

/-- Degreewise pullback along an identity is naturally isomorphic to the
identity functor on cochain complexes. -/
def complexPullbackId (T : SchemeBaseChange S) :
    complexPullback (𝟙 T) ≅ 𝟭 (CochainComplex T.left.Modules ℤ) :=
  NatIso.mapHomologicalComplex (modulePullbackId T) (ComplexShape.up ℤ) ≪≫
    CategoryTheory.Functor.mapHomologicalComplexIdIso T.left.Modules (ComplexShape.up ℤ)

/-- Degreewise pullback along a composite is naturally isomorphic to the
composite of the two degreewise pullbacks. -/
def complexPullbackComp {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V) :
    complexPullback g ⋙ complexPullback f ≅ complexPullback (f ≫ g) :=
  CategoryTheory.Functor.mapHomologicalComplexCompIso (modulePullbackComp f g)
    (ComplexShape.up ℤ)

/-- The derived pullback functor attached to an identity morphism. -/
abbrev identityDerivedPullback (T : SchemeBaseChange S) :
    T.DerivedFiber ⥤ T.DerivedFiber :=
  derivedPullback (𝟙 T)

/-- The derived pullback functor attached to a composite of exact pullbacks. -/
abbrev compositeDerivedPullback {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V) [IsExactPullback f] [IsExactPullback g] :
    V.DerivedFiber ⥤ T.DerivedFiber :=
  derivedPullback (f ≫ g)

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.SchemeDerived

/-!
# Exact pullback on scheme-derived fibers

Mathlib constructs an additive pullback functor on sheaves of modules for
every scheme morphism, together with coherent identity and composition
isomorphisms.  This file exposes that functor for morphisms between scheme
base changes and lifts it to the concrete derived categories from
`Families.SchemeDerived` when the pullback functor is exact.

Exactness is an explicit hypothesis.  In particular, this file does not
assert that pullback along an arbitrary scheme morphism is exact, prove the
hypothesis from flatness, construct a left-derived functor for a nonexact
pullback, or supply pseudofunctor coherence after passage to derived
categories.  It also asserts no geometric slicing, relative HN, openness,
boundedness, moduli, or Theorem 22.2 conclusion.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- Pullback of sheaves of modules along a morphism of scheme base changes. -/
abbrev modulePullback {T U : SchemeBaseChange S} (f : T ⟶ U) :
    U.left.Modules ⥤ T.left.Modules :=
  Scheme.Modules.pullback f.left

/-- Module pullback along the identity is naturally isomorphic to the
identity functor. -/
def modulePullbackId (T : SchemeBaseChange S) :
    modulePullback (𝟙 T) ≅ 𝟭 T.left.Modules :=
  Scheme.Modules.pullbackId T.left

/-- Module pullback along a composite is the composite of the pullbacks. -/
def modulePullbackComp {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V) :
    modulePullback g ⋙ modulePullback f ≅ modulePullback (f ≫ g) :=
  Scheme.Modules.pullbackComp f.left g.left

/-- Degreewise pullback of cochain complexes of module sheaves. -/
abbrev complexPullback {T U : SchemeBaseChange S} (f : T ⟶ U) :
    CochainComplex U.left.Modules ℤ ⥤ CochainComplex T.left.Modules ℤ :=
  (modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The explicit exactness requirement under which ordinary module pullback
descends to the derived categories by mapping complexes degreewise. -/
class IsExactPullback {T U : SchemeBaseChange S} (f : T ⟶ U) : Prop where
  /-- Pullback preserves finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits (modulePullback f)
  /-- Pullback preserves finite colimits. -/
  preservesFiniteColimits : PreservesFiniteColimits (modulePullback f)

attribute [instance] IsExactPullback.preservesFiniteLimits
  IsExactPullback.preservesFiniteColimits

/-- Module-sheaf pullback preserves finite colimits for every scheme
morphism, because it is left adjoint to module-sheaf pushforward. -/
theorem modulePullback_preservesFiniteColimits
    {T U : SchemeBaseChange S} (f : T ⟶ U) :
    PreservesFiniteColimits (modulePullback f) :=
  inferInstance

/-- Construct exact module-sheaf pullback from the only nonautomatic
obligation: preservation of finite limits. -/
theorem IsExactPullback.of_preservesFiniteLimits
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [PreservesFiniteLimits (modulePullback f)] : IsExactPullback f where
  preservesFiniteLimits := inferInstance
  preservesFiniteColimits := modulePullback_preservesFiniteColimits f

/-- Exactness of module-sheaf pullback is equivalent to preservation of
finite limits; finite-colimit preservation is automatic. -/
theorem isExactPullback_iff_preservesFiniteLimits
    {T U : SchemeBaseChange S} (f : T ⟶ U) :
    IsExactPullback f ↔ PreservesFiniteLimits (modulePullback f) := by
  constructor
  · exact fun h ↦ h.preservesFiniteLimits
  · exact fun _ ↦ IsExactPullback.of_preservesFiniteLimits f

/-- The triangulated pullback functor between concrete scheme-derived fibers,
defined when module pullback is exact. -/
def derivedPullback {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsExactPullback f] : U.DerivedFiber ⥤ T.DerivedFiber :=
  (modulePullback f).mapDerivedCategory

/-- The derived pullback is induced by degreewise pullback of cochain
complexes and the two localization functors. -/
def derivedPullbackFactors {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsExactPullback f] :
    SchemeDerivedCategory.Q U.left ⋙ derivedPullback f ≅
      complexPullback f ⋙ SchemeDerivedCategory.Q T.left :=
  (modulePullback f).mapDerivedCategoryFactors

instance {T U : SchemeBaseChange S} (f : T ⟶ U) [IsExactPullback f] :
    (derivedPullback f).CommShift ℤ := by
  dsimp [derivedPullback]
  exact CategoryTheory.Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt
    (modulePullback f)

instance {T U : SchemeBaseChange S} (f : T ⟶ U) [IsExactPullback f] :
    (derivedPullback f).IsTriangulated := by
  dsimp [derivedPullback]
  exact CategoryTheory.Functor.instIsTriangulatedDerivedCategoryMapDerivedCategory
    (modulePullback f)

/-- Pullback on the triangulated Grothendieck groups of the concrete derived
fibers. -/
def derivedPullK₀ {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsExactPullback f] : K₀ U.DerivedFiber →+ K₀ T.DerivedFiber :=
  K₀.map (derivedPullback f)

theorem derivedPullK₀_of {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsExactPullback f] (E : U.DerivedFiber) :
    derivedPullK₀ f (K₀.of _ E) = K₀.of _ ((derivedPullback f).obj E) := by
  simp [derivedPullK₀]

/-- Exact pullback from a scheme base change to its residue-field derived
fiber.  Exactness of this particular module pullback remains explicit. -/
abbrev derivedPullToResidue (T : SchemeBaseChange S) (x : T.left)
    [IsExactPullback (T.residueTo x)] :
    T.DerivedFiber ⥤ T.ResidueDerivedFiber x :=
  derivedPullback (T.residueTo x)

/-- Exact pullback on Grothendieck groups from a scheme base change to its
residue-field derived fiber. -/
abbrev derivedPullK₀ToResidue (T : SchemeBaseChange S) (x : T.left)
    [IsExactPullback (T.residueTo x)] :
    K₀ T.DerivedFiber →+ K₀ (T.ResidueDerivedFiber x) :=
  derivedPullK₀ (T.residueTo x)

theorem derivedPullK₀ToResidue_of (T : SchemeBaseChange S) (x : T.left)
    [IsExactPullback (T.residueTo x)] (E : T.DerivedFiber) :
    T.derivedPullK₀ToResidue x (K₀.of _ E) =
      K₀.of _ ((T.derivedPullToResidue x).obj E) :=
  derivedPullK₀_of (T.residueTo x) E

end SchemeBaseChange

end


end AlgebraicGeometry.DerivedCategory.Families

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.ExactPullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion

/-!
# Right-derived pushforward along scheme morphisms

Ordinary pushforward of module sheaves is left exact, so applying it degreewise does not in
general define a functor on derived categories. `RightDerivedPushforward` records an actual
functor, its comparison with degreewise pushforward, and Mathlib's right-derived universal
property. Thus later base-change constructions can accept the genuinely derived operation without
postulating an unrelated functor.

When module-sheaf pushforward is exact, its degreewise derived functor inhabits the interface.
Closed immersions provide a concrete geometric instance of this normalization.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}} {T U : SchemeBaseChange S}

/-- Degreewise pushforward of cochain complexes of module sheaves. -/
abbrev complexPushforward (f : T ⟶ U) :
    CochainComplex T.left.Modules ℤ ⥤ CochainComplex U.left.Modules ℤ :=
  (modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The exactness condition under which module-sheaf pushforward derives degreewise. -/
class IsExactPushforward (f : T ⟶ U) : Prop where
  /-- Pushforward preserves finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits (modulePushforward f)
  /-- Pushforward preserves finite colimits. -/
  preservesFiniteColimits : PreservesFiniteColimits (modulePushforward f)

attribute [instance] IsExactPushforward.preservesFiniteLimits
  IsExactPushforward.preservesFiniteColimits

/-- Module-sheaf pushforward preserves finite limits for every scheme morphism because it is a
right adjoint. -/
theorem modulePushforward_preservesFiniteLimits (f : T ⟶ U) :
    PreservesFiniteLimits (modulePushforward f) :=
  inferInstance

/-- Construct exact pushforward from its only nonautomatic obligation. -/
theorem IsExactPushforward.of_preservesFiniteColimits (f : T ⟶ U)
    [PreservesFiniteColimits (modulePushforward f)] : IsExactPushforward f where
  preservesFiniteLimits := modulePushforward_preservesFiniteLimits f
  preservesFiniteColimits := inferInstance

/-- Pushforward along a closed immersion is exact. -/
noncomputable instance isExactPushforward_of_isClosedImmersion (f : T ⟶ U)
    [IsClosedImmersion f.left] : IsExactPushforward f :=
  IsExactPushforward.of_preservesFiniteColimits f

/-- Degreewise derived pushforward when module-sheaf pushforward is exact. -/
def derivedPushforward (f : T ⟶ U) [IsExactPushforward f] :
    T.DerivedFiber ⥤ U.DerivedFiber :=
  (modulePushforward f).mapDerivedCategory

/-- Exact derived pushforward is induced by degreewise pushforward before localization. -/
def derivedPushforwardFactors (f : T ⟶ U) [IsExactPushforward f] :
    SchemeDerivedCategory.Q T.left ⋙ derivedPushforward f ≅
      complexPushforward f ⋙ SchemeDerivedCategory.Q U.left :=
  (modulePushforward f).mapDerivedCategoryFactors

instance (f : T ⟶ U) [IsExactPushforward f] :
    (derivedPushforward f).CommShift ℤ := by
  dsimp [derivedPushforward]
  exact CategoryTheory.Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt
    (modulePushforward f)

instance (f : T ⟶ U) [IsExactPushforward f] :
    (derivedPushforward f).IsTriangulated := by
  dsimp [derivedPushforward]
  exact CategoryTheory.Functor.instIsTriangulatedDerivedCategoryMapDerivedCategory
    (modulePushforward f)

/-- An actual right-derived pushforward along an arbitrary scheme base-change morphism. -/
structure RightDerivedPushforward (f : T ⟶ U) where
  /-- The functor on unbounded derived categories of module sheaves. -/
  functor : T.DerivedFiber ⥤ U.DerivedFiber
  /-- Comparison from degreewise pushforward to the derived functor after localization. -/
  unit : complexPushforward f ⋙ SchemeDerivedCategory.Q U.left ⟶
    SchemeDerivedCategory.Q T.left ⋙ functor
  /-- The comparison exhibits `functor` as the right-derived pushforward. -/
  isRightDerived : functor.IsRightDerivedFunctor unit
    (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))

namespace RightDerivedPushforward

variable {f : T ⟶ U}

attribute [instance] isRightDerived

/-- Exact derived pushforward satisfies the arbitrary right-derived interface. -/
def ofExact (f : T ⟶ U) [IsExactPushforward f] : RightDerivedPushforward f where
  functor := derivedPushforward f
  unit := (derivedPushforwardFactors f).inv
  isRightDerived := CategoryTheory.Functor.isRightDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
    (derivedPushforward f) (derivedPushforwardFactors f)

/-- Right-derived pushforward along the identity. -/
def identity (T : SchemeBaseChange S) : RightDerivedPushforward (𝟙 T) :=
  ofExact (𝟙 T)

/-- Every right-derived pushforward agrees canonically with degreewise derived pushforward when
ordinary pushforward is exact. -/
def exactComparison (P : RightDerivedPushforward f) [IsExactPushforward f] :
    P.functor ≅ derivedPushforward f := by
  let E := ofExact f
  letI := P.isRightDerived
  letI := E.isRightDerived
  exact CategoryTheory.Functor.rightDerivedUnique P.functor E.functor P.unit E.unit
    (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))

/-- Transport right-derived pushforward data along equality of the underlying morphisms. -/
def congr {g : T ⟶ U} (P : RightDerivedPushforward f) (h : f = g) :
    RightDerivedPushforward g := by
  subst g
  exact P

end RightDerivedPushforward

end SchemeBaseChange

end


end AlgebraicGeometry.DerivedCategory.Families

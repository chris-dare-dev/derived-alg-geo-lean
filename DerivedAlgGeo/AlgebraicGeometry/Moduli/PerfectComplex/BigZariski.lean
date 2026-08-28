/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Presheaf
import DerivedAlgGeo.CategoryTheory.Sites.StackInGroupoids

/-!
# The relative-perfect presheaf on the big Zariski site over a base

This file places the universally-gluable relative-perfect moduli problem on
the correctly oriented site `Over S` with the topology
`Scheme.zariskiTopology.over S`. Its transition data uses actual
left-derived pullback and an actual lift to the universally-gluable
relative-perfect loci.

`RelativePerfectBigZariskiStack` adds Mathlib's effective descent condition.
It is intentionally a structure rather than a theorem: constructing its
`isStack` field requires effective descent for the complexes and their
isomorphisms. Once supplied, the existing stack infrastructure immediately
gives fully faithful morphism descent and effective object descent for every
big-Zariski covering family.

## Main definitions

- `RelativePerfectBigZariskiPresheaf`: the concrete relative-perfect
  pseudofunctor on `Over S`.
- `RelativePerfectBigZariskiStack`: the same pseudofunctor with effective
  big-Zariski descent.
- `RelativePerfectBigZariskiStack.cechDescentEquivalence`: the resulting
  equivalence with Čech descent data.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Bicategory
open CategoryTheory.Triangulated.StabilityCondition.Families
open Opposite

noncomputable section

universe u

/-- The universally-gluable relative-perfect moduli presheaf on the big
Zariski site of schemes over `S`.

Every transition contains an actual left-derived pullback and an actual lift
to the relative-perfect locus. The final comparison identifies that lifted
pullback with the pseudofunctor transition. -/
structure RelativePerfectBigZariskiPresheaf (S : Scheme.{u}) where
  /-- The contravariant groupoid-valued pseudofunctor on schemes over `S`. -/
  presheaf : Pseudofunctor
    (LocallyDiscrete (SchemeBaseChange S)ᵒᵖ) Cat.{u + 1, u + 1}
  /-- Identification of every fiber with the concrete core of
  universally-gluable relative-perfect complexes. -/
  fiberEquivalence (T : SchemeBaseChange S) :
    presheaf.obj (.mk (op T)) ≌ RelativePerfectModuliFiber T
  /-- The actual lifted left-derived pullback attached to every morphism of
  schemes over `S`. -/
  pullback {T U : SchemeBaseChange S} (f : T ⟶ U) :
    RelativePerfectPullback f
  /-- The concrete lifted pullback agrees with the pseudofunctor
  transition. -/
  transitionComparison {T U : SchemeBaseChange S} (f : T ⟶ U) :
    (fiberEquivalence U).functor ⋙ (pullback f).coreFunctor ≅
      (presheaf.map f.op.toLoc).toFunctor ⋙ (fiberEquivalence T).functor

namespace RelativePerfectBigZariskiPresheaf

variable {S : Scheme.{u}}

/-- Every fiber of the big-Zariski relative-perfect presheaf is a groupoid. -/
instance fiber_isGroupoid (M : RelativePerfectBigZariskiPresheaf S)
    (T : LocallyDiscrete (SchemeBaseChange S)ᵒᵖ) :
    IsGroupoid (M.presheaf.obj T) :=
  isGroupoid_of_reflects_iso (M.fiberEquivalence T.as.unop).functor

/-- After forgetting to the ambient derived categories, a pseudofunctor
transition is the stored arbitrary left-derived pullback. -/
def ambientComparison (M : RelativePerfectBigZariskiPresheaf S)
    {T U : SchemeBaseChange S} (f : T ⟶ U) :
    (M.fiberEquivalence U).functor ⋙ relativePerfectModuliForget U ⋙
        (M.pullback f).ambient.functor ≅
      (M.presheaf.map f.op.toLoc).toFunctor ⋙
        (M.fiberEquivalence T).functor ⋙ relativePerfectModuliForget T :=
  Functor.associator (M.fiberEquivalence U).functor
      (relativePerfectModuliForget U) (M.pullback f).ambient.functor ≪≫
    Functor.isoWhiskerLeft (M.fiberEquivalence U).functor
      (M.pullback f).coreComparison.symm ≪≫
    (Functor.associator (M.fiberEquivalence U).functor
      (M.pullback f).coreFunctor (relativePerfectModuliForget T)).symm ≪≫
    Functor.isoWhiskerRight (M.transitionComparison f)
      (relativePerfectModuliForget T)

/-- On an exact arrow, the ambient transition is the repository's exact
derived pullback. -/
def exactAmbientComparison (M : RelativePerfectBigZariskiPresheaf S)
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [SchemeBaseChange.IsExactPullback f] :
    (M.fiberEquivalence U).functor ⋙ relativePerfectModuliForget U ⋙
        SchemeBaseChange.derivedPullback f ≅
      (M.presheaf.map f.op.toLoc).toFunctor ⋙
        (M.fiberEquivalence T).functor ⋙ relativePerfectModuliForget T :=
  Functor.associator (M.fiberEquivalence U).functor
      (relativePerfectModuliForget U)
      (SchemeBaseChange.derivedPullback f) ≪≫
    Functor.isoWhiskerLeft (M.fiberEquivalence U).functor
      (Functor.isoWhiskerLeft (relativePerfectModuliForget U)
        (M.pullback f).ambient.exactComparison.symm) ≪≫
    (Functor.associator (M.fiberEquivalence U).functor
      (relativePerfectModuliForget U) (M.pullback f).ambient.functor).symm ≪≫
    M.ambientComparison f

end RelativePerfectBigZariskiPresheaf

/-- A universally-gluable relative-perfect presheaf with effective descent
for the big Zariski topology over `S`. -/
structure RelativePerfectBigZariskiStack (S : Scheme.{u}) extends
    RelativePerfectBigZariskiPresheaf S where
  /-- Effective descent for objects and morphisms. -/
  isStack : toRelativePerfectBigZariskiPresheaf.presheaf.IsStack
    (Scheme.zariskiTopology.over S)

namespace RelativePerfectBigZariskiStack

variable {S : Scheme.{u}}

/-- The stack in groupoids underlying a relative-perfect big-Zariski stack. -/
def toStackInGroupoids (M : RelativePerfectBigZariskiStack S) :
    StackInGroupoids (SchemeBaseChange S) (Scheme.zariskiTopology.over S) where
  presheaf := M.presheaf
  fiberIsGroupoid := M.fiber_isGroupoid
  isStack := M.isStack

/-- Effective Čech descent for every big-Zariski cover over `S`. -/
def cechDescentEquivalence (M : RelativePerfectBigZariskiStack S)
    {T : SchemeBaseChange S}
    (U : StackInGroupoids.Cover (J := Scheme.zariskiTopology.over S) T) :=
  M.toStackInGroupoids.cechDescentEquivalence U

/-- Morphisms of relative-perfect complexes satisfy descent along every
big-Zariski cover over `S`. -/
def fullyFaithfulToCechDescent (M : RelativePerfectBigZariskiStack S)
    {T : SchemeBaseChange S}
    (U : StackInGroupoids.Cover (J := Scheme.zariskiTopology.over S) T) :=
  M.toStackInGroupoids.fullyFaithfulToCechDescent U

/-- Every compatible big-Zariski descent object is effective. -/
theorem essSurjToCechDescent (M : RelativePerfectBigZariskiStack S)
    {T : SchemeBaseChange S}
    (U : StackInGroupoids.Cover (J := Scheme.zariskiTopology.over S) T) :
    (M.toStackInGroupoids.toCechDescent U).EssSurj :=
  M.toStackInGroupoids.essSurjToCechDescent U

end RelativePerfectBigZariskiStack

end

end AlgebraicGeometry

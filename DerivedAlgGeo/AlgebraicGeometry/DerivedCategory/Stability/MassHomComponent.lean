/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.MassHom
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Algebraic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.FiniteDistance

/-!
# Mass--Hom bounds on the distinguished component

The statement layer of Theorem 7.5 of arXiv:2607.28411v1: a stability
condition in the distinguished connected component of `Stab(Dᵇ(Coh X))` has a
perfect mass--Hom bound. The algebraic base case, the pushforward and pullback
transfers, and connected-component invariance are proved elsewhere; this file
assembles them.

## Main definitions

* `DistinguishedComponentInhabitant` — a stability condition with a perfect
  mass--Hom bound, together with membership of the target in its connected
  component.
* `DistinguishedComponentInhabitant.ofAlgebraicTransferChain` — that
  inhabitant, from the algebraic seed and the two transfers once their
  geometric data are provided.

## Main results

* `hasPerfectMassHomBound_of_distinguishedComponentInhabitant` — Theorem 7.5,
  given an inhabitant.
* `hasPerfectMassHomBound_autPair_act_iff` — Remark 1.4: the bound is
  invariant under a compatible derived autoequivalence that preserves the
  perfect test class.

## Implementation notes

The distinguished stability condition on an arbitrary projective scheme is not
constructed here, so its existence enters as `DistinguishedComponentInhabitant`
and Theorem 7.5 is formal given one. No projectivity, ampleness, adjunction, or
generation assertion is manufactured: the lower-shriek and finite-pullback
functors remain explicit inputs, as in Lemma 7.4.

## References

* arXiv:2607.28411v1, Remark 1.4, Lemma 7.4 and Theorem 7.5.

## Tags

stability condition, mass--Hom bound, connected component, autoequivalence
-/

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.SerreFunctor
open AlgebraicGeometry AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
open scoped Topology

namespace AlgebraicGeometry.DerivedCategory

noncomputable section

universe w u u'

/-- A point of the distinguished connected component with a perfect mass--Hom
bound: the input from which Theorem 7.5 is formal. -/
structure DistinguishedComponentInhabitant
    (k : Type w) [Field k]
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    [Linear k (SchemeBoundedCoherentDerivedCategory X)]
    [HomFinite k (SchemeBoundedCoherentDerivedCategory X)]
    {Λ : Type u'} [AddCommGroup Λ]
    {v : K₀ (SchemeBoundedCoherentDerivedCategory X) →+ Λ}
    (σ : StabilityCondition.WithClassMap
      (SchemeBoundedCoherentDerivedCategory X) v) where
  /-- The constructed base point of the distinguished component. -/
  base : StabilityCondition.WithClassMap
    (SchemeBoundedCoherentDerivedCategory X) v
  /-- The base point has the bound supplied by the algebraic seed and the two
  transfer steps. -/
  base_hasPerfectMassHomBound : HasPerfectMassHomBound (k := k) X base
  /-- The target lies in the connected component selected by that base
  point. -/
  target_mem_connectedComponent : σ ∈ connectedComponent base

/-- Assemble the inhabitant from the proof chain of Theorem 7.5:
an algebraic seed, the flat pushforward step, the finite pullback step, and
membership in the resulting connected component.

The functors, adjunctions, preimage data, and generation containments are
exactly the open geometric inputs of the two Lemma 7.4 adapters. -/
noncomputable def DistinguishedComponentInhabitant.ofAlgebraicTransferChain
    {S : Scheme.{u}} {T U X : SchemeBaseChange S}
    (f : T ⟶ U) (i : X ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [IsLocallyNoetherian X.left]
    [Flat f.left] [IsFinite i.left]
    {k : Type w} [Field k]
    [Linear k T.BoundedCoherentDerivedFiber]
    [Linear k U.BoundedCoherentDerivedFiber]
    [Linear k X.BoundedCoherentDerivedFiber]
    [∀ n : ℤ, (shiftFunctor U.BoundedCoherentDerivedFiber n).Linear k]
    [∀ n : ℤ, (shiftFunctor X.BoundedCoherentDerivedFiber n).Linear k]
    [HomFinite k T.BoundedCoherentDerivedFiber]
    [HomFinite k U.BoundedCoherentDerivedFiber]
    [HomFinite k X.BoundedCoherentDerivedFiber]
    [HomFiniteBounded k T.BoundedCoherentDerivedFiber]
    {Λ : Type u'} [AddCommGroup Λ]
    {vT : K₀ T.BoundedCoherentDerivedFiber →+ Λ}
    (σT : StabilityCondition.WithClassMap T.BoundedCoherentDerivedFiber vT)
    (hσT : σT.IsAlgebraic)
    (hpush : BoundedCoherentPullbackPreimageData f σT.slicing)
    (lowerShriek : T.BoundedCoherentDerivedFiber ⥤
      U.BoundedCoherentDerivedFiber)
    [lowerShriek.Additive] [lowerShriek.Linear k]
    (lowerShriekAdjunction : lowerShriek ⊣ boundedCoherentDerivedPullback f)
    (hpushGenerates : boundedSchemePerfect U.left ≤
      ((boundedSchemePerfect T.left).map lowerShriek).triangEnvelope)
    (hpull : BoundedCoherentPushforwardPreimageData i
      (σT.boundedCoherentPushforward f hpush).slicing)
    (pull : U.BoundedCoherentDerivedFiber ⥤ X.BoundedCoherentDerivedFiber)
    [pull.Additive] [pull.Linear k]
    (pullAdjunction : pull ⊣ boundedCoherentDerivedPushforward i)
    (hpullGenerates : boundedSchemePerfect X.left ≤
      ((boundedSchemePerfect U.left).map pull).triangEnvelope)
    (σX : StabilityCondition.WithClassMap X.BoundedCoherentDerivedFiber
      ((vT.comp (K₀.map (boundedCoherentDerivedPullback f))).comp
        (K₀.map (boundedCoherentDerivedPushforward i))))
    (hcomponent : σX ∈ connectedComponent
      ((σT.boundedCoherentPushforward f hpush).boundedCoherentPullback i hpull)) :
    DistinguishedComponentInhabitant k X.left σX := by
  have hTglobal : σT.HasGlobalMassHomBound (k := k) :=
    hσT.hasGlobalMassHomBound
  have hTperfect : HasPerfectMassHomBound (k := k) T.left σT := by
    exact hTglobal.anti (by intro E hE; trivial)
  have hUperfect : HasPerfectMassHomBound (k := k) U.left
      (σT.boundedCoherentPushforward f hpush) :=
    hasPerfectMassHomBound_flatPushforward f σT hTperfect hpush
      lowerShriek lowerShriekAdjunction hpushGenerates
  have hXperfect : HasPerfectMassHomBound (k := k) X.left
      ((σT.boundedCoherentPushforward f hpush).boundedCoherentPullback i hpull) :=
    hasPerfectMassHomBound_finitePullback i
      (σT.boundedCoherentPushforward f hpush) hUperfect hpull
      pull pullAdjunction hpullGenerates
  exact ⟨_, hXperfect, hcomponent⟩

/-- Theorem 7.5: a stability condition in the distinguished component has a
perfect mass--Hom bound, given an inhabitant of that component. -/
theorem hasPerfectMassHomBound_of_distinguishedComponentInhabitant
    {k : Type w} [Field k]
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    [Linear k (SchemeBoundedCoherentDerivedCategory X)]
    [HomFinite k (SchemeBoundedCoherentDerivedCategory X)]
    {Λ : Type u'} [AddCommGroup Λ]
    {v : K₀ (SchemeBoundedCoherentDerivedCategory X) →+ Λ}
    (σ : StabilityCondition.WithClassMap
      (SchemeBoundedCoherentDerivedCategory X) v)
    (h : DistinguishedComponentInhabitant k X σ) :
    HasPerfectMassHomBound (k := k) X σ :=
  h.base_hasPerfectMassHomBound.of_mem_connectedComponent
    h.target_mem_connectedComponent

open WeakStabilityCondition.StabilityCondition.GroupAction in
/-- Remark 1.4: the perfect mass--Hom bound is invariant under a compatible
derived autoequivalence which preserves the perfect test class. -/
theorem hasPerfectMassHomBound_autPair_act_iff
    {k : Type w} [Field k]
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    [Linear k (SchemeBoundedCoherentDerivedCategory X)]
    [HomFinite k (SchemeBoundedCoherentDerivedCategory X)]
    {Λ : Type u'} [AddCommGroup Λ]
    {v : K₀ (SchemeBoundedCoherentDerivedCategory X) →+ Λ}
    (σ : StabilityCondition.WithClassMap
      (SchemeBoundedCoherentDerivedCategory X) v)
    (a : AutPair v)
    [a.Φ.e.functor.Linear k] [a.Φ.e.inverse.Linear k]
    (hperfect : boundedSchemePerfect X =
      (boundedSchemePerfect X).inverseImage a.Φ.e.inverse) :
    HasPerfectMassHomBound (k := k) X (a.act σ) ↔
      HasPerfectMassHomBound (k := k) X σ := by
  letI : (boundedSchemePerfect X).IsClosedUnderIsomorphisms := by
    dsimp [boundedSchemePerfect, schemePerfect]
    infer_instance
  constructor
  · intro hacted
    have hacted' : (a.act σ).HasMassHomBound (k := k)
        ((boundedSchemePerfect X).inverseImage a.Φ.e.inverse) := by
      simpa only [← hperfect] using hacted
    exact (StabilityCondition.WithClassMap.HasMassHomBound.autPair_act_iff
      (σ := σ) (T := boundedSchemePerfect X) a).1 hacted'
  · intro hσ
    have hacted :=
      StabilityCondition.WithClassMap.HasMassHomBound.autPair_act
        (σ := σ) (T := boundedSchemePerfect X) a hσ
    simpa only [← hperfect] using hacted

end

end AlgebraicGeometry.DerivedCategory

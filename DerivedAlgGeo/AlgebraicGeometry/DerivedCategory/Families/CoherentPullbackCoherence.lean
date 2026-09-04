/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.PerfectPullback

/-!
# Identity and composition for coherent derived pullback

The contract `HasCoherentPullback` determines its functors up to isomorphism: the comparison
isomorphism reads the sheaf-level pullback as module-sheaf pullback, and `derivedFactors`
reads the derived pullback as degreewise sheaf-level pullback on complexes.  So the identity
and composition laws of the coherent, bounded coherent, and perfect derived pullbacks are
theorems about every instance of the contract, the mirror image of
`Families/CoherentPushforwardCoherence.lean`.

## Main definitions

* `SchemeBaseChange.HasCoherentPullback.sheafPullbackId` and `sheafPullbackComp`: on `Coh`,
  from the comparison isomorphisms and `modulePullbackId`/`modulePullbackComp`, lifted through
  the fully faithful `Coh.ι`.
* `SchemeBaseChange.coherentDerivedPullbackId` and `coherentDerivedPullbackComp`: on
  `D(Coh)`, by the universal property of the localization at the contract's factorization.
* `SchemeBaseChange.boundedCoherentDerivedPullbackId` and `boundedCoherentDerivedPullbackComp`:
  on `Dᵇ(Coh)`, lifted through the fully faithful `DerivedCategory.Bounded.ι`.
* `SchemeBaseChange.perfectDerivedPullbackId` and `perfectDerivedPullbackComp`: on `Perf`,
  lifted through the fully faithful `(schemePerfect _).ι`.

## Implementation notes

The derived pullback of the contract is data, not `Functor.mapDerivedCategory` of the sheaf
pullback, so the derived laws cannot come from `NatIso.mapDerivedCategory` as on the
pushforward side.  They come from `Localization.liftNatIso` with the `Lifting` instances that
the factorization supplies, packaged as `DerivedCategory.isoOfFactors`,
`DerivedCategory.idFactors`, and `DerivedCategory.compFactors` in
`Algebra/Homology/DerivedCategory/ExactFunctor.lean`.  Each lift through a fully faithful
functor is `Functor.fullyFaithfulCancelRight`, applied to an isomorphism assembled from the
inclusion comparisons and associators; nothing is computed on sections or on complexes.  The
direction convention is that of `modulePullbackComp`:
`pullback g ⋙ pullback f ≅ pullback (f ≫ g)`.

The consumer is `Stability/BoundedCoherentBaseChange.lean`, where these give the identity and
composition laws of the `f^♯` witnesses.  The triangle and pentagon coherence equations
between the isomorphisms are not stated, as on the pushforward side.

## References

* arXiv:2607.28411v1, Proposition 3.8 and the pseudofunctoriality it uses implicitly;
  arXiv:2601.22994, Definition 3.1.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

section Sheaf

/-- Coherent pullback along an identity is the identity, for every instance of the contract:
the comparison isomorphism reads it as module-sheaf pullback along `𝟙`, which is
`modulePullbackId`, and the fully faithful `Coh.ι` cancels. -/
def HasCoherentPullback.sheafPullbackId (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] [HasCoherentPullback (𝟙 T)] :
    HasCoherentPullback.sheafPullback (𝟙 T) ≅ 𝟭 (Coh T.left) :=
  Functor.fullyFaithfulCancelRight (Coh.ι T.left)
    (HasCoherentPullback.comparison (f := 𝟙 T) ≪≫
      Functor.isoWhiskerLeft (Coh.ι T.left) (modulePullbackId T) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The composite of two coherent pullbacks is the coherent pullback along the composite, for
every instance of the contract: three comparison isomorphisms and `modulePullbackComp`
identify both sides after `Coh.ι`, which cancels. -/
def HasCoherentPullback.sheafPullbackComp {T U V : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]
    [HasCoherentPullback f] [HasCoherentPullback g] [HasCoherentPullback (f ≫ g)] :
    HasCoherentPullback.sheafPullback g ⋙ HasCoherentPullback.sheafPullback f ≅
      HasCoherentPullback.sheafPullback (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (Coh.ι T.left)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (HasCoherentPullback.sheafPullback g)
        (HasCoherentPullback.comparison (f := f)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (HasCoherentPullback.comparison (f := g)) (modulePullback f) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Coh.ι V.left) (modulePullbackComp f g) ≪≫
      (HasCoherentPullback.comparison (f := f ≫ g)).symm)

end Sheaf

section Derived

/-- The coherent derived pullback along an identity is the identity: `derivedFactors` writes
it as degreewise `sheafPullback (𝟙 T)`, `DerivedCategory.idFactors` writes `𝟭` as degreewise
`𝟭 (Coh T.left)`, and `sheafPullbackId` identifies the two sheaf-level functors, so
`DerivedCategory.isoOfFactors` applies. -/
def coherentDerivedPullbackId (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] [HasCoherentPullback (𝟙 T)] :
    coherentDerivedPullback (𝟙 T) ≅ 𝟭 (SchemeCoherentDerivedCategory T.left) :=
  DerivedCategory.isoOfFactors (HasCoherentPullback.derivedFactors (f := 𝟙 T))
    (DerivedCategory.idFactors (Coh T.left)) (HasCoherentPullback.sheafPullbackId T)

/-- The composite of two coherent derived pullbacks is the coherent derived pullback along the
composite: the composite factors degreewise through the composite of the sheaf-level
pullbacks, and `sheafPullbackComp` identifies that with the sheaf-level pullback along
`f ≫ g`. -/
def coherentDerivedPullbackComp {T U V : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]
    [HasCoherentPullback f] [HasCoherentPullback g] [HasCoherentPullback (f ≫ g)] :
    coherentDerivedPullback g ⋙ coherentDerivedPullback f ≅ coherentDerivedPullback (f ≫ g) :=
  DerivedCategory.isoOfFactors
    (DerivedCategory.compFactors (HasCoherentPullback.derivedFactors (f := g))
      (HasCoherentPullback.derivedFactors (f := f)))
    (HasCoherentPullback.derivedFactors (f := f ≫ g)) (HasCoherentPullback.sheafPullbackComp f g)

end Derived

section Bounded

/-- The bounded coherent pullback along an identity is the identity, lifted through the fully
faithful `DerivedCategory.Bounded.ι` from `coherentDerivedPullbackId`. -/
def boundedCoherentDerivedPullbackId (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] [HasCoherentPullback (𝟙 T)] :
    boundedCoherentDerivedPullback (𝟙 T) ≅ 𝟭 T.BoundedCoherentDerivedFiber :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Bounded.ι
    (boundedCoherentDerivedPullbackCompInclusion (𝟙 T) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Bounded.ι (coherentDerivedPullbackId T) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The composite of two bounded coherent pullbacks is the bounded coherent pullback along the
composite, lifted through the fully faithful `DerivedCategory.Bounded.ι` from
`coherentDerivedPullbackComp` and the three inclusion comparisons. -/
def boundedCoherentDerivedPullbackComp {T U V : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]
    [HasCoherentPullback f] [HasCoherentPullback g] [HasCoherentPullback (f ≫ g)] :
    boundedCoherentDerivedPullback g ⋙ boundedCoherentDerivedPullback f ≅
      boundedCoherentDerivedPullback (f ≫ g) :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Bounded.ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (boundedCoherentDerivedPullback g)
        (boundedCoherentDerivedPullbackCompInclusion f) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedCoherentDerivedPullbackCompInclusion g)
        (coherentDerivedPullback f) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Bounded.ι (coherentDerivedPullbackComp f g) ≪≫
      (boundedCoherentDerivedPullbackCompInclusion (f ≫ g)).symm)

end Bounded

section Perfect

/-- The perfect pullback along an identity is the identity, lifted through the fully faithful
`(schemePerfect _).ι` from `coherentDerivedPullbackId`. -/
def perfectDerivedPullbackId (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] [HasCoherentPullback (𝟙 T)] :
    perfectDerivedPullback (𝟙 T) ≅ 𝟭 T.PerfectDerivedFiber :=
  Functor.fullyFaithfulCancelRight (schemePerfect T.left).ι
    (perfectDerivedPullbackCompInclusion (𝟙 T) ≪≫
      Functor.isoWhiskerLeft (schemePerfect T.left).ι (coherentDerivedPullbackId T) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The composite of two perfect pullbacks is the perfect pullback along the composite, lifted
through the fully faithful `(schemePerfect _).ι` from `coherentDerivedPullbackComp` and the
three inclusion comparisons. -/
def perfectDerivedPullbackComp {T U V : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]
    [HasCoherentPullback f] [HasCoherentPullback g] [HasCoherentPullback (f ≫ g)] :
    perfectDerivedPullback g ⋙ perfectDerivedPullback f ≅ perfectDerivedPullback (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (schemePerfect T.left).ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (perfectDerivedPullback g) (perfectDerivedPullbackCompInclusion f) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (perfectDerivedPullbackCompInclusion g)
        (coherentDerivedPullback f) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (schemePerfect V.left).ι (coherentDerivedPullbackComp f g) ≪≫
      (perfectDerivedPullbackCompInclusion (f ≫ g)).symm)

end Perfect

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.CoherentPushforward

/-!
# Identity and composition for the bounded coherent direct image

The direct image `f_* : Dᵇ(Coh X) ⥤ Dᵇ(Coh Y)` of `Families/CoherentPushforward.lean` is
pseudofunctorial: along an identity it is the identity, and along a composite it is the
composite, up to natural isomorphism.  This file proves both for every instance of
`HasCoherentPushforward`, at the three levels the direct image is built in.

## Main definitions

* `SchemeBaseChange.HasCoherentPushforward.sheafPushforwardId` and
  `SchemeBaseChange.HasCoherentPushforward.sheafPushforwardComp`: on coherent sheaves, from
  the contract's comparison isomorphism and Mathlib's `Modules.pushforwardId` and
  `pushforwardComp`, lifted through the fully faithful `Coh.ι`.
* `SchemeBaseChange.coherentDerivedPushforwardId` and `coherentDerivedPushforwardComp`: on
  `D(Coh)`, through the pseudofunctoriality of `Functor.mapDerivedCategory`.
* `SchemeBaseChange.boundedCoherentDerivedPushforwardId` and
  `boundedCoherentDerivedPushforwardComp`: on `Dᵇ(Coh)`, lifted through the fully faithful
  `DerivedCategory.Bounded.ι`.

## Implementation notes

Unlike the pullback side, where `GeometricDerivedPullbackIdentity` and
`GeometricDerivedPullbackComposition` postulate the bounded isomorphisms as classes with no
inhabitant, nothing here is assumed: the contract's comparison isomorphism determines the
coherent pushforward up to isomorphism, so the laws are theorems about every instance.  The
consumer is `Stability/BoundedCoherentPullback.lean`, where they give the identity and
composition laws of the `f^♯` witnesses.

Each lift through a fully faithful functor is `Functor.fullyFaithfulCancelRight`, applied to
an isomorphism assembled from the comparison isomorphisms and associators; nothing is computed
on sections or on complexes.

The triangle and pentagon coherence equations between these isomorphisms are not stated, as
they are not for pullback.

## References

* arXiv:2607.28411v1, Definition 3.1; the laws are what make `(f ≫ g)^♯ = f^♯ ∘ g^♯` and
  `𝟙^♯ = 𝟙` meaningful for the pullback of stability conditions.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

section Sheaf

/-- Coherent pushforward along an identity is the identity, for every instance of the
contract: the comparison isomorphism reads it as module-sheaf pushforward along `𝟙`, which is
`Modules.pushforwardId`, and the fully faithful `Coh.ι` cancels. -/
def HasCoherentPushforward.sheafPushforwardId (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] [HasCoherentPushforward (𝟙 T)] :
    HasCoherentPushforward.sheafPushforward (𝟙 T) ≅ 𝟭 (Coh T.left) :=
  Functor.fullyFaithfulCancelRight (Coh.ι T.left)
    (HasCoherentPushforward.comparison (f := 𝟙 T) ≪≫
      Functor.isoWhiskerLeft (Coh.ι T.left) (Scheme.Modules.pushforwardId T.left) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The composite of two coherent pushforwards is the coherent pushforward along the
composite, for every instance of the contract: three comparison isomorphisms and
`Modules.pushforwardComp` identify both sides after `Coh.ι`, which cancels.  The direction is
that of `Modules.pushforwardComp`. -/
def HasCoherentPushforward.sheafPushforwardComp {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]
    [HasCoherentPushforward f] [HasCoherentPushforward g] [HasCoherentPushforward (f ≫ g)] :
    HasCoherentPushforward.sheafPushforward f ⋙ HasCoherentPushforward.sheafPushforward g ≅
      HasCoherentPushforward.sheafPushforward (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (Coh.ι V.left)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (HasCoherentPushforward.sheafPushforward f)
        (HasCoherentPushforward.comparison (f := g)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (HasCoherentPushforward.comparison (f := f))
        (modulePushforward g) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Coh.ι T.left) (Scheme.Modules.pushforwardComp f.left g.left) ≪≫
      (HasCoherentPushforward.comparison (f := f ≫ g)).symm)

end Sheaf

section Derived

/-- The derived direct image along an identity is the identity: transport
`sheafPushforwardId` through `mapDerivedCategory` and use
`Functor.mapDerivedCategoryIdIso`. -/
def coherentDerivedPushforwardId (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] [HasCoherentPushforward (𝟙 T)] :
    coherentDerivedPushforward (𝟙 T) ≅ 𝟭 (SchemeCoherentDerivedCategory T.left) :=
  NatIso.mapDerivedCategory (HasCoherentPushforward.sheafPushforwardId T) ≪≫
    Functor.mapDerivedCategoryIdIso (Coh T.left)

/-- The composite of two derived direct images is the derived direct image along the
composite: `Functor.mapDerivedCategoryCompIso` at the factorization `sheafPushforwardComp`,
which is exactly the shape of `derivedPullbackComp` on the pullback side. -/
def coherentDerivedPushforwardComp {T U V : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]
    [HasCoherentPushforward f] [HasCoherentPushforward g] [HasCoherentPushforward (f ≫ g)] :
    coherentDerivedPushforward f ⋙ coherentDerivedPushforward g ≅
      coherentDerivedPushforward (f ≫ g) :=
  Functor.mapDerivedCategoryCompIso (HasCoherentPushforward.sheafPushforwardComp f g)

end Derived

section Bounded

/-- The bounded direct image along an identity is the identity, lifted through the fully
faithful `DerivedCategory.Bounded.ι` from `coherentDerivedPushforwardId`. -/
def boundedCoherentDerivedPushforwardId (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] [HasCoherentPushforward (𝟙 T)] :
    boundedCoherentDerivedPushforward (𝟙 T) ≅ 𝟭 T.BoundedCoherentDerivedFiber :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Bounded.ι
    (boundedCoherentDerivedPushforwardCompInclusion (𝟙 T) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Bounded.ι (coherentDerivedPushforwardId T) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The composite of two bounded direct images is the bounded direct image along the
composite, lifted through the fully faithful `DerivedCategory.Bounded.ι` from
`coherentDerivedPushforwardComp` and the three inclusion comparisons. -/
def boundedCoherentDerivedPushforwardComp {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]
    [HasCoherentPushforward f] [HasCoherentPushforward g] [HasCoherentPushforward (f ≫ g)] :
    boundedCoherentDerivedPushforward f ⋙ boundedCoherentDerivedPushforward g ≅
      boundedCoherentDerivedPushforward (f ≫ g) :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Bounded.ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (boundedCoherentDerivedPushforward f)
        (boundedCoherentDerivedPushforwardCompInclusion g) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedCoherentDerivedPushforwardCompInclusion f)
        (coherentDerivedPushforward g) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Bounded.ι (coherentDerivedPushforwardComp f g) ≪≫
      (boundedCoherentDerivedPushforwardCompInclusion (f ≫ g)).symm)

end Bounded

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families

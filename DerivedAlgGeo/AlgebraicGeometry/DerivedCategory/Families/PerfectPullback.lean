/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BoundedGeometry
import DerivedAlgGeo.AlgebraicGeometry.Divisors.FiniteLocallyFreePullback

/-!
# Coherent pullback preserves perfect complexes

Every coherent pullback contract sends the finite locally free generators of the perfect
objects to finite locally free generators, hence, by
`coherentDerivedPullback_preservesPerfect`, every perfect complex to a perfect complex.  The
contract identifies its sheaf-level functor with module-sheaf pullback through `comparison`;
module-sheaf pullback preserves fixed-rank locally free atlases along every morphism
(`FiniteLocallyFreeData.pullback`); and the contract's derived pullback commutes with the
degree-zero embedding through its factorization `derivedFactors`
(`Functor.singleFunctorIsoOfFactors`).  So `PreservesPerfectPullback` holds for every
instance of `HasCoherentPullback`, and `perfectDerivedPullback` is available wherever
`boundedCoherentDerivedPullback` is.  No flatness enters.

## Main definitions

* `SchemeBaseChange.derivedPullbackSingleFunctor`: the contract's derived pullback commutes
  with `DerivedCategory.singleFunctor`.

## Main results

* `SchemeBaseChange.schemeFiniteLocallyFreeGenerator_le_inverseImage_coherentDerivedPullback`:
  generators go to generators;
* `SchemeBaseChange.preservesPerfectPullbackOfHasCoherentPullback`: the instance.

## References

* arXiv:2607.28411v1, Definition 3.6 and Proposition 3.8, whose pullback of stability
  conditions along a flat morphism is stated on `Dᵇ(Coh)` and restricts to perfect complexes;
  arXiv:2601.22994, Definition 3.1.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- The contract's derived pullback commutes with the degree-`n` embedding, through its
factorization `derivedFactors`. -/
def derivedPullbackSingleFunctor {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [HasCoherentPullback f]
    (n : ℤ) :
    DerivedCategory.singleFunctor (Coh U.left) n ⋙ coherentDerivedPullback f ≅
      HasCoherentPullback.sheafPullback f ⋙ DerivedCategory.singleFunctor (Coh T.left) n :=
  (HasCoherentPullback.sheafPullback f).singleFunctorIsoOfFactors (coherentDerivedPullback f)
    (HasCoherentPullback.derivedFactors (f := f)) n

/-- Coherent pullback sends finite locally free generators to finite locally free generators:
the atlas of `F` pulls back along `f.left` and is transported through `comparison`, and the
derived pullback of the degree-zero object `F` is the degree-zero object of the pulled-back
sheaf. -/
theorem schemeFiniteLocallyFreeGenerator_le_inverseImage_coherentDerivedPullback
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [HasCoherentPullback f] :
    schemeFiniteLocallyFreeGenerator U.left ≤
      (schemeFiniteLocallyFreeGenerator T.left).inverseImage (coherentDerivedPullback f) := by
  rintro E ⟨F, n, ⟨D⟩, ⟨e⟩⟩
  exact ⟨(HasCoherentPullback.sheafPullback f).obj F, n,
    ⟨(D.pullback f.left).ofIso ((HasCoherentPullback.comparison (f := f)).app F).symm⟩,
    ⟨(coherentDerivedPullback f).mapIso e ≪≫ (derivedPullbackSingleFunctor f 0).app F⟩⟩

/-- Every coherent pullback contract preserves perfect complexes: generators go to
generators, which lie in the envelope. -/
instance preservesPerfectPullbackOfHasCoherentPullback {T U : SchemeBaseChange S}
    (f : T ⟶ U) [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] : PreservesPerfectPullback f where
  mapsGenerator E hE := (schemeFiniteLocallyFreeGenerator T.left).le_triangEnvelope _
    (schemeFiniteLocallyFreeGenerator_le_inverseImage_coherentDerivedPullback f E hE)

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families

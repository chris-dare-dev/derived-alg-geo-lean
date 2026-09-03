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
(`Functor.singleFunctorIsoOfFactors`).  So perfect complexes are preserved by every
instance of `HasCoherentPullback`, with no further hypothesis, and the perfect lift
`perfectDerivedPullback` follows.  Its identity and composition laws are in
`Families/CoherentPullbackCoherence.lean`.  No flatness enters.

## Main definitions

* `SchemeBaseChange.derivedPullbackSingleFunctor`: the contract's derived pullback commutes
  with `DerivedCategory.singleFunctor`;
* `SchemeBaseChange.perfectDerivedPullback`: pullback on perfect derived fibers;
* `SchemeBaseChange.perfectDerivedPullbackCompInclusion`: the perfect lift forgets to coherent
  derived pullback.

## Main results

* `SchemeBaseChange.schemeFiniteLocallyFreeGenerator_le_inverseImage_coherentDerivedPullback`:
  generators go to generators;
* `SchemeBaseChange.coherentDerivedPullback_preservesPerfect`: every coherent pullback contract
  preserves perfect complexes.

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

/-- **Every coherent pullback contract preserves perfect complexes.**  Generators go
to generators, which lie in the envelope, and a triangulated functor that sends the
generators into a thick triangulated subcategory sends the whole envelope into it. -/
theorem coherentDerivedPullback_preservesPerfect
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] :
    schemePerfect U.left ≤
      (schemePerfect T.left).inverseImage (coherentDerivedPullback f) := by
  letI : ((schemePerfect T.left).inverseImage
      (coherentDerivedPullback f)).IsStableUnderRetracts :=
    { of_retract := fun r h ↦ ObjectProperty.prop_of_retract
        (schemeFiniteLocallyFreeGenerator T.left).triangEnvelope
        (r.map (coherentDerivedPullback f)) h }
  letI : ((schemePerfect T.left).inverseImage
      (coherentDerivedPullback f)).IsTriangulated := by
    change (((schemeFiniteLocallyFreeGenerator T.left).triangEnvelope).inverseImage
      (coherentDerivedPullback f)).IsTriangulated
    infer_instance
  change (schemeFiniteLocallyFreeGenerator U.left).triangEnvelope ≤ _
  apply (ObjectProperty.triangEnvelope_le_iff
    (P := schemeFiniteLocallyFreeGenerator U.left)
    (Q := (schemePerfect T.left).inverseImage
      (coherentDerivedPullback f))).2
  exact fun E hE ↦ (schemeFiniteLocallyFreeGenerator T.left).le_triangEnvelope _
    (schemeFiniteLocallyFreeGenerator_le_inverseImage_coherentDerivedPullback f E hE)

/-- Pullback on perfect derived fibers, the restriction of coherent derived pullback. -/
def perfectDerivedPullback {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] :
    U.PerfectDerivedFiber ⥤ T.PerfectDerivedFiber :=
  (schemePerfect T.left).lift
    ((schemePerfect U.left).ι ⋙ coherentDerivedPullback f)
    (fun E ↦ coherentDerivedPullback_preservesPerfect f E.obj E.property)

/-- The perfect lift forgets to coherent derived pullback. -/
def perfectDerivedPullbackCompInclusion
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] :
    perfectDerivedPullback f ⋙ (schemePerfect T.left).ι ≅
      (schemePerfect U.left).ι ⋙ coherentDerivedPullback f :=
  Iso.refl _

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families

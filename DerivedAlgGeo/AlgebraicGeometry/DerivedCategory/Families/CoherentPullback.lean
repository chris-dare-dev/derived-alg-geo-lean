/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BoundedGeometry
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pullback

/-!
# Exact pullback inhabits the coherent pullback contract

`HasCoherentPullback` (`Families/BoundedGeometry.lean`) is the contract behind the inverse
image `f^* : Dᵇ(Coh U) ⥤ Dᵇ(Coh T)` and the pushforward `f_♯σ` of stability conditions along
it.  This file gives it its first inhabitant: every morphism of scheme base changes whose
module-sheaf pullback is exact, in particular every flat morphism
(`SchemeBaseChange.isExactPullback_of_flat`).

## Main definitions

* `SchemeBaseChange.hasCoherentPullbackOfIsExactPullback`: the instance.

## Implementation notes

The sheaf-level functor is `Coh.pullback`, coherent along every morphism; exactness of the
pullback is what `IsExactPullback` supplies and what `Coh.pullback_preservesFiniteLimits`
consumes.  The derived fields come from `HasCoherentPullback.ofExactSheafPullback`, which
takes Mathlib's `Functor.mapDerivedCategory` of the exact functor; the comparison is
`Coh.pullbackCompι`, an `Iso.refl`, so nothing is transported.

Perfect complexes are preserved by this instance as by every instance of the contract
(`coherentDerivedPullback_preservesPerfect`, `Families/PerfectPullback.lean`): module-sheaf
pullback sends finite locally free sheaves to finite locally free sheaves along every
morphism.

## References

* arXiv:2607.28411v1, Definition 3.6 and Proposition 3.8, which pull back along a proper
  faithfully flat morphism; arXiv:2601.22994, Definition 3.1.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- Exact module-sheaf pullback between locally Noetherian scheme base changes restricts to
coherent sheaves and descends to the bounded coherent derived categories; flat morphisms are
the standing example.  The coherent functor is `Coh.pullback`, and
`HasCoherentPullback.ofExactSheafPullback` supplies the derived fields. -/
instance hasCoherentPullbackOfIsExactPullback {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [IsExactPullback f] :
    HasCoherentPullback f :=
  HasCoherentPullback.ofExactSheafPullback f (Coh.pullback f.left) (Coh.pullbackCompι f.left)

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families

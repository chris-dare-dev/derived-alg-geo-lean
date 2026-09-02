/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.BoundedCoherentBaseChange
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.LocallyFinite

/-!
# Pushforward of stability conditions along bounded coherent pullback

Definition 3.6(3) of arXiv:2607.28411v1 on the geometric object it is about.
For a morphism `f : T ⟶ U` of scheme base changes with a coherent pullback,
a stability condition `σ` on `Dᵇ(Coh T)` whose slicing lifts along
`f^* : Dᵇ(Coh U) ⥤ Dᵇ(Coh T)` pushes forward to `f_♯σ` on `Dᵇ(Coh U)`,
with class map `v ∘ f^*` and unchanged charge.

## Main definitions

* `PreStabilityCondition.WithClassMap.boundedCoherentPushforward` and
  `StabilityCondition.WithClassMap.boundedCoherentPushforward`: `f_♯σ`
  from an explicit preimage witness for the bounded coherent pullback.
* `PreStabilityCondition.WithClassMap.boundedCoherentPushforwardOfInducing`
  and its stability-level twin: `f_♯σ` from the phase-indexed A.17 output
  for the bounded coherent pullback, which is the shape in which
  Proposition 3.8 delivers the witness.

## Implementation notes

Every declaration here is the categorical `preimage` of
`Phase/Transfer/PreStability.lean` and `Phase/Transfer/LocallyFinite.lean`
at the functor `boundedCoherentDerivedPullback f`; nothing geometric is
proved.  The slicing of the result is `BoundedCoherentPullbackPreimageData.preimage`,
so the identity and composition laws of that structure apply to the slicing
of `f_♯σ` unchanged.

The pullback `f^♯σ` of Definition 3.1(3), computed through a direct image
`f_* : Dᵇ(Coh T) ⥤ Dᵇ(Coh U)`, has no realization yet: the repository owns
no derived direct image on `Dᵇ(Coh)`.  That is a recorded seam, not an
omission of this file.

## References

* arXiv:2607.28411v1, Definition 3.6, Remark 3.7, Proposition 3.8.
-/

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Triangulated

open AlgebraicGeometry AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u u'

variable {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
  [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [HasCoherentPullback f]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ T.BoundedCoherentDerivedFiber →+ Λ}

namespace PreStabilityCondition.WithClassMap

/-- Definition 3.6(3) of arXiv:2607.28411v1 on `Dᵇ(Coh)`: the pushforward
`f_♯σ` of a pre-stability condition along the bounded coherent pullback
`f^*`, given the witness that `f^*` detects a slicing. -/
def boundedCoherentPushforward (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackPreimageData f σ.slicing) :
    WithClassMap U.BoundedCoherentDerivedFiber
      (v.comp (K₀.map (boundedCoherentDerivedPullback f))) :=
  σ.pushforward (boundedCoherentDerivedPullback f) h.preimageData

/-- The slicing of `f_♯σ` is the geometric preimage slicing, so the identity
and composition laws of `BoundedCoherentPullbackPreimageData` apply to it. -/
@[simp]
theorem boundedCoherentPushforward_slicing
    (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackPreimageData f σ.slicing) :
    (σ.boundedCoherentPushforward f h).slicing = h.preimage := rfl

/-- `f_♯σ` from the phase-indexed A.17 output for the bounded coherent
pullback, the form in which Proposition 3.8 of arXiv:2607.28411v1 delivers
the slicing witness. -/
def boundedCoherentPushforwardOfInducing
    (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackInducingData f σ.slicing) :
    WithClassMap U.BoundedCoherentDerivedFiber
      (v.comp (K₀.map (boundedCoherentDerivedPullback f))) :=
  σ.boundedCoherentPushforward f h.toPreimageData

end PreStabilityCondition.WithClassMap

namespace StabilityCondition.WithClassMap

/-- Definition 3.6(3) of arXiv:2607.28411v1 on `Dᵇ(Coh)` for stability
conditions: `f_♯σ` is again a stability condition, by the categorical
local-finiteness transfer. -/
def boundedCoherentPushforward (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackPreimageData f σ.slicing) :
    WithClassMap U.BoundedCoherentDerivedFiber
      (v.comp (K₀.map (boundedCoherentDerivedPullback f))) :=
  σ.pushforward (boundedCoherentDerivedPullback f) h.preimageData

/-- The slicing of `f_♯σ` is the geometric preimage slicing. -/
@[simp]
theorem boundedCoherentPushforward_slicing
    (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackPreimageData f σ.slicing) :
    (σ.boundedCoherentPushforward f h).slicing = h.preimage := rfl

/-- `f_♯σ` for stability conditions from the phase-indexed A.17 output. -/
def boundedCoherentPushforwardOfInducing
    (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackInducingData f σ.slicing) :
    WithClassMap U.BoundedCoherentDerivedFiber
      (v.comp (K₀.map (boundedCoherentDerivedPullback f))) :=
  σ.boundedCoherentPushforward f h.toPreimageData

end StabilityCondition.WithClassMap

end

end CategoryTheory.Triangulated

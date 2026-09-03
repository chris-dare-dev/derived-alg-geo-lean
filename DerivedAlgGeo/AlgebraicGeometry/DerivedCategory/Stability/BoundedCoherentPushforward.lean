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

## Main results

* `PreStabilityCondition.WithClassMap.boundedCoherentPushforward_slicing` and
  its stability-level twin: the slicing of `f_♯σ` is
  `BoundedCoherentPullbackPreimageData.preimage`, so that structure's
  identity and composition laws apply to `f_♯σ` verbatim.
* `boundedCoherentPushforward_Z` and `boundedCoherentPushforward_charge`, in
  both namespaces: the charge is unchanged on the class lattice and, on an
  object, is the original charge of its pullback.

## Implementation notes

Every declaration here is the categorical `preimage` of
`Phase/Transfer/PreStability.lean` and `Phase/Transfer/LocallyFinite.lean`
at the functor `boundedCoherentDerivedPullback f`; nothing geometric is
proved.  The definitions are ordinary `def`s rather than `abbrev`s, so the
`simp` companions below are what expose the slicing and the charge to the
simplifier at the geometric layer.

The declarations stay in `CategoryTheory.Triangulated.{Pre,}StabilityCondition.WithClassMap`
rather than in the geometric namespace of `BoundedCoherentBaseChange.lean`,
so that `σ.boundedCoherentPushforward f h` is dot notation on the categorical
carrier; this is the geometric-realization row of Tier 2 in
`docs/architecture/placement.md`, which lets a realization keep the
interface's namespace.

The pullback `f^♯σ` of Definition 3.1(3), computed through the direct image
`f_* : Dᵇ(Coh T) ⥤ Dᵇ(Coh U)`, is `boundedCoherentPullback` in
`Stability/BoundedCoherentPullback.lean`, for morphisms with an exact
coherent pushforward.

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

/-- Pushforward leaves the central charge on `Λ` untouched; only the class
map changes.  Definitional; recorded for `simp`. -/
@[simp]
theorem boundedCoherentPushforward_Z
    (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackPreimageData f σ.slicing) :
    (σ.boundedCoherentPushforward f h).Z = σ.Z := rfl

/-- The charge of an object for `f_♯σ` is the charge of its pullback for
`σ`, the geometric form of `(f_♯Z)(E) = Z(f^* E)`. -/
@[simp]
theorem boundedCoherentPushforward_charge
    (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackPreimageData f σ.slicing)
    (E : U.BoundedCoherentDerivedFiber) :
    (σ.boundedCoherentPushforward f h).charge E =
      σ.charge ((boundedCoherentDerivedPullback f).obj E) :=
  σ.preimage_charge (boundedCoherentDerivedPullback f) h.preimageData E

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
local-finiteness transfer `Slicing.PreimageData.isLocallyFinite`. -/
def boundedCoherentPushforward (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackPreimageData f σ.slicing) :
    WithClassMap U.BoundedCoherentDerivedFiber
      (v.comp (K₀.map (boundedCoherentDerivedPullback f))) :=
  σ.pushforward (boundedCoherentDerivedPullback f) h.preimageData

/-- The slicing of `f_♯σ` is the geometric preimage slicing, so the identity
and composition laws of `BoundedCoherentPullbackPreimageData` apply to it
unchanged. -/
@[simp]
theorem boundedCoherentPushforward_slicing
    (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackPreimageData f σ.slicing) :
    (σ.boundedCoherentPushforward f h).slicing = h.preimage := rfl

/-- Pushforward leaves the central charge on `Λ` untouched.  Definitional;
recorded for `simp`. -/
@[simp]
theorem boundedCoherentPushforward_Z
    (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackPreimageData f σ.slicing) :
    (σ.boundedCoherentPushforward f h).Z = σ.Z := rfl

/-- The charge of an object for `f_♯σ` is the charge of its pullback for
`σ`.  Not a `simp` lemma: `simp` derives it from
`StabilityCondition.WithClassMap.preimage_toWithClassMap` and the
pre-stability `preimage_charge`, so it is recorded as the direct restatement
a caller can `rw` with. -/
theorem boundedCoherentPushforward_charge
    (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackPreimageData f σ.slicing)
    (E : U.BoundedCoherentDerivedFiber) :
    (σ.boundedCoherentPushforward f h).charge E =
      σ.charge ((boundedCoherentDerivedPullback f).obj E) :=
  σ.preimage_charge (boundedCoherentDerivedPullback f) h.preimageData E

/-- `f_♯σ` for stability conditions from the phase-indexed A.17 output, the
form in which Proposition 3.8 of arXiv:2607.28411v1 delivers the slicing
witness; local finiteness travels by `StabilityCondition.WithClassMap.preimage`. -/
def boundedCoherentPushforwardOfInducing
    (σ : WithClassMap T.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPullbackInducingData f σ.slicing) :
    WithClassMap U.BoundedCoherentDerivedFiber
      (v.comp (K₀.map (boundedCoherentDerivedPullback f))) :=
  σ.boundedCoherentPushforward f h.toPreimageData

end StabilityCondition.WithClassMap

end

end CategoryTheory.Triangulated

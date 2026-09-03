/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.CoherentPushforward
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.HN
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.LocallyFinite

/-!
# Pullback of stability conditions along bounded coherent direct image

Definition 3.1(3) of arXiv:2607.28411v1 on the geometric object it is about.
For a morphism `f : T ⟶ U` of scheme base changes with an exact coherent
pushforward, a stability condition `σ` on `Dᵇ(Coh U)` whose slicing lifts
along `f_* : Dᵇ(Coh T) ⥤ Dᵇ(Coh U)` pulls back to `f^♯σ` on `Dᵇ(Coh T)`,
with class map `v ∘ f_*` and unchanged charge.  This is also the pullback
half of Definition 3.1 of arXiv:2601.22994, where `f` is a finite morphism
of smooth projective varieties; finite morphisms inhabit
`HasCoherentPushforward` through `hasCoherentPushforwardOfIsFinite`.

## Main definitions

* `SchemeBaseChange.BoundedCoherentPushforwardPreimageData`: the explicit
  witness that `f_*` detects a slicing, the conclusion of Proposition 3.3.
* `SchemeBaseChange.BoundedCoherentPushforwardInducingData`: the phase-indexed
  A.17 output for `f_*`, the form in which Proposition 3.3 delivers it.
* `PreStabilityCondition.WithClassMap.boundedCoherentPullback` and
  `StabilityCondition.WithClassMap.boundedCoherentPullback`: `f^♯σ` from an
  explicit witness.
* `PreStabilityCondition.WithClassMap.boundedCoherentPullbackOfInducing` and
  its stability-level twin: `f^♯σ` from the A.17 output.

## Main results

* `boundedCoherentPullback_slicing`, `boundedCoherentPullback_Z`, and
  `boundedCoherentPullback_charge`, in both namespaces: the slicing of `f^♯σ`
  is the geometric preimage slicing, the charge on `Λ` is unchanged, and the
  charge of an object is the charge of its direct image.

## Implementation notes

Every declaration here is the categorical `preimage` of
`Phase/Transfer/PreStability.lean` and `Phase/Transfer/LocallyFinite.lean` at
the functor `boundedCoherentDerivedPushforward f`; nothing geometric is
proved.  Lemma 3.5(2) and (3) of arXiv:2607.28411v1, the extreme phases and
the slicing distance under `f^♯`, are therefore available through
`PreStabilityCondition.WithClassMap.preimage_phiPlus` and
`slicingDist_preimage_le` at this functor with no further work.

Unlike `BoundedCoherentPullbackPreimageData`, the witness structures carry no
identity or composition laws, because `boundedCoherentDerivedPushforward`
has no identity or composition isomorphisms yet; see the implementation notes
of `Families/CoherentPushforward.lean`.

The declarations stay in
`CategoryTheory.Triangulated.{Pre,}StabilityCondition.WithClassMap` so that
`σ.boundedCoherentPullback f h` is dot notation on the categorical carrier;
this is the geometric-realization row of Tier 2 in
`docs/architecture/placement.md`.

Proposition 3.3 itself, which produces the witness from condition (3.1) on
`f_* 𝒪_X ⊗ −`, is not proved here: its inputs are the Ind-extensions of the
standard slicings inside `Dqc` and the adjunction `f^* ⊣ f_*` on `Dqc`, the
same open geometric inputs as Proposition 3.8.

## References

* arXiv:2607.28411v1, Definition 3.1, Remark 3.2, Proposition 3.3, Lemma 3.5.
* arXiv:2601.22994, Definition 3.1.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- Explicit preimage-slicing data for bounded coherent direct image along one
morphism of locally Noetherian scheme base changes: the two non-formal slicing
axioms for `f_*`.  This is the conclusion of Proposition 3.3 of
arXiv:2607.28411v1, which this file consumes and does not prove.  Kept as a
structure rather than an abbreviation so that the composition law can be added
beside `BoundedCoherentPullbackPreimageData.comp` without changing
consumers. -/
structure BoundedCoherentPushforwardPreimageData
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPushforward f]
    (s : Slicing U.BoundedCoherentDerivedFiber) : Prop where
  /-- The two non-formal slicing axioms for the actual bounded coherent
  direct image. -/
  preimageData : s.PreimageData (boundedCoherentDerivedPushforward f)

namespace BoundedCoherentPushforwardPreimageData

variable {T U : SchemeBaseChange S} {f : T ⟶ U}
  [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
  [HasCoherentPushforward f]
  {s : Slicing U.BoundedCoherentDerivedFiber}

/-- The pullback slicing `f^♯𝒫` on the source fiber constructed from the
explicit witness: an object has phase `φ` exactly when its direct image
does. -/
def preimage (h : BoundedCoherentPushforwardPreimageData f s) :
    Slicing T.BoundedCoherentDerivedFiber :=
  s.preimage (boundedCoherentDerivedPushforward f) h.preimageData

end BoundedCoherentPushforwardPreimageData

/-- The phase-indexed A.17 output for `f_*`, given its own name so that
Proposition 3.3 of arXiv:2607.28411v1 has a typed conclusion to deliver into;
`toPreimageData` is its only consumer. -/
structure BoundedCoherentPushforwardInducingData
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPushforward f]
    (s : Slicing U.BoundedCoherentDerivedFiber) where
  /-- The induced source t-structures with the (A.8) recognition formulas. -/
  inducedTStructures :
    s.InducedTStructures (boundedCoherentDerivedPushforward f)

namespace BoundedCoherentPushforwardInducingData

variable {T U : SchemeBaseChange S} {f : T ⟶ U}
  [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
  [HasCoherentPushforward f]
  {s : Slicing U.BoundedCoherentDerivedFiber}

/-- Apply the owned finite phase-truncation theorem to the actual A.17
output. -/
theorem toPreimageData (h : BoundedCoherentPushforwardInducingData f s) :
    BoundedCoherentPushforwardPreimageData f s where
  preimageData := h.inducedTStructures.preimageData

end BoundedCoherentPushforwardInducingData

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families

namespace CategoryTheory.Triangulated

open AlgebraicGeometry AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u u'

variable {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
  [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] [HasCoherentPushforward f]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ U.BoundedCoherentDerivedFiber →+ Λ}

namespace PreStabilityCondition.WithClassMap

/-- Definition 3.1(3) of arXiv:2607.28411v1 on `Dᵇ(Coh)`: the pullback
`f^♯σ` of a pre-stability condition along the bounded coherent direct image
`f_*`, given the witness that `f_*` detects a slicing. -/
def boundedCoherentPullback (σ : WithClassMap U.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPushforwardPreimageData f σ.slicing) :
    WithClassMap T.BoundedCoherentDerivedFiber
      (v.comp (K₀.map (boundedCoherentDerivedPushforward f))) :=
  σ.pullback (boundedCoherentDerivedPushforward f) h.preimageData

/-- The slicing of `f^♯σ` is the geometric preimage slicing, so the
slicing-level API of `Phase.Transfer.Basic` applies to it verbatim. -/
@[simp]
theorem boundedCoherentPullback_slicing
    (σ : WithClassMap U.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPushforwardPreimageData f σ.slicing) :
    (σ.boundedCoherentPullback f h).slicing = h.preimage := rfl

/-- Pullback leaves the central charge on `Λ` untouched; only the class map
changes.  Definitional; recorded for `simp`. -/
@[simp]
theorem boundedCoherentPullback_Z
    (σ : WithClassMap U.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPushforwardPreimageData f σ.slicing) :
    (σ.boundedCoherentPullback f h).Z = σ.Z := rfl

/-- The charge of an object for `f^♯σ` is the charge of its direct image for
`σ`, the geometric form of `(f^♯Z)(E) = Z(f_* E)`. -/
@[simp]
theorem boundedCoherentPullback_charge
    (σ : WithClassMap U.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPushforwardPreimageData f σ.slicing)
    (E : T.BoundedCoherentDerivedFiber) :
    (σ.boundedCoherentPullback f h).charge E =
      σ.charge ((boundedCoherentDerivedPushforward f).obj E) :=
  σ.preimage_charge (boundedCoherentDerivedPushforward f) h.preimageData E

/-- `f^♯σ` from the phase-indexed A.17 output for the bounded coherent direct
image, the form in which Proposition 3.3 of arXiv:2607.28411v1 delivers the
slicing witness. -/
def boundedCoherentPullbackOfInducing
    (σ : WithClassMap U.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPushforwardInducingData f σ.slicing) :
    WithClassMap T.BoundedCoherentDerivedFiber
      (v.comp (K₀.map (boundedCoherentDerivedPushforward f))) :=
  σ.boundedCoherentPullback f h.toPreimageData

end PreStabilityCondition.WithClassMap

namespace StabilityCondition.WithClassMap

/-- Definition 3.1(3) of arXiv:2607.28411v1 on `Dᵇ(Coh)` for stability
conditions: `f^♯σ` is again a stability condition, by the categorical
local-finiteness transfer `Slicing.PreimageData.isLocallyFinite`.  This is
the content of Remark 3.2: once `f^♯𝒫` is a slicing, `f^♯σ` is a stability
condition with respect to `(Λ, f^♯v)`. -/
def boundedCoherentPullback (σ : WithClassMap U.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPushforwardPreimageData f σ.slicing) :
    WithClassMap T.BoundedCoherentDerivedFiber
      (v.comp (K₀.map (boundedCoherentDerivedPushforward f))) :=
  σ.pullback (boundedCoherentDerivedPushforward f) h.preimageData

/-- The slicing of `f^♯σ` is the geometric preimage slicing, restated at the
stability-condition level so callers need not pass through the underlying
pre-stability condition. -/
@[simp]
theorem boundedCoherentPullback_slicing
    (σ : WithClassMap U.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPushforwardPreimageData f σ.slicing) :
    (σ.boundedCoherentPullback f h).slicing = h.preimage := rfl

/-- Pullback leaves the central charge on `Λ` untouched.  Definitional;
recorded for `simp`. -/
@[simp]
theorem boundedCoherentPullback_Z
    (σ : WithClassMap U.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPushforwardPreimageData f σ.slicing) :
    (σ.boundedCoherentPullback f h).Z = σ.Z := rfl

/-- The charge of an object for `f^♯σ` is the charge of its direct image for
`σ`.  Not a `simp` lemma: `simp` derives it from
`StabilityCondition.WithClassMap.preimage_toWithClassMap` and the
pre-stability `preimage_charge`, so it is recorded as the direct restatement
a caller can `rw` with. -/
theorem boundedCoherentPullback_charge
    (σ : WithClassMap U.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPushforwardPreimageData f σ.slicing)
    (E : T.BoundedCoherentDerivedFiber) :
    (σ.boundedCoherentPullback f h).charge E =
      σ.charge ((boundedCoherentDerivedPushforward f).obj E) :=
  σ.preimage_charge (boundedCoherentDerivedPushforward f) h.preimageData E

/-- `f^♯σ` for stability conditions from the phase-indexed A.17 output, the
form in which Proposition 3.3 of arXiv:2607.28411v1 delivers the slicing
witness; local finiteness travels by `StabilityCondition.WithClassMap.preimage`. -/
def boundedCoherentPullbackOfInducing
    (σ : WithClassMap U.BoundedCoherentDerivedFiber v)
    (h : BoundedCoherentPushforwardInducingData f σ.slicing) :
    WithClassMap T.BoundedCoherentDerivedFiber
      (v.comp (K₀.map (boundedCoherentDerivedPushforward f))) :=
  σ.boundedCoherentPullback f h.toPreimageData

end StabilityCondition.WithClassMap

end

end CategoryTheory.Triangulated

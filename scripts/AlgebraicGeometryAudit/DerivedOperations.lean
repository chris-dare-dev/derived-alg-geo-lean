/-
General derived-operation slice of the AlgebraicGeometry audit: the derived tensor and
derived pushforward capabilities on scheme-derived categories, and the twisted pushforward
built from them.

## The import list is part of the record

These four imports are the whole file, and **none of them is `FourierMukai` and none of
them is in the stability tree**. That is the MO1.10 (#1321) acceptance obligation made
mechanical: before the extraction, printing the axioms of `HasDerivedTensor` or
`HasDerivedPushforward` required importing kernels, correspondences and convolution,
because the capabilities lived inside the Fourier--Mukai subtree. Adding a
`FourierMukai` import here to make a record resolve would mean a capability had drifted
back; the records of things that genuinely are about transforms stay in
`GeometricLedgers.lean`.

## Still inhabitant-free

INHABITANT-FREE BY DESIGN, exactly as the ledgers are. Nothing below constructs a
derived tensor or a derived pushforward, and no scheme is shown to admit either. A clean
axiom list here is NOT evidence that `Dᵇ(Coh X)` is closed under derived tensor -- on a
singular `X` it is not -- nor that any morphism admits a coherent derived direct image.
These are records of *contracts*, and relocating them to their own owners discharged
nothing.

`twistedPushforward` at the end is the one assembled operation: `Rf_*(K ⊗^L -)`, from the
two capabilities and nothing else. Its axiom list is clean for the same reason the
ledgers' are -- the inputs are hypotheses.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.DerivedPushforward
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.TwistedPushforward

/-! ## Derived pushforward on bounded coherent derived fibers

`Families/DerivedPushforward.lean`. The slot where *properness* lives: pushforward
preserves coherence only for a proper morphism, so a caller discharging this class is
asserting exactly that much geometry. Stated directly on `Dᵇ(Coh)` rather than on `Coh`
with a derived lift, because pushforward of a coherent sheaf is not coherent in general
and there is no sheaf-level functor to induce from.

Deliberately NOT connected by an instance to the stronger `HasCoherentPushforward` next
door, whose exactness on coherent sheaves finite morphisms do inhabit. Deriving one from
the other is mathematics, and MO1.10 is a placement split. -/

#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPushforward
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPushforward.derivedPushforward
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPushforward.additive
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPushforward.commShift
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedPushforward.isTriangulated
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedPushforward
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedPushforward_additive
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedPushforwardCommShift
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedPushforward_isTriangulated

/-! ## The bounded coherent derived tensor: the raw capability

`Tensor/BoundedCoherent.lean`. A bifunctor with two-slot exactness and Koszul shift
coherence stored once as an `ExactBifunctor`, with the one-slot projections and the
right-twist projections derived from it.

This is NOT the restriction of the unbounded K-flat tensor of `Tensor/Unbounded.lean`.
That restriction is a missing theorem: the bounded coherent derived category of a
singular scheme is not closed under arbitrary derived tensor, and a clean axiom list on
the class does not make it so. -/

#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.derivedTensor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.exact
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.exactBifunctor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.additive
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.commShift
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.isTriangulated
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.firstFamily
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.secondFamily
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.flipAdditive
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.flipCommShift
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasDerivedTensor.flipIsTriangulated
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedTensor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedTensor_additive
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedTensorCommShift
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedTensor_isTriangulated
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedTensorFlipCommShift
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedTensorFlip_isTriangulated
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.derivedTensorExactBifunctor

/-! ## The coherent derived tensor: the monoidal refinement

`Tensor/Coherent.lean`. Extending `MonoidalCategory` makes functoriality, associator and
unitor naturality, the pentagon and the triangle fields of one structure, so different
routes through a fourfold tensor product are known to agree instead of each theorem
choosing its own comparison.

Coherence is MORE to supply, not less: `hasDerivedTensorOfCoherent` forgets down to the
raw capability and there is deliberately no adapter the other way. -/

#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor.toMonoidalCategory
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor.exact
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor.exactBifunctor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor.additive
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor.commShift
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasCoherentDerivedTensor.isTriangulated
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.hasDerivedTensorOfCoherent
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.hasCoherentDerivedTensorIsCompatibleWithTriangulation
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.coherentDerivedTensorAssoc
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.coherentDerivedTensorUnit
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.coherentDerivedTensorLeftUnitor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.coherentDerivedTensorRightUnitor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.coherentDerivedTensor_pentagon
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.coherentDerivedTensor_triangle

/-! ## The relative input: strong monoidality of derived pullback

`Tensor/Relative.lean`. The only tier that mentions a morphism of scheme base changes,
and therefore the only one a consumer of the absolute tensor need not import.

Still supplied: strong monoidality of derived pullback is a theorem this repository does
not prove, and arbitrary derived pullback remains SF8 #554's obligation. -/

#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasMonoidalDerivedPullback
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.HasMonoidalDerivedPullback.toMonoidal
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.monoidalDerivedPullbackTensorIso
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.monoidalDerivedPullbackLeftUnitor
#print axioms AlgebraicGeometry.DerivedCategory.FourierMukai.monoidalDerivedPullbackRightUnitor

/-! ## The twisted pushforward: the independent consumer

`DerivedCategory/TwistedPushforward.lean`. `Rf_*(K ⊗^L -)` on bounded coherent derived
fibers, from the tensor capability and the pushforward capability and nothing else -- no
correspondence, no kernel, no product, no projections.

It is what the extraction was for. A caller that also has a derived pullback precomposes
and gets the Fourier--Mukai transform; a caller pushing a twisted relative family to its
base does not need one, and no longer imports one.

Conditional on both capabilities, so still inhabited by nothing. -/

#print axioms AlgebraicGeometry.DerivedCategory.twistedPushforward
#print axioms AlgebraicGeometry.DerivedCategory.twistedPushforward_obj
#print axioms AlgebraicGeometry.DerivedCategory.twistedPushforward_isTriangulated
#print axioms AlgebraicGeometry.DerivedCategory.twistedPushforward_additive
#print axioms AlgebraicGeometry.DerivedCategory.twistedPushforwardMap
#print axioms AlgebraicGeometry.DerivedCategory.twistedPushforwardMap_app

/-! ## Restricting a monoidal structure to the bounded coherent tier

`DerivedCategory/Tensor/BoundedMonoidal.lean` (#892). `Dᵇ(Coh X)` is an `abbrev` for
`t.bounded.FullSubcategory`, so Mathlib's `fullMonoidalSubcategory` applies to it on the
nose; `schemeBoundedCoherentDerivedCategory_eq` records that identification as `rfl`
rather than leaving it to a comment.

The input is `ObjectProperty.IsMonoidal t.bounded` -- finite Tor-dimension, supplied and
not proved, because on a singular scheme `⊗^L` leaves `Dᵇ(Coh)`. What this buys is that
the `MonoidalCategory` parent of `HasCoherentDerivedTensor` becomes something a named
constructor produces rather than something a caller supplies from nothing.

Everything here is a `def`. Mathlib already has a global `fullMonoidalSubcategory`
instance on the same `abbrev`, so a repo-level instance would be a third synthesis route
across the 68 `HasCoherentDerivedTensor` binder sites, not a second.

Still inhabited by nothing: no scheme in this repository is shown to satisfy the
`IsMonoidal` hypothesis. -/

#print axioms AlgebraicGeometry.DerivedCategory.boundedProperty
#print axioms AlgebraicGeometry.DerivedCategory.schemeBoundedCoherentDerivedCategory_eq
#print axioms AlgebraicGeometry.DerivedCategory.boundedMonoidalCategory
#print axioms AlgebraicGeometry.DerivedCategory.boundedTensorι
#print axioms AlgebraicGeometry.DerivedCategory.boundedTensorιMonoidal

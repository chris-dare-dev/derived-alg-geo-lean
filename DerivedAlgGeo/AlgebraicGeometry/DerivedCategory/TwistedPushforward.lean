/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.BoundedCoherent
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.DerivedPushforward

/-!
# Twist by a fixed object, then push forward

`Rf_*(K ⊗^L -)` on bounded coherent derived fibers, assembled from the two general
capabilities and from nothing else: a derived tensor on the source
(`Tensor/BoundedCoherent.lean`) and a derived pushforward along `f`
(`Families/DerivedPushforward.lean`).

## Why this file exists

It is the independent consumer that MO1.10 (#1321) owes the extracted owners, and the
demonstration that they are usable on their own.  **Its import list is the point**: two
imports, neither of them `FourierMukai` nor anything in the stability tree.  Before the
extraction the same operation could not be stated without importing kernels,
correspondences and convolution, because the two capabilities lived inside the
Fourier--Mukai subtree.

The operation itself is ordinary and older than Fourier--Mukai theory: a relative family
twisted by a fixed object and pushed to the base.  A caller with a correspondence gets
the Fourier--Mukai transform by precomposing with a derived pullback, and
`FourierMukai/KernelCorrespondence.lean` does exactly that -- but the converse is not
needed, and nothing here mentions a kernel, a product, a projection or a transform.

## What this file does not assert

Nothing constructs either capability, so nothing here exhibits a single instance of
`twistedPushforward` on an actual scheme.  Both hypotheses travel unchanged: `f` carries
the properness the pushforward capability stands for, and `HasDerivedTensor Z` carries
the closure of `Dᵇ(Coh Z)` under derived tensor, which is false for a general singular
`Z`.  The exactness conclusions below are conditional on both.

## References

* `docs/architecture/cutover-ledger.md`, row 10.
-/

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory

open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
open AlgebraicGeometry.DerivedCategory.FourierMukai

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open AlgebraicGeometry
open SchemeBaseChange

variable {S : Scheme.{u}}

section

variable {Z U : SchemeBaseChange S}
  [IsLocallyNoetherian Z.left] [IsLocallyNoetherian U.left]

/-- **Twist by `K`, then push forward along `f`.**

`Rf_*(K ⊗^L -) : Dᵇ(Coh Z) ⥤ Dᵇ(Coh U)`, built from a supplied derived tensor on `Z` and
a supplied derived pushforward along `f`.

An `abbrev`, so that instance search sees the composite and derives shift and
triangulation from the two constituents rather than needing them restated here. -/
@[reducible] noncomputable def twistedPushforward (f : Z ⟶ U)
    [HasDerivedTensor Z] [HasDerivedPushforward f]
    (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    SchemeBoundedCoherentDerivedCategory Z.left ⥤
      SchemeBoundedCoherentDerivedCategory U.left :=
  (derivedTensor Z).obj K ⋙ derivedPushforward f

@[simp]
theorem twistedPushforward_obj (f : Z ⟶ U)
    [HasDerivedTensor Z] [HasDerivedPushforward f]
    (K E : SchemeBoundedCoherentDerivedCategory Z.left) :
    (twistedPushforward f K).obj E =
      (derivedPushforward f).obj (((derivedTensor Z).obj K).obj E) :=
  rfl

/-- **The twisted pushforward is triangulated.**

The general statement the two capabilities were extracted to make reachable: exactness of
`Rf_*(K ⊗^L -)` follows from exactness of the tensor twist and of the pushforward, with
no correspondence, no kernel and no product in sight. -/
theorem twistedPushforward_isTriangulated (f : Z ⟶ U)
    [HasDerivedTensor Z] [HasDerivedPushforward f]
    (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    (twistedPushforward f K).IsTriangulated :=
  inferInstance

/-- The twisted pushforward is additive. -/
theorem twistedPushforward_additive (f : Z ⟶ U)
    [HasDerivedTensor Z] [HasDerivedPushforward f]
    (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    (twistedPushforward f K).Additive :=
  inferInstance

/-- Twisting is functorial in the twisting object: a map of twists induces a natural
transformation of twisted pushforwards.  Uses only the functoriality already present in
the tensor capability. -/
noncomputable def twistedPushforwardMap (f : Z ⟶ U)
    [HasDerivedTensor Z] [HasDerivedPushforward f]
    {K L : SchemeBoundedCoherentDerivedCategory Z.left} (φ : K ⟶ L) :
    twistedPushforward f K ⟶ twistedPushforward f L :=
  Functor.whiskerRight ((derivedTensor Z).map φ) (derivedPushforward f)

@[simp]
theorem twistedPushforwardMap_app (f : Z ⟶ U)
    [HasDerivedTensor Z] [HasDerivedPushforward f]
    {K L : SchemeBoundedCoherentDerivedCategory Z.left} (φ : K ⟶ L)
    (E : SchemeBoundedCoherentDerivedCategory Z.left) :
    (twistedPushforwardMap f φ).app E =
      (derivedPushforward f).map (((derivedTensor Z).map φ).app E) :=
  rfl

end

end AlgebraicGeometry.DerivedCategory

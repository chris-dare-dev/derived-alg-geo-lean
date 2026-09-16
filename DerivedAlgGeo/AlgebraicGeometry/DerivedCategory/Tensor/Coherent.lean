/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import DerivedAlgGeo.CategoryTheory.Monoidal.Triangulated
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.BoundedCoherent

/-!
# Coherent derived tensor products

`HasDerivedTensor` is the bare capability of `Tensor/BoundedCoherent.lean`: a bifunctor
exact in both variables.  Consumers that rebracket or unitalize need more.  In
particular, independently choosing an associator and two unitors does not say that
different routes through a fourfold tensor product agree.

`HasCoherentDerivedTensor` is the stable root for those consumers.  It packages the
tensor as a Mathlib `MonoidalCategory`, so naturality, the pentagon, and the triangle are
fields of one structure rather than unrelated theorem-specific capabilities.  Its
`ExactBifunctor` field retains the complete two-slot exactness and Koszul shift coherence
used by Fourier--Mukai transforms and kernel variation.

The instance below is the one-way migration adapter

`HasCoherentDerivedTensor -> HasDerivedTensor`.

There is intentionally no adapter in the other direction: a raw bifunctor is not promoted
to coherent data.  Raw instances remain useful for intermediate realizations that only
construct a single transform, but public convolution, associativity, and unit APIs
require this coherent root.

## Still a supplied capability

Coherence is *more* to supply, not less.  Nothing here inhabits either class, and
extending `MonoidalCategory` does not make `Dᵇ(Coh Z)` closed under derived tensor; on a
singular `Z` it is not.  A caller instantiating `HasCoherentDerivedTensor` asserts the
closure and the coherence together.

## Placement

MO1.10 (#1321) extracted this file's contents from
`DerivedCategory/FourierMukai/DerivedTensorCoherence.lean`, splitting the relative tier --
strong monoidality of derived pullback along a morphism -- into `Tensor/Relative.lean`.
Per the cutover ledger's standing decision that paths move and namespaces do not, the
declarations keep the `AlgebraicGeometry.DerivedCategory.FourierMukai` namespace they
were introduced with.

## References

* `docs/architecture/cutover-ledger.md`, row 10.
-/

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.FourierMukai
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SchemeBaseChange

variable {S : Scheme.{u}}

noncomputable section

/-- A derived tensor product together with its complete monoidal coherence.

Extending `MonoidalCategory` makes functoriality, associator and unitor
naturality, the pentagon, and the triangle part of the same root structure.
The remaining field records exactness and compatible shifts of the complete
tensor bifunctor. -/
class HasCoherentDerivedTensor (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left]
    extends MonoidalCategory (SchemeBoundedCoherentDerivedCategory Z.left) where
  /-- Exactness and coherent shifts of tensor in both variables. -/
  exact : Functor.ExactBifunctor
    (curriedTensor (SchemeBoundedCoherentDerivedCategory Z.left))

namespace HasCoherentDerivedTensor

variable {Z : SchemeBaseChange S} [IsLocallyNoetherian Z.left]
  [HasCoherentDerivedTensor Z]

/-- The exact-bifunctor witness carried by coherent derived tensor. -/
def exactBifunctor : Functor.ExactBifunctor
    (curriedTensor (SchemeBoundedCoherentDerivedCategory Z.left)) :=
  HasCoherentDerivedTensor.exact

/-- Legacy projection: additivity of each left tensor twist. -/
theorem additive (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((curriedTensor
      (SchemeBoundedCoherentDerivedCategory Z.left)).obj K).Additive := by
  letI := exactBifunctor |>.secondCommShift K
  letI := exactBifunctor |>.secondTriangulated K
  infer_instance

/-- Legacy projection: shift coherence of each left tensor twist. -/
@[reducible] def commShift
    (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((curriedTensor
      (SchemeBoundedCoherentDerivedCategory Z.left)).obj K).CommShift ℤ :=
  exactBifunctor |>.secondCommShift K

/-- Legacy projection: triangulatedness of each left tensor twist. -/
theorem isTriangulated (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    letI := commShift K
    ((curriedTensor
      (SchemeBoundedCoherentDerivedCategory Z.left)).obj K).IsTriangulated :=
  exactBifunctor |>.secondTriangulated K

end HasCoherentDerivedTensor

/-- Forget coherence when a consumer only needs the raw tensor bifunctor.

This is deliberately one-way: no raw `HasDerivedTensor` is upgraded to a
coherent tensor product. -/
instance hasDerivedTensorOfCoherent (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasCoherentDerivedTensor Z] :
    HasDerivedTensor Z where
  derivedTensor := curriedTensor (SchemeBoundedCoherentDerivedCategory Z.left)
  exact := HasCoherentDerivedTensor.exactBifunctor

/-- The coherent associator in the orientation used by the kernel ledgers:
`A ⊗ (B ⊗ -) ≅ (A ⊗ B) ⊗ -`. -/
def coherentDerivedTensorAssoc (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasCoherentDerivedTensor Z]
    (A B : SchemeBoundedCoherentDerivedCategory Z.left) :
    (derivedTensor Z).obj B ⋙ (derivedTensor Z).obj A ≅
      (derivedTensor Z).obj (((derivedTensor Z).obj A).obj B) :=
  (tensorLeftTensor A B).symm

/-- The tensor unit selected by the coherent root. -/
abbrev coherentDerivedTensorUnit (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasCoherentDerivedTensor Z] :
    SchemeBoundedCoherentDerivedCategory Z.left :=
  𝟙_ (SchemeBoundedCoherentDerivedCategory Z.left)

/-- The coherent left unitor as an isomorphism of twist functors. -/
def coherentDerivedTensorLeftUnitor (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasCoherentDerivedTensor Z] :
    (derivedTensor Z).obj (coherentDerivedTensorUnit Z) ≅
      𝟭 (SchemeBoundedCoherentDerivedCategory Z.left) :=
  leftUnitorNatIso (SchemeBoundedCoherentDerivedCategory Z.left)

/-- The coherent right unitor as an isomorphism of twist functors. -/
def coherentDerivedTensorRightUnitor (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasCoherentDerivedTensor Z] :
    (derivedTensor Z).flip.obj (coherentDerivedTensorUnit Z) ≅
      𝟭 (SchemeBoundedCoherentDerivedCategory Z.left) :=
  rightUnitorNatIso (SchemeBoundedCoherentDerivedCategory Z.left)

/-- The pentagon law exposed at the derived-tensor root. -/
theorem coherentDerivedTensor_pentagon (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasCoherentDerivedTensor Z]
    (W X Y V : SchemeBoundedCoherentDerivedCategory Z.left) :
    MonoidalCategory.Pentagon W X Y V :=
  MonoidalCategory.pentagon W X Y V

/-- The triangle law exposed at the derived-tensor root. -/
theorem coherentDerivedTensor_triangle (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasCoherentDerivedTensor Z]
    (X Y : SchemeBoundedCoherentDerivedCategory Z.left) :
    (α_ X (𝟙_ (SchemeBoundedCoherentDerivedCategory Z.left)) Y).hom ≫
        X ◁ (λ_ Y).hom =
      (ρ_ X).hom ▷ Y :=
  MonoidalCategory.triangle X Y

/-- A coherent geometric derived tensor realizes the generic compatibility
interface between monoidal and triangulated structure from
`CategoryTheory/Monoidal/Triangulated.lean`. The instance lives with the
geometric object it is about, as `Abelian (ModuleCat R)` lives with
`ModuleCat`, rather than in an instance leaf below the categorical source. -/
instance hasCoherentDerivedTensorIsCompatibleWithTriangulation
    (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left]
    [HasCoherentDerivedTensor Z] :
    CategoryTheory.MonoidalCategory.IsCompatibleWithTriangulation
      (SchemeBoundedCoherentDerivedCategory Z.left) where
  tensorExact := HasCoherentDerivedTensor.exactBifunctor

end

end AlgebraicGeometry.DerivedCategory.FourierMukai

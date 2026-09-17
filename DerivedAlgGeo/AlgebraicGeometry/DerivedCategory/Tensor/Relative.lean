/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.Coherent

/-!
# The relative derived tensor input: pullback compatibility

The **relative** tier of the `Tensor/` owner.  `Tensor/BoundedCoherent.lean` and
`Tensor/Coherent.lean` both speak about a single scheme base change; this file is about a
*morphism* of them, and records how a coherent derived tensor on the source relates to
one on the target across derived pullback.

`HasMonoidalDerivedPullback f` is that record.  It extends Mathlib's `Functor.Monoidal`,
which includes the tensorator and unit comparison, their naturality, associativity and
unitality laws, and proofs that the lax and oplax maps are inverse.  Tensor and unit
compatibility therefore cannot be selected independently at each theorem site.

## Still a supplied capability

Like the tiers it builds on, this file inhabits nothing.  Strong monoidality of derived
pullback is a theorem about a morphism of schemes that this repository does not prove, and
`HasMonoidalDerivedPullback` is where a caller discharges it.  Arbitrary derived pullback
itself remains SF8 #554's obligation; this class consumes the existing
`HasCoherentPullback` contract rather than restating it.

## Placement

MO1.10 (#1321) extracted this file's contents from
`DerivedCategory/FourierMukai/DerivedTensorCoherence.lean`.  Separating it from
`Tensor/Coherent.lean` is the ledger's requirement that the unbounded, bounded-coherent
and relative inputs be distinguishable: a consumer needing only the absolute coherent
tensor imports `Tensor/Coherent.lean` and never mentions a morphism.  Per the cutover
ledger's standing decision that paths move and namespaces do not, the declarations keep
the `AlgebraicGeometry.DerivedCategory.FourierMukai` namespace they were introduced with.

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

/-- Derived pullback as a strong monoidal functor.

Mathlib's `Functor.Monoidal` root includes the tensorator and unit comparison,
their naturality, associativity and unitality laws, and proofs that the lax and
oplax maps are inverse. Thus tensor and unit compatibility cannot be selected
independently at each theorem site. -/
class HasMonoidalDerivedPullback {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [HasCoherentDerivedTensor T]
    [HasCoherentDerivedTensor U]
    extends (boundedCoherentDerivedPullback f).Monoidal

/-- Strong monoidality in the orientation consumed by the kernel ledgers:
`f*(K ⊗ -) ≅ f*K ⊗ f*(-)`. -/
def monoidalDerivedPullbackTensorIso {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [HasCoherentDerivedTensor T]
    [HasCoherentDerivedTensor U] [HasMonoidalDerivedPullback f]
    (K : SchemeBoundedCoherentDerivedCategory U.left) :
    (derivedTensor U).obj K ⋙ boundedCoherentDerivedPullback f ≅
      boundedCoherentDerivedPullback f ⋙
        (derivedTensor T).obj ((boundedCoherentDerivedPullback f).obj K) :=
  (Functor.Monoidal.commTensorLeft (boundedCoherentDerivedPullback f) K).symm

/-- The pullback of the source unit acts as a left unit, derived from the
strong monoidal unit comparison and the target left unitor. -/
def monoidalDerivedPullbackLeftUnitor {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [HasCoherentDerivedTensor T]
    [HasCoherentDerivedTensor U] [HasMonoidalDerivedPullback f] :
    (derivedTensor T).obj
        ((boundedCoherentDerivedPullback f).obj (coherentDerivedTensorUnit U)) ≅
      𝟭 (SchemeBoundedCoherentDerivedCategory T.left) :=
  (derivedTensor T).mapIso
      (Functor.Monoidal.εIso (boundedCoherentDerivedPullback f)).symm ≪≫
    coherentDerivedTensorLeftUnitor T

/-- The pullback of the source unit acts as a right unit, derived from the
strong monoidal unit comparison and the target right unitor. -/
def monoidalDerivedPullbackRightUnitor {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [HasCoherentDerivedTensor T]
    [HasCoherentDerivedTensor U] [HasMonoidalDerivedPullback f] :
    (derivedTensor T).flip.obj
        ((boundedCoherentDerivedPullback f).obj (coherentDerivedTensorUnit U)) ≅
      𝟭 (SchemeBoundedCoherentDerivedCategory T.left) :=
  (derivedTensor T).flip.mapIso
      (Functor.Monoidal.εIso (boundedCoherentDerivedPullback f)).symm ≪≫
    coherentDerivedTensorRightUnitor T

end

end AlgebraicGeometry.DerivedCategory.FourierMukai

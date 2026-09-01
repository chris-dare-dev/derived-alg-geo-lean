/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import DerivedAlgGeo.CategoryTheory.Monoidal.Triangulated
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai.KernelCorrespondence

/-!
# Coherent derived tensor products

`HasDerivedTensor` is the intentionally raw Fourier--Mukai input: it supplies
only a bifunctor whose left twists are exact.  Kernel composition needs more.
In particular, independently choosing an associator and two unitors does not
say that different routes through a fourfold tensor product agree.

`HasCoherentDerivedTensor` is the stable root for consumers that rebracket or
unitalize derived tensor products.  It packages the tensor as a Mathlib
`MonoidalCategory`, so naturality, the pentagon, and the triangle are fields of
one structure rather than unrelated theorem-specific capabilities.  The
exactness fields retain the part of `HasDerivedTensor` used by
Fourier--Mukai transforms.

The instance below is the one-way migration adapter

`HasCoherentDerivedTensor -> HasDerivedTensor`.

There is intentionally no adapter in the other direction: a raw bifunctor is
not promoted to coherent data.  Raw instances remain useful for intermediate
realizations that only construct a single transform, but public convolution,
associativity, and unit APIs require this coherent root.
-/

universe u

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
The remaining fields record exactness of each left twist, as required by the
Fourier--Mukai correspondence layer. -/
class HasCoherentDerivedTensor (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left]
    extends MonoidalCategory (SchemeBoundedCoherentDerivedCategory Z.left) where
  /-- Every left tensor twist is additive. -/
  additive : ∀ K, ((curriedTensor
    (SchemeBoundedCoherentDerivedCategory Z.left)).obj K).Additive
  /-- Every left tensor twist commutes with the triangulated shift. -/
  commShift : ∀ K, ((curriedTensor
    (SchemeBoundedCoherentDerivedCategory Z.left)).obj K).CommShift ℤ
  /-- Every left tensor twist is triangulated. -/
  isTriangulated : ∀ K, ((curriedTensor
    (SchemeBoundedCoherentDerivedCategory Z.left)).obj K).IsTriangulated

/-- Forget coherence when a consumer only needs the raw tensor bifunctor.

This is deliberately one-way: no raw `HasDerivedTensor` is upgraded to a
coherent tensor product. -/
instance hasDerivedTensorOfCoherent (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasCoherentDerivedTensor Z] :
    HasDerivedTensor Z where
  derivedTensor := curriedTensor (SchemeBoundedCoherentDerivedCategory Z.left)
  additive := HasCoherentDerivedTensor.additive
  commShift := HasCoherentDerivedTensor.commShift
  isTriangulated := HasCoherentDerivedTensor.isTriangulated

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
  tensorAdditive := HasCoherentDerivedTensor.additive
  tensorCommShift := HasCoherentDerivedTensor.commShift
  tensorIsTriangulated := HasCoherentDerivedTensor.isTriangulated

end

end AlgebraicGeometry.DerivedCategory.FourierMukai

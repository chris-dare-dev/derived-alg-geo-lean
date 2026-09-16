/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BoundedGeometry
import DerivedAlgGeo.CategoryTheory.Triangulated.ExactFunctorFamily

/-!
# The bounded coherent derived tensor product, as a supplied capability

`HasDerivedTensor Z` is the geometry-level contract for a derived tensor product on
`Dᵇ(Coh Z)`, exact in both variables.  It is a **supplied capability, not a
construction**: this file inhabits nothing, and no scheme in this repository is shown
to admit one.

## What this file does not assert

`Dᵇ(Coh Z)` is **not** automatically closed under arbitrary derived tensor.  On a
singular scheme the derived tensor of two bounded coherent complexes need not be
bounded, and nothing here asserts otherwise.  A caller instantiating `HasDerivedTensor`
is asserting exactly that closure in whatever generality it supplies the class;
relocating the class to this owner established it nowhere.

Neither is this class obtained by restricting the unbounded K-flat tensor product of
`Tensor/Unbounded.lean`.  That restriction is a missing theorem, not a definition.

No monoidal structure is asked for: not associativity, not symmetry, not a unit.  A
consumer that rebrackets or unitalizes derived tensor products wants
`Tensor/Coherent.lean` instead, whose `HasCoherentDerivedTensor` packages the coherence
as one `MonoidalCategory` and maps into this class one way only.

## Placement

MO1.10 (#1321) extracted this capability from
`DerivedCategory/FourierMukai/KernelCorrespondence.lean`.  Fourier--Mukai is a
*consumer*: a transform needs a tensor, but a tensor is not about transforms, and a
caller wanting a general derived tensor should not have to import kernels, convolution
or correspondences to get one.  Per the cutover ledger's standing decision that paths
move and namespaces do not, the declarations keep the
`AlgebraicGeometry.DerivedCategory.FourierMukai` namespace they were introduced with;
the path, not the namespace, records what they are about.

## References

* `docs/architecture/cutover-ledger.md`, row 10.
-/

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.FourierMukai
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open AlgebraicGeometry
open SchemeBaseChange

variable {S : Scheme.{u}}

/-- **Derived tensor product on `Dᵇ(Coh Z)`, supplied.**

The `⊗^L` slot of a Fourier--Mukai correspondence, and of anything else that twists a
bounded coherent complex by another one.  Stated as a bifunctor, matching
`Correspondence.tensor`, so that `tensor.obj K` is "twist by the kernel `K`".  Its
exactness is packaged once as an `ExactBifunctor`: both partial tensor functors are
exact, the shift comparisons are natural in the fixed variable, and the two shift
directions satisfy Mathlib's Koszul compatibility law.

This two-slot contract is what kernel variation actually needs.  A fixed Fourier--Mukai
transform consumes exactness in the second tensor variable, whereas varying the kernel
and taking its cone consumes exactness in the first.  Independent one-slot witnesses
would not supply the required global naturality.

No monoidal structure is asked for: not associativity, not symmetry, not a unit.
`Correspondence` uses none of them, and `FourierMukai/Basic.lean`'s own docstring is
explicit that it assumes none.

**Nothing inhabits this class.**  In particular it is not a theorem here that
`Dᵇ(Coh Z)` is closed under derived tensor; on a singular `Z` it is not. -/
class HasDerivedTensor (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left] where
  /-- The derived tensor bifunctor. -/
  derivedTensor :
    SchemeBoundedCoherentDerivedCategory Z.left ⥤
      SchemeBoundedCoherentDerivedCategory Z.left ⥤
        SchemeBoundedCoherentDerivedCategory Z.left
  /-- Exactness and coherent shift behavior in both tensor variables. -/
  exact : Functor.ExactBifunctor derivedTensor

namespace HasDerivedTensor

variable {Z : SchemeBaseChange S} [IsLocallyNoetherian Z.left]
  [HasDerivedTensor Z]

/-- The exact-bifunctor witness selected by the derived tensor contract. -/
def exactBifunctor : Functor.ExactBifunctor (HasDerivedTensor.derivedTensor (Z := Z)) :=
  HasDerivedTensor.exact

/-- Exactness of the family obtained by varying the first (kernel) input. -/
noncomputable def firstFamily :
    Functor.ExactFamily (HasDerivedTensor.derivedTensor (Z := Z)) :=
  exactBifunctor |>.firstFamily

/-- Exactness of the family obtained by varying the second input. -/
noncomputable def secondFamily :
    Functor.ExactFamily (HasDerivedTensor.derivedTensor (Z := Z)).flip :=
  exactBifunctor |>.secondFamily

/-- A fixed first input gives a shift-coherent partial tensor functor. -/
@[reducible] noncomputable def commShift
    (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((HasDerivedTensor.derivedTensor (Z := Z)).obj K).CommShift ℤ :=
  exactBifunctor |>.secondCommShift K

/-- A fixed first input gives a triangulated partial tensor functor. -/
theorem isTriangulated (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    letI := commShift K
    ((HasDerivedTensor.derivedTensor (Z := Z)).obj K).IsTriangulated :=
  exactBifunctor |>.secondTriangulated K

/-- A fixed first input gives an additive partial tensor functor. -/
theorem additive (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((HasDerivedTensor.derivedTensor (Z := Z)).obj K).Additive := by
  letI := commShift K
  letI := isTriangulated K
  infer_instance

/-- A fixed second input gives a shift-coherent partial tensor functor. -/
@[reducible] noncomputable def flipCommShift
    (E : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((HasDerivedTensor.derivedTensor (Z := Z)).flip.obj E).CommShift ℤ :=
  exactBifunctor |>.firstCommShift E

/-- A fixed second input gives a triangulated partial tensor functor. -/
theorem flipIsTriangulated (E : SchemeBoundedCoherentDerivedCategory Z.left) :
    letI := flipCommShift E
    ((HasDerivedTensor.derivedTensor (Z := Z)).flip.obj E).IsTriangulated :=
  exactBifunctor |>.firstTriangulated E

/-- A fixed second input gives an additive partial tensor functor. -/
theorem flipAdditive (E : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((HasDerivedTensor.derivedTensor (Z := Z)).flip.obj E).Additive := by
  letI := flipCommShift E
  letI := flipIsTriangulated E
  infer_instance

end HasDerivedTensor

/-- The derived tensor bifunctor, named. -/
def derivedTensor (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left]
    [HasDerivedTensor Z] :
    SchemeBoundedCoherentDerivedCategory Z.left ⥤
      SchemeBoundedCoherentDerivedCategory Z.left ⥤
        SchemeBoundedCoherentDerivedCategory Z.left :=
  HasDerivedTensor.derivedTensor

instance derivedTensor_additive (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left]
    [HasDerivedTensor Z] (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((derivedTensor Z).obj K).Additive := by
  dsimp [derivedTensor]
  exact HasDerivedTensor.additive K

noncomputable instance derivedTensorCommShift (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left]
    [HasDerivedTensor Z] (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((derivedTensor Z).obj K).CommShift ℤ := by
  dsimp [derivedTensor]
  exact HasDerivedTensor.commShift K

instance derivedTensor_isTriangulated (Z : SchemeBaseChange S) [IsLocallyNoetherian Z.left]
    [HasDerivedTensor Z] (K : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((derivedTensor Z).obj K).IsTriangulated := by
  dsimp [derivedTensor]
  exact HasDerivedTensor.isTriangulated K

noncomputable instance derivedTensorFlipCommShift (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasDerivedTensor Z]
    (E : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((derivedTensor Z).flip.obj E).CommShift ℤ := by
  dsimp [derivedTensor]
  exact HasDerivedTensor.flipCommShift E

instance derivedTensorFlip_isTriangulated (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasDerivedTensor Z]
    (E : SchemeBoundedCoherentDerivedCategory Z.left) :
    ((derivedTensor Z).flip.obj E).IsTriangulated := by
  dsimp [derivedTensor]
  exact HasDerivedTensor.flipIsTriangulated E

/-- The derived tensor bifunctor with its exactness in both variables exposed. -/
noncomputable def derivedTensorExactBifunctor (Z : SchemeBaseChange S)
    [IsLocallyNoetherian Z.left] [HasDerivedTensor Z] :
    Functor.ExactBifunctor (derivedTensor Z) :=
  HasDerivedTensor.exactBifunctor

end AlgebraicGeometry.DerivedCategory.FourierMukai

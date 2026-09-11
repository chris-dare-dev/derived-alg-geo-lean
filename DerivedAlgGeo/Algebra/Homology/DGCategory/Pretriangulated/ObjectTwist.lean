/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Copower
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.NaturalTransformationCone

/-!
# The twist of an object

The Seidel--Thomas twist of an object `E` is the cone of the evaluation map

`RHom(E,X) ⊗ E ⟶ X`.

`EvaluationData E` is a choice of the tensoring for every `X`, its `functor` is
`RHom(E,-) ⊗ E`, and its `evaluation` is the degree-zero transformation to the
identity.  `evaluation_isClosed` is what this construction needs: a closed
degree-zero transformation has objectwise cones, and those cones assemble to a
dg endofunctor exactly as the counit's do for an adjunction.

## Why this is a second twist, not a duplicate of the first

`DGAdjunction.CounitConeData.twist` is the cone of an adjunction counit
`L R ⟶ id`.  This one is the cone of a transformation attached to a single
*object*, with no adjunction in sight.  The two agree when `RHom(E,-)` and
`- ⊗ E` are the adjoint pair of a spherical functor out of `Perf(k)`, but the
repository has no `Perf(k)` as a dg category, so that comparison cannot be
stated here and is not attempted.  What the object form buys is that it is
available now, from an `EvaluationData` alone.

## What is claimed, and what is not

The cone exists, is a dg endofunctor, and receives the canonical inclusion from
the identity.  Nothing here says the twist is an autoequivalence, calls `E`
spherical, or connects it to `SerreFunctor.IsSphericalObject`; those are the
seams the roadmap records.  Exactness is separate and lives with the
capabilities in `ConeExactness.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace EvaluationData

variable {C : Type u} [DGCategory.{v} C] {E : C} (V : EvaluationData E)

/-- Chosen objectwise cones of the evaluation map `RHom(E,X) ⊗ E ⟶ X`. -/
abbrev TwistConeData :=
  DGFunctor.HomogeneousNatTrans.ConeData V.evaluation

/-- A pretriangulated category supplies cones of all evaluation components. -/
noncomputable def chosenTwistConeData [IsPretriangulated C] :
    V.TwistConeData :=
  DGFunctor.HomogeneousNatTrans.chosenConeData V.evaluation V.evaluation_isClosed

namespace TwistConeData

variable {V} (K : V.TwistConeData)

/-- **The twist of the object `E`**: the dg endofunctor `Cone(RHom(E,-) ⊗ E ⟶ id)`. -/
noncomputable abbrev twist : DGFunctor C C := K.functor

/-- The canonical closed transformation `id ⟶ T_E`. -/
noncomputable abbrev inclusion :
    DGFunctor.HomogeneousNatTrans (DGFunctor.id C) K.twist 0 :=
  K.inr

theorem inclusion_isClosed :
    DGFunctor.HomogeneousNatTrans.IsClosed K.inclusion :=
  K.inr_isClosed

end TwistConeData

end EvaluationData

end CategoryTheory

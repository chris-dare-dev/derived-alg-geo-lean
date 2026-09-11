/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Copower
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ConeExactness

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
seams the roadmap records.  ## Exactness, and what it reduces to

`ConeData.preservesShifts` and `preservesChosenCones` say a cone functor carries
a capability as soon as both of its ends do.  Here the ends are `RHom(E,-) ⊗ E`
and the identity, and the identity's capabilities are free, so the twist's
exactness reduces to the evaluation functor's -- `preservesShifts` and
`preservesChosenCones` below take exactly that one hypothesis.

The shift half needs no hypothesis at all.  `DGFunctor.preservesShifts` says
every dg functor preserves shifts -- a shift element is a two-sided invertible
element, and dg functors preserve composition and identities -- so
`preservesShifts` below is unconditional.  This has nothing to do with copowers;
it would hold for any `F` in place of `RHom(E,-) ⊗ E`.

The cone half does need one.  `PreservesChosenCones` asks that maps *into* the
cone split, which is a mapping-in condition, while `IsCopowerOf` is a
mapping-out property: it controls degree-`p` morphisms out of `V.obj X`, as
cochains out of `dgHom E X`.  Nothing in the universal property the copower is
given by says anything about maps into it, so `preservesChosenCones` takes the
capability for `V.functor` as an argument and leaves discharging it open.
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

/-- **The object twist preserves shifts.**

Half of exactness, and unconditional: `DGFunctor.preservesShifts` supplies the
capability for both ends of the cone.  The cone half is
`preservesChosenCones`, which is not free. -/
noncomputable def preservesShifts : DGFunctor.PreservesShifts K.twist :=
  DGFunctor.preservesShifts _

/-- **The object twist preserves chosen cones as soon as `RHom(E,-) ⊗ E` does.**

The 3-by-3 lemma with the identity as one of the two ends. -/
noncomputable def preservesChosenCones
    (hV : DGFunctor.PreservesChosenCones V.functor) :
    DGFunctor.PreservesChosenCones K.twist :=
  DGFunctor.HomogeneousNatTrans.ConeData.preservesChosenCones K hV
    (DGFunctor.PreservesChosenCones.id C)

end TwistConeData

end EvaluationData

end CategoryTheory

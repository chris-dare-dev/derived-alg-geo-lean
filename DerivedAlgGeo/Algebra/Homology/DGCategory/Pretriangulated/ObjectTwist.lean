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
available now from evaluation data plus chosen cones, with the cone choices
supplied automatically in a pretriangulated category.

## What is claimed, and what is not

The cone exists, is a dg endofunctor, and receives the canonical inclusion from
the identity.  Its dg-functor isomorphism class is independent of both the
evaluation data and the objectwise cone choices; the canonical comparisons
commute strictly with the inclusions and satisfy identity and composition
coherence.  Nothing here says the twist is an autoequivalence, calls `E`
spherical, or connects it to `SerreFunctor.IsSphericalObject`; those are the
seams the roadmap records.

## Exactness, and what it reduces to

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

/-- Cone preservation for the evaluation functor is independent of the
selected evaluation data.  This is deliberately not an instance: the
capability remains explicit input to object-twist exactness. -/
noncomputable def preservesChosenConesOfCompare (W : EvaluationData E)
    (hV : DGFunctor.PreservesChosenCones V.functor) :
    DGFunctor.PreservesChosenCones W.functor :=
  DGFunctor.PreservesChosenCones.ofIso hV (compareIso V W)

/-- The canonical comparison between evaluation functors and the identity on
the target form a strictly commuting square of dg natural transformations. -/
lemma compare_evaluation_square (W : EvaluationData E) :
    DGFunctor.HomogeneousNatTrans.composition V.functor (DGFunctor.id C)
        (DGFunctor.id C) 0 0 0 (by omega) V.evaluation
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) =
      DGFunctor.HomogeneousNatTrans.composition V.functor W.functor
        (DGFunctor.id C) 0 0 0 (by omega) (compare V W) W.evaluation :=
  (dgComp_id (C := DGFunctor C C) 0 V.evaluation).trans
    (compare_comp_evaluation V W).symm

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

/-- The object-twist dg functor is independent, up to a canonical closed
degree-zero isomorphism, of both the evaluation data and the chosen cones. -/
noncomputable def compareIso {W : EvaluationData E}
    (L : W.TwistConeData) :
    (show Z0 (DGFunctor C C) from K.twist) ≅
      (show Z0 (DGFunctor C C) from L.twist) :=
  DGFunctor.HomogeneousNatTrans.ConeData.isoOfStrictSquare K L
    (EvaluationData.compareIso V W)
    (Iso.refl (show Z0 (DGFunctor C C) from DGFunctor.id C))
    (V.compare_evaluation_square W)

@[simp]
lemma compareIso_hom_val {W : EvaluationData E} (L : W.TwistConeData) :
    (K.compareIso L).hom.val =
      K.isConeOf.lift L.isConeOf (EvaluationData.compare V W)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0 :=
  rfl

@[simp]
lemma compareIso_inv_val {W : EvaluationData E} (L : W.TwistConeData) :
    (K.compareIso L).inv.val =
      L.isConeOf.lift K.isConeOf (EvaluationData.compare W V)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0 :=
  rfl

/-- The canonical twist comparison strictly commutes with the inclusions from
the identity functor. -/
lemma inclusion_comp_compareIso_hom_val {W : EvaluationData E}
    (L : W.TwistConeData) :
    DGFunctor.HomogeneousNatTrans.composition (DGFunctor.id C) K.twist L.twist
        0 0 0 (by omega) K.inclusion (K.compareIso L).hom.val =
      L.inclusion := by
  rw [compareIso]
  refine (DGFunctor.HomogeneousNatTrans.ConeData.inr_comp_isoOfStrictSquare_hom
    K L (EvaluationData.compareIso V W)
      (Iso.refl (show Z0 (DGFunctor C C) from DGFunctor.id C))
      (V.compare_evaluation_square W)).trans ?_
  exact dgId_comp (C := DGFunctor C C) 0 L.inclusion

/-- The canonical twist comparison from a cone choice to itself is strictly
the identity homogeneous natural transformation. -/
@[simp]
lemma compareIso_self_hom_val :
    (K.compareIso K).hom.val =
      DGFunctor.HomogeneousNatTrans.id K.twist := by
  rw [compareIso_hom_val, EvaluationData.compare_self]
  exact K.isConeOf.homogeneousLift_id

/-- The canonical twist comparison from a choice to itself is the identity
isomorphism. -/
@[simp]
lemma compareIso_self :
    K.compareIso K = Iso.refl _ := by
  apply Iso.ext
  apply Subtype.ext
  exact K.compareIso_self_hom_val

/-- Canonical twist comparisons compose strictly at the level of their
underlying homogeneous natural transformations. -/
lemma compareIso_hom_val_comp {W X : EvaluationData E}
    (L : W.TwistConeData) (M : X.TwistConeData) :
    DGFunctor.HomogeneousNatTrans.composition K.twist L.twist M.twist
        0 0 0 (by omega) (K.compareIso L).hom.val
        (L.compareIso M).hom.val =
      (K.compareIso M).hom.val := by
  rw [compareIso_hom_val, compareIso_hom_val, compareIso_hom_val]
  change DGCategoryStruct.dgComp 0 0 (0 + 0) (by omega)
      (K.isConeOf.homogeneousLift L.isConeOf 0
        (EvaluationData.compare V W)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0)
      (L.isConeOf.homogeneousLift M.isConeOf 0
        (EvaluationData.compare W X)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0) =
    K.isConeOf.homogeneousLift M.isConeOf 0
      (EvaluationData.compare V X)
      (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0
  rw [K.isConeOf.homogeneousLift_strict_comp L.isConeOf M.isConeOf 0 0]
  change K.isConeOf.homogeneousLift M.isConeOf 0
      (DGFunctor.HomogeneousNatTrans.composition V.functor W.functor X.functor
        0 0 0 (by omega) (EvaluationData.compare V W)
        (EvaluationData.compare W X))
      (DGFunctor.HomogeneousNatTrans.composition (DGFunctor.id C)
        (DGFunctor.id C) (DGFunctor.id C) 0 0 0 (by omega)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C))
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C))) 0 =
    K.isConeOf.homogeneousLift M.isConeOf 0
      (EvaluationData.compare V X)
      (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0
  rw [EvaluationData.compare_comp]
  change K.isConeOf.homogeneousLift M.isConeOf 0
      (EvaluationData.compare V X)
      (DGFunctor.HomogeneousNatTrans.composition (DGFunctor.id C)
        (DGFunctor.id C) (DGFunctor.id C) 0 0 0 (by omega)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C))
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C))) 0 =
    K.isConeOf.homogeneousLift M.isConeOf 0
      (EvaluationData.compare V X)
      (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0
  have hid :
      DGFunctor.HomogeneousNatTrans.composition (DGFunctor.id C)
        (DGFunctor.id C) (DGFunctor.id C) 0 0 0 (by omega)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C))
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) =
      DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C) := by
    exact dgId_comp (C := DGFunctor C C) 0 _
  rw [hid]

/-- Canonical twist comparison isomorphisms are transitive. -/
lemma compareIso_trans {W X : EvaluationData E}
    (L : W.TwistConeData) (M : X.TwistConeData) :
    (K.compareIso L).trans (L.compareIso M) = K.compareIso M := by
  apply Iso.ext
  apply Subtype.ext
  exact K.compareIso_hom_val_comp L M

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

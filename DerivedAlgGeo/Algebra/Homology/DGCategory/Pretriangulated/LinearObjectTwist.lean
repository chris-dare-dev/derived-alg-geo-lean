/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearEvaluation
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ConeExactness

/-!
# The object twist from scalar-linear evaluation data

The cone of the scalar-linear evaluation map

`DGLinear.homComplex k E X ⊗ₖ E ⟶ X`

is the direct scalar-linear version of the Seidel--Thomas object twist.  This
file only packages the existing generic cone interface under
`LinearEvaluationData.TwistConeData`.  In particular, the cone construction,
choice comparison, shift preservation, and chosen-cone preservation all remain
owned by the generic `HomogeneousNatTrans.ConeData` layer.

No comparison with additive `EvaluationData` is asserted: the two evaluation
packages represent different universal properties.  Nor does this file claim
that the evaluation functor preserves chosen cones or that the resulting twist
is an autoequivalence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace LinearEvaluationData

variable (k : Type w) [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]
  {E : C} (V : LinearEvaluationData k E)

/-- Cone preservation for scalar-linear evaluation is independent of the
selected evaluation data.  This remains explicit rather than an instance. -/
noncomputable def preservesChosenConesOfCompare (W : LinearEvaluationData k E)
    (hV : DGFunctor.PreservesChosenCones V.functor) :
    DGFunctor.PreservesChosenCones W.functor :=
  DGFunctor.PreservesChosenCones.ofIso hV (compareIso V W)

/-- The canonical scalar-linear evaluation comparison and the identity on the
target form a strictly commuting square. -/
lemma compare_evaluation_square (W : LinearEvaluationData k E) :
    DGFunctor.HomogeneousNatTrans.composition V.functor (DGFunctor.id C)
        (DGFunctor.id C) 0 0 0 (by omega) V.evaluation
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) =
      DGFunctor.HomogeneousNatTrans.composition V.functor W.functor
        (DGFunctor.id C) 0 0 0 (by omega) (compare V W) W.evaluation :=
  (dgComp_id (C := DGFunctor C C) 0 V.evaluation).trans
    (compare_comp_evaluation V W).symm

/-- Chosen objectwise cones of scalar-linear evaluation. -/
abbrev TwistConeData :=
  DGFunctor.HomogeneousNatTrans.ConeData V.evaluation

/-- A pretriangulated category supplies cones of all scalar-linear evaluation
components. -/
noncomputable def chosenTwistConeData [IsPretriangulated C] :
    V.TwistConeData k :=
  DGFunctor.HomogeneousNatTrans.chosenConeData V.evaluation V.evaluation_isClosed

namespace TwistConeData

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]
  {E : C} {V : LinearEvaluationData k E} (K : V.TwistConeData k)

/-- The scalar-linear object twist: the cone of evaluation. -/
noncomputable abbrev twist : DGFunctor C C := K.functor

/-- The scalar-linear object twist is independent, up to a canonical closed
degree-zero isomorphism, of both the evaluation data and the cone choices. -/
noncomputable def compareIso {W : LinearEvaluationData k E}
    (L : W.TwistConeData k) :
    (show Z0 (DGFunctor C C) from K.twist) ≅
      (show Z0 (DGFunctor C C) from L.twist) :=
  DGFunctor.HomogeneousNatTrans.ConeData.isoOfStrictSquare K L
    (LinearEvaluationData.compareIso V W)
    (Iso.refl (show Z0 (DGFunctor C C) from DGFunctor.id C))
    (V.compare_evaluation_square k W)

/-- The forward cone comparison is the generic lift of the evaluation
comparison and the identity target map. -/
@[simp]
lemma compareIso_hom_val {W : LinearEvaluationData k E}
    (L : W.TwistConeData k) :
    (K.compareIso L).hom.val =
      K.isConeOf.lift L.isConeOf (LinearEvaluationData.compare V W)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0 :=
  rfl

/-- Exposing the inverse as the reverse strict-square lift lets downstream
coherence proofs avoid unfolding `isoOfStrictSquare`. -/
@[simp]
lemma compareIso_inv_val {W : LinearEvaluationData k E}
    (L : W.TwistConeData k) :
    (K.compareIso L).inv.val =
      L.isConeOf.lift K.isConeOf (LinearEvaluationData.compare W V)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0 :=
  rfl

/-- The scalar-linear twist comparison from a cone choice to itself is
strictly the identity homogeneous natural transformation. -/
lemma compareIso_self_hom_val :
    (K.compareIso K).hom.val =
      DGFunctor.HomogeneousNatTrans.id K.twist := by
  rw [compareIso_hom_val, LinearEvaluationData.compare_self]
  exact K.isConeOf.homogeneousLift_id

/-- The scalar-linear twist comparison from a choice to itself is the identity
isomorphism. -/
@[simp]
lemma compareIso_self : K.compareIso K = Iso.refl _ := by
  apply Iso.ext
  apply Subtype.ext
  exact K.compareIso_self_hom_val

/-- Strict composition descends from the corresponding law for linear
evaluation comparisons, so changing choices in stages gives the direct cone
comparison already before passing to `H⁰`. -/
lemma compareIso_hom_val_comp {W X : LinearEvaluationData k E}
    (L : W.TwistConeData k) (M : X.TwistConeData k) :
    DGFunctor.HomogeneousNatTrans.composition K.twist L.twist M.twist
        0 0 0 (by omega) (K.compareIso L).hom.val
        (L.compareIso M).hom.val =
      (K.compareIso M).hom.val := by
  rw [compareIso_hom_val, compareIso_hom_val, compareIso_hom_val]
  change DGCategoryStruct.dgComp 0 0 (0 + 0) (by omega)
      (K.isConeOf.homogeneousLift L.isConeOf 0
        (LinearEvaluationData.compare V W)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0)
      (L.isConeOf.homogeneousLift M.isConeOf 0
        (LinearEvaluationData.compare W X)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0) =
    K.isConeOf.homogeneousLift M.isConeOf 0
      (LinearEvaluationData.compare V X)
      (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0
  rw [K.isConeOf.homogeneousLift_strict_comp L.isConeOf M.isConeOf 0 0]
  change K.isConeOf.homogeneousLift M.isConeOf 0
      (DGFunctor.HomogeneousNatTrans.composition V.functor W.functor X.functor
        0 0 0 (by omega) (LinearEvaluationData.compare V W)
        (LinearEvaluationData.compare W X))
      (DGFunctor.HomogeneousNatTrans.composition (DGFunctor.id C)
        (DGFunctor.id C) (DGFunctor.id C) 0 0 0 (by omega)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C))
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C))) 0 =
    K.isConeOf.homogeneousLift M.isConeOf 0
      (LinearEvaluationData.compare V X)
      (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0
  rw [LinearEvaluationData.compare_comp]
  change K.isConeOf.homogeneousLift M.isConeOf 0
      (LinearEvaluationData.compare V X)
      (DGFunctor.HomogeneousNatTrans.composition (DGFunctor.id C)
        (DGFunctor.id C) (DGFunctor.id C) 0 0 0 (by omega)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C))
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C))) 0 =
    K.isConeOf.homogeneousLift M.isConeOf 0
      (LinearEvaluationData.compare V X)
      (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0
  have hid :
      DGFunctor.HomogeneousNatTrans.composition (DGFunctor.id C)
        (DGFunctor.id C) (DGFunctor.id C) 0 0 0 (by omega)
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C))
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) =
      DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C) := by
    exact dgId_comp (C := DGFunctor C C) 0 _
  rw [hid]

/-- The strict composition law packages as transitivity of the canonical
isomorphisms in the closed degree-zero dg-functor category. -/
lemma compareIso_trans {W X : LinearEvaluationData k E}
    (L : W.TwistConeData k) (M : X.TwistConeData k) :
    (K.compareIso L).trans (L.compareIso M) = K.compareIso M := by
  apply Iso.ext
  apply Subtype.ext
  exact K.compareIso_hom_val_comp L M

/-- The scalar-linear object twist preserves shifts. -/
noncomputable def preservesShifts : DGFunctor.PreservesShifts K.twist :=
  DGFunctor.preservesShifts _

/-- The scalar-linear object twist preserves chosen cones as soon as its
evaluation endpoint does. -/
noncomputable def preservesChosenCones
    (hV : DGFunctor.PreservesChosenCones V.functor) :
    DGFunctor.PreservesChosenCones K.twist :=
  DGFunctor.HomogeneousNatTrans.ConeData.preservesChosenCones K hV
    (DGFunctor.PreservesChosenCones.id C)

end TwistConeData

end LinearEvaluationData

end CategoryTheory

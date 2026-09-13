/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearCopowerAdjunction
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.AdjunctionCone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.LinearObjectTwist

/-!
# Scalar-linear object twists as adjunction counit twists

When all scalar-linear copowers exist, the selected evaluation transformation
is definitionally the counit of the copower--Hom dg adjunction.  Consequently
its cone data is already `DGAdjunction.CounitConeData`; no transport or second
cone construction is needed.

An arbitrary `LinearEvaluationData` choice need not be definitionally the
selected one.  Its canonical evaluation comparison forms a strict square with
the adjunction counit, so the existing cone comparison identifies the two
twist functors in `Z⁰`.  The comparison commutes strictly with the canonical
inclusion and coheres with changes of scalar-linear evaluation data.

This is an identification of twist candidates.  It does not construct
`Perf(k)`, restrict the source of the adjunction, produce an adjoint on the
other side, or assert sphericality or invertibility.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable (k : Type w) [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HasLinearCopowers k C]

/-- The selected scalar-linear evaluation cone data and the counit cone data
of the copower--Hom dg adjunction are definitionally the same type. -/
theorem linearCopowerAdjunction_counitConeData_eq (E : C) :
    (linearCopowerAdjunction k E).CounitConeData =
      (LinearEvaluationData.ofHasLinearCopowers k E).TwistConeData k :=
  rfl

namespace LinearEvaluationData.TwistConeData

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HasLinearCopowers k C]
  {E : C} {V : LinearEvaluationData k E} (K : V.TwistConeData k)

/-- The canonical `Z⁰` identification of a scalar-linear object twist with
a counit-cone twist of the selected copower--Hom dg adjunction. -/
noncomputable def adjunctionTwistIso
    (L : (linearCopowerAdjunction k E).CounitConeData) :
    (show Z0 (DGFunctor C C) from K.twist) ≅
      (show Z0 (DGFunctor C C) from
        DGAdjunction.CounitConeData.twist (linearCopowerAdjunction k E) L) :=
  K.compareIso L

/-- The adjunction-twist comparison is exactly the existing canonical cone
comparison to the selected scalar-linear evaluation data. -/
theorem adjunctionTwistIso_eq_compareIso
    (L : (linearCopowerAdjunction k E).CounitConeData) :
    K.adjunctionTwistIso L = K.compareIso L :=
  rfl

/-- The forward adjunction-twist comparison is the strict cone lift of the
canonical evaluation comparison and the identity target map. -/
theorem adjunctionTwistIso_hom_val
    (L : (linearCopowerAdjunction k E).CounitConeData) :
    (K.adjunctionTwistIso L).hom.val =
      K.isConeOf.lift L.isConeOf
        (LinearEvaluationData.compare V
          (LinearEvaluationData.ofHasLinearCopowers k E))
        (DGFunctor.HomogeneousNatTrans.id (DGFunctor.id C)) 0 :=
  rfl

/-- The adjunction-twist identification strictly preserves the canonical map
from the identity functor into the cone. -/
theorem inclusion_comp_adjunctionTwistIso_hom_val
    (L : (linearCopowerAdjunction k E).CounitConeData) :
    DGFunctor.HomogeneousNatTrans.composition (DGFunctor.id C) K.twist
        (DGAdjunction.CounitConeData.twist (linearCopowerAdjunction k E) L)
        0 0 0 (by omega) K.inr
        (K.adjunctionTwistIso L).hom.val =
      DGAdjunction.CounitConeData.inclusion
        (linearCopowerAdjunction k E) L :=
  K.inclusion_comp_compareIso_hom_val L

/-- For the selected evaluation data and the same cone choice, the
object-twist/adjunction-twist identification is the identity. -/
theorem adjunctionTwistIso_self
    (K : (LinearEvaluationData.ofHasLinearCopowers k E).TwistConeData k) :
    K.adjunctionTwistIso K = Iso.refl _ :=
  K.compareIso_self

/-- For the selected evaluation data, the object-twist functor and the
adjunction counit-twist functor are definitionally identical. -/
theorem twist_eq_adjunctionTwist
    (K : (LinearEvaluationData.ofHasLinearCopowers k E).TwistConeData k) :
    K.twist = DGAdjunction.CounitConeData.twist
      (linearCopowerAdjunction k E) K :=
  rfl

/-- Changing arbitrary scalar-linear evaluation data before comparing with
the adjunction twist gives the direct adjunction-twist comparison. -/
theorem compareIso_trans_adjunctionTwistIso
    {W : LinearEvaluationData k E} (L : W.TwistConeData k)
    (M : (linearCopowerAdjunction k E).CounitConeData) :
    (K.compareIso L).trans (L.adjunctionTwistIso M) =
      K.adjunctionTwistIso M :=
  K.compareIso_trans L M

end LinearEvaluationData.TwistConeData

end CategoryTheory

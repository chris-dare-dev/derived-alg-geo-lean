/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.FunctorCategoryH0
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.AdjunctionCone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.NaturalTransformationShift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Whiskering

/-!
# Canonical adjunction comparison maps from dg cones

Let `S : A ⟶ B` have a left dg adjoint `L` and a right dg adjoint `R`.
The counit cone of `S ⊣ R` and the unit cone of `L ⊣ S` determine the two
standard comparison maps

`L T[-1] ⟶ R` and `R ⟶ C L`,

where `T = Cone(S R ⟶ 𝟭)` and `C = Cone(𝟭 ⟶ R S)`.  This file constructs
their closed degree-zero dg representatives and their images in `H⁰`.

The first construction is why source-shift regrading is the right primitive:
the closed degree-one projection `T ⟶ S R` becomes `T[-1] ⟶ S R` in degree
zero before applying `L`.  Thus no shift-preservation comparison for `L` is
needed.

No invertibility is claimed here.  Whether either induced `H⁰` map is an
isomorphism is additional spherical-functor data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGAdjunction

variable {A : Type u} {B : Type u'}
  [DGCategory.{v} A] [DGCategory.{v} B]
  {S : DGFunctor A B} {L R : DGFunctor B A}

namespace CounitConeData

variable (leftAdj : DGAdjunction L S) (rightAdj : DGAdjunction S R)
  (K : rightAdj.CounitConeData) [IsPretriangulated B]

/-- The canonical comparison `L T[-1] ⟶ R` associated to the twist cone
`T = Cone(S R ⟶ 𝟭_B)`.

It is the degree-zero source regrading of the cone projection `T ⟶ S R`,
postcomposed with `L`, followed by the counit `L S ⟶ 𝟭_A` evaluated after
`R`. -/
noncomputable def twistAdjointComparison :
    DGFunctor.HomogeneousNatTrans
      ((K.twist.shiftedFunctor (-1 : ℤ)).comp L) R 0 :=
  let counitWhisker : DGFunctor.HomogeneousNatTrans
      ((R.comp S).comp L) R 0 :=
    DGFunctor.HomogeneousNatTrans.whiskerLeft R leftAdj.counit
  DGFunctor.HomogeneousNatTrans.comp
    (DGFunctor.HomogeneousNatTrans.whiskerRight
      (DGFunctor.HomogeneousNatTrans.sourceShiftEquiv K.twist (R.comp S)
        (-1 : ℤ) 1 0 (by omega) K.fst) L)
    counitWhisker

/-- The objectwise formula for the twist adjunction comparison. -/
theorem twistAdjointComparison_app (X : B) :
    DGFunctor.HomogeneousNatTrans.app
        (twistAdjointComparison (rightAdj := rightAdj) leftAdj K) X =
      dgComp 0 0 0 (by omega)
        (L.map 0 (dgComp (-1) 1 0 (by omega)
          (K.twist.shiftWitness (-1 : ℤ) X).inv
          (DGFunctor.HomogeneousNatTrans.app K.fst X)))
        (DGFunctor.HomogeneousNatTrans.app leftAdj.counit (R.obj X)) := by
  change dgComp 0 0 0 (by omega)
      (L.map 0 (DGFunctor.HomogeneousNatTrans.app
        (DGFunctor.HomogeneousNatTrans.sourceShiftEquiv K.twist (R.comp S)
          (-1 : ℤ) 1 0 (by omega) K.fst) X))
      (DGFunctor.HomogeneousNatTrans.app leftAdj.counit (R.obj X)) = _
  rw [DGFunctor.HomogeneousNatTrans.sourceShiftEquiv_apply_app]
  congr

/-- The twist adjunction comparison is a closed degree-zero transformation. -/
theorem twistAdjointComparison_isClosed :
    DGFunctor.HomogeneousNatTrans.IsClosed
      (twistAdjointComparison (rightAdj := rightAdj) leftAdj K) := by
  apply DGFunctor.isClosed_of_mem_cocycles
  apply Z0.comp_mem
  · apply DGFunctor.mem_cocycles_of_isClosed
    apply DGFunctor.HomogeneousNatTrans.IsClosed.whiskerRight
    exact (DGFunctor.HomogeneousNatTrans.sourceShiftEquiv_isClosed_iff
      K.twist (R.comp S) (-1 : ℤ) 1 0 (by omega) K.fst).2 K.fst_isClosed
  · apply DGFunctor.mem_cocycles_of_isClosed
    exact leftAdj.counit_isClosed.whiskerLeft R

/-- The twist adjunction comparison as an ordinary natural transformation on
`H⁰`. -/
noncomputable def twistAdjointComparisonH0 :
    ((K.twist.shiftedFunctor (-1 : ℤ)).comp L).h0 ⟶ R.h0 :=
  DGFunctor.HomogeneousNatTrans.h0
    (twistAdjointComparison (rightAdj := rightAdj) leftAdj K)
    (twistAdjointComparison_isClosed (rightAdj := rightAdj) leftAdj K)

end CounitConeData

namespace UnitConeData

variable (leftAdj : DGAdjunction L S) (rightAdj : DGAdjunction S R)
  (K : rightAdj.UnitConeData)

/-- The canonical comparison `R ⟶ C L` associated to the unit cone
`C = Cone(𝟭_A ⟶ R S)`.

It is the unit `𝟭_B ⟶ S L` postcomposed with `R`, followed by the target
inclusion `R S ⟶ C` evaluated after `L`. -/
noncomputable def cotwistAdjointComparison :
    DGFunctor.HomogeneousNatTrans R (L.comp K.unitCone) 0 :=
  let inclusionWhisker : DGFunctor.HomogeneousNatTrans
      ((L.comp S).comp R) (L.comp K.functor) 0 :=
    DGFunctor.HomogeneousNatTrans.whiskerLeft L K.inr
  DGFunctor.HomogeneousNatTrans.comp
    (DGFunctor.HomogeneousNatTrans.whiskerRight leftAdj.unit R)
    inclusionWhisker

/-- The objectwise formula for the cotwist adjunction comparison. -/
theorem cotwistAdjointComparison_app (X : B) :
    DGFunctor.HomogeneousNatTrans.app
        (cotwistAdjointComparison (rightAdj := rightAdj) leftAdj K) X =
      dgComp 0 0 0 (by omega)
        (R.map 0 (DGFunctor.HomogeneousNatTrans.app leftAdj.unit X))
        (DGFunctor.HomogeneousNatTrans.app K.inr (L.obj X)) :=
  rfl

/-- The cotwist adjunction comparison is a closed degree-zero
transformation. -/
theorem cotwistAdjointComparison_isClosed :
    DGFunctor.HomogeneousNatTrans.IsClosed
      (cotwistAdjointComparison (rightAdj := rightAdj) leftAdj K) := by
  apply DGFunctor.isClosed_of_mem_cocycles
  apply Z0.comp_mem
  · apply DGFunctor.mem_cocycles_of_isClosed
    exact leftAdj.unit_isClosed.whiskerRight R
  · apply DGFunctor.mem_cocycles_of_isClosed
    exact K.inr_isClosed.whiskerLeft L

/-- The cotwist adjunction comparison as an ordinary natural transformation
on `H⁰`. -/
noncomputable def cotwistAdjointComparisonH0 :
    R.h0 ⟶ (L.comp K.unitCone).h0 :=
  DGFunctor.HomogeneousNatTrans.h0
    (cotwistAdjointComparison (rightAdj := rightAdj) leftAdj K)
    (cotwistAdjointComparison_isClosed (rightAdj := rightAdj) leftAdj K)

end UnitConeData

end DGAdjunction

end CategoryTheory

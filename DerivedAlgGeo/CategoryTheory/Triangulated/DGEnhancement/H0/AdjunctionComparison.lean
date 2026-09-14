/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.AdjunctionComparison
import DerivedAlgGeo.Algebra.Homology.DGCategory.AdjunctionH0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.NaturalTransformationConeShift
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ShiftedFunctor

/-!
# H⁰ coherence and conventional shifted targets for dg-adjunction comparisons

For the twist comparison, this file first identifies the descended dg
composite with the inverse-rotated first map, right-whiskered by the left
adjoint and followed by the descended left counit.  It then normalizes that
last raw dg whisker to ordinary left whiskering of the `H⁰` counit, with the
canonical compositor, associator, and unitor.  Both factorizations use generic
descent coherence rather than an adjunction-specific comparison map.

The strict dg cone construction gives the cotwist comparison in the
shift-free form

`R ⟶ C L`,

where `C = Cone(𝟭 ⟶ R S)`.  If the conventional cotwist is `F = C[-1]`,
Anno--Logvinenko write the target as `(F L)[1]`.  These are canonically
isomorphic, not definitionally equal: the two successive shifts `[-1][1]`
must be cancelled.

This file performs that normalization through Mathlib's
`shiftFunctorCompIsoId`, using the `HasShift` package on closed dg functors and
then descending its component to `H⁰`.  Thus the result inherits the packaged
addition, zero, unit, and associativity coherence; no second comparison or
paper-specific shift convention is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGAdjunction.CounitConeData

variable {A : Type u} {B : Type u'}
  [DGCategory.{v} A] [DGCategory.{v} B]
  {S : DGFunctor A B} {L R : DGFunctor B A}
  (leftAdj : DGAdjunction L S) (rightAdj : DGAdjunction S R)
  (K : rightAdj.CounitConeData) [IsPretriangulated B]

/-- **The twist adjunction comparison factors through inverse rotation.**

The descended dg comparison is the first map of the inverse-rotated twist
triangle, postcomposed with `L`, followed by the descended left-counit whisker.
The two `h0CompIso` terms are the canonical compositor needed to pass between
`H⁰` of a dg composite and the composite of its `H⁰` functors. -/
theorem twistAdjointComparisonH0_eq_inverseRotateFirstH0 :
    twistAdjointComparisonH0 (rightAdj := rightAdj) leftAdj K =
      (DGFunctor.h0CompIso (K.twist.shiftedFunctor (-1 : ℤ)) L).hom ≫
        Functor.whiskerRight
          ((K.twist.shiftedFunctorH0Iso (-1)).hom ≫
            K.inverseRotateFirstH0 rightAdj.counit_isClosed) L.h0 ≫
        (DGFunctor.h0CompIso (R.comp S) L).inv ≫
        DGFunctor.HomogeneousNatTrans.h0
          (DGFunctor.HomogeneousNatTrans.whiskerLeft R leftAdj.counit)
          (leftAdj.counit_isClosed.whiskerLeft R) := by
  let η := DGFunctor.HomogeneousNatTrans.sourceShiftEquiv K.twist (R.comp S)
    (-1 : ℤ) 1 0 (by omega) K.fst
  have hη : DGFunctor.HomogeneousNatTrans.IsClosed η :=
    (DGFunctor.HomogeneousNatTrans.sourceShiftEquiv_isClosed_iff K.twist
      (R.comp S) (-1 : ℤ) 1 0 (by omega) K.fst).2 K.fst_isClosed
  have hηL := hη.whiskerRight L
  have hεR := leftAdj.counit_isClosed.whiskerLeft R
  change DGFunctor.HomogeneousNatTrans.h0
      (DGFunctor.HomogeneousNatTrans.comp
        (DGFunctor.HomogeneousNatTrans.whiskerRight η L)
        (DGFunctor.HomogeneousNatTrans.whiskerLeft R leftAdj.counit)) _ = _
  rw [DGFunctor.HomogeneousNatTrans.h0_comp'
    (DGFunctor.HomogeneousNatTrans.whiskerRight η L)
    (DGFunctor.HomogeneousNatTrans.whiskerLeft R leftAdj.counit) hηL hεR]
  rw [DGFunctor.HomogeneousNatTrans.h0_whiskerRight η hη L]
  have hηh0 : DGFunctor.HomogeneousNatTrans.h0 η hη = K.shiftedFstH0 := rfl
  rw [hηh0, K.shiftedFstH0_eq rightAdj.counit_isClosed,
    Functor.whiskerRight_comp]
  simp only [Category.assoc]

/-- **The twist adjunction comparison factors through the ordinary `H⁰`
counit.**

This is the fully normalized form of
`twistAdjointComparisonH0_eq_inverseRotateFirstH0`: the terminal descended
dg whisker has been replaced by ordinary left whiskering of `leftAdj.h0Counit`.
The remaining compositor, associator, and unitor are precisely the canonical
comparison from strict dg composition to ordinary functor composition. -/
theorem twistAdjointComparisonH0_eq_inverseRotateFirstH0_comp_h0Counit :
    twistAdjointComparisonH0 (rightAdj := rightAdj) leftAdj K =
      (DGFunctor.h0CompIso (K.twist.shiftedFunctor (-1 : ℤ)) L).hom ≫
        Functor.whiskerRight
          ((K.twist.shiftedFunctorH0Iso (-1)).hom ≫
            K.inverseRotateFirstH0 rightAdj.counit_isClosed) L.h0 ≫
        Functor.whiskerRight (DGFunctor.h0CompIso R S).hom L.h0 ≫
        (Functor.associator R.h0 S.h0 L.h0).hom ≫
        Functor.whiskerLeft R.h0 leftAdj.h0Counit ≫
        (Functor.rightUnitor R.h0).hom := by
  rw [twistAdjointComparisonH0_eq_inverseRotateFirstH0]
  exact congrArg
    (fun τ =>
      (DGFunctor.h0CompIso (K.twist.shiftedFunctor (-1 : ℤ)) L).hom ≫
        Functor.whiskerRight
          ((K.twist.shiftedFunctorH0Iso (-1)).hom ≫
            K.inverseRotateFirstH0 rightAdj.counit_isClosed) L.h0 ≫ τ)
    (leftAdj.h0_whiskerLeft_counit R)

end DGAdjunction.CounitConeData

namespace DGAdjunction.UnitConeData

variable {A : Type u} {B : Type u'}
  [DGCategory.{v} A] [DGCategory.{v} B]
  {S : DGFunctor A B} {L R : DGFunctor B A}
  (leftAdj : DGAdjunction L S) (rightAdj : DGAdjunction S R)
  (K : rightAdj.UnitConeData) [IsPretriangulated A]

/-- The canonical comparison with the conventional cotwist target
`(C[-1] L)[1]`.

It is the shift-free map `R ⟶ C L`, followed by the inverse of the canonical
cancellation `(C L)[-1][1] ≅ C L`. -/
noncomputable def cotwistAdjointComparisonShiftedH0 :
    R.h0 ⟶
      ((L.comp (K.unitCone.shiftedFunctor (-1 : ℤ))).shiftedFunctor 1).h0 :=
  cotwistAdjointComparisonH0 (rightAdj := rightAdj) leftAdj K ≫
    (DGFunctor.shiftedFunctorCompIsoIdH0 (L.comp K.unitCone)
      (-1 : ℤ) 1 (by omega)).inv

/-- The conventional cotwist comparison is the shift-free comparison followed
by the canonical opposite-shift cancellation. -/
theorem cotwistAdjointComparisonShiftedH0_eq :
    cotwistAdjointComparisonShiftedH0 (rightAdj := rightAdj) leftAdj K =
      cotwistAdjointComparisonH0 (rightAdj := rightAdj) leftAdj K ≫
        (DGFunctor.shiftedFunctorCompIsoIdH0 (L.comp K.unitCone)
          (-1 : ℤ) 1 (by omega)).inv :=
  rfl

end DGAdjunction.UnitConeData

end CategoryTheory

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.AdjunctionComparison
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ShiftedFunctor

/-!
# Conventional shifted targets for dg-adjunction comparisons

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
noncomputable def cotwistAdjointComparisonShifted_h0 :
    R.h0 ⟶
      ((L.comp (K.unitCone.shiftedFunctor (-1 : ℤ))).shiftedFunctor 1).h0 :=
  cotwistAdjointComparison_h0 (rightAdj := rightAdj) leftAdj K ≫
    (DGFunctor.shiftedFunctorCompIsoIdH0 (L.comp K.unitCone)
      (-1 : ℤ) 1 (by omega)).inv

/-- The conventional cotwist comparison is the shift-free comparison followed
by the canonical opposite-shift cancellation. -/
theorem cotwistAdjointComparisonShifted_h0_eq :
    cotwistAdjointComparisonShifted_h0 (rightAdj := rightAdj) leftAdj K =
      cotwistAdjointComparison_h0 (rightAdj := rightAdj) leftAdj K ≫
        (DGFunctor.shiftedFunctorCompIsoIdH0 (L.comp K.unitCone)
          (-1 : ℤ) 1 (by omega)).inv :=
  rfl

end DGAdjunction.UnitConeData

end CategoryTheory

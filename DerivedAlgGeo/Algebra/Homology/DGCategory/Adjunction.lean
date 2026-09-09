/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.NaturalTransformation

/-!
# Adjunctions of dg functors

This is the dg-enriched unit/counit presentation of an adjunction.  The unit
and counit are closed degree-zero homogeneous natural transformations and the
two triangle identities hold before passage to `H⁰`.

The structure is intentionally independent of cones and triangulated
categories.  A counit cone is a downstream construction, not part of what an
adjunction is.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} {D : Type u'}
  [DGCategory.{v} C] [DGCategory.{v} D]

/-- A dg adjunction `L ⊣ R`, presented by closed degree-zero unit and counit
transformations satisfying the triangle identities componentwise. -/
structure DGAdjunction (L : DGFunctor C D) (R : DGFunctor D C) where
  /-- The unit `id_C ⟶ R L`. -/
  unit : DGFunctor.HomogeneousNatTrans (DGFunctor.id C) (L.comp R) 0
  /-- The counit `L R ⟶ id_D`. -/
  counit : DGFunctor.HomogeneousNatTrans (R.comp L) (DGFunctor.id D) 0
  /-- The unit is closed. -/
  unit_isClosed : DGFunctor.HomogeneousNatTrans.IsClosed unit
  /-- The counit is closed. -/
  counit_isClosed : DGFunctor.HomogeneousNatTrans.IsClosed counit
  /-- The triangle identity on the left adjoint. -/
  left_triangle (X : C) :
    dgComp 0 0 0 (by omega)
        (L.map 0 (DGFunctor.HomogeneousNatTrans.app unit X))
        (DGFunctor.HomogeneousNatTrans.app counit (L.obj X)) =
      dgId (L.obj X)
  /-- The triangle identity on the right adjoint. -/
  right_triangle (Y : D) :
    dgComp 0 0 0 (by omega)
        (DGFunctor.HomogeneousNatTrans.app unit (R.obj Y))
        (R.map 0 (DGFunctor.HomogeneousNatTrans.app counit Y)) =
      dgId (R.obj Y)

namespace DGAdjunction

variable {L : DGFunctor C D} {R : DGFunctor D C} (A : DGAdjunction L R)

/-- The endofunctor `R L` appearing as the source of the unit. -/
abbrev unitEndofunctor : DGFunctor C C := L.comp R

/-- The endofunctor `L R` appearing as the source of the counit. -/
abbrev counitEndofunctor : DGFunctor D D := R.comp L

end DGAdjunction

end CategoryTheory

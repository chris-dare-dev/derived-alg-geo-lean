/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Adjunction
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.NaturalTransformationCone

/-!
# Counit cones and twists of dg adjunctions

For a dg adjunction `L ⊣ R`, the twist-side endofunctor is the cone of the
counit

`L R ⟶ id_D`.

This file is only the generic adjunction layer.  It neither assumes that the
result is an autoequivalence nor calls the adjunction spherical.  Those are
additional properties.  Likewise, the usual cotwist is a shift of the cone of
the unit `id_C ⟶ R L`; the unshifted unit cone is exposed here while a
functorial dg shift is left as a separate capability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGAdjunction

variable {C : Type u} {D : Type u'}
  [DGCategory.{v} C] [DGCategory.{v} D]
  {L : DGFunctor C D} {R : DGFunctor D C}
  (A : DGAdjunction L R)

/-- Chosen objectwise cones of the adjunction counit. -/
abbrev CounitConeData :=
  DGFunctor.HomogeneousNatTrans.ConeData A.counit

/-- A pretriangulated target supplies cones of all counit components. -/
noncomputable def chosenCounitConeData [IsPretriangulated D] :
    A.CounitConeData :=
  DGFunctor.HomogeneousNatTrans.chosenConeData A.counit A.counit_isClosed

namespace CounitConeData

variable (K : A.CounitConeData)

/-- The counit-cone dg endofunctor, i.e. the twist candidate associated to
`L ⊣ R`. -/
noncomputable abbrev twist : DGFunctor D D := K.functor

/-- The canonical closed transformation `id_D ⟶ twist`. -/
noncomputable abbrev inclusion :
    DGFunctor.HomogeneousNatTrans (DGFunctor.id D) K.twist 0 :=
  K.inr

/-- The degree-`-1` boundary transformation `L R ⟶ twist`. -/
noncomputable abbrev boundary :
    DGFunctor.HomogeneousNatTrans (R.comp L) K.twist (-1) :=
  K.inl

/-- The twist inclusion is closed. -/
theorem inclusion_isClosed :
    DGFunctor.HomogeneousNatTrans.IsClosed K.inclusion :=
  K.inr_isClosed

/-- The differential of the twist boundary is the counit followed by the
canonical inclusion. -/
theorem differential_boundary :
    DGFunctor.HomogeneousNatTrans.differential K.boundary =
      DGFunctor.HomogeneousNatTrans.comp A.counit K.inclusion :=
  K.differential_inl

end CounitConeData

/-- Chosen objectwise cones of the adjunction unit.  The conventional cotwist
is obtained from this cone by a shift by `-1`. -/
abbrev UnitConeData :=
  DGFunctor.HomogeneousNatTrans.ConeData A.unit

/-- A pretriangulated source supplies cones of all unit components. -/
noncomputable def chosenUnitConeData [IsPretriangulated C] :
    A.UnitConeData :=
  DGFunctor.HomogeneousNatTrans.chosenConeData A.unit A.unit_isClosed

namespace UnitConeData

variable (K : A.UnitConeData)

/-- The unshifted cone of the unit `id_C ⟶ R L`. -/
noncomputable abbrev unitCone : DGFunctor C C := K.functor

end UnitConeData

end DGAdjunction

end CategoryTheory

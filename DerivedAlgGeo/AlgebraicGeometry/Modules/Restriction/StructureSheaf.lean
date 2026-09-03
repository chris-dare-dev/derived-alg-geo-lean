/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The slice equivalences and the structure sheaf

Mathlib's `Scheme.Modules.overEquiv U` identifies sheaves of modules on the slice of the
Zariski site over `U` with module sheaves on the open subscheme `U`.  This file records that
both halves of the equivalence match the structure sheaves, in the shape
`unit ≅ F.obj unit` that `SheafOfModules.Presentation.map` and its relatives take as their
structure-sheaf identification.

## Main definitions

* `overEquivFunctorUnitIso`, `overEquivInverseUnitIso`: the two identifications.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

/-- The structure sheaf of the open subscheme is the image of the slice's structure sheaf under
the slice equivalence.  Stated as `unit ≅ F.obj unit`, the shape `Presentation.map` takes for
its `η`; it is the inverses of `restrictUnitIso` and of `overFunctorEquiv` at the structure
sheaf. -/
def overEquivFunctorUnitIso (U : X.Opens) :
    SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      (overEquiv U).functor.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  (restrictUnitIso U.ι).symm ≪≫
    ((overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)).symm

/-- The slice's structure sheaf is the image of the open subscheme's under the inverse slice
equivalence: `overEquivFunctorUnitIso` transported by the inverse, corrected by the unit of the
equivalence. -/
def overEquivInverseUnitIso (V : X.Opens) :
    SheafOfModules.unit (X.ringCatSheaf.over V) ≅
      (overEquiv V).inverse.obj (SheafOfModules.unit V.toScheme.ringCatSheaf) :=
  (overEquiv V).unitIso.app _ ≪≫ (overEquiv V).inverse.mapIso (overEquivFunctorUnitIso V).symm

end

end AlgebraicGeometry.Scheme.Modules

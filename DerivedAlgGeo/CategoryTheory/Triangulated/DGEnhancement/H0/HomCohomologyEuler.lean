/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.HomCohomology
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import Mathlib.Algebra.Homology.EulerCharacteristic

/-!
# Euler characteristic of a dg Hom-complex

The cohomology of a scalar-linear dg Hom-complex is the family of morphism
spaces into the selected shifts in `H⁰`.  Consequently Mathlib's junk-total
homological Euler characteristic agrees with the repository's junk-total
`chiHom`.  No boundedness or finite-dimensionality hypothesis is needed for
this equality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Triangulated

namespace H0

variable {k : Type w} [Field k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]

/-- The homological Euler characteristic of the dg Hom-complex is the Euler
pairing of the corresponding objects of `H⁰`.  Both sides retain their
existing junk values on infinite support. -/
theorem homComplex_homologyEulerChar_eq_chiHom (X Y : C) :
    (DGLinear.homComplex k X Y).homologyEulerChar =
      chiHom k (H0 C) (show H0 C from X) (show H0 C from Y) := by
  apply finsum_congr
  intro i
  change (i.negOnePow : ℤ) *
      Module.finrank k ((DGLinear.homComplex k X Y).homology i) =
    (i.negOnePow : ℤ) *
      Module.finrank k ((show H0 C from X) ⟶ (show H0 C from Y)⟦i⟧)
  rw [(homologyShiftLinearEquiv (k := k) X Y i).finrank_eq]

end H0

end CategoryTheory

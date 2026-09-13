/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.LinearShiftHomology
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Shift

/-!
# Hom cohomology as morphisms into selected shifts in `H⁰`

For a scalar-linear pretriangulated dg category, the explicit shift comparison
`IsShiftBy.homologyLinearEquiv` specializes to the object selected by the
existing `HasShift (H0 C) ℤ` instance.  Thus

`Hⁿ(dgHom X Y) ≃ₗ[k] Hom_{H⁰ C}(X, Y⟦n⟧)`.

The result asserts no finiteness, formality, Euler characteristic, or `K₀`
formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace H0

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]

/-- Cohomology of a scalar-linear dg Hom-complex as morphisms into the selected
shift in `H⁰`. -/
noncomputable def homologyShiftLinearEquiv (X Y : C) (n : ℤ) :
    ((DGLinear.homComplex k X Y).homology n : Type v) ≃ₗ[k]
      ((show H0 C from X) ⟶ (show H0 C from Y)⟦n⟧) :=
  (IsPretriangulated.shiftWitness C Y n).homologyLinearEquiv (k := k) X

end H0

end CategoryTheory

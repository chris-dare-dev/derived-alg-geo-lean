/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Instances.HomotopyCategory.Pretriangulated
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Instances.HomotopyCategory.Seam

/-!
# `C^dg A` enhances the homotopy category

`Enhancement` is a structure with three fields and no inhabitant until this
file. `dg-enhancements-e6`'s acceptance asks for exactly that — *"it is
inhabited by a constructed example before any theorem quantifies over it"* —
and both halves of the example are already proved:

* `Cdg.isPretriangulated` (`dg-enhancements-e5`) supplies the shift, the cone
  and the zero object;
* `Cdg.seam` (`dg-enhancements-e4`) supplies `H⁰ (C^dg A) ≌ HomotopyCategory A`.

So the enhancement is the two of them adjacent, and it is a `def` with no proof
obligations of its own. That it reads as trivial is the point: the content was
paid for in e4 and e5, and an `Enhancement` that needed new mathematics to
inhabit would mean the structure had been mis-stated.

## This is `C^dg`, not `K^dg`

`dg-enhancements-e7` wants `K^dg(A)` to enhance `HomotopyCategory A` with an
agreement theorem against Mathlib's own triangulated instance. That is a
different and stronger statement. What is here is the enhancement whose
existence e6 needs in order to quantify over enhancements at all.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open CochainComplex Limits

variable (A : Type u) [Category.{v} A] [Preadditive A]
  [HasBinaryBiproducts A] [HasZeroObject A]

/-- `C^dg A` is a dg enhancement of the homotopy category of `A`. -/
noncomputable def Cdg.enhancement :
    Enhancement (HomotopyCategory A (ComplexShape.up ℤ)) where
  dgCat := Cdg A
  equiv := Cdg.seam

end CategoryTheory

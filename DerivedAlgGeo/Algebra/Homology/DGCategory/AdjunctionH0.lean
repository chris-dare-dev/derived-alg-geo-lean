/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Adjunction
import DerivedAlgGeo.Algebra.Homology.DGCategory.NaturalTransformationH0

/-!
# A dg adjunction is an adjunction on `H⁰`

`DGAdjunction L R` carries closed degree-zero unit and counit with the two
triangle identities holding on the nose in the dg category.  Each of those is
exactly what an ordinary `Adjunction` between the induced functors on `H⁰`
asks for, once the components are read as homotopy classes.

This adapter is what makes the dg notion comparable with the rest of the
library: `RightAdjointKernelData` and the Fourier--Mukai layer speak in
Mathlib `Adjunction`s, and without `DGAdjunction.h0` a dg adjunction could
never be offered to them.

## The two identifications are trivial, and that is the point

`H⁰` of the identity dg functor is the identity functor and `H⁰` of a
composite is the composite, both by isomorphisms whose components are
identities (`DGFunctor.h0IdIso`, `DGFunctor.h0CompIso`).  Conjugating by them
changes no component, so the two triangle identities below reduce to
`DGAdjunction.left_triangle` and `DGAdjunction.right_triangle` applied to a
representative, with no homotopy and no sign.

## What this does not say

It does not say that a dg adjunction is *more* than an adjunction on `H⁰`, and
it does not go the other way: an ordinary adjunction between `H⁰ L` and
`H⁰ R` carries no dg unit or counit, and nothing here produces one.  It also
does not relate the strict dg notion to the homotopy adjunctions of
Anno--Logvinenko, whose units and counits are quasi-isomorphisms of bimodules
rather than closed degree-zero transformations; that comparison needs the
Morita framework the roadmap lists as open.
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

/-- The unit of a dg adjunction, read on `H⁰`. -/
noncomputable def h0Unit (A : DGAdjunction L R) : 𝟭 (H0 C) ⟶ L.h0 ⋙ R.h0 :=
  (DGFunctor.h0IdIso).inv ≫
    DGFunctor.HomogeneousNatTrans.h0 A.unit A.unit_isClosed ≫
      (DGFunctor.h0CompIso L R).hom

/-- The counit of a dg adjunction, read on `H⁰`. -/
noncomputable def h0Counit (A : DGAdjunction L R) : R.h0 ⋙ L.h0 ⟶ 𝟭 (H0 D) :=
  (DGFunctor.h0CompIso R L).inv ≫
    DGFunctor.HomogeneousNatTrans.h0 A.counit A.counit_isClosed ≫
      (DGFunctor.h0IdIso).hom

@[simp]
theorem h0Unit_app (A : DGAdjunction L R) (X : H0 C) :
    A.h0Unit.app X =
      H0.homMk (C := C)
        ⟨DGFunctor.HomogeneousNatTrans.app A.unit (H0.of C X),
          A.unit_isClosed.app_mem_cocycles _⟩ := by
  show 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.comp_id, Category.id_comp]
  rfl

@[simp]
theorem h0Counit_app (A : DGAdjunction L R) (Y : H0 D) :
    A.h0Counit.app Y =
      H0.homMk (C := D)
        ⟨DGFunctor.HomogeneousNatTrans.app A.counit (H0.of D Y),
          A.counit_isClosed.app_mem_cocycles _⟩ := by
  show 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.comp_id, Category.id_comp]
  rfl

/-- **A dg adjunction induces an adjunction on `H⁰`.**

The unit and counit are the descended dg transformations, and each triangle
identity is the corresponding dg identity read on a representative. -/
noncomputable def h0 (A : DGAdjunction L R) : L.h0 ⊣ R.h0 where
  unit := A.h0Unit
  counit := A.h0Counit
  left_triangle_components X := by
    rw [h0Unit_app, h0Counit_app]
    show H0.homMk (C := D) _ ≫ H0.homMk (C := D) _ = _
    rw [H0.homMk_comp]
    exact congrArg _ (Subtype.ext (A.left_triangle (H0.of C X)))
  right_triangle_components Y := by
    rw [h0Unit_app, h0Counit_app]
    show H0.homMk (C := C) _ ≫ H0.homMk (C := C) _ = _
    rw [H0.homMk_comp]
    exact congrArg _ (Subtype.ext (A.right_triangle (H0.of D Y)))

@[simp]
theorem h0_unit (A : DGAdjunction L R) : A.h0.unit = A.h0Unit := rfl

@[simp]
theorem h0_counit (A : DGAdjunction L R) : A.h0.counit = A.h0Counit := rfl

end DGAdjunction

end CategoryTheory

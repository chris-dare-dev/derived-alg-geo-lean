/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Adjunction
import DerivedAlgGeo.Algebra.Homology.DGCategory.FunctorCategoryH0

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

The same comparison coherence normalizes a descended left-whiskered dg
counit to ordinary left whiskering of `h0Counit`, including the canonical
functor associator and right unitor.  This is kept at the generic adjunction
root so cone and twist consumers do not repeat the component calculation.

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

universe v u u' u''

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

/-- Descending a left-whiskered dg counit is ordinary left whiskering of the
`H⁰` counit, after the canonical compositor, associator, and unitor
comparisons.  The leading inverse compositor presents the source as
`(P.h0 ⋙ R.h0) ⋙ L.h0`. -/
theorem h0_whiskerLeft_counit {E : Type u''} [DGCategory.{v} E]
    (A : DGAdjunction L R) (P : DGFunctor E D) :
    (DGFunctor.h0CompIso (P.comp R) L).inv ≫
        DGFunctor.HomogeneousNatTrans.h0
          (DGFunctor.HomogeneousNatTrans.whiskerLeft P A.counit)
          (A.counit_isClosed.whiskerLeft P) =
      Functor.whiskerRight (DGFunctor.h0CompIso P R).hom L.h0 ≫
        (Functor.associator P.h0 R.h0 L.h0).hom ≫
          Functor.whiskerLeft P.h0 A.h0Counit ≫
            (Functor.rightUnitor P.h0).hom := by
  have hwhisk := DGFunctor.HomogeneousNatTrans.h0_whiskerLeft
    P A.counit A.counit_isClosed
  calc
    _ = (DGFunctor.h0CompIso (P.comp R) L).inv ≫
        ((DGFunctor.h0CompIso P (R.comp L)).hom ≫
          Functor.whiskerLeft P.h0
            (DGFunctor.HomogeneousNatTrans.h0 A.counit A.counit_isClosed) ≫
          (DGFunctor.h0CompIso P (DGFunctor.id D)).inv) :=
      congrArg (fun τ => (DGFunctor.h0CompIso (P.comp R) L).inv ≫ τ) hwhisk
    _ = _ := by
      have hcounit :
          DGFunctor.HomogeneousNatTrans.h0 A.counit A.counit_isClosed =
            (DGFunctor.h0CompIso R L).hom ≫ A.h0Counit ≫
              (DGFunctor.h0IdIso (C := D)).inv := by
        unfold h0Counit
        simp
      rw [hcounit, Functor.whiskerLeft_comp, Functor.whiskerLeft_comp]
      have hassoc :
          (DGFunctor.h0CompIso (P.comp R) L).hom ≫
              Functor.whiskerRight (DGFunctor.h0CompIso P R).hom L.h0 ≫
                (Functor.associator P.h0 R.h0 L.h0).hom =
            (DGFunctor.h0CompIso P (R.comp L)).hom ≫
              Functor.whiskerLeft P.h0 (DGFunctor.h0CompIso R L).hom := by
        simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
          Functor.isoWhiskerLeft_hom] using
            congrArg Iso.hom (DGFunctor.h0CompIso_assoc P R L)
      have hassoc' :
          (DGFunctor.h0CompIso (P.comp R) L).inv ≫
              (DGFunctor.h0CompIso P (R.comp L)).hom ≫
                Functor.whiskerLeft P.h0 (DGFunctor.h0CompIso R L).hom =
            Functor.whiskerRight (DGFunctor.h0CompIso P R).hom L.h0 ≫
              (Functor.associator P.h0 R.h0 L.h0).hom := by
        rw [← cancel_epi (DGFunctor.h0CompIso (P.comp R) L).hom]
        simp only [Iso.hom_inv_id_assoc]
        convert hassoc.symm using 1
        all_goals rfl
      have hunit :
          Functor.whiskerLeft P.h0 (DGFunctor.h0IdIso (C := D)).inv ≫
              (DGFunctor.h0CompIso P (DGFunctor.id D)).inv =
            (Functor.rightUnitor P.h0).hom := by
        have h := congrArg
          (fun e => (Functor.rightUnitor P.h0).hom ≫ e.inv)
          (DGFunctor.h0CompIso_comp_id P)
        simpa [Category.assoc] using h
      have h₁ := congrArg
        (fun τ => τ ≫ Functor.whiskerLeft P.h0 A.h0Counit ≫
          Functor.whiskerLeft P.h0 (DGFunctor.h0IdIso (C := D)).inv ≫
            (DGFunctor.h0CompIso P (DGFunctor.id D)).inv) hassoc'
      have h₂ := congrArg
        (fun τ =>
          Functor.whiskerRight (DGFunctor.h0CompIso P R).hom L.h0 ≫
            (Functor.associator P.h0 R.h0 L.h0).hom ≫
              Functor.whiskerLeft P.h0 A.h0Counit ≫ τ) hunit
      calc
        _ = Functor.whiskerRight (DGFunctor.h0CompIso P R).hom L.h0 ≫
              (Functor.associator P.h0 R.h0 L.h0).hom ≫
                Functor.whiskerLeft P.h0 A.h0Counit ≫
                  Functor.whiskerLeft P.h0
                    (DGFunctor.h0IdIso (C := D)).inv ≫
                    (DGFunctor.h0CompIso P (DGFunctor.id D)).inv := by
          simpa only [Category.assoc] using h₁
        _ = _ := by
          convert h₂ using 1
          all_goals simp only [DGFunctor.comp_id]

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

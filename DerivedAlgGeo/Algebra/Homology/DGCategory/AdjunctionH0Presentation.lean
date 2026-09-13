/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.AdjunctionH0

/-!
# Presenting a dg adjunction on ordinary categories

A strict dg adjunction `A : L ⊣ R` induces `A.h0 : L.h0 ⊣ R.h0`.  An
application usually does not use the literal homotopy categories, however: it
has equivalences `H⁰ C ≌ X` and `H⁰ D ≌ Y`, and names the transported
functors by ordinary functors `F : X ⥤ Y` and `G : Y ⥤ X`.

`DGAdjunction.H0Presentation` packages exactly those two functor
identifications.  Its `toAdjunction` is obtained only by composing Mathlib
adjunctions and transporting along Mathlib natural isomorphisms.  The
construction therefore introduces no second notion of transported
adjunction.  The unit and counit accessors expose the comparison maps needed
by cone and kernel presentations downstream.

The category equivalences are arguments rather than `Enhancement`s because
pretriangulated structure is irrelevant here.  Taking them to be the
comparison equivalences of two enhancements is the intended principal use.

## What this does not provide

The functor isomorphisms are supplied data.  In particular, this file does not
show that a geometric functor has a dg lift, construct a Fourier--Mukai
kernel, or turn an ordinary adjunction into a dg adjunction.  Nor does it
identify the transported adjunction with some independently chosen
adjunction: that requires compatibility of units or counits, not merely the
fact that the endpoint functors are isomorphic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v vX vY uC uD uX uY

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGAdjunction

variable {C : Type uC} {D : Type uD} {X : Type uX} {Y : Type uY}
  [DGCategory.{v} C] [DGCategory.{v} D]
  [Category.{vX} X] [Category.{vY} Y]
  {L : DGFunctor C D} {R : DGFunctor D C}

/-- The left functor obtained from `L.h0` by changing source and target along
the supplied category equivalences. -/
abbrev transportedH0Left (eC : H0 C ≌ X) (eD : H0 D ≌ Y) : X ⥤ Y :=
  (eC.inverse ⋙ L.h0) ⋙ eD.functor

/-- The right functor obtained from `R.h0` by changing source and target along
the supplied category equivalences.  Its parentheses match the right adjoint
produced by two applications of `Adjunction.comp`. -/
abbrev transportedH0Right (eC : H0 C ≌ X) (eD : H0 D ≌ Y) : Y ⥤ X :=
  eD.inverse ⋙ (R.h0 ⋙ eC.functor)

/-- Transport the adjunction induced by a strict dg adjunction through two
equivalences of ordinary categories.

This is the composite of `eC.symm.toAdjunction`, `A.h0`, and
`eD.toAdjunction`; all coherence is inherited from Mathlib's
`Adjunction.comp`. -/
noncomputable def transportedH0
    (A : DGAdjunction L R) (eC : H0 C ≌ X) (eD : H0 D ≌ Y) :
    transportedH0Left (L := L) eC eD ⊣
      transportedH0Right (R := R) eC eD :=
  (eC.symm.toAdjunction.comp A.h0).comp eD.toAdjunction

/-- Expand both `Adjunction.comp` steps in the transported unit, making the
original `h0Unit` visible between the source- and target-equivalence units. -/
theorem transportedH0_unit_app
    (A : DGAdjunction L R) (eC : H0 C ≌ X) (eD : H0 D ≌ Y) (Z : X) :
    (A.transportedH0 eC eD).unit.app Z =
      ((eC.symm.toAdjunction).unit.app Z ≫
        eC.symm.inverse.map (A.h0Unit.app (eC.symm.functor.obj Z))) ≫
          eC.symm.inverse.map
            (R.h0.map
              (eD.toAdjunction.unit.app
                ((eC.symm.functor ⋙ L.h0).obj Z))) := by
  rw [transportedH0, Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  rw [DGAdjunction.h0_unit]
  rw [Functor.comp_map]
  rfl

/-- Expand both `Adjunction.comp` steps in the transported counit, making the
original `h0Counit` visible between the source- and target-equivalence
counits. -/
theorem transportedH0_counit_app
    (A : DGAdjunction L R) (eC : H0 C ≌ X) (eD : H0 D ≌ Y) (Z : Y) :
    (A.transportedH0 eC eD).counit.app Z =
      eD.functor.map
          (L.h0.map
              ((eC.symm.toAdjunction).counit.app
                (R.h0.obj (eD.inverse.obj Z))) ≫
            A.h0Counit.app (eD.inverse.obj Z)) ≫
        eD.toAdjunction.counit.app Z := by
  rw [transportedH0, Adjunction.comp_counit_app, Adjunction.comp_counit_app]
  rw [DGAdjunction.h0_counit]
  rfl

/-- Data presenting two dg functors, after passage to `H⁰` and transport
through category equivalences, by named ordinary functors.

The data depends only on the endpoint functors.  A particular adjunction
between them is supplied later to `toAdjunction`, so the same presentation may
be reused for more than one adjunction structure. -/
structure H0Presentation
    (eC : H0 C ≌ X) (eD : H0 D ≌ Y)
    (F : X ⥤ Y) (G : Y ⥤ X) where
  /-- Identification of the transported left dg functor with its ordinary
  presentation. -/
  leftIso : transportedH0Left (L := L) eC eD ≅ F
  /-- Identification of the transported right dg functor with its ordinary
  presentation. -/
  rightIso : transportedH0Right (R := R) eC eD ≅ G

namespace H0Presentation

variable {eC : H0 C ≌ X} {eD : H0 D ≌ Y}
  {F : X ⥤ Y} {G : Y ⥤ X}
  (P : H0Presentation (L := L) (R := R) eC eD F G)

/-- The ordinary adjunction presented by `P`.

Mathlib first transports the composed `H⁰` adjunction along `leftIso`, then
along `rightIso`. -/
noncomputable def toAdjunction (A : DGAdjunction L R) : F ⊣ G :=
  (A.transportedH0 eC eD).ofNatIsoLeft P.leftIso |>.ofNatIsoRight P.rightIso

/-- The presented unit is the transported `H⁰` unit followed by the two
stored functor comparisons. -/
theorem toAdjunction_unit (A : DGAdjunction L R) :
    (P.toAdjunction A).unit =
      ((A.transportedH0 eC eD).unit ≫
        Functor.whiskerRight P.leftIso.hom
          (transportedH0Right (R := R) eC eD)) ≫
            Functor.whiskerLeft F P.rightIso.hom :=
  rfl

/-- The presented counit is the inverse right comparison, then the inverse
left comparison, followed by the transported `H⁰` counit.  This is the
normal form consumed by a counit-cone or counit-kernel presentation. -/
theorem toAdjunction_counit (A : DGAdjunction L R) :
    (P.toAdjunction A).counit =
      Functor.whiskerRight P.rightIso.inv F ≫
        Functor.whiskerLeft (transportedH0Right (R := R) eC eD) P.leftIso.inv ≫
          (A.transportedH0 eC eD).counit :=
  rfl

/-- Pointwise normal form of the presented unit. -/
theorem toAdjunction_unit_app (A : DGAdjunction L R) (Z : X) :
    (P.toAdjunction A).unit.app Z =
      (A.transportedH0 eC eD).unit.app Z ≫
        (transportedH0Right (R := R) eC eD).map (P.leftIso.hom.app Z) ≫
          P.rightIso.hom.app (F.obj Z) := by
  rw [P.toAdjunction_unit A]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc]
  rfl

/-- Pointwise normal form of the presented counit. -/
theorem toAdjunction_counit_app (A : DGAdjunction L R) (Z : Y) :
    (P.toAdjunction A).counit.app Z =
      F.map (P.rightIso.inv.app Z) ≫
        P.leftIso.inv.app
          ((transportedH0Right (R := R) eC eD).obj Z) ≫
          (A.transportedH0 eC eD).counit.app Z := by
  rw [P.toAdjunction_counit A]
  rfl

end H0Presentation

end DGAdjunction

end CategoryTheory

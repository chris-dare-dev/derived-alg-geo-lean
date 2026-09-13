/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.FunctorCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Functor
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Shift
import DerivedAlgGeo.CategoryTheory.Triangulated.ShiftFunctor

/-!
# The dg shift of a functor computes the `H⁰` shift

`DGFunctor.shiftedFunctor` shifts a dg functor by `n`, and `H0.shiftFunctor`
shifts an object of `H⁰` by `n`.  Both are built from the same choice, namely
`IsPretriangulated.exists_shift`, so they agree:

`H⁰ (F[n]) = H⁰ F ⋙ (-)[n]`,

The object equality is `rfl`; the morphism equality is the second computation
lemma below.  The resulting functor equality and its natural-isomorphism
wrapper make ordinary categorical properties such as equivalence and
triangulatedness reusable for shifted dg functors.

## Why it is not just `rfl` on morphisms

Two things differ, and both are harmless.  The shifted functor carries the
Koszul sign `(-1)^(n p)`, which at the degree `p = 0` of an `H⁰` morphism is
`+1`.  And the shifted functor's action is `IsShiftBy.shiftMap` at degree
zero, while the `H⁰` shift's is `IsShiftBy.mapShift`; those are the same map,
but `shiftMap` indexes its middle composite by `n + 0` where `mapShift` uses
`n`, and for a variable `n` that is only propositionally an equality.
`IsShiftBy.shiftMap_zero_eq_mapShift` crosses it.

## What this is for

It makes "the cotwist is the shift of the cone functor" a statement about the
dg functor rather than only about each value: the first vertex of an inversely
rotated cone triangle is `Z⟦-1⟧` in `H⁰`, and by the object lemma below that
is the value of the dg shifted functor.

The equality and natural isomorphism are categorical interfaces.  The
sign-correct `CommShift` and exactness packages below transport through that
interface; the two computation lemmas remain available for strict objectwise
formulas.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v vX vY u u' uX uY

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]
  [IsPretriangulated D]

/-- **On objects, the dg shifted functor is the `H⁰` shift.**  Both choose the
shifted object with `IsPretriangulated.exists_shift`, so this is `rfl`.

Not `@[simp]`: `h0_obj` and `shiftedFunctor_obj` both rewrite inside this
statement's own left-hand side, so it is not in simp normal form.  Use it with
`rw`. -/
theorem shiftedFunctor_h0_obj (F : DGFunctor C D) (n : ℤ) (X : H0 C) :
    (F.shiftedFunctor n).h0.obj X =
      (CategoryTheory.shiftFunctor (H0 D) n).obj (F.h0.obj X) :=
  rfl

/-- **On morphisms too.**  The Koszul sign is `+1` because an `H⁰` morphism has
degree zero, and the two transports agree by
`IsShiftBy.shiftMap_zero_eq_mapShift`. -/
@[simp]
theorem shiftedFunctor_h0_map (F : DGFunctor C D) (n : ℤ) {X Y : H0 C}
    (f : X ⟶ Y) :
    (F.shiftedFunctor n).h0.map f =
      (CategoryTheory.shiftFunctor (H0 D) n).map (F.h0.map f) := by
  induction f using Quotient.ind with
  | _ f =>
    refine congrArg (fun z => H0.homMk (C := D) z) (Subtype.ext ?_)
    show (n * 0).negOnePow •
        (F.shiftWitness n (H0.of C X)).shiftMap (F.shiftWitness n (H0.of C Y)) 0
          (F.map 0 (f : (dgHom (H0.of C X) (H0.of C Y)).X 0)) =
      IsShiftBy.mapShift (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) n)
        (IsPretriangulated.shiftWitness D (F.obj (H0.of C Y)) n)
        (F.map 0 (f : (dgHom (H0.of C X) (H0.of C Y)).X 0))
    rw [mul_zero, Int.negOnePow_zero, one_smul,
      IsShiftBy.shiftMap_zero_eq_mapShift]
    -- The two witnesses are the same choice: both are
    -- `(IsPretriangulated.exists_shift (F.obj X) n).choose_spec.some`.
    rfl

/-- The object and morphism computations assemble into an equality of ordinary
functors. -/
theorem shiftedFunctor_h0_eq (F : DGFunctor C D) (n : ℤ) :
    (F.shiftedFunctor n).h0 =
      F.h0 ⋙ CategoryTheory.shiftFunctor (H0 D) n := by
  exact Functor.hext (fun _ => rfl) (fun X Y f =>
    heq_of_eq (F.shiftedFunctor_h0_map n f))

/-- **The dg shift computes the pointwise shift on `H⁰`, functorially.**

This categorical interface packages `shiftedFunctor_h0_eq` as a natural
isomorphism for consumers that should transport structure through isomorphism
rather than rewrite functors. -/
noncomputable def shiftedFunctorH0Iso (F : DGFunctor C D) (n : ℤ) :
    (F.shiftedFunctor n).h0 ≅
      F.h0 ⋙ CategoryTheory.shiftFunctor (H0 D) n :=
  eqToIso (F.shiftedFunctor_h0_eq n)

section Transport

variable {X : Type uX} {Y : Type uY}
  [Category.{vX} X] [Category.{vY} Y]

/-- Transporting `H⁰` of a shifted dg functor through ordinary equivalences
agrees with transporting `H⁰` first and then shifting in the target.

Only the forward target equivalence needs a shift comparison: the shift occurs
after `H⁰ F`, so no `CommShift` structure is required on the source
equivalence. -/
noncomputable def transportedShiftedFunctorH0Iso (F : DGFunctor C D) (n : ℤ)
    (eC : H0 C ≌ X) (eD : H0 D ≌ Y) [HasShift Y ℤ]
    [eD.functor.CommShift ℤ] :
    (eC.inverse ⋙ (F.shiftedFunctor n).h0) ⋙ eD.functor ≅
      ((eC.inverse ⋙ F.h0) ⋙ eD.functor) ⋙ shiftFunctor Y n :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft eC.inverse (F.shiftedFunctorH0Iso n))
      eD.functor ≪≫
    Functor.associator eC.inverse
      (F.h0 ⋙ shiftFunctor (H0 D) n) eD.functor ≪≫
    Functor.isoWhiskerLeft eC.inverse
      (Functor.associator F.h0 (shiftFunctor (H0 D) n) eD.functor) ≪≫
    (Functor.associator eC.inverse F.h0
      (shiftFunctor (H0 D) n ⋙ eD.functor)).symm ≪≫
    Functor.isoWhiskerLeft (eC.inverse ⋙ F.h0)
      (eD.functor.commShiftIso n) ≪≫
    (Functor.associator (eC.inverse ⋙ F.h0) eD.functor
      (shiftFunctor Y n)).symm

end Transport

/-- If `H⁰ F` is an equivalence, then so is `H⁰` of every shifted dg functor.

This is only an ordinary categorical conclusion; it neither asserts that the
shifted dg functor is a quasi-equivalence nor supplies triangulatedness. -/
theorem shiftedFunctor_h0_isEquivalence (F : DGFunctor C D) (n : ℤ)
    (hF : F.h0.IsEquivalence) : (F.shiftedFunctor n).h0.IsEquivalence := by
  letI := hF
  haveI : (F.h0 ⋙ CategoryTheory.shiftFunctor (H0 D) n).IsEquivalence :=
    inferInstance
  exact Functor.isEquivalence_of_iso (F.shiftedFunctorH0Iso n).symm

/-- The ordinary equivalence on `H⁰` induced from an equivalence `H⁰ F` after
shifting the dg functor. -/
noncomputable def shiftedFunctorH0Equivalence (F : DGFunctor C D) (n : ℤ)
    (hF : F.h0.IsEquivalence) : H0 C ≌ H0 D :=
  letI := F.shiftedFunctor_h0_isEquivalence n hF
  (F.shiftedFunctor n).h0.asEquivalence

section Exactness

variable {A : Type u} {B : Type u'} [DGCategory.{v} A] [DGCategory.{v} B]
  [IsPretriangulated A] [IsPretriangulated B]

set_option backward.isDefEq.respectTransparency false in
/-- The sign-correct shift comparison on `H⁰` of a shifted dg functor.

It is obtained by composing the canonical comparison on `H⁰(F)` with the
signed comparison on `[n]`, then transporting that structure across
`shiftedFunctorH0Iso`.  The result is explicit rather than a global instance,
so consumers control which shift comparison is in scope. -/
@[reducible]
noncomputable def shiftedFunctorH0CommShift (F : DGFunctor A B) (n : ℤ)
    (hF : PreservesShifts F) : (F.shiftedFunctor n).h0.CommShift ℤ := by
  letI : F.h0.CommShift ℤ :=
    commShift (C := A) (D := B) F hF
  letI : (shiftFunctor (H0 B) n).CommShift ℤ :=
    Pretriangulated.shiftFunctorCommShift (H0 B) n
  letI : (F.h0 ⋙ shiftFunctor (H0 B) n).CommShift ℤ := inferInstance
  exact Functor.CommShift.ofIso (F.shiftedFunctorH0Iso n).symm ℤ

set_option backward.isDefEq.respectTransparency false in
/-- A dg functor remains exact on `H⁰` after every integral dg shift.  The
shift argument selects the comparison used by `shiftedFunctorH0CommShift`;
cone preservation is automatic for every dg functor.

The proof composes the exact functor `H⁰(F)` with the sign-correct exact
ordinary shift `[n]`, then transports exactness across
`shiftedFunctorH0Iso`. -/
theorem shiftedFunctorH0IsTriangulated (F : DGFunctor A B) (n : ℤ)
    (hShift : PreservesShifts F) :
    letI : (F.shiftedFunctor n).h0.CommShift ℤ :=
      shiftedFunctorH0CommShift F n hShift
    (F.shiftedFunctor n).h0.IsTriangulated := by
  letI : F.h0.CommShift ℤ :=
    commShift (C := A) (D := B) F hShift
  letI : F.h0.IsTriangulated :=
    isTriangulated_of_preservesShifts_and_chosenCones
      (C := A) (D := B) F hShift (preservesChosenCones F)
  letI : (shiftFunctor (H0 B) n).CommShift ℤ :=
    Pretriangulated.shiftFunctorCommShift (H0 B) n
  letI : (shiftFunctor (H0 B) n).IsTriangulated :=
    Pretriangulated.shiftFunctorIsTriangulated (H0 B) n
  letI : (F.h0 ⋙ shiftFunctor (H0 B) n).CommShift ℤ := inferInstance
  letI : (F.h0 ⋙ shiftFunctor (H0 B) n).IsTriangulated := inferInstance
  let e := (F.shiftedFunctorH0Iso n).symm
  letI : (F.shiftedFunctor n).h0.CommShift ℤ :=
    shiftedFunctorH0CommShift F n hShift
  haveI : NatTrans.CommShift e.hom ℤ := by
    exact Functor.CommShift.ofIso_compatibility e ℤ
  exact Functor.isTriangulated_of_iso e

end Exactness

end DGFunctor

end CategoryTheory

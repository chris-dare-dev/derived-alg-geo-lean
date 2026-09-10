/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.FunctorCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Shift

/-!
# The dg shift of a functor computes the `H⁰` shift

`DGFunctor.shiftedFunctor` shifts a dg functor by `n`, and `H0.shiftFunctor`
shifts an object of `H⁰` by `n`.  Both are built from the same choice, namely
`IsPretriangulated.exists_shift`, so they agree:

`H⁰ (F[n]) = H⁰ F ⋙ (-)[n]`,

on objects by `rfl` and on morphisms by the two lemmas below.

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

## What is not claimed

No equality of functors.  `Functor.ext` would need the object equality
transported across the morphism equality, and nothing here needs it; the two
computation lemmas are what consumers rewrite with.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

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

end DGFunctor

end CategoryTheory

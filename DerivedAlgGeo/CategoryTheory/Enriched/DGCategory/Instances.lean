/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Ring.Basic
import DerivedAlgGeo.CategoryTheory.Enriched.DGCategory.Basic

/-!
# A non-vacuous dg category

`DGCategory` is a structure with five axioms, and a structure with five axioms
is worth nothing until something satisfies them. This file exhibits an instance
on an arbitrary object type, so the axiom set is proved consistent before
anything is built on top of it.

`Const X` has `X` as its objects and, between any two of them, the cochain
complex that is `ℤ` in every degree with zero differential. Composition is
multiplication and the identity is `1`. Associativity is `mul_assoc` and the
unit laws are `one_mul` and `mul_one`, so those three axioms have content. The
differential is zero, so the Leibniz rule and the cocycle condition hold for
the uninteresting reason — which is the honest thing to say about them. A
non-zero differential waits for `C^dg` in `dg-enhancements-e4`.

## An idiom this file establishes

`AddCommGrpCat.of ℤ`'s carrier is not transparent to instance search, so a goal
stated on `↑((constComplex).X p)` cannot use `mul_assoc`: the `Semigroup`
instance is not found. Two things work. For a term proof, pin the type on the
lemma — `mul_assoc (G := ℤ) f g h`. For a tactic proof, bind the arguments at
type `ℤ` in the field's lambda — `fun _ q _ _ _ _ (f : ℤ) (g : ℤ) => ...` —
after which the goal is about `ℤ` and ordinary `simp` works.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u


namespace CategoryTheory

/-- The cochain complex that is `ℤ` in every degree, with zero differential. -/
@[simps]
def constComplex : CochainComplex AddCommGrpCat.{0} ℤ where
  X _ := AddCommGrpCat.of ℤ
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/-- Objects for the dg category `constComplex` presents. A type synonym, so
that giving it a `DGCategory` instance does not attach one to `X` itself. -/
def Const (X : Type u) : Type u := X

namespace Const

instance dgCategory (X : Type u) : DGCategory.{0} (Const X) where
  dgHom _ _ := constComplex
  dgId _ := (1 : ℤ)
  dgComp _ _ _ _ := AddMonoidHom.mul (R := ℤ)
  dgComp_assoc _ _ _ _ _ _ _ _ _ f g h := mul_assoc (G := ℤ) f g h
  dgId_comp _ f := one_mul (M := ℤ) f
  dgComp_id _ f := mul_one (M := ℤ) f
  dgId_cocycle _ := rfl
  dgComp_leibniz := fun _ q _ _ _ _ (f : ℤ) (g : ℤ) => by
    show (0 : ℤ) = f * (0 : ℤ) + q.negOnePow • ((0 : ℤ) * g)
    simp

end Const

end CategoryTheory

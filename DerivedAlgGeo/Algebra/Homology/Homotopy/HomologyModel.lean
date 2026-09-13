/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Zero-differential homology models

This file packages the homology objects of a cochain complex in an abelian
category as a new complex with zero differential.  It makes no formality
claim: an equivalence with the original complex requires additional splitting
hypotheses and belongs in a specialization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

open CategoryTheory

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The zero-differential complex whose object in degree `i` is the homology of
`K` in degree `i`. -/
noncomputable def homologyModel (K : CochainComplex A ℤ) : CochainComplex A ℤ :=
  CochainComplex.of (fun i => K.homology i) (fun _ => 0) (fun _ => by simp)

@[simp]
lemma homologyModel_X (K : CochainComplex A ℤ) (i : ℤ) :
    (homologyModel K).X i = K.homology i :=
  rfl

@[simp]
lemma homologyModel_d (K : CochainComplex A ℤ) (i j : ℤ) :
    (homologyModel K).d i j = 0 := by
  by_cases hij : i + 1 = j
  · subst j
    change CochainComplex.of.d (fun n => K.homology n) (fun _ => 0)
      i (i + 1) = 0
    rw [CochainComplex.of_d]
  · exact (homologyModel K).shape i j (by simpa [ComplexShape.up] using hij)

end CochainComplex

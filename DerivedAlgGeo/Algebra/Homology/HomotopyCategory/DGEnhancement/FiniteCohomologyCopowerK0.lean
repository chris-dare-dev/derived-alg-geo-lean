/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.FiniteCohomologyCopower
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Biproduct
import Mathlib.Algebra.Homology.EulerCharacteristic

/-!
# Grothendieck classes of scalar-linear copowers

A supplied finite cohomology presentation reduces a scalar-linear copower to
a finite biproduct of shifts.  Finite-free homology then makes its
Grothendieck class the homological Euler characteristic of the coefficient
complex times the class of the object.

This result consumes the presentation as explicit data.  It does not infer
formality or a finite presentation from bounded or finite-dimensional
homology.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CochainComplex.FiniteCohomologyPresentation

open CategoryTheory CategoryTheory.DGCategoryStruct CategoryTheory.DGCategory
  CategoryTheory.Limits CategoryTheory.Triangulated
open scoped BigOperators

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {k : Type v} [CommRing k] [Nontrivial k] [StrongRankCondition k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HasLinearCopowers k C]
  {K : CochainComplex (ModuleCat.{v} k) ℤ}

/-- A supplied finite cohomology presentation with finite-free homology
computes the class of the selected scalar-linear copower by Mathlib's
homological Euler characteristic. -/
theorem linearCopowerK₀Of [IsPretriangulated C]
    (P : CochainComplex.FiniteCohomologyPresentation K)
    [∀ i : {i // i ∈ P.degrees}, Module.Free k (K.homology i.1)]
    [∀ i : {i // i ∈ P.degrees}, Module.Finite k (K.homology i.1)]
    (X : C) :
    K₀.of (H0 C) (show H0 C from linearCopowerObj (C := C) K X) =
      K.homologyEulerChar • K₀.of (H0 C) (show H0 C from X) := by
  have hsupport :
      GradedObject.finrankSupport (fun i => K.homology i) ⊆ P.degrees := by
    intro i hi
    rw [GradedObject.finrankSupport, Function.mem_support] at hi
    by_contra hmem
    haveI : Subsingleton (K.homology i) :=
      ModuleCat.isZero_iff_subsingleton.mp (P.isZero_homology_of_not_mem i hmem)
    exact hi Module.finrank_zero_of_subsingleton
  have heuler :=
    HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
      K P.degrees hsupport
  calc
    K₀.of (H0 C) (show H0 C from linearCopowerObj (C := C) K X) =
        K₀.of (H0 C) (⨁ fun i : {i // i ∈ P.degrees} =>
          ⨁ fun _ : Fin (Module.finrank k (K.homology i.1)) =>
            (show H0 C from X)⟦-i.1⟧) :=
      K₀.of_iso (H0 C) (P.linearCopowerFinrankIso X)
    _ = ∑ i : {i // i ∈ P.degrees},
        K₀.of (H0 C) (⨁ fun _ : Fin (Module.finrank k (K.homology i.1)) =>
          (show H0 C from X)⟦-i.1⟧) :=
      K₀.of_biproduct (H0 C) _
    _ = ∑ i : {i // i ∈ P.degrees},
        ((i.1.negOnePow : ℤ) * Module.finrank k (K.homology i.1)) •
          K₀.of (H0 C) (show H0 C from X) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [K₀.of_biproduct]
      simp_rw [K₀.of_shift_int]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [← Int.coe_negOnePow ℤ (-i.1), Int.negOnePow_neg]
      rw [← Nat.cast_smul_eq_nsmul ℤ, ← mul_smul, mul_comm]
      rfl
    _ = (∑ i ∈ P.degrees,
        (i.negOnePow : ℤ) * Module.finrank k (K.homology i)) •
          K₀.of (H0 C) (show H0 C from X) := by
      rw [← Finset.sum_smul]
      exact congrArg (· • K₀.of (H0 C) (show H0 C from X))
        (Finset.sum_attach P.degrees fun i ↦
          (i.negOnePow : ℤ) * Module.finrank k (K.homology i))
    _ = K.homologyEulerChar • K₀.of (H0 C) (show H0 C from X) := by
      simpa using congrArg (· • K₀.of (H0 C) (show H0 C from X)) heuler.symm

end CochainComplex.FiniteCohomologyPresentation

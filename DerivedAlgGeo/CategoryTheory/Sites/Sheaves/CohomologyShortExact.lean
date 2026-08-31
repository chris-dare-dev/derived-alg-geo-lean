/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Vanishing `H¹` makes global sections surjective

For a short exact sequence of abelian sheaves whose first term has vanishing
degree-one cohomology, global sections of the second term surject onto global
sections of the third.

## Why this is stated here rather than in the geometry

`Sheaf.H F n` is `Ext (constantSheaf ℤ) F n`, so this is the covariant `Ext`
long exact sequence read at `n = 0` and nothing else. Nothing about schemes,
affines, or quasi-coherence enters, and the geometric consumer supplies only the
vanishing hypothesis. Keeping the generic statement generic is what lets the
affine-vanishing calculation and the quasi-coherence argument stay in separate
files.

## Main results

* `CategoryTheory.Sheaf.H_map_surjective_of_subsingleton_H_one`;
* `CategoryTheory.Sheaf.sections_surjective_of_subsingleton_H_one`.
-/

universe w' w v u

namespace CategoryTheory

open Abelian Opposite Limits

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}

/-- **Degree-zero cohomology is surjective when `H¹` of the sub vanishes.**

The tail of the covariant `Ext` long exact sequence,

`H F₂ 0 → H F₃ 0 → H F₁ 1`,

read with the last term subsingleton. `Ext.covariant_sequence_exact₃` is the
exactness; the connecting composite is forced to zero because there is nowhere
for it to land. -/
theorem H_map_surjective_of_subsingleton_H_one (hS : S.ShortExact)
    [Subsingleton (H S.X₁ 1)] :
    Function.Surjective (H.map S.g 0) := by
  intro x₃
  obtain ⟨x₂, hx₂⟩ :=
    Ext.covariant_sequence_exact₃ _ hS x₃ (n₁ := 1) rfl (by subsingleton)
  exact ⟨x₂, hx₂⟩

variable {T : C} (hT : IsTerminal T)

include hT in
/-- **Global sections are surjective when `H¹` of the sub vanishes.**

`H.equiv₀` identifies degree-zero cohomology with evaluation at a terminal
object, and `H.equiv₀_naturality` says that identification is natural, so
surjectivity transports across it. -/
theorem sections_surjective_of_subsingleton_H_one (hS : S.ShortExact)
    [Subsingleton (H S.X₁ 1)] :
    Function.Surjective (S.g.hom.app (op T)) := by
  intro y
  obtain ⟨x₂, hx₂⟩ := H_map_surjective_of_subsingleton_H_one hS
    ((H.equiv₀ S.X₃ hT).symm y)
  refine ⟨H.equiv₀ S.X₂ hT x₂, ?_⟩
  calc S.g.hom.app (op T) (H.equiv₀ S.X₂ hT x₂)
      = H.equiv₀ S.X₃ hT (H.map S.g 0 x₂) :=
        H.equiv₀_naturality (f := S.g) hT x₂
    _ = H.equiv₀ S.X₃ hT ((H.equiv₀ S.X₃ hT).symm y) := by rw [hx₂]
    _ = y := (H.equiv₀ S.X₃ hT).apply_symm_apply y

end Sheaf

end CategoryTheory

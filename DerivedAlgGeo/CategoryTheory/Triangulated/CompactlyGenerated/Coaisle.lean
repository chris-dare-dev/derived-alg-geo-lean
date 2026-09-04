/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.FiniteSupport

/-!
# Coaisles of compactly generated t-structures

The aisle of a compactly generated t-structure is the coproduct-and-extension closure of its
generators, so the degree-one coaisle is the right orthogonal of that closure.  A coproduct of
objects of the coaisle is again right orthogonal to every generator, because a map from a
compact generator into a coproduct is a finite sum of maps into the summands
(`IsCompactObject.exists_finite_sum`), and right orthogonality to a fixed object passes from
the generators to their closure by the same induction as in
`TStructure.coprodBoundedAisle_rightOrthogonal_of_isGE` (Lemma A.14 of arXiv:2607.28411v1).

## Main results

* `TStructure.IsCompactlyGeneratedBy.isGE_one_coproduct`.

## References

* arXiv:2607.28411v1, Definition A.11 and Lemma A.14.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u

namespace CategoryTheory.Triangulated.TStructure.IsCompactlyGeneratedBy

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {t : TStructure C} {G : ObjectProperty C}

/-- The degree-one coaisle of a compactly generated t-structure is closed under coproducts.

Degree one and not a general `n` because `IsCompactlyGeneratedBy` fixes the aisle at degree
zero (`le_zero_eq`), so `t.isGE_iff_orthogonal 0 1` is the pair that matches it; it is also the
degree the recognition formula (A.8) uses, through
`Slicing.IndExtensions.isGE_one_iff_ltProp`.  The index universe is `Type 0` because
`IsCompactObject.exists_finite_sum` is, and that lemma is pinned there by the `DirectSum`
bridge in its proof; generalizing this one means generalizing that one first. -/
theorem isGE_one_coproduct (h : t.IsCompactlyGeneratedBy.{0} G) {ι : Type} (X : ι → C)
    [HasCoproduct X] (hX : ∀ i, t.IsGE (X i) 1) : t.IsGE (∐ X) 1 := by
  rw [t.isGE_iff_orthogonal 0 1 rfl]
  intro Z f hZ
  have hZ' : G.coprodClosure.{0} Z := by
    rw [← h.le_zero_eq]
    exact hZ.le
  clear hZ
  induction hZ' with
  | of_mem Z hZ =>
      obtain ⟨s, g, rfl⟩ := IsCompactObject.exists_finite_sum (h.compact Z hZ) X f
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [t.zero_of_isLE_of_isGE (g i) 0 1 (by omega) (h.isLE_zero_of_generator hZ) (hX i),
        zero_comp]
  | of_iso e _ ih =>
      rw [← cancel_epi e.hom, comp_zero]
      exact ih (e.hom ≫ f)
  | of_coproduct c hc _ ih =>
      apply hc.hom_ext
      intro j
      rw [comp_zero]
      exact ih j (c.ι.app j ≫ f)
  | of_extension T hT _ _ ih₁ ih₃ =>
      have hzero : T.mor₁ ≫ f = 0 := ih₁ (T.mor₁ ≫ f)
      obtain ⟨k, rfl⟩ := Triangle.yoneda_exact₂ T hT f hzero
      rw [ih₃ k, comp_zero]

end CategoryTheory.Triangulated.TStructure.IsCompactlyGeneratedBy

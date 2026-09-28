/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite support in a supplied coproduct

For a particular coproduct whose summands vanish outside a finite set, the sum
of its canonical projection-inclusion endomorphisms is the identity. Thus
incoming maps are determined by those finitely many projections. The converse
identifies the exact support premise needed by this finite identity. No
ambient finite-coproduct assumption or replacement coproduct is introduced.

## Main results

* `CategoryTheory.Limits.Sigma.sum_π_ι_eq_id_of_isZero_all` gives the finite
  projection-inclusion identity for every chosen equality instance;
  `CategoryTheory.Limits.Sigma.isZero_of_sum_π_ι_eq_id_of_not_mem_all`
  and `CategoryTheory.Limits.Sigma.sum_π_ι_eq_id_iff_isZero_all` give its
  universal converse and characterization;
  `CategoryTheory.Limits.Sigma.sum_π_ι_eq_id_of_isZero` selects one without
  requiring a caller instance, and
  `CategoryTheory.Limits.Sigma.isZero_of_sum_π_ι_eq_id_of_not_mem` gives its converse.
* `CategoryTheory.Limits.Sigma.hom_ext_of_finite_support` compares incoming maps
  on the finite nonzero support.
* `CategoryTheory.Limits.Sigma.hom_eq_zero_of_finite_support` detects a zero
  incoming map.

## Implementation notes

The universal identity, converse, and iff preserve the caller's equality
instance, which determines the literal `CategoryTheory.Limits.Sigma.π`. Incoming-map extensionality
uses that identity. The three caller-free statements choose classical equality
as specializations of the universal results.

## References

Mathlib's `CategoryTheory.Limits.Sigma.π`,
`CategoryTheory.Limits.Sigma.ι_π_eq_id`, and
`CategoryTheory.Limits.Sigma.ι_π_of_ne` supply the projection laws.

## Tags

coproduct, finite support, projection, zero object
-/

open CategoryTheory Category
open scoped BigOperators

universe u v w

namespace CategoryTheory.Limits.Sigma

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I : Type w} (f : I → C) [HasCoproduct f]

/-! The universal results quantify over the equality instance so callers may
instantiate them with precisely the projections appearing in their statement. -/

/-- The identity holds for every equality decision procedure defining the
literal `CategoryTheory.Limits.Sigma.π`; finite support is the only restriction on summands. -/
lemma sum_π_ι_eq_id_of_isZero_all [DecidableEq I] (s : Finset I)
    (hz : ∀ i, i ∉ s → IsZero (f i)) :
    ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i = 𝟙 (∐ f) := by
  apply Sigma.hom_ext
  intro j
  rw [Preadditive.comp_sum, comp_id]
  by_cases hj : j ∈ s
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      rw [← assoc, Sigma.ι_π_of_ne _ hbj.symm, zero_comp]
    · exact fun h => False.elim (h hj)
  · have hjzero := (hz j hj).eq_zero_of_src (Sigma.ι f j)
    simp [hjzero]

/-- Compose the claimed identity with the inclusion of an omitted summand.
Every cross term vanishes by orthogonality, forcing that summand's identity
morphism to vanish. -/
lemma isZero_of_sum_π_ι_eq_id_of_not_mem_all [DecidableEq I] (s : Finset I)
    (hid : ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i = 𝟙 (∐ f))
    (j : I) (hj : j ∉ s) : IsZero (f j) := by
  have hι : Sigma.ι f j = 0 := by
    calc
      Sigma.ι f j = Sigma.ι f j ≫ ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i := by
        rw [hid, comp_id]
      _ = 0 := by
        rw [Preadditive.comp_sum]
        apply Finset.sum_eq_zero
        intro i hi
        rw [← assoc, Sigma.ι_π_of_ne _ (by aesop), zero_comp]
  rw [IsZero.iff_id_eq_zero, ← Sigma.ι_π_eq_id f j, hι, zero_comp]

/-- Combine the inclusion test for the forward identity with the omitted
summand obstruction for the converse, retaining the caller's projection
convention in both directions. -/
lemma sum_π_ι_eq_id_iff_isZero_all [DecidableEq I] (s : Finset I) :
    (∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i = 𝟙 (∐ f)) ↔
      ∀ i, i ∉ s → IsZero (f i) := by
  exact ⟨fun hid i hi => isZero_of_sum_π_ι_eq_id_of_not_mem_all f s hid i hi,
    fun hz => sum_π_ι_eq_id_of_isZero_all f s hz⟩

section ChosenDecidableEq
variable [DecidableEq I]

/-- Compose with the finite projection-inclusion identity for the given
projection convention to compare incoming maps on their nonzero support. -/
lemma hom_ext_of_finite_support (s : Finset I)
    (hz : ∀ i, i ∉ s → IsZero (f i)) {A : C} {x y : A ⟶ ∐ f}
    (h : ∀ i ∈ s, x ≫ Sigma.π f i = y ≫ Sigma.π f i) : x = y := by
  calc
    x = x ≫ ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i := by
      rw [sum_π_ι_eq_id_of_isZero_all f s hz, comp_id]
    _ = y ≫ ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i := by
      rw [Preadditive.comp_sum, Preadditive.comp_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← assoc, h i hi, assoc]
    _ = y := by rw [sum_π_ι_eq_id_of_isZero_all f s hz, comp_id]

/-- Specialize `CategoryTheory.Limits.Sigma.hom_ext_of_finite_support` to
comparison with the zero map.
The projection convention remains the caller's. -/
lemma hom_eq_zero_of_finite_support (s : Finset I)
    (hz : ∀ i, i ∉ s → IsZero (f i)) {A : C} (x : A ⟶ ∐ f)
    (h : ∀ i ∈ s, x ≫ Sigma.π f i = 0) : x = 0 := by
  apply hom_ext_of_finite_support f s hz
  intro i hi
  simpa using h i hi

end ChosenDecidableEq

section ClassicalProjection
open scoped Classical

/-- Specialize `CategoryTheory.Limits.Sigma.sum_π_ι_eq_id_of_isZero_all` using
classical equality so callers need not supply a decidability instance; the
universal theorem supplies the coproduct-inclusion argument. -/
lemma sum_π_ι_eq_id_of_isZero (s : Finset I)
    (hz : ∀ i, i ∉ s → IsZero (f i)) :
    ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i = 𝟙 (∐ f) :=
  sum_π_ι_eq_id_of_isZero_all f s hz

/-- Specialize
`CategoryTheory.Limits.Sigma.isZero_of_sum_π_ι_eq_id_of_not_mem_all` using
classical equality. The universal converse supplies the omitted-summand
argument. -/
lemma isZero_of_sum_π_ι_eq_id_of_not_mem (s : Finset I)
    (hid : ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i = 𝟙 (∐ f))
    (j : I) (hj : j ∉ s) : IsZero (f j) :=
  isZero_of_sum_π_ι_eq_id_of_not_mem_all f s hid j hj

/-- Specialize `CategoryTheory.Limits.Sigma.sum_π_ι_eq_id_iff_isZero_all` using
classical equality; the universal characterization contains the
omitted-summand obstruction. -/
lemma sum_π_ι_eq_id_iff_isZero (s : Finset I) :
    (∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i = 𝟙 (∐ f)) ↔
      ∀ i, i ∉ s → IsZero (f i) :=
  sum_π_ι_eq_id_iff_isZero_all f s

end ClassicalProjection
end CategoryTheory.Limits.Sigma

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Lifting an epimorphism along a separator

Let `G` be a separator of an abelian category and `π : M ⟶ N` an epimorphism. Some
subobject of `M` that is a quotient of a coproduct of copies of `G`, one for each
subobject of `N`, still maps onto `N`. This is Stacks, Lemma 19.12.1 (Tag 079J): the
size of the subobject is bounded in terms of `N` alone.

## Main definitions

None: this file proves properties of Mathlib's `CategoryTheory.IsSeparator`.

## Main results

* `CategoryTheory.IsSeparator.exists_jointlyEpi_comp_of_epi`: morphisms `G ⟶ M`, one
  for each subobject of `N`, whose composites with `π` are jointly epimorphic.
* `CategoryTheory.IsSeparator.exists_subobject_epi_of_epi`: Tag 079J, the image of the
  induced morphism from the coproduct.

## Implementation notes

The Stacks project bounds the cardinality of the subobject by that of a coproduct of
copies of `G` indexed by a set of the size of `N`. An abstract category has no
cardinality of objects, so the bound is the index type `Subobject N` itself. The first
statement needs no coproduct, so it applies when `Subobject N` is not small enough for
the coproduct to exist.

## References

* [The Stacks project, Tag 079J](https://stacks.math.columbia.edu/tag/079J)

## Tags

separator, generator, epimorphism, subobject, abelian category
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {G : C}

/-- Let `G` be a separator and `π : M ⟶ N` an epimorphism. There are morphisms `G ⟶ M`,
one for each subobject of `N`, whose composites with `π` are jointly epimorphic: for a
proper subobject `N'`, the chosen morphism composed with `π` does not factor through `N'`.
This is the construction in the proof of Stacks, Lemma 19.12.1 (Tag 079J). -/
theorem IsSeparator.exists_jointlyEpi_comp_of_epi (hG : IsSeparator G) {M N : C}
    (π : M ⟶ N) [Epi π] :
    ∃ f : Subobject N → (G ⟶ M),
      ∀ ⦃Z : C⦄ (a b : N ⟶ Z), (∀ N', f N' ≫ π ≫ a = f N' ≫ π ≫ b) → a = b := by
  have h (N' : Subobject N) : ∃ g : G ⟶ M, N' ≠ ⊤ → ¬ N'.Factors (g ≫ π) := by
    by_cases hN' : N' = ⊤
    · exact ⟨0, fun h => absurd hN' h⟩
    · by_contra! H
      apply hN'
      have hc : cokernel.π N'.arrow = 0 := by
        rw [← cancel_epi π, comp_zero]
        refine hG.def _ _ (fun g => ?_)
        rw [comp_zero, ← Category.assoc, ← Subobject.factorThru_arrow _ _ (H g).2,
          Category.assoc, cokernel.condition, comp_zero]
      have := Abelian.epi_of_cokernel_π_eq_zero _ hc
      have := isIso_of_mono_of_epi N'.arrow
      exact (Subobject.isIso_arrow_iff_eq_top N').1 this
  choose f hf using h
  refine ⟨f, fun Z a b hab => ?_⟩
  rw [← sub_eq_zero]
  by_contra hne
  have htop : kernelSubobject (a - b) ≠ ⊤ := fun htop => hne (by
    simpa using (kernelSubobject_factors_iff (a - b) (𝟙 N)).1
      (htop ▸ Subobject.top_factors (𝟙 N)))
  exact hf _ htop ((kernelSubobject_factors_iff (a - b) (f _ ≫ π)).2
    (by rw [Category.assoc, Preadditive.comp_sub, Preadditive.comp_sub, sub_eq_zero, hab]))

/-- **Stacks, Lemma 19.12.1 (Tag 079J).** Let `G` be a separator of an abelian category
and `π : M ⟶ N` an epimorphism. Some subobject `M'` of `M` maps onto `N` and is a
quotient of a coproduct of copies of `G` indexed by the subobjects of `N`. -/
@[stacks 079J]
theorem IsSeparator.exists_subobject_epi_of_epi (hG : IsSeparator G) {M N : C}
    (π : M ⟶ N) [Epi π] [HasCoproduct fun _ : Subobject N => G] :
    ∃ (M' : Subobject M) (p : (∐ fun _ : Subobject N => G) ⟶ (M' : C)),
      Epi p ∧ Epi (M'.arrow ≫ π) := by
  obtain ⟨f, hf⟩ := hG.exists_jointlyEpi_comp_of_epi π
  have : Epi (Sigma.desc f ≫ π) :=
    ⟨fun a b h => hf a b (fun N' => by simpa using Sigma.ι _ N' ≫= h)⟩
  refine ⟨imageSubobject (Sigma.desc f), factorThruImageSubobject _, inferInstance, ?_⟩
  have : Epi (factorThruImageSubobject (Sigma.desc f) ≫
      (imageSubobject (Sigma.desc f)).arrow ≫ π) := by
    rwa [imageSubobject_arrow_comp_assoc]
  exact epi_of_epi (factorThruImageSubobject _) _

end CategoryTheory

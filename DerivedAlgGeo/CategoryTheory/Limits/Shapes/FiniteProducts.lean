/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Coproducts of finitely supported families

A family of objects with only finitely many nonzero members has a coproduct when its finite
subfamily has a coproduct. The colimit cocone uses that subfamily's coproduct and zero maps
from objects outside its support.

## Main result

* `CategoryTheory.Limits.hasCoproduct_of_finite_support` constructs the coproduct of the full
  family from its finite support.

## Implementation notes

The finite subfamily supplies the apex. Its coproduct inclusions are extended by zero
maps outside the support, where `IsZero` makes every cocone leg unique.
An empty support is allowed.

## References

This extends Mathlib's `CategoryTheory.Limits.HasCoproduct` and
`CategoryTheory.Limits.Cofan` APIs for a finitely supported family.
-/

open CategoryTheory

universe u v w

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

private noncomputable def finiteSupportCofan {I : Type w} (X : I → C) (s : Finset I)
    [HasCoproduct (fun i : s => X i)] : Cofan X := by
  classical
  exact Cofan.mk (∐ fun i : s => X i)
    (fun i => if hi : i ∈ s then Sigma.ι (fun i : s => X i) ⟨i, hi⟩ else 0)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def finiteSupportCofanIsColimit {I : Type w} (X : I → C) (s : Finset I)
    [HasCoproduct (fun i : s => X i)]
    (hzero : ∀ i, i ∉ s → IsZero (X i)) : IsColimit (finiteSupportCofan X s) := by
  classical
  refine Cofan.IsColimit.mk _ (fun t => Sigma.desc (fun i : s => t.inj i)) ?_ ?_
  · intro t i
    by_cases hi : i ∈ s
    · simp [finiteSupportCofan, hi]
    · exact (hzero i hi).eq_of_src _ _
  · intro t m hm
    apply Sigma.hom_ext m (Sigma.desc (fun i : s => t.inj i))
    intro i
    rw [Sigma.ι_desc]
    simpa [finiteSupportCofan, i.property] using hm i

/-- Extend the coproduct cocone of a finite subfamily by zero maps on all other indices.
The `IsZero` hypothesis makes those other cocone legs unique, so the extended cocone is
colimiting, even when the finite support is empty. -/
theorem hasCoproduct_of_finite_support
    {I : Type w} (X : I → C) (s : Finset I) [HasCoproduct (fun i : s => X i)]
    (hzero : ∀ i, i ∉ s → IsZero (X i)) : HasCoproduct X :=
  ⟨⟨finiteSupportCofan X s, finiteSupportCofanIsColimit X s hzero⟩⟩

end CategoryTheory.Limits

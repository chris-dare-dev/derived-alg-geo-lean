/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Morphism properties stable under coproducts

`Sigma.map` of a family of morphisms in a class `W` stable under coproducts of that shape is
in `W`: it is `colimMap` of the family, and `MorphismProperty.colimMap` is Mathlib's statement
for a general colimit shape.  Mathlib inlines this one-liner where it needs it; it is named here
because the localization of a category along a coproduct-stable class uses it for the common
denominators of families of right fractions.

## Main results

* `MorphismProperty.sigma_map`: `Sigma.map` of a family in `W` is in `W`.
-/

open CategoryTheory Limits

universe w v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- `Sigma.map` of a family of morphisms in `W` is in `W` when `W` is stable under
coproducts of that shape. -/
theorem sigma_map (W : MorphismProperty C) {ι : Type w} [HasCoproductsOfShape ι C]
    [W.IsStableUnderCoproductsOfShape ι] {X Y : ι → C} (s : ∀ i, X i ⟶ Y i)
    (hs : ∀ i, W (s i)) : W (Limits.Sigma.map s) :=
  MorphismProperty.colimMap (W := W) _ (fun ⟨i⟩ => hs i)

end CategoryTheory.MorphismProperty
